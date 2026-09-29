-- Prove2me | solution 1 for DihedralWeightOne.weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/83e243b3-ffd5-583b-856f-d4574295121f

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Theorems.Thm_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DihedralWeightOne_weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

noncomputable section

namespace WeightOneLevelZero

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups ModularForm

theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g') = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ u)

theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

theorem ratArch_globalPoints_mapGL (ε : SL(2, ℤ)) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) =
      (ε : GL (Fin 2) ℝ) := by
  rw [ratArch_globalPoints]
  exact Matrix.SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) ε

theorem det_ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ((LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ)).det.val : ℝ) =
      (((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ) := by
  rw [ratArch_globalPoints, GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, eq_ratCast]

theorem exists_algebraMap_eq_of_mem_integralFiniteAdeles {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integralFiniteAdeles hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

theorem exists_mapGL_eq_of_mem_finiteIntegralGL2 {γ : GL (Fin 2) ℚ}
    (hint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hpos : 0 < ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ)) :
    ∃ δ : SL(2, ℤ), Matrix.SpecialLinearGroup.mapGL ℚ δ = γ := by
  rw [mem_finiteIntegralGL2_iff] at hint
  obtain ⟨hγ, hγinv⟩ := hint
  have hγ' : ∀ i j, ∃ n : ℤ, (n : ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) i j := fun i j =>
    exists_intCast_eq_of_mem_integralFiniteAdeles (by rw [← glFin_globalPoints_apply]; exact hγ i j)
  have hγinv' : ∀ i j, ∃ n : ℤ, (n : ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j :=
    fun i j => exists_intCast_eq_of_mem_integralFiniteAdeles (by
      rw [← glFin_globalPoints_apply, map_inv, map_inv]; exact hγinv i j)
  choose a ha using hγ'
  choose b hb using hγinv'
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => a i j with hA
  set B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => b i j with hB
  have hAmap : A.map (Int.castRingHom ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hA, ha]
  have hBmap : B.map (Int.castRingHom ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hB, hb]
  have hAB : A * B = 1 := by
    have hinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℚ) :=
      Matrix.map_injective (f := ⇑(Int.castRingHom ℚ)) Int.cast_injective
    apply hinj
    dsimp only
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _),
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdetAB : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdetQ : ((A.det : ℤ) : ℚ) = ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hAmap]
    exact (RingHom.map_det (Int.castRingHom ℚ) A)
  have hdetA : A.det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetAB with h1 | h1
    · exact h1
    · exfalso
      rw [← hdetQ, h1] at hpos
      norm_num at hpos
  refine ⟨⟨A, hdetA⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  change (algebraMap ℤ ℚ) (A i j) = _
  rw [← hAmap, Matrix.map_apply]
  rfl

theorem exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne {M : ℕ} (hM : M ≠ 0)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (γ : GL (Fin 2) ℚ) (h : AdelicGL2 (𝓞 ℚ) ℚ)
      (u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)),
      AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
          u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) ∧
            x = globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u := by
  obtain ⟨γ', hlev, hpos⟩ :=
    AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat (AdelicDock.ratLevel_ne_bot hM) x
  set y : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ' * x with hy
  set u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    AdelicLevel.glFin (𝓞 ℚ) ℚ y with hu
  refine ⟨γ'⁻¹, y * (AdelicDock.finEmbed (𝓞 ℚ) ℚ u)⁻¹, u, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel]
  · have hy_pos : LanglandsTunnell.ratArchGL2 y ∈ Matrix.GLPos (Fin 2) ℝ :=
      hpos default (IsTotallyReal.isReal default)
    rw [← map_inv, ratArch_mul, ratArch_finEmbed]
    simpa using hy_pos
  · exact (AdelicLevel.mem_levelOne_iff).mp hlev
  · rw [map_inv, hy]
    group

theorem pow_factorization_dvd_of_valued_le_idealBound {M : ℕ} (hM : M ≠ 0) (n : ℤ) (p : ℕ) [Fact p.Prime]
    (h : Valued.v ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (AdelicDock.padicPlace p)) ≤
      idealBound (𝓞 ℚ) (AdelicDock.ratLevel M) (AdelicDock.padicPlace p)) :
    ((p : ℤ) ^ M.factorization p) ∣ n := by
  have hL : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (AdelicDock.padicPlace p) =
      (n : (AdelicDock.padicPlace p).adicCompletion ℚ) := by
    change ((algebraMap ℚ ((AdelicDock.padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) n = _
    exact eq_intCast _ n
  have hR : AdelicDock.padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) = (n : (AdelicDock.padicPlace p).adicCompletion ℚ) := by
    rw [PadicInt.coe_intCast, map_intCast]
  have hcoe : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (AdelicDock.padicPlace p) =
      AdelicDock.padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) := hL.trans hR.symm
  rw [hcoe, AdelicDock.valued_coe_le_idealBound_iff p hM] at h
  rw [← PadicInt.norm_int_le_pow_iff_dvd]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr h

theorem natCast_dvd_of_mem_idealBall {M : ℕ} (hM : M ≠ 0) (n : ℤ)
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) :
    (M : ℤ) ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, ← Nat.factorization_prime_le_iff_dvd hM (Int.natAbs_ne_zero.mpr hn)]
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : ((p : ℤ) ^ M.factorization p) ∣ n :=
    pow_factorization_dvd_of_valued_le_idealBound hM n p (h (AdelicDock.padicPlace p))
  have hdvd' : p ^ M.factorization p ∣ n.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]; exact_mod_cast hdvd
  exact (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hn)).mp hdvd'

variable {M : ℕ}

theorem slash_eq (f : CuspForm (CongruenceSubgroup.Gamma1 M) 1) (ε : SL(2, ℤ))
    (hε : ε ∈ CongruenceSubgroup.Gamma1 M) :
    (⇑f) ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = ⇑f :=
  SlashInvariantForm.slash_action_eqn f (ε : GL (Fin 2) ℝ) ⟨ε, hε, rfl⟩

theorem apply_decomp₁ (hM : M ≠ 0) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    {γ : GL (Fin 2) ℚ} {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) :
    DihedralWeightOne.weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑f)
        (globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ k)
      = DihedralWeightOne.weightOneArchLift (⇑f) (LanglandsTunnell.ratArchGL2 h) := by
  obtain ⟨hleft, hlev, harch⟩ :=
    DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift hM (⇑f)
      (slash_eq f)
  rw [mul_assoc, hleft, hlev k hk, harch h hh hpos]

theorem slash_eq_nebentypus_smul {ε : DirichletCharacter ℂ M} {f : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hε : CuspForm.HasNebentypus ε f) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (⇑f) ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = ε ((γ 1 1 : ℤ) : ZMod M) • (⇑f) := by
  ext τ
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, hε γ hγ τ, Pi.smul_apply, smul_eq_mul]
  have hd : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hd0 : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [hd] at hd0 ⊢
  rw [_root_.zpow_neg, zpow_one]
  field_simp

theorem weightOneArchLift_coe_mul {ε : DirichletCharacter ℂ M} {f : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hε : CuspForm.HasNebentypus ε f) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    {g : GL (Fin 2) ℝ} (hg : 0 < (g.det.val : ℝ)) :
    DihedralWeightOne.weightOneArchLift (⇑f) ((γ : GL (Fin 2) ℝ) * g)
      = ε ((γ 1 1 : ℤ) : ZMod M) * DihedralWeightOne.weightOneArchLift (⇑f) g := by
  have hdet : (((γ : GL (Fin 2) ℝ) * g).det.val : ℝ) = (g.det.val : ℝ) := by
    rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
    have : ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.det_coe]
    rw [this, one_mul]
  unfold DihedralWeightOne.weightOneArchLift
  rw [hdet, SlashAction.slash_mul, slash_eq_nebentypus_smul hε hγ, ModularForm.smul_slash, UpperHalfPlane.σ,
    if_pos hg, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rfl

theorem exists_sl_of_levelZero (hM : M ≠ 0)
    {γ γ' : GL (Fin 2) ℚ} {h h' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {u u' : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hu' : u' ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) (hh' : glFin (𝓞 ℚ) ℚ h' = 1)
    (hpos' : LanglandsTunnell.ratArchGL2 h' ∈ GLPos (Fin 2) ℝ)
    (hx : globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u =
      globalPoints (𝓞 ℚ) ℚ γ' * h' * AdelicDock.finEmbed (𝓞 ℚ) ℚ u') :
    ∃ ε₀ : SL(2, ℤ), ε₀ ∈ CongruenceSubgroup.Gamma0 M ∧
      LanglandsTunnell.ratArchGL2 h' = (ε₀ : GL (Fin 2) ℝ) * LanglandsTunnell.ratArchGL2 h ∧
      glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε₀)) = u' * u⁻¹ := by
  set P := globalPoints (𝓞 ℚ) ℚ with hP
  set E := AdelicDock.finEmbed (𝓞 ℚ) ℚ with hE
  set δ : GL (Fin 2) ℚ := γ'⁻¹ * γ with hδ
  have hquot : P δ = h' * E u' * (E u)⁻¹ * h⁻¹ := by
    have Eq : P γ * (h * E u) = P γ' * (h' * E u') := by rw [← mul_assoc, ← mul_assoc, hx]
    rw [hδ, map_mul, map_inv]
    have : P γ = P γ' * (h' * E u') * (h * E u)⁻¹ := eq_mul_inv_of_mul_eq Eq
    rw [this, _root_.mul_inv_rev]
    group
  have hfinq : glFin (𝓞 ℚ) ℚ (P δ) = u' * u⁻¹ := by
    rw [hquot, map_mul, map_mul, map_mul, map_inv, map_inv, hh, hh', hE, AdelicDock.glFin_finEmbed,
      AdelicDock.glFin_finEmbed, one_mul, inv_one, mul_one]
  have hK0 : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
    rw [hfinq]; exact Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hu)
  have hint : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
    (mem_finiteIntegralGL2_iff).mpr ⟨hK0.1.integral, hK0.2.integral⟩
  have harch : LanglandsTunnell.ratArchGL2 (P δ) =
      LanglandsTunnell.ratArchGL2 h' * (LanglandsTunnell.ratArchGL2 h)⁻¹ := by
    rw [hquot, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_inv, hE, ratArch_finEmbed,
      ratArch_finEmbed, inv_one, mul_one, mul_one]
  have hdetpos : 0 < ((GeneralLinearGroup.det δ : ℚˣ) : ℚ) := by
    have h1 : 0 < ((LanglandsTunnell.ratArchGL2 (P δ)).det.val : ℝ) := by
      rw [harch, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos hpos' (inv_pos.mpr hpos)
    rw [det_ratArch_globalPoints] at h1
    exact_mod_cast h1
  obtain ⟨ε₀, hε₀⟩ := exists_mapGL_eq_of_mem_finiteIntegralGL2 hint hdetpos
  have hε0 : ε₀ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    have hll : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((ε₀ 1 0 : ℤ) : ℚ)) ∈
        idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
      have := hK0.1.lowerLeft
      rw [← hε₀] at this
      rw [show (((ε₀ 1 0 : ℤ) : ℚ)) =
            ((Matrix.SpecialLinearGroup.mapGL ℚ ε₀ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0
          by rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]; rfl, ← glFin_globalPoints_apply]
      exact this
    have hdvd := natCast_dvd_of_mem_idealBall hM _ hll
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hdvd
  refine ⟨ε₀, hε0, ?_, ?_⟩
  · rw [← ratArch_globalPoints_mapGL, hε₀, harch, inv_mul_cancel_right]
  · rw [hε₀, hfinq]

section BallLemmas
variable {N : Ideal (𝓞 ℚ)}
local notation "Ball" => idealBall (𝓞 ℚ) ℚ N
local notation "Int𝔸" => integralFiniteAdeles (𝓞 ℚ) ℚ

theorem neg_mem_idealBall {x : FiniteAdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ Ball) : -x ∈ Ball := fun v => by
  rw [show (-x) v = -(x v) from rfl, Valuation.map_neg]; exact hx v

theorem sub_mem_idealBall {x y : FiniteAdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ Ball) (hy : y ∈ Ball) : x - y ∈ Ball := by
  rw [sub_eq_add_neg]; exact add_mem_idealBall hx (neg_mem_idealBall hy)

theorem lowerRight_mul_sub_mem {X Y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hX : IsLevelZeroMatrix (𝓞 ℚ) ℚ N X) (hY : IsLevelZeroMatrix (𝓞 ℚ) ℚ N Y) :
    (X * Y) 1 1 - X 1 1 * Y 1 1 ∈ Ball := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, add_sub_cancel_right]
  exact mul_mem_idealBall_right hX.lowerLeft (hY.integral 0 1)

theorem mul_sub_mul_mem {a a' b b' : FiniteAdeleRing (𝓞 ℚ) ℚ} (ha : a - a' ∈ Ball) (hb : b - b' ∈ Ball)
    (ha' : a' ∈ Int𝔸) (hbI : b ∈ Int𝔸) : a * b - a' * b' ∈ Ball := by
  have : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [this]
  exact add_mem_idealBall (mul_mem_idealBall_right ha hbI) (mul_mem_idealBall_left ha' hb)

end BallLemmas

theorem algebraMap_mul_lowerRight_sub_one_mem {N : Ideal (𝓞 ℚ)}
    {k k' u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ N) (hk' : k' ∈ finiteLevelOne (𝓞 ℚ) ℚ N)
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ N) (d : ℚ) (hdI : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) d ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hd : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) d
      ∈ idealBall (𝓞 ℚ) ℚ N) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) d *
        ((k' * (k * u)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
  set A := algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) d with hA

  have hK' : IsLevelOneMatrix (𝓞 ℚ) ℚ N (k' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hk'.1
  have hKi : IsLevelOneMatrix (𝓞 ℚ) ℚ N ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hk.2
  have hUi : IsLevelZeroMatrix (𝓞 ℚ) ℚ N ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hu.2
  have hU : IsLevelZeroMatrix (𝓞 ℚ) ℚ N (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := hu.1

  have hut : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1
      ∈ idealBall (𝓞 ℚ) ℚ N := by
    have h1 := lowerRight_mul_sub_mem hU hUi
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq] at h1

    have := neg_mem_idealBall h1
    rwa [neg_sub] at this

  have hdt : A * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
    have h2 : A * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        ∈ idealBall (𝓞 ℚ) ℚ N := by
      rw [← sub_mul]
      exact mul_mem_idealBall_right (by have := neg_mem_idealBall hd; rwa [neg_sub] at this) (hUi.integral 1 1)
    have := add_mem_idealBall h2 hut
    rwa [sub_add_sub_cancel] at this

  have hm1 := lowerRight_mul_sub_mem hK'.toIsLevelZeroMatrix (Subgroup.inv_mem _ (Subgroup.mul_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ hk) hu)).1

  rw [← Units.val_mul] at hm1
  have hm2 := lowerRight_mul_sub_mem hUi hKi.toIsLevelZeroMatrix
  rw [← Units.val_mul, ← _root_.mul_inv_rev] at hm2

  have hk'1 : (k' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1 ∈ idealBall (𝓞 ℚ) ℚ N := hK'.lowerRight
  have hki1 : ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1 ∈ idealBall (𝓞 ℚ) ℚ N := hKi.lowerRight

  have h3 : (((k * u)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
    have h := mul_sub_mul_mem (N := N) (show ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 ∈ idealBall (𝓞 ℚ) ℚ N by rw [sub_self]; exact zero_mem_idealBall N)
      hki1 (hUi.integral 1 1) (hKi.integral 1 1)
    rw [mul_one] at h
    have := add_mem_idealBall hm2 h
    rwa [sub_add_sub_cancel] at this

  have h4 : ((k' * (k * u)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
    have h := mul_sub_mul_mem (N := N) hk'1 h3 one_mem_integralFiniteAdeles
      ((Subgroup.inv_mem _ (Subgroup.mul_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ hk) hu)).1.integral 1 1)
    rw [one_mul] at h
    have := add_mem_idealBall hm1 h
    rwa [sub_add_sub_cancel] at this

  have h5 : A * ((k' * (k * u)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - A * ((u⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 ∈ idealBall (𝓞 ℚ) ℚ N := by
    rw [← mul_sub]; exact mul_mem_idealBall_left hdI h4
  have := add_mem_idealBall h5 hdt
  rwa [sub_add_sub_cancel] at this

theorem intCast_mem_integralFiniteAdeles (n : ℤ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro v
  have h := AdelicBox.algebraMap_mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) v (n : 𝓞 ℚ)
  rw [map_intCast] at h
  exact h

end WeightOneLevelZero

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix WeightOneLevelZero DihedralWeightOne in
open scoped MatrixGroups ModularForm in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hε : CuspForm.HasNebentypus ε h)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (d : ℤ)
    (hd : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
      (ε (d : ZMod M))⁻¹ * weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) x := by
  have hM : M ≠ 0 := NeZero.ne M
  obtain ⟨γ, y, k, hh, hpos, hk, hx⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM x
  obtain ⟨γ', y', k', hh', hpos', hk', hx'⟩ :=
    exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u)
  rw [hx', apply_decomp₁ hM h hh' hpos' hk', hx, apply_decomp₁ hM h hh hpos hk]
  have hku : k * u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) :=
    Subgroup.mul_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ hk) hu
  have hk'0 : k' ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := finiteLevelOne_le_finiteLevelZero _ _ _ hk'
  have heq : globalPoints (𝓞 ℚ) ℚ γ * y * AdelicDock.finEmbed (𝓞 ℚ) ℚ (k * u) =
      globalPoints (𝓞 ℚ) ℚ γ' * y' * AdelicDock.finEmbed (𝓞 ℚ) ℚ k' := by
    rw [← hx', hx, map_mul, ← mul_assoc]
  obtain ⟨ε₀, hε0, harch, hfin⟩ := exists_sl_of_levelZero hM hku hh hpos hk'0 hh' hpos' heq

  have he : ε ((ε₀ 1 1 : ℤ) : ZMod M) = (ε (d : ZMod M))⁻¹ := by
    have hent : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((ε₀ 1 1 : ℤ) : ℚ))
        = ((k' * (k * u)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 := by
      rw [← hfin, glFin_globalPoints_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
      rfl
    have hball := algebraMap_mul_lowerRight_sub_one_mem hk hk' hu (d : ℚ) (intCast_mem_integralFiniteAdeles d) hd
    rw [← hent, ← map_mul, ← Int.cast_mul, show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((1 : ℤ) : ℚ) by rw [Int.cast_one, map_one], ← map_sub,
      ← Int.cast_sub] at hball
    have hdvd := natCast_dvd_of_mem_idealBall hM _ hball
    have hZ : ((d : ZMod M)) * ((ε₀ 1 1 : ℤ) : ZMod M) = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hdvd
      rwa [Int.cast_sub, Int.cast_mul, Int.cast_one, sub_eq_zero] at this
    have hmul : ε (d : ZMod M) * ε ((ε₀ 1 1 : ℤ) : ZMod M) = 1 := by rw [← map_mul, hZ, map_one]
    exact (eq_inv_of_mul_eq_one_right hmul)
  rw [harch, weightOneArchLift_coe_mul hε hε0 (show 0 < (LanglandsTunnell.ratArchGL2 y).det.val from hpos), he]

end S_DihedralWeightOne_weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
end P2MW
export P2MW.S_DihedralWeightOne_weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero (solution)
