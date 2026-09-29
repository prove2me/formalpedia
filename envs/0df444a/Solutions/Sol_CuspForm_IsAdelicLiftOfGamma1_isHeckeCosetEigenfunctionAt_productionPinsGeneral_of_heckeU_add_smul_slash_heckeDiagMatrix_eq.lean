-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOfGamma1.isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fd288c82-59ad-5261-b95a-77f40cea278a

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Theorems.Thm_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm
import Theorems.Thm_NumberField_AdelicLevel_finEmbed_globalPoints_diag_mul_heckeGenAt_inv_mem_levelOne_rat
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_det_gen_mul_eq_nebentypus_mul
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

noncomputable section

namespace Ws41
namespace Lift7

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane AutomorphicForm.SiegelCoordinates HeckeIntegralSeam

open scoped MatrixGroups ModularForm

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)

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

variable {M : ℕ}

theorem apply_decomp {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφg : g.IsAdelicLiftOf φ) {γ : GL (Fin 2) ℚ} {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) :
    φ (globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ k) = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
  rw [mul_assoc, hφg.left_inv, hφg.level_inv k hk, hφg.apply_eq h hh hpos]

abbrev archPart (k : 𝔾) : 𝔾 := adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ k)

abbrev finPart (k : 𝔾) : 𝔾 := AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ k)

theorem eq_of_glArch_eq_of_glFin_eq {g g' : 𝔾} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ g')
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g') : g = g' := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) ha) i) j
    rwa [glArch_apply, glArch_apply] at this
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) hf) i) j
    rwa [glFin_apply, glFin_apply] at this

theorem glArch_archPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (archPart k) = glArch (𝓞 ℚ) ℚ k :=
  glArch_adelicArchGLIncl ℚ _

theorem glFin_archPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (archPart k) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem glArch_finPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (finPart k) = 1 :=
  AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _

theorem glFin_finPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (finPart k) = glFin (𝓞 ℚ) ℚ k :=
  AdelicDock.glFin_finEmbed (𝓞 ℚ) ℚ _

theorem archPart_mul_finPart (k : 𝔾) : archPart k * finPart k = k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, glArch_archPart, glArch_finPart, mul_one])
    (by rw [map_mul, glFin_archPart, glFin_finPart, one_mul])

theorem archPart_mul_finPart_comm (k k' : 𝔾) : archPart k * finPart k' = finPart k' * archPart k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, map_mul, glArch_archPart, glArch_finPart, mul_one, one_mul])
    (by rw [map_mul, map_mul, glFin_archPart, glFin_finPart, one_mul, mul_one])

theorem finPart_eq_self_of_glArch_eq_one {u : 𝔾} (hu : glArch (𝓞 ℚ) ℚ u = 1) : finPart u = u :=
  eq_of_glArch_eq_of_glFin_eq (by rw [glArch_finPart, hu]) (glFin_finPart u)

theorem ratArch_archPart (k : 𝔾) : LanglandsTunnell.ratArchGL2 (archPart k) = LanglandsTunnell.ratArchGL2 k := by
  unfold LanglandsTunnell.ratArchGL2
  rw [glArch_archPart]

theorem slash_two_scalar (f : UpperHalfPlane → ℂ) (c : GL (Fin 2) ℝ) (r : ℝ) (hr : r ≠ 0)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℝ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    f ∣[(2 : ℤ)] c = f := by
  have h00 : c 0 0 = r := by
    have := congr_fun (congr_fun hc 0) 0; simpa using this
  have h01 : c 0 1 = 0 := by
    have := congr_fun (congr_fun hc 0) 1; simpa using this
  have h10 : c 1 0 = 0 := by
    have := congr_fun (congr_fun hc 1) 0; simpa using this
  have h11 : c 1 1 = r := by
    have := congr_fun (congr_fun hc 1) 1; simpa using this
  have hdet : c.det.val = r * r := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdetpos : 0 < c.det.val := by rw [hdet]; exact mul_self_pos.mpr hr
  have hsmul : ∀ z : UpperHalfPlane, c • z = z := by
    intro z
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos, UpperHalfPlane.num, UpperHalfPlane.denom, h00, h01, h10, h11]
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    push_cast
    rw [zero_mul, zero_add, add_zero, mul_div_cancel_left₀ _ hr']
  funext z
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hdetpos, hsmul z, UpperHalfPlane.denom, h10, h11,
    hdet]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_zero, zero_mul, zero_add]
  field_simp
  rw [abs_of_nonneg (sq_nonneg r), show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one]
  push_cast
  ring

section HeckeCosetRepIndep
open QuotientGroup
variable {G : Type*} [Group G] {U : Subgroup G} {g : G}
  {ι : Type*} [Fintype ι] {reps : ι → G} (hsys : IsHeckeCosetSystem U g reps)

include hsys

noncomputable def leftPermIndex (u₀ : G) (hu₀ : u₀ ∈ U) (i : ι) : ι :=
  (hsys.covers (u₀ * reps i) (HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hu₀)).choose

omit [Fintype ι] in
theorem mk_leftPermIndex (u₀ : G) (hu₀ : u₀ ∈ U) (i : ι) :
    (QuotientGroup.mk (u₀ * reps i) : G ⧸ U)
      = QuotientGroup.mk (reps ((leftPermIndex hsys) u₀ hu₀ i)) :=
  (hsys.covers (u₀ * reps i) (HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hu₀)).choose_spec

theorem leftPermIndex_bijective (u₀ : G) (hu₀ : u₀ ∈ U) :
    Function.Bijective ((leftPermIndex hsys) u₀ hu₀) := by
  refine (Finite.injective_iff_bijective).mp fun i₁ i₂ hi => ?_
  have h₁ := (mk_leftPermIndex hsys) u₀ hu₀ i₁
  have h₂ := (mk_leftPermIndex hsys) u₀ hu₀ i₂
  rw [hi] at h₁
  have heq : (QuotientGroup.mk (u₀ * reps i₁) : G ⧸ U) = QuotientGroup.mk (u₀ * reps i₂) :=
    h₁.trans h₂.symm
  have hrep : (QuotientGroup.mk (reps i₁) : G ⧸ U) = QuotientGroup.mk (reps i₂) := by
    rw [QuotientGroup.eq] at heq ⊢
    simpa [mul_assoc] using heq
  exact hsys.mk_injective hrep

theorem sum_mul_left_eq {M : Type*} [AddCommMonoid M]
    (φ : G → M) (hφ : ∀ x, ∀ u ∈ U, φ (x * u) = φ x)
    (h u₀ : G) (hu₀ : u₀ ∈ U) :
    ∑ i, φ (h * (u₀ * reps i)) = ∑ i, φ (h * reps i) := by
  refine Fintype.sum_bijective ((leftPermIndex hsys) u₀ hu₀)
    ((leftPermIndex_bijective hsys) u₀ hu₀) _ _ fun i => ?_
  have hu' : (reps ((leftPermIndex hsys) u₀ hu₀ i))⁻¹ * (u₀ * reps i) ∈ U :=
    QuotientGroup.eq.mp ((mk_leftPermIndex hsys) u₀ hu₀ i).symm
  have hueq : h * (u₀ * reps i)
      = h * reps ((leftPermIndex hsys) u₀ hu₀ i)
        * ((reps ((leftPermIndex hsys) u₀ hu₀ i))⁻¹ * (u₀ * reps i)) := by
    rw [mul_assoc h, ← mul_assoc (reps _), mul_inv_cancel, one_mul]
  rw [hueq, hφ _ _ hu']

end HeckeCosetRepIndep

variable {M : ℕ}

theorem apply_decomp₁ {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : CuspForm.IsAdelicLiftOfGamma1 f φ) {γ : GL (Fin 2) ℚ} {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) :
    φ (globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ k)
      = ((⇑f) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
  rw [mul_assoc, hφ.left_inv, hφ.level_inv k hk, hφ.apply_eq h hh hpos]

theorem apply_finOnly_mul_eq {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : CuspForm.IsAdelicLiftOfGamma1 f φ) (β : GL (Fin 2) ℚ) (hβ : 0 < ((GeneralLinearGroup.det β : ℚˣ) : ℚ))
    (R y : 𝔾) (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hu : u ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (hR : R * AdelicDock.finEmbed (𝓞 ℚ) ℚ u = finPart (globalPoints (𝓞 ℚ) ℚ β))
    (hy : glFin (𝓞 ℚ) ℚ y = 1) (hypos : LanglandsTunnell.ratArchGL2 y ∈ GLPos (Fin 2) ℝ) :
    φ (R * y) = ((⇑f) ∣[(2 : ℤ)] ((LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ β))⁻¹
      * LanglandsTunnell.ratArchGL2 y)) UpperHalfPlane.I := by
  set P := globalPoints (𝓞 ℚ) ℚ β with hP
  set A := archPart P with hA
  have hRfin : glArch (𝓞 ℚ) ℚ R = 1 := by
    have := congrArg (glArch (𝓞 ℚ) ℚ) hR
    rw [map_mul, AdelicDock.glArch_finEmbed, mul_one, glArch_finPart] at this

    exact this

  have hR' : R = A⁻¹ * P * AdelicDock.finEmbed (𝓞 ℚ) ℚ u⁻¹ := by
    have h1 : finPart P = A⁻¹ * P := by
      rw [hA, eq_inv_mul_iff_mul_eq, archPart_mul_finPart]
    rw [← h1, ← hR, map_inv, mul_inv_cancel_right]
  have hcommAy : A⁻¹ * P = P * A⁻¹ := by

    have h1 : A⁻¹ * P = finPart P := by rw [hA, inv_mul_eq_iff_eq_mul, archPart_mul_finPart]
    have h2 : P * A⁻¹ = finPart P := by
      rw [hA, mul_inv_eq_iff_eq_mul, ← archPart_mul_finPart_comm P P, archPart_mul_finPart]
    rw [h1, h2]
  have hEy : AdelicDock.finEmbed (𝓞 ℚ) ℚ u⁻¹ * y = y * AdelicDock.finEmbed (𝓞 ℚ) ℚ u⁻¹ := by
    have hy' : archPart y = y := by
      refine eq_of_glArch_eq_of_glFin_eq (glArch_archPart y) ?_
      rw [glFin_archPart, hy]
    have := archPart_mul_finPart_comm y (AdelicDock.finEmbed (𝓞 ℚ) ℚ u⁻¹)
    rw [hy', finPart_eq_self_of_glArch_eq_one (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _)] at this
    exact this.symm
  have hfin : glFin (𝓞 ℚ) ℚ (A⁻¹ * y) = 1 := by rw [map_mul, map_inv, glFin_archPart, inv_one, one_mul, hy]
  have hdetA : 0 < (LanglandsTunnell.ratArchGL2 A).det.val := by
    rw [ratArch_archPart, det_ratArch_globalPoints]; exact_mod_cast hβ
  have hpos : LanglandsTunnell.ratArchGL2 (A⁻¹ * y) ∈ GLPos (Fin 2) ℝ := by
    show 0 < (LanglandsTunnell.ratArchGL2 (A⁻¹ * y)).det.val
    rw [ratArch_mul, ratArch_inv, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_pos (inv_pos.mpr hdetA) hypos
  have hshape : R * y = P * (A⁻¹ * y) * AdelicDock.finEmbed (𝓞 ℚ) ℚ u⁻¹ := by
    rw [hR', mul_assoc (A⁻¹ * P), hEy, ← mul_assoc (A⁻¹ * P), hcommAy, mul_assoc P A⁻¹ y]
  rw [hshape, apply_decomp₁ hφ hfin hpos (Subgroup.inv_mem _ hu), ratArch_mul, ratArch_inv, ratArch_archPart]

theorem finEmbed_glFin_of_glArch_eq_one' (u : AdelicGL2 (𝓞 ℚ) ℚ) (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u) = u := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hmat : AdelicDock.finMat (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
    refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
    · rw [AdelicDock.mapMatrix_arch_finMat]
      ext i j
      have h : (glArch (𝓞 ℚ) ℚ u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
          = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j := by rw [hu, Units.val_one]
      rw [glArch_apply] at h
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]
      exact h.symm
    · rw [AdelicDock.mapMatrix_fin_finMat]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, glFin_apply]
  rw [AdelicDock.coe_finEmbed, hmat]

theorem apply_mul_eq_of_mem_U {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : CuspForm.IsAdelicLiftOfGamma1 f φ) (x u : 𝔾)
    (hu : u ∈ levelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) ⊓ finiteAdelicGL2Subgroup ℚ) : φ (x * u) = φ x := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hu
  rw [← finEmbed_glFin_of_glArch_eq_one' u h2]
  exact hφ.level_inv _ (mem_levelOne_iff.mp h1) x

theorem mul_comm_of_glArch_glFin {r y : 𝔾} (hr : glArch (𝓞 ℚ) ℚ r = 1) (hy : glFin (𝓞 ℚ) ℚ y = 1) :
    y * r = r * y :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, map_mul, hr, mul_one, one_mul])
    (by rw [map_mul, map_mul, hy, mul_one, one_mul])

theorem upperUnit_one_mul_diag (p : ℚ) (hp : p ≠ 0) (b : ℚ) :
    upperUnit (1 : ℚ) b 1 one_ne_zero one_ne_zero * upperUnit p 0 1 hp one_ne_zero
      = upperUnit p b 1 hp one_ne_zero := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul]
  fin_cases i <;> fin_cases j <;>
    simp [upperUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem ratArch_globalPoints_upperUnit_inv (p : ℕ) (hp : p ≠ 0) (j : ℕ) :
    (LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ
        (upperUnit (p : ℚ) (-(j : ℚ)) 1 (Nat.cast_ne_zero.mpr hp) one_ne_zero)))⁻¹
      = GeneralLinearGroup.mkOfDetNeZero ((p : ℝ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)
        * ModularForm.heckeMatrix p j := by
  rw [ratArch_globalPoints]
  apply inv_eq_of_mul_eq_one_right
  refine Matrix.GeneralLinearGroup.ext fun i k => ?_
  rw [Units.val_mul, Units.val_mul, Units.val_one, ModularForm.val_heckeMatrix hp]
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  fin_cases i <;> fin_cases k <;>
    simp [upperUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, hp']

theorem ratArch_globalPoints_diag (p : ℕ) (hp : p ≠ 0) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ
        (upperUnit (p : ℚ) 0 1 (Nat.cast_ne_zero.mpr hp) one_ne_zero))
      = ModularForm.heckeDiagMatrix p := by
  rw [ratArch_globalPoints]
  refine Matrix.GeneralLinearGroup.ext fun i k => ?_
  rw [ModularForm.val_heckeDiagMatrix hp]
  fin_cases i <;> fin_cases k <;>
    simp [upperUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem absNorm_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal).Prime := by
  haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ)
      Rat.ringOfIntegersEquiv.symm.surjective
  set π := Submodule.IsPrincipal.generator v.asIdeal with hπdef
  have hspan := (Submodule.IsPrincipal.span_singleton_generator v.asIdeal).symm
  have hπprime : Prime π := Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot
  have hπℤ : Prime (Rat.ringOfIntegersEquiv π) := (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.toMulEquiv).mpr hπprime
  have hrank : Module.finrank ℤ (𝓞 ℚ) = 1 := (RingOfIntegers.rank ℚ).trans (Module.finrank_self (R := ℚ))
  have hπeq : algebraMap ℤ (𝓞 ℚ) (Rat.ringOfIntegersEquiv π) = π := by
    rw [algebraMap_int_eq, eq_intCast,
      show ((Rat.ringOfIntegersEquiv π : ℤ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv π) from
        (map_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm, RingEquiv.symm_apply_apply]
  rw [hspan, Ideal.absNorm_span_singleton, ← hπdef, ← hπeq, Algebra.norm_algebraMap, hrank, pow_one]
  exact Int.prime_iff_natAbs_prime.mp hπℤ

theorem absNorm_ratLevel (M : ℕ) : Ideal.absNorm (AdelicDock.ratLevel M) = M := by
  have hrank : Module.finrank ℤ (𝓞 ℚ) = 1 := (RingOfIntegers.rank ℚ).trans (Module.finrank_self (R := ℚ))
  rw [AdelicDock.ratLevel, Ideal.absNorm_span_singleton,
    show ((M : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (M : ℤ) by simp, Algebra.norm_algebraMap, hrank, pow_one,
    Int.natAbs_natCast]

theorem apply_centralScalar_unitAt_mul {ε : DirichletCharacter ℂ M} [NeZero M]
    {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2} (hε : CuspForm.HasNebentypus ε f)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : CuspForm.IsAdelicLiftOfGamma1 f φ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ AdelicDock.ratLevel M)
    (t : (v.adicCompletion ℚ)ˣ) (ht : Valued.v (t : v.adicCompletion ℚ) = 1) (x : 𝔾) :
    φ (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) * x) = φ x := by
  set T : 𝔾 := centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) with hT
  have hTarch : glArch (𝓞 ℚ) ℚ T = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glArch_apply, Units.val_one]
    show ((Matrix.scalar (Fin 2) ((Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
      AdeleRing (𝓞 ℚ) ℚ)) i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> rfl
  have hcomm : T * x = x * T := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))).eq
  have hK0 : glFin (𝓞 ℚ) ℚ T ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
    have hval : ∀ (s : (v.adicCompletion ℚ)ˣ), Valued.v (s : v.adicCompletion ℚ) = 1 →
        ∀ i j, ((Matrix.scalar (Fin 2) ((localUnit (𝓞 ℚ) ℚ v s : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
      intro s hs i j w
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · by_cases hw : w = v
        · subst hw; rw [localUnit_apply_self]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hs.le
        · rw [localUnit_apply_of_ne _ _ _ _ hw]; exact one_mem _
      · exact zero_mem _
    have hll : ∀ (s : (v.adicCompletion ℚ)ˣ), ((Matrix.scalar (Fin 2) ((localUnit (𝓞 ℚ) ℚ v s : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := fun s => by
      rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_neg (by decide)]; exact zero_mem_idealBall _
    have ht' : Valued.v ((t⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]
    have hshape : ∀ (s : (v.adicCompletion ℚ)ˣ), (glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ
        (Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v s))) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        = Matrix.scalar (Fin 2) ((localUnit (𝓞 ℚ) ℚ v s : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      intro s; refine Matrix.ext fun i j => ?_
      rw [glFin_apply]
      show ((Matrix.scalar (Fin 2) ((Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v s) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ)) i j).2 = _
      rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs <;> rfl
    refine ⟨⟨fun i j => ?_, ?_⟩, ⟨fun i j => ?_, ?_⟩⟩
    · rw [hshape]; exact hval t ht i j
    · rw [hshape]; exact hll t
    · rw [← map_inv, hT, ← map_inv, ← map_inv, ← map_inv, hshape]; exact hval t⁻¹ ht' i j
    · rw [← map_inv, hT, ← map_inv, ← map_inv, ← map_inv, hshape]; exact hll t⁻¹
  have hd : ((glFin (𝓞 ℚ) ℚ T : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((1 : ℤ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
    intro w
    rw [Int.cast_one, map_one, glFin_apply]
    show Valued.v ((((Matrix.scalar (Fin 2) ((Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t) :
        (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) 1 1).2 - 1) w) ≤ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    show Valued.v (((localUnit (𝓞 ℚ) ℚ v t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w - (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) w) ≤ _
    by_cases hw : w = v
    · subst hw
      rw [idealBound_eq_one_of_not_dvd (AdelicDock.ratLevel_ne_bot (NeZero.ne M)) hv, localUnit_apply_self]
      refine Valuation.map_sub_le _ ht.le ?_
      rw [show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1 from rfl, map_one]
    · rw [localUnit_apply_of_ne _ _ _ _ hw, show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1 from rfl, sub_self, map_zero]
      exact zero_le'
  rw [hcomm, ← finEmbed_glFin_of_glArch_eq_one' T hTarch,
    CuspForm.IsAdelicLiftOfGamma1.apply_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero hε hφ _ hK0 1 hd x,
    Int.cast_one, map_one, inv_one, one_mul]

end Ws41.Lift7

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix Ws41.Lift7 AutomorphicForm.SiegelCoordinates HeckeIntegralSeam UpperHalfPlane in

open scoped MatrixGroups ModularForm in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ AdelicDock.ratLevel M) (c : ℂ)
    (hT : ModularForm.heckeU 2 (Ideal.absNorm v.asIdeal) ⇑h
          + ε ((Ideal.absNorm v.asIdeal : ℕ) : ZMod M) •
              ((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
        = c • ⇑h) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt ℚ ((productionPinsGeneral ℚ).U (AdelicDock.ratLevel M))
      ((productionPinsGeneral ℚ).gen v) v Φ c := by
  have hM : M ≠ 0 := NeZero.ne M
  set p : ℕ := Ideal.absNorm v.asIdeal with hpdef
  have hp : p.Prime := absNorm_prime v
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpv : (p : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hpM : ¬ p ∣ Ideal.absNorm (AdelicDock.ratLevel M) := by
    rw [absNorm_ratLevel]
    intro hdvd; apply hv
    rw [AdelicDock.ratLevel, Ideal.dvd_span_singleton]
    obtain ⟨e, he⟩ := hdvd
    have : ((M : ℕ) : 𝓞 ℚ) = ((p : ℕ) : 𝓞 ℚ) * (e : 𝓞 ℚ) := by rw [he]; push_cast; ring
    rw [this]; exact v.asIdeal.mul_mem_right _ hpv
  have hpC : (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) ≠ 0 := by rw [map_ne_zero]; exact_mod_cast hp0
  set ϖ : (v.adicCompletion ℚ)ˣ := Units.mk0 _ hpC with hϖdef
  have hϖ : (ϖ : v.adicCompletion ℚ) = algebraMap ℚ _ (p : ℚ) := rfl

  set L := AdelicDock.ratLevel M with hL
  set U : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ) := levelOne (𝓞 ℚ) ℚ L ⊓ finiteAdelicGL2Subgroup ℚ with hU
  set gA := heckeGenAt (𝓞 ℚ) ℚ v ϖ with hgA
  set reps : Fin (p + 1) → AdelicGL2 (𝓞 ℚ) ℚ := fun i =>
        if (i : ℕ) < p then
          AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperUnit (1 : ℚ) (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero))) * gA
        else
          centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v ϖ)) * gA⁻¹ with hreps
  have hsys : IsHeckeCosetSystem U (heckeGen (𝓞 ℚ) ℚ v) reps :=
    isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm L p hp hpM v hpv ϖ hϖ
  refine ⟨reps, hsys, fun g => ?_⟩

  have hΦU : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ U, Φ (x * u) = Φ x := fun x u hu => apply_mul_eq_of_mem_U hΦ x u hu

  obtain ⟨γ, y, k, hy, hpos, hk, hx⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM g
  have hEk : AdelicDock.finEmbed (𝓞 ℚ) ℚ k ∈ U :=
    Subgroup.mem_inf.mpr ⟨mem_levelOne_iff.mpr (by rw [AdelicDock.glFin_finEmbed]; exact hk), AdelicDock.glArch_finEmbed _ _ k⟩

  have hgA_arch : glArch (𝓞 ℚ) ℚ gA = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glArch_apply, Units.val_one, hgA]
    exact heckeGenAt_fst (R := 𝓞 ℚ) (K := ℚ) ϖ i j
  have hreps_arch : ∀ i, glArch (𝓞 ℚ) ℚ (reps i) = 1 := by
    intro i
    simp only [hreps]
    split_ifs
    · rw [map_mul, AdelicDock.glArch_finEmbed, one_mul, hgA_arch]
    · rw [map_mul, map_inv, hgA_arch, inv_one, mul_one]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [glArch_apply, Units.val_one]
      show ((Matrix.scalar (Fin 2) ((Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ v ϖ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) i j).1
        = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
      rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
      split_ifs <;> rfl
  have hstep1 : SmoothCusp.heckeCosetSum ℚ reps Φ g = ∑ i, Φ (reps i * y) := by
    unfold SmoothCusp.heckeCosetSum
    rw [hx]
    have hassoc : ∀ i, Φ (globalPoints (𝓞 ℚ) ℚ γ * y * AdelicDock.finEmbed (𝓞 ℚ) ℚ k * reps i)
        = Φ (globalPoints (𝓞 ℚ) ℚ γ * y * (AdelicDock.finEmbed (𝓞 ℚ) ℚ k * reps i)) := fun i => by rw [mul_assoc]
    simp only [hassoc]
    rw [sum_mul_left_eq hsys Φ hΦU (globalPoints (𝓞 ℚ) ℚ γ * y) _ hEk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, hΦ.left_inv, mul_comm_of_glArch_glFin (hreps_arch i) hy]

  have hd_ne : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  obtain ⟨hmem₁, hmem₂⟩ := finEmbed_globalPoints_diag_mul_heckeGenAt_inv_mem_levelOne_rat L p hp v hpv ϖ hϖ

  set w₂ : AdelicGL2 (𝓞 ℚ) ℚ := gA⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperUnit (p : ℚ) 0 1 (Nat.cast_ne_zero.mpr hp.ne_zero) one_ne_zero))) with hw₂
  have hw₂U : w₂ ∈ U := hmem₂
  have hw₂arch : glArch (𝓞 ℚ) ℚ w₂ = 1 := (Subgroup.mem_inf.mp hw₂U).2
  have hw₂fin : glFin (𝓞 ℚ) ℚ w₂ ∈ finiteLevelOne (𝓞 ℚ) ℚ L := mem_levelOne_iff.mp (Subgroup.mem_inf.mp hw₂U).1
  have hfirst : ∀ i : Fin p, Φ (reps (Fin.castSucc i) * y)
      = (((⇑h) ∣[(2 : ℤ)] ModularForm.heckeMatrix p i) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 y) UpperHalfPlane.I := by
    intro i
    have hi : ((Fin.castSucc i : Fin (p + 1)) : ℕ) < p := by simp
    have hrep : reps (Fin.castSucc i) = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperUnit (1 : ℚ) (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero))) * gA := by
      simp only [hreps]; rw [if_pos hi]; rfl
    set β : GL (Fin 2) ℚ := upperUnit (p : ℚ) (-((i : ℕ) : ℚ)) 1 hd_ne one_ne_zero with hβ
    have hβdet : 0 < ((GeneralLinearGroup.det β : ℚˣ) : ℚ) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hβ]
      simp [upperUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two, hp.pos]
    have hR : reps (Fin.castSucc i) * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ w₂) = finPart (globalPoints (𝓞 ℚ) ℚ β) := by
      rw [finEmbed_glFin_of_glArch_eq_one' w₂ hw₂arch, hrep, hw₂, mul_assoc, mul_inv_cancel_left, ← map_mul, ← map_mul,
        ← map_mul, upperUnit_one_mul_diag (p : ℚ) hd_ne]
    have hC : (⇑h) ∣[(2 : ℤ)] (GeneralLinearGroup.mkOfDetNeZero ((p : ℝ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)) = ⇑h :=
      slash_two_scalar _ _ ((p : ℝ)⁻¹) (inv_ne_zero (Nat.cast_ne_zero.mpr hp0)) rfl
    rw [apply_finOnly_mul_eq hΦ β hβdet _ y _ hw₂fin hR hy hpos, hβ, ratArch_globalPoints_upperUnit_inv p hp0 i,
      SlashAction.slash_mul, SlashAction.slash_mul, hC]
  have hlast : Φ (reps (Fin.last p) * y)
      = ε ((p : ℕ) : ZMod M) * (((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 y) UpperHalfPlane.I := by
    have hrep : reps (Fin.last p) = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v ϖ)) * gA⁻¹ := by
      simp only [hreps]; rw [if_neg (by simp)]

    set Ju : (AdeleRing (𝓞 ℚ) ℚ)ˣ := Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v) with hJu
    have hJu' : Ju = Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v)) := by
      rw [hJu]
      refine Units.ext ?_
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      show Matrix.det ((diagOne ((Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ))
        (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = _
      rw [show ((diagOne ((Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ))
          (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
          = Matrix.diagonal ![(((Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ))
            (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ), 1] from rfl,
        Matrix.det_diagonal, Fin.prod_univ_two]
      simp
    set t : (v.adicCompletion ℚ)ˣ := (uniformizerUnit ℚ v)⁻¹ * ϖ with htdef
    have ht : Valued.v (t : v.adicCompletion ℚ) = 1 := by
      rw [htdef, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit, hϖ,
        RatIdele.valued_algebraMap_rat]
      have : v.valuation ℚ ((p : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
        rw [show ((p : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((p : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
          HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast hp0)
          (by
            have hmax : (Ideal.span {((p : ℕ) : 𝓞 ℚ)}).IsMaximal := by
              have hpr : Prime ((p : ℕ) : 𝓞 ℚ) := by
                have hcast : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) :=
                  (map_natCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
                rw [hcast]
                exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.mp hp)
              exact ((Ideal.span_singleton_prime (by exact_mod_cast hp0)).mpr hpr).isMaximal
                ((Ideal.span_singleton_eq_bot (α := 𝓞 ℚ)).not.mpr (by exact_mod_cast hp0))
            exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hpv)).symm)
      rw [this, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    have hsplit : Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v ϖ)
        = Ju * Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t) := by
      rw [hJu', ← map_mul, ← map_mul, htdef, mul_inv_cancel_left]

    set w₁ : AdelicGL2 (𝓞 ℚ) ℚ := AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperUnit (p : ℚ) 0 1 (Nat.cast_ne_zero.mpr hp.ne_zero) one_ne_zero))) * gA⁻¹ with hw₁
    have hw₁U : w₁⁻¹ ∈ U := Subgroup.inv_mem _ hmem₁
    have hw₁arch : glArch (𝓞 ℚ) ℚ w₁⁻¹ = 1 := (Subgroup.mem_inf.mp hw₁U).2
    have hw₁fin : glFin (𝓞 ℚ) ℚ w₁⁻¹ ∈ finiteLevelOne (𝓞 ℚ) ℚ L := mem_levelOne_iff.mp (Subgroup.mem_inf.mp hw₁U).1
    set β : GL (Fin 2) ℚ := (upperUnit (p : ℚ) 0 1 (Nat.cast_ne_zero.mpr hp.ne_zero) one_ne_zero)⁻¹ with hβ
    have hβdet : 0 < ((GeneralLinearGroup.det β : ℚˣ) : ℚ) := by
      rw [hβ, map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]
      simp [upperUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two, hp.pos]
    have hR : gA⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ w₁⁻¹) = finPart (globalPoints (𝓞 ℚ) ℚ β) := by
      rw [finEmbed_glFin_of_glArch_eq_one' w₁⁻¹ hw₁arch, hw₁, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left,
        ← map_inv, ← map_inv, hβ]
      rfl
    rw [hrep, hsplit, map_mul, mul_assoc, mul_assoc,
      CuspForm.IsAdelicLiftOfGamma1.apply_centralScalar_det_gen_mul_eq_nebentypus_mul hε hΦ v hv,
      apply_centralScalar_unitAt_mul hε hΦ v hv t ht,
      apply_finOnly_mul_eq hΦ β hβdet _ y _ hw₁fin hR hy hpos, hβ, map_inv, ratArch_inv, inv_inv,
      ratArch_globalPoints_diag p hp0, SlashAction.slash_mul]

  rw [hstep1, Fin.sum_univ_castSucc, hlast, Finset.sum_congr rfl fun i _ => hfirst i]

  have hposY : 0 < (LanglandsTunnell.ratArchGL2 y).det.val := hpos
  have hσ : ∀ z : ℂ, σ (LanglandsTunnell.ratArchGL2 y) z = z := fun z => by rw [UpperHalfPlane.σ, if_pos hposY]; rfl
  have hsum : ∑ i : Fin p, (((⇑h) ∣[(2 : ℤ)] ModularForm.heckeMatrix p i) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 y) UpperHalfPlane.I
      = ((ModularForm.heckeU 2 p ⇑h) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 y) UpperHalfPlane.I := by
    rw [ModularForm.heckeU_def, SlashAction.sum_slash, Finset.sum_apply, Finset.sum_range]
  rw [hsum]
  have hfinal := congrArg (fun F : UpperHalfPlane → ℂ => (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 y) UpperHalfPlane.I) hT
  simp only [SlashAction.add_slash, ModularForm.smul_slash, hσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hfinal
  rw [hfinal, hx, apply_decomp₁ hΦ hy hpos hk]

end S_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq (solution)
