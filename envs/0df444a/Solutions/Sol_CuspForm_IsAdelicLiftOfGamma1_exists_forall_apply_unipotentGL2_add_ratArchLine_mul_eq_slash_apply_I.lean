-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOfGamma1.exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9b2ec268-2875-5b07-8efd-4750f1f237f1

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_AdelicTraceProducer

import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_globalPoints_mul_mul_eq_slash_ratArchGL2_apply_I
import Theorems.Thm_NumberField_AdelicLevel_exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.StandardAddChar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm MatrixGroups

noncomputable section

namespace Ws41
namespace L5b

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel AdelicDock Matrix
open scoped MatrixGroups

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

def ratArchHom : 𝔾 →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

theorem ratArchHom_apply (g : 𝔾) : ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

theorem ratArch_mul (g g' : 𝔾) :
    LanglandsTunnell.ratArchGL2 (g * g') = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

theorem ratArch_inv (g : 𝔾) : LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

theorem ratArch_eq_one_of_glArch_eq_one {u : 𝔾} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

theorem ratArch_finEmbed (u : GL (Fin 2) 𝔸f) : LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (glArch_finEmbed (𝓞 ℚ) ℚ u)

theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

theorem map_castHom_mapGL (γ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ γ)
      = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem ratArch_globalPoints_mapGL (ε : SL(2, ℤ)) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) = (ε : GL (Fin 2) ℝ) := by
  rw [ratArch_globalPoints]
  exact Matrix.SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) ε

theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) 𝔸f) i j
      = algebraMap ℚ 𝔸f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

theorem exists_algebraMap_eq_of_mem_integralFiniteAdeles {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ AdelicLevel.integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ 𝔸f q ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integralFiniteAdeles hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

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

theorem det_ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    (LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ)).det.val
      = (((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ) := by
  rw [ratArch_globalPoints, Matrix.GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, eq_ratCast]

theorem intCast_mem_integralFiniteAdeles (n : ℤ) :
    algebraMap ℚ 𝔸f (n : ℚ) ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro v
  have h := AdelicBox.algebraMap_mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) v (n : 𝓞 ℚ)
  rw [map_intCast] at h
  exact h

def epsQ : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(-1 : ℚ), 0; 0, 1] (by rw [Matrix.det_fin_two_of]; norm_num)

theorem epsQ_mul_epsQ : epsQ * epsQ = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_one]
  simp only [epsQ, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem epsQ_inv : epsQ⁻¹ = epsQ := inv_eq_of_mul_eq_one_right epsQ_mul_epsQ

theorem det_epsQ : ((Matrix.GeneralLinearGroup.det epsQ : ℚˣ) : ℚ) = -1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp only [epsQ, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.det_fin_two_of]
  norm_num

theorem isLevelOneMatrix_glFin_globalPoints_epsQ (N : Ideal (𝓞 ℚ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ N
      (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ epsQ) : Matrix (Fin 2) (Fin 2) 𝔸f) := by
  have h00 : (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ epsQ) : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0
      = algebraMap ℚ 𝔸f ((-1 : ℤ) : ℚ) := by
    rw [glFin_globalPoints_apply]; simp [epsQ]
  have h01 : (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ epsQ) : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1 = 0 := by
    rw [glFin_globalPoints_apply]; simp [epsQ]
  have h10 : (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ epsQ) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 = 0 := by
    rw [glFin_globalPoints_apply]; simp [epsQ]
  have h11 : (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ epsQ) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 = 1 := by
    rw [glFin_globalPoints_apply]; simp [epsQ]
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]; rw [h00]; exact intCast_mem_integralFiniteAdeles _
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; rw [h01]; exact zero_mem_integralFiniteAdeles
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]; rw [h10]; exact zero_mem_integralFiniteAdeles
    · simp only [Fin.mk_one, Fin.isValue]; rw [h11]; exact one_mem_integralFiniteAdeles
  · rw [h10]; exact zero_mem_idealBall N
  · rw [h11, sub_self]; exact zero_mem_idealBall N

theorem glFin_globalPoints_epsQ_mem (N : Ideal (𝓞 ℚ)) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ epsQ) ∈ finiteLevelOne (𝓞 ℚ) ℚ N := by
  rw [mem_finiteLevelOne_iff]
  refine ⟨isLevelOneMatrix_glFin_globalPoints_epsQ N, ?_⟩
  rw [← map_inv, ← map_inv, epsQ_inv]
  exact isLevelOneMatrix_glFin_globalPoints_epsQ N

theorem finiteLevelZero_le_finiteIntegralGL2 (N : Ideal (𝓞 ℚ)) :
    finiteLevelZero (𝓞 ℚ) ℚ N ≤ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
  intro g hg
  rw [mem_finiteIntegralGL2_iff]
  exact ⟨hg.1.integral, hg.2.integral⟩

theorem mem_U_iff (N : Ideal (𝓞 ℚ)) (u : 𝔾) :
    u ∈ (productionPinsGeneral ℚ).U N ↔ glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ N ∧ glArch (𝓞 ℚ) ℚ u = 1 := by
  show u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ ↔ _
  rw [Subgroup.mem_inf, mem_levelOne_iff, mem_finiteAdelicGL2Subgroup_iff]

theorem finEmbed_mem_U {N : Ideal (𝓞 ℚ)} {k : GL (Fin 2) 𝔸f} (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ N) :
    finEmbed (𝓞 ℚ) ℚ k ∈ (productionPinsGeneral ℚ).U N := by
  rw [mem_U_iff, glFin_finEmbed, glArch_finEmbed]
  exact ⟨hk, rfl⟩

theorem glFin_unipotentGL2_val (x : AdeleRing (𝓞 ℚ) ℚ) :
    (glFin (𝓞 ℚ) ℚ (unipotentGL2 x) : Matrix (Fin 2) (Fin 2) 𝔸f) = !![1, x.2; 0, 1] := by
  ext i j
  rw [glFin_apply, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_unipotentGL2_eq_of_snd_eq {x y : AdeleRing (𝓞 ℚ) ℚ} (h : x.2 = y.2) :
    glFin (𝓞 ℚ) ℚ (unipotentGL2 x) = glFin (𝓞 ℚ) ℚ (unipotentGL2 y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_unipotentGL2_val, glFin_unipotentGL2_val, h]

theorem glFin_unipotentGL2_mem_integral {x : AdeleRing (𝓞 ℚ) ℚ}
    (hx : x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) :
    glFin (𝓞 ℚ) ℚ (unipotentGL2 x) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
  have hval := glFin_unipotentGL2_val x
  have hinv : (((glFin (𝓞 ℚ) ℚ (unipotentGL2 x))⁻¹ : GL (Fin 2) 𝔸f) : Matrix (Fin 2) (Fin 2) 𝔸f) = !![1, -x.2; 0, 1] := by
    rw [← map_inv]
    refine Matrix.ext fun i j => ?_
    rw [glFin_apply]
    change ((!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 = _
    fin_cases i <;> fin_cases j <;> rfl
  have hx' : -x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
    simpa using sub_mem_integralFiniteAdeles zero_mem_integralFiniteAdeles hx
  rw [mem_finiteIntegralGL2_iff, hval, hinv]
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [one_mem_integralFiniteAdeles, zero_mem_integralFiniteAdeles, hx]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [one_mem_integralFiniteAdeles, zero_mem_integralFiniteAdeles, hx']

def nArch (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by rw [Matrix.det_fin_two_of]; simp)

theorem nArch_apply (t : ℝ) : ((nArch t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, t; 0, 1] := rfl

theorem det_nArch (t : ℝ) : (nArch t).det.val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change Matrix.det !![(1 : ℝ), t; 0, 1] = _
  rw [Matrix.det_fin_two_of]; ring

def realCoord (x : AdeleRing (𝓞 ℚ) ℚ) : ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)) (x.1 default)

theorem ratArch_unipotentGL2 (x : AdeleRing (𝓞 ℚ) ℚ) :
    LanglandsTunnell.ratArchGL2 (unipotentGL2 x) = nArch (realCoord x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp (adeleArch (𝓞 ℚ) ℚ)))
      ((unipotentGL2 x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j)
    = (nArch (realCoord x) : Matrix (Fin 2) (Fin 2) ℝ) i j
  have h1 : ((1 : AdeleRing (𝓞 ℚ) ℚ).1 default) = 1 := rfl
  have h0 : ((0 : AdeleRing (𝓞 ℚ) ℚ).1 default) = 0 := rfl
  rw [unipotentGL2_coe, nArch_apply]
  fin_cases i <;> fin_cases j <;> simp [realCoord, archEval_apply, adeleArch_apply, h1, h0]

theorem det_ratArch_unipotentGL2 (x : AdeleRing (𝓞 ℚ) ℚ) :
    (LanglandsTunnell.ratArchGL2 (unipotentGL2 x)).det.val = 1 := by
  rw [ratArch_unipotentGL2, det_nArch]

theorem coe_SL_inv (ρ : SL(2, ℤ)) : ((ρ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = ((ρ : GL (Fin 2) ℝ))⁻¹ := by
  simp

theorem det_coe_SL (ρ : SL(2, ℤ)) : ((ρ : GL (Fin 2) ℝ)).det.val = 1 := by
  simp

end Ws41.L5b

end

open Ws41.L5b NumberField.AdelicLevel AdelicDock in
theorem solution
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (x : AdeleRing (𝓞 ℚ) ℚ) (hx : x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ)
    (h₁ q : AdelicGL2 (𝓞 ℚ) ℚ) (hh₁ : glFin (𝓞 ℚ) ℚ h₁ = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h₁ ∈ Matrix.GLPos (Fin 2) ℝ)
    (hq : glArch (𝓞 ℚ) ℚ q = 1) (hqint : glFin (𝓞 ℚ) ℚ q ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    ∃ ρ : SL(2, ℤ), ∀ t : ℝ,
      Φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (x.1 + ratArchLine t, x.2) * (h₁ * q)) =
        ((⇑h) ∣[(2 : ℤ)] (((ρ : GL (Fin 2) ℝ))⁻¹ *
            LanglandsTunnell.ratArchGL2 (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (x.1 + ratArchLine t, x.2) * h₁)))
          UpperHalfPlane.I := by
  have hM : (M : ℕ) ≠ 0 := NeZero.ne M
  have hN : AdelicDock.ratLevel M ≠ ⊥ := AdelicDock.ratLevel_ne_bot hM
  have hx' : x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := fun v => hx v
  have hK1 : ∀ N : Ideal (𝓞 ℚ), finiteLevelOne (𝓞 ℚ) ℚ N ≤ finiteIntegralGL2 (𝓞 ℚ) ℚ := fun N =>
    (finiteLevelOne_le_finiteLevelZero _ _ N).trans (finiteLevelZero_le_finiteIntegralGL2 N)

  have hnfin : ∀ t : ℝ,
      glFin (𝓞 ℚ) ℚ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (x.1 + ratArchLine t, x.2))
        = glFin (𝓞 ℚ) ℚ (unipotentGL2 x) := fun t => glFin_unipotentGL2_eq_of_snd_eq rfl
  set w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) := glFin (𝓞 ℚ) ℚ (unipotentGL2 x) * glFin (𝓞 ℚ) ℚ q
    with hw
  have hwint : w ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
    Subgroup.mul_mem _ (glFin_unipotentGL2_mem_integral hx') hqint

  obtain ⟨γ₀, hγ₀⟩ := NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat hN w
  have hint_of : ∀ γ' : GL (Fin 2) ℚ,
      glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ') * w ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) →
        glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ') ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    intro γ' h'
    have h2 := Subgroup.mul_mem _ (hK1 _ h') (Subgroup.inv_mem _ hwint)
    rwa [mul_inv_cancel_right] at h2
  obtain ⟨γ, hγK, hγpos⟩ : ∃ γ : GL (Fin 2) ℚ,
      glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) * w ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) ∧
        0 < ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
    by_cases hsgn : 0 < ((Matrix.GeneralLinearGroup.det γ₀ : ℚˣ) : ℚ)
    · exact ⟨γ₀, hγ₀, hsgn⟩
    · refine ⟨epsQ * γ₀, ?_, ?_⟩
      · rw [map_mul, map_mul, mul_assoc]
        exact Subgroup.mul_mem _ (glFin_globalPoints_epsQ_mem _) hγ₀
      · have hne : ((Matrix.GeneralLinearGroup.det γ₀ : ℚˣ) : ℚ) ≠ 0 := Units.ne_zero _
        have hlt : ((Matrix.GeneralLinearGroup.det γ₀ : ℚˣ) : ℚ) < 0 := lt_of_le_of_ne (not_lt.mp hsgn) hne
        rw [map_mul, Units.val_mul, det_epsQ]
        linarith
  have hγint := hint_of γ hγK
  obtain ⟨ρ, hρ⟩ := exists_mapGL_eq_of_mem_finiteIntegralGL2 hγint hγpos
  refine ⟨ρ⁻¹, fun t => ?_⟩

  set n : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) := unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (x.1 + ratArchLine t, x.2)
    with hn
  set k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) := glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) * w with hk
  have hgfin : glFin (𝓞 ℚ) ℚ (n * (h₁ * q)) = w := by
    rw [map_mul, map_mul, hnfin t, hh₁, one_mul]
  set X : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) := globalPoints (𝓞 ℚ) ℚ γ * (n * (h₁ * q)) * (finEmbed (𝓞 ℚ) ℚ k)⁻¹
    with hX
  have hXfin : glFin (𝓞 ℚ) ℚ X = 1 := by
    rw [hX, map_mul, map_mul, map_inv, glFin_finEmbed, hgfin, hk, mul_inv_cancel]
  have hdecomp : n * (h₁ * q) = globalPoints (𝓞 ℚ) ℚ γ⁻¹ * X * finEmbed (𝓞 ℚ) ℚ k := by
    rw [hX, map_inv]; group
  have hnq : LanglandsTunnell.ratArchGL2 (n * (h₁ * q)) = LanglandsTunnell.ratArchGL2 (n * h₁) := by
    rw [← mul_assoc, ratArch_mul (n * h₁) q, ratArch_eq_one_of_glArch_eq_one hq, mul_one]
  have hXarch : LanglandsTunnell.ratArchGL2 X = (ρ : GL (Fin 2) ℝ) * LanglandsTunnell.ratArchGL2 (n * h₁) := by
    rw [hX, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one, ← hρ,
      ratArch_globalPoints_mapGL, hnq]
  have hXpos : LanglandsTunnell.ratArchGL2 X ∈ Matrix.GLPos (Fin 2) ℝ := by
    have hpos' : 0 < (LanglandsTunnell.ratArchGL2 h₁).det.val := hpos
    show 0 < (LanglandsTunnell.ratArchGL2 X).det.val
    rw [hXarch, map_mul, Units.val_mul, det_coe_SL, one_mul, ratArch_mul, map_mul, Units.val_mul,
      det_ratArch_unipotentGL2, one_mul]
    exact hpos'
  rw [hdecomp, CuspForm.IsAdelicLiftOfGamma1.apply_globalPoints_mul_mul_eq_slash_ratArchGL2_apply_I hΦ γ⁻¹ X
      (finEmbed (𝓞 ℚ) ℚ k) (finEmbed_mem_U hγK) hXfin hXpos, hXarch, coe_SL_inv, inv_inv]

end S_CuspForm_IsAdelicLiftOfGamma1_exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOfGamma1_exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I (solution)
