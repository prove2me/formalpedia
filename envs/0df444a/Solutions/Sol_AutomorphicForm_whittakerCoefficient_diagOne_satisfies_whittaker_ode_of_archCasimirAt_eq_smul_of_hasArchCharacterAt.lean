-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/643c5cae-4689-5fe3-a022-c86258c3a061

import Theorems.Thm_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt
import Theorems.Thm_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal
import Theorems.Thm_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt.AutomorphicForm IsDedekindDomain MeasureTheory"

noncomputable section

namespace Elem17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

theorem map_diagOne {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagOne a) = diagOne (Units.map f.toMonoidHom a) := by
  ext i j
  change f ((diagOne a : Matrix (Fin 2) (Fin 2) A) i j) =
    (diagOne (Units.map f.toMonoidHom a) : Matrix (Fin 2) (Fin 2) B) i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem map_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom a) := by
  ext i j
  change f ((Matrix.scalar (Fin 2) (a : A)) i j) = (Matrix.scalar (Fin 2) ((Units.map f.toMonoidHom a : Bˣ) : B)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem scalar_coe_apply {A : Type*} [CommRing A] (a : Aˣ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      if i = j then (a : A) else 0 := by
  change (Matrix.scalar (Fin 2) (a : A)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

omit [NumberField F] in
theorem glArch_ext {x y : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w x = archComponent F w y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => funext fun w => ?_
  exact congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

theorem archComponent_glArch_diagOne (w : InfinitePlace F) (a : (AdeleRing (𝓞 F) F)ˣ) :
    archComponent F w (glArch (𝓞 F) F (diagOne a)) =
      diagOne (Units.map (archEval F w).toMonoidHom (Units.map (adeleArch (𝓞 F) F).toMonoidHom a)) := by
  change Matrix.GeneralLinearGroup.map (archEval F w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 F) F) (diagOne a)) = _
  rw [map_diagOne, map_diagOne]

theorem glFin_diagOne_of_snd_eq_one (a : (AdeleRing (𝓞 F) F)ˣ) (ha : ((a : AdeleRing (𝓞 F) F)).2 = 1) :
    glFin (𝓞 F) F (diagOne a) = 1 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 F) F) (diagOne a) = 1
  rw [map_diagOne]
  have : Units.map (adeleFin (𝓞 F) F).toMonoidHom a = 1 := Units.ext ha
  rw [this, map_one]

theorem archComponent_glArch_centralScalar (w : InfinitePlace F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (archEval F w).toMonoidHom (Units.map (adeleArch (𝓞 F) F).toMonoidHom z)) := by
  change Matrix.GeneralLinearGroup.map (archEval F w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 F) F) (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) = _
  rw [map_scalar, map_scalar]

theorem glFin_centralScalar_of_snd_eq_one (z : (AdeleRing (𝓞 F) F)ˣ) (hz : ((z : AdeleRing (𝓞 F) F)).2 = 1) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F z) = 1 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 F) F) (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = 1
  rw [map_scalar]
  have : Units.map (adeleFin (𝓞 F) F).toMonoidHom z = 1 := Units.ext hz
  rw [this, map_one]

theorem glArch_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glArch (𝓞 F) F (archRealGLAt hw m) = archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
  glArch_adelicArchGLIncl F _

theorem archComponent_glArch_archRealGLAt_self {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent F w (glArch (𝓞 F) F (archRealGLAt hw m)) =
      glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]

theorem archComponent_glArch_archRealGLAt_of_ne {w w' : InfinitePlace F} (hw : w.IsReal) (hw' : w' ≠ w)
    (m : GL (Fin 2) ℝ) : archComponent F w' (glArch (𝓞 F) F (archRealGLAt hw m)) = 1 := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_of_ne F hw']

theorem glFin_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 F) F (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl F _

end Elem17

end

namespace AutomorphicForm
p2m_export "AutomorphicForm" "hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt CarrierPins productionPinsOf AdelicGL2 centralScalar finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe unipotentGL2_add archRealGLAt archRealLiftAt archRealLiftAt_of_det_ne_zero IsArchSmoothAt ArchDir splitTorusGL2 archFlowMatrix archDerivAt archCasimirAt eq_of_glArch_eq_of_glFin_eq archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl glEquivOfRingEquiv rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal archWeightCharAt rowIsometrySubgroup₀ archWeightOneℝ archWeightCharℝ HasArchCharacterAt₀ whittakerCoefficient gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight whittakerCoefficient_unipotentGL2_mul"
namespace TorusOdeAux
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K]

theorem whittakerCoefficient_smul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (c : ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ (c • φ) α g = c * whittakerCoefficient K pins ψ φ α g := by
  letI := pins.nS
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1; funext x; simp [Pi.smul_apply, smul_eq_mul]; ring

theorem archRealGLAt_mul_comm_of_archComponent_eq_one {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ)
    {g : AdelicGL2 (𝓞 K) K} (hg : archComponent K w (glArch (𝓞 K) K g) = 1) :
    archRealGLAt hw m * g = g * archRealGLAt hw m := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [map_mul, map_mul]
    apply Elem17.glArch_ext
    intro w'
    rw [map_mul, map_mul]
    by_cases hw' : w' = w
    · subst hw'; rw [hg, mul_one, one_mul]
    · rw [Elem17.archComponent_glArch_archRealGLAt_of_ne hw hw', one_mul, mul_one]
  · rw [map_mul, map_mul, Elem17.glFin_archRealGLAt, one_mul, mul_one]

theorem whittakerCoefficient_mul_of_rightChar
    (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (k : AdelicGL2 (𝓞 K) K) (c : ℂ) (hφ : ∀ g, φ (g * k) = c * φ g) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = c * whittakerCoefficient K pins ψ φ α g := by
  letI := pins.nS
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [← mul_assoc, hφ]; ring

theorem diagSign_mul_unipotent (ε : ℝ) (hε0 : ε ≠ 0) (x : ℝ) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![ε, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hε0]) * unipotentGL2 x =
      unipotentGL2 (ε * x) * Matrix.GeneralLinearGroup.mkOfDetNeZero !![ε, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hε0]) := by
  ext i j
  simp only [Units.val_mul, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.mkOfDetNeZero]

end AutomorphicForm.TorusOdeAux

open AutomorphicForm.TorusOdeAux

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (lam : ℂ) (ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hφs : IsArchSmoothAt hw φ)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d φ))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' φ)))
    (hφΩ : archCasimirAt hw φ = lam • φ)
    (hφn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) φ)
    (g₀ : AdelicGL2 (𝓞 K) K) (hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    let f : ℝ → ℂ := fun y =>
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1
        (g₀ * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]))
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * n : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by
  intro f
  classical
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he_def
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hdetP : (!![ε, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by simp [Matrix.det_fin_two_of, hε0]
  let P : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![ε, 0; 0, 1] hdetP
  let g₁ : AdelicGL2 (𝓞 K) K := g₀ * archRealGLAt hw P
  let W : (AdelicGL2 (𝓞 K) K → ℂ) → AdelicGL2 (𝓞 K) K → ℂ := fun φ' g =>
    whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (φ') 1 (g)
  let F : GL (Fin 2) ℝ → ℂ := fun h => W φ (g₁ * archRealGLAt hw h)
  have hFg : ∀ h : GL (Fin 2) ℝ, g₀ * archRealGLAt hw (P * h) = g₁ * archRealGLAt hw h := by
    intro h; simp only [g₁, map_mul, mul_assoc]

  obtain ⟨hT1, hT2, hT3⟩ :=
    AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt K D w hw φ hφc hφs hD1 hD2 g₁
  let DF : ArchDir → GL (Fin 2) ℝ → ℂ := fun d h => W (archDerivAt hw d φ) (g₁ * archRealGLAt hw h)
  let DHH : GL (Fin 2) ℝ → ℂ := fun h => W (archDerivAt hw .H (archDerivAt hw .H φ)) (g₁ * archRealGLAt hw h)
  let DEF : GL (Fin 2) ℝ → ℂ := fun h => W (archDerivAt hw .E (archDerivAt hw .Fm φ)) (g₁ * archRealGLAt hw h)
  have hD : ∀ (d : ArchDir) (h : GL (Fin 2) ℝ), HasDerivAt (fun t : ℝ => F (h * archFlowMatrix d t)) (DF d h) 0 :=
    fun d h => hT1 d h
  have hDHH : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .H (h * archFlowMatrix .H t)) (DHH h) 0 :=
    fun h => hT2 .H .H h
  have hDEF : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .Fm (h * archFlowMatrix .E t)) (DEF h) 0 :=
    fun h => hT2 .E .Fm h
  have hΩ : ∀ h : GL (Fin 2) ℝ, -((1 / 4 : ℂ) * DHH h - (1 / 2 : ℂ) * DF .H h + DEF h) = lam * F h := by
    intro h
    have h3 := hT3 h
    show -((1 / 4 : ℂ) * W _ _ - (1 / 2 : ℂ) * W _ _ + W _ _) = lam * W φ _
    rw [← h3]
    show W (archCasimirAt hw φ) _ = _
    rw [hφΩ]
    exact whittakerCoefficient_smul K _ _ lam φ 1 _

  have hper' : ∀ (G : AdelicGL2 (𝓞 K) K) (β : K) (uA : (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uA) * G) = φ (unipotentGL2 uA * G) := by
    intro G β uA; rw [unipotentGL2_add, mul_assoc, hper]
  have hN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      F (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * (ε * x)) * F h := by
    intro x h
    dsimp only [F, W]
    have h1 : g₁ * archRealGLAt hw (unipotentGL2 x * h) =
        archRealGLAt hw (unipotentGL2 (ε * x)) * (g₁ * archRealGLAt hw h) := by
      have hc := archRealGLAt_mul_comm_of_archComponent_eq_one K hw (unipotentGL2 (ε * x)) hg₀
      calc g₁ * archRealGLAt hw (unipotentGL2 x * h)
          = g₀ * (archRealGLAt hw (P * unipotentGL2 x)) * archRealGLAt hw h := by
            simp only [g₁, map_mul, mul_assoc]
        _ = g₀ * (archRealGLAt hw (unipotentGL2 (ε * x) * P)) * archRealGLAt hw h := by
            rw [diagSign_mul_unipotent ε hε0 x]
        _ = (g₀ * archRealGLAt hw (unipotentGL2 (ε * x))) * archRealGLAt hw P * archRealGLAt hw h := by
            simp only [map_mul, mul_assoc]
        _ = (archRealGLAt hw (unipotentGL2 (ε * x)) * g₀) * archRealGLAt hw P * archRealGLAt hw h := by rw [hc]
        _ = archRealGLAt hw (unipotentGL2 (ε * x)) * (g₁ * archRealGLAt hw h) := by
            simp only [g₁, mul_assoc]

    obtain ⟨hE, -⟩ := NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
      K w hw 1 (by rfl) (ε * x)
    rw [map_one, one_mul, mul_one] at hE
    dsimp only at hE
    rw [h1, hE]
    rw [AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (NumberField.StandardAddChar.stdAddChar K)
      (NumberField.StandardAddChar.adelicTraceData K).isGlobalAddChar_psiK.principalInvariant φ _ (hper' _) 1]
    rw [map_one, one_mul]
    congr 1
    have : (((1 : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 w * e.symm (ε * x) = e.symm (ε * x) := by
      rw [Units.val_one]; exact one_mul _
    rw [← he_def, this]
    have hψ := NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal K w hw (ε * x)
    rw [← he_def] at hψ
    rw [hψ]; push_cast; ring_nf

  have he' : ∀ x : ℝ, ‖e.symm x‖ = ‖x‖ := fun x => by
    rw [← AutomorphicForm.norm_ringEquivRealOfIsReal hw (e.symm x), ← he_def, e.apply_symm_apply]
  have hK : ∀ (k : GL (Fin 2) ℝ) (hk : k ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
      F (h * k) = ((archWeightCharℝ n ⟨k, hk⟩ : ℂˣ) : ℂ) * F h := by
    intro k hk h
    let k' : rowIsometrySubgroup₀ w.Completion := rowIsometrySubgroup₀Map e.symm he' ⟨k, hk⟩
    have hkk : archRealGLAt hw k = adelicArchGLInclAt K w (k' : GL (Fin 2) w.Completion) := rfl
    have hchar : archWeightCharAt hw n k' = archWeightCharℝ n ⟨k, hk⟩ := by
      show (zpowGroupHom n) (archWeightOneℝ (rowIsometrySubgroup₀Map e (AutomorphicForm.norm_ringEquivRealOfIsReal hw)
        (rowIsometrySubgroup₀Map e.symm he' ⟨k, hk⟩))) = (zpowGroupHom n) (archWeightOneℝ ⟨k, hk⟩)
      congr 2
      apply Subtype.ext
      apply Units.ext
      ext i j
      show e (e.symm ((k : Matrix (Fin 2) (Fin 2) ℝ) i j)) = (k : Matrix (Fin 2) (Fin 2) ℝ) i j
      exact e.apply_symm_apply _
    dsimp only [F, W]
    rw [map_mul, ← mul_assoc, hkk]
    rw [whittakerCoefficient_mul_of_rightChar K _ _ φ _ _ (fun g => hφn k' g) 1, hchar]

  obtain ⟨hdiff, hdiff', hode⟩ :=
    AutomorphicForm.gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
      F ε hε n lam ν hν DF DHH DEF hD hDHH hDEF hΩ hN hK

  have heq : ∀ y : ℝ, 0 < y → f y = F (splitTorusGL2 (Real.log y / 2)) := by
    intro y hy
    have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
    have hA : Matrix.of (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) =
        !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := Equiv.apply_symm_apply _ _
    have hdet : (Matrix.of (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])).det ≠ 0 := by
      rw [hA, Matrix.det_fin_two_of]; simp [hsq, hε0]
    have hM : Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet = P * splitTorusGL2 (Real.log y / 2) := by
      apply Units.ext
      show Matrix.of (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) =
        (!![ε, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (splitTorusGL2 (Real.log y / 2) : Matrix (Fin 2) (Fin 2) ℝ)
      rw [hA]
      have hexp : Real.exp (Real.log y / 2) = Real.sqrt y := by
        rw [show Real.log y / 2 = Real.log (Real.sqrt y) by rw [Real.log_sqrt hy.le], Real.exp_log (Real.sqrt_pos.2 hy)]
      have hexp' : Real.exp (-(Real.log y / 2)) = (Real.sqrt y)⁻¹ := by rw [Real.exp_neg, hexp]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, splitTorusGL2, hexp, hexp']
    show W φ (g₀ * archRealLiftAt hw _) = W φ (g₁ * archRealGLAt hw _)
    rw [archRealLiftAt_of_det_ne_zero hw hdet, hM, hFg]
  have heqOn : Set.EqOn f (fun y => F (splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) := fun y hy => heq y hy
  have hev : ∀ y : ℝ, 0 < y → f =ᶠ[nhds y] fun y => F (splitTorusGL2 (Real.log y / 2)) := by
    intro y hy
    filter_upwards [Ioi_mem_nhds hy] with s hs using heq s hs
  have hder : ∀ y : ℝ, 0 < y → deriv f y = deriv (fun y => F (splitTorusGL2 (Real.log y / 2))) y :=
    fun y hy => (hev y hy).deriv_eq
  have hevd : ∀ y : ℝ, 0 < y → deriv f =ᶠ[nhds y] deriv (fun y => F (splitTorusGL2 (Real.log y / 2))) := by
    intro y hy
    filter_upwards [Ioi_mem_nhds hy] with s hs using hder s hs
  refine ⟨hdiff.congr heqOn, hdiff'.congr (fun y hy => hder y hy), ?_⟩
  intro y hy
  rw [(hevd y hy).deriv_eq, heq y hy]
  exact hode y hy

end S_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt (solution)
