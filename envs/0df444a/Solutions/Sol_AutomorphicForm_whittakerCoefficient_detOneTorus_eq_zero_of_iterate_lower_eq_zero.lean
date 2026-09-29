-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f80284e9-f2e1-561a-9041-6c92ad8a19cb

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Theorems.Thm_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal
import Theorems.Thm_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
import Theorems.Thm_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
import Theorems.Thm_LanglandsTunnell_eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

open MeasureTheory

noncomputable section

namespace Os17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicHaar

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
private theorem glArch_ext {x y : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w x = archComponent F w y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => funext fun w => ?_
  exact congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

private theorem archRealGLAt_mul_comm_of_archComponent_eq_one {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ)
    {g : AdelicGL2 (𝓞 F) F} (hg : archComponent F w (glArch (𝓞 F) F g) = 1) :
    archRealGLAt hw m * g = g * archRealGLAt hw m := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [map_mul, map_mul]
    apply glArch_ext
    intro w'
    rw [map_mul, map_mul]
    by_cases hw' : w' = w
    · subst hw'; rw [hg, mul_one, one_mul]
    · rw [show glArch (𝓞 F) F (archRealGLAt hw m) = archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) from
        glArch_adelicArchGLIncl F _, archComponent_archGLIncl_of_ne F hw', one_mul, mul_one]
  · rw [map_mul, map_mul, show glFin (𝓞 F) F (archRealGLAt hw m) = 1 from glFin_adelicArchGLIncl F _, one_mul, mul_one]

omit [NumberField F] in

private theorem diagSign_mul_unipotent (ε : ℝ) (hε0 : ε ≠ 0) (x : ℝ) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![ε, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hε0]) * unipotentGL2 x =
      unipotentGL2 (ε * x) * Matrix.GeneralLinearGroup.mkOfDetNeZero !![ε, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hε0]) := by
  ext i j
  simp only [Units.val_mul, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.mkOfDetNeZero]

omit [NumberField F] in

private theorem splitTorus_mul_unipotent (s x : ℝ) :
    splitTorusGL2 s * unipotentGL2 x = unipotentGL2 (Real.exp (2 * s) * x) * splitTorusGL2 s := by
  ext i j
  simp only [Units.val_mul, unipotentGL2_coe, splitTorusGL2_coe]
  have h2 : Real.exp (2 * s) * x * Real.exp (-s) = Real.exp s * x := by
    rw [show (2 : ℝ) * s = s + s by ring, Real.exp_add, Real.exp_neg]; field_simp
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

private abbrev pins (D : Set (AdelicGL2 (𝓞 F) F)) :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private abbrev W (D : Set (AdelicGL2 (𝓞 F) F)) (x : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  whittakerCoefficient F (pins D) (NumberField.StandardAddChar.stdAddChar F) x 1 g

private theorem W_smul (D : Set (AdelicGL2 (𝓞 F) F)) (c : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    W D (c • x) g = c * W D x g := by
  letI := (pins (F := F) D).nS
  show (∫ u, (c • x) (unipotentGL2 u * g) * _ ∂(pins D).ν) = c * ∫ u, x (unipotentGL2 u * g) * _ ∂(pins D).ν
  rw [← integral_const_mul]
  congr 1; funext u; simp only [Pi.smul_apply, smul_eq_mul]; ring

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

omit [NumberField F] in
private theorem continuous_unipotentGL2 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ fun x : A => (unipotentGL2 x : GL (Fin 2) A)) = fun x => !![(1 : A), x; 0, 1] :=
      funext fun x => unipotentGL2_coe x
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun x : A => (((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) =
        fun x => !![(1 : A), -x; 0, 1] := funext fun x => rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem psi_continuous : Continuous (NumberField.StandardAddChar.stdAddChar F : AdeleRing (𝓞 F) F → ℂ) :=
  (NumberField.StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK.continuous

private theorem integrable_integrand (D : Set (AdelicGL2 (𝓞 F) F)) {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Continuous x) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun u : AdeleRing (𝓞 F) F => x (unipotentGL2 u * g) *
      NumberField.StandardAddChar.stdAddChar F (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u))) (pins D).ν := by
  have hc : Continuous fun u : AdeleRing (𝓞 F) F => x (unipotentGL2 u * g) *
      NumberField.StandardAddChar.stdAddChar F (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u)) :=
    (hx.comp ((continuous_unipotentGL2 (A := AdeleRing (𝓞 F) F)).mul continuous_const)).mul (psi_continuous.comp (continuous_const.mul continuous_id).neg)
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  haveI : IsProbabilityMeasure (pins (F := F) D).ν := isProbabilityMeasure_cond_adelicBox F
  refine Integrable.of_bound hc.aestronglyMeasurable M ?_
  have : ∀ᵐ u ∂((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)), ‖x (unipotentGL2 u * g) *
      NumberField.StandardAddChar.stdAddChar F (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u))‖ ≤ M :=
    (ae_restrict_iff' (measurableSet_adelicBox F)).mpr (Filter.Eventually.of_forall fun u hu => hM u (hBC hu))
  show ∀ᵐ u ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)), _
  exact Measure.ae_smul_measure this _

private theorem W_sub (D : Set (AdelicGL2 (𝓞 F) F)) {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous x₁) (h₂ : Continuous x₂) (g : AdelicGL2 (𝓞 F) F) :
    W D (x₁ - x₂) g = W D x₁ g - W D x₂ g := by
  letI := (pins (F := F) D).nS
  show (∫ u, (x₁ - x₂) (unipotentGL2 u * g) * _ ∂(pins D).ν) = (∫ u, x₁ (unipotentGL2 u * g) * _ ∂(pins D).ν) - ∫ u, x₂ (unipotentGL2 u * g) * _ ∂(pins D).ν
  rw [← integral_sub (integrable_integrand D h₁ g) (integrable_integrand D h₂ g)]
  congr 1; funext u; simp only [Pi.sub_apply]; ring

private theorem W_add (D : Set (AdelicGL2 (𝓞 F) F)) {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous x₁) (h₂ : Continuous x₂) (g : AdelicGL2 (𝓞 F) F) :
    W D (x₁ + x₂) g = W D x₁ g + W D x₂ g := by
  letI := (pins (F := F) D).nS
  show (∫ u, (x₁ + x₂) (unipotentGL2 u * g) * _ ∂(pins D).ν) = (∫ u, x₁ (unipotentGL2 u * g) * _ ∂(pins D).ν) + ∫ u, x₂ (unipotentGL2 u * g) * _ ∂(pins D).ν
  rw [← integral_add (integrable_integrand D h₁ g) (integrable_integrand D h₂ g)]
  congr 1; funext u; simp only [Pi.add_apply]; ring

end Os17

namespace Os17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicHaar

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

private structure Reg (x : AdelicGL2 (𝓞 F) F → ℂ) : Prop where
  cont : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) x)
  smooth : IsArchSmoothAt hw x
  per : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F), x (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = x g

private theorem smooth_foldr {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : IsArchSmoothAt hw x) (l : List ArchDir) :
    IsArchSmoothAt hw (l.foldr (archDerivAt hw) x) := by
  induction l with
  | nil => exact hx
  | cons d l ih => exact ih.archDerivAt d

private theorem foldr_smul (c : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) (l : List ArchDir) :
    l.foldr (archDerivAt hw) (c • x) = c • l.foldr (archDerivAt hw) x := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [List.foldr_cons, List.foldr_cons, ih, archDerivAt_smul]

private theorem foldr_add {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : IsArchSmoothAt hw x₁) (h₂ : IsArchSmoothAt hw x₂) (l : List ArchDir) :
    l.foldr (archDerivAt hw) (x₁ + x₂) = l.foldr (archDerivAt hw) x₁ + l.foldr (archDerivAt hw) x₂ := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, archDerivAt_add (smooth_foldr hw h₁ l) (smooth_foldr hw h₂ l)]

private theorem reg_deriv {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (d : ArchDir) : Reg hw (archDerivAt hw d x) where
  cont l := by
    have h := hx.cont (l ++ [d])
    rwa [List.foldr_append] at h
  smooth := hx.smooth.archDerivAt d
  per β g := by
    show _root_.deriv (fun t : ℝ => x (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g * archFlowAt hw d t)) 0 =
      _root_.deriv (fun t : ℝ => x (g * archFlowAt hw d t)) 0
    congr 1; funext t; rw [mul_assoc, hx.per]

private theorem reg_smul {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (c : ℂ) : Reg hw (c • x) where
  cont l := by rw [foldr_smul]; exact (hx.cont l).const_smul c
  smooth := hx.smooth.smul c
  per β g := by simp only [Pi.smul_apply, hx.per]

private theorem reg_add {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Reg hw x₁) (h₂ : Reg hw x₂) : Reg hw (x₁ + x₂) where
  cont l := by rw [foldr_add hw h₁.smooth h₂.smooth]; exact (h₁.cont l).add (h₂.cont l)
  smooth := h₁.smooth.add h₂.smooth
  per β g := by simp only [Pi.add_apply, h₁.per, h₂.per]

private theorem reg_sub {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Reg hw x₁) (h₂ : Reg hw x₂) : Reg hw (x₁ - x₂) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ x₂]; exact reg_add hw h₁ (reg_smul hw h₂ (-1))

private theorem reg_continuous {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) : Continuous x := hx.cont []

private theorem reg_hD1 {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (d : ArchDir) : Continuous (archDerivAt hw d x) := hx.cont [d]

private theorem reg_hD2 {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (d d' : ArchDir) :
    Continuous (archDerivAt hw d (archDerivAt hw d' x)) := hx.cont [d, d']

private def op (σ : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .H x + σ • (archDerivAt hw .E x + archDerivAt hw .Fm x)

private theorem reg_op {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (σ : ℂ) : Reg hw (op hw σ x) :=
  reg_add hw (reg_deriv hw hx .H) (reg_smul hw (reg_add hw (reg_deriv hw hx .E) (reg_deriv hw hx .Fm)) σ)

private theorem reg_op_iter {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (σ : ℂ) (j : ℕ) : Reg hw ((op hw σ)^[j] x) := by
  induction j with
  | zero => exact hx
  | succ j ih => rw [Function.iterate_succ_apply']; exact reg_op hw ih σ

private theorem op_apply (σ : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    op hw σ x g = archDerivAt hw .H x g + σ * (archDerivAt hw .E x g + archDerivAt hw .Fm x g) := by
  simp only [op, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

section Torus

variable (D : Set (AdelicGL2 (𝓞 F) F)) (g₀ : AdelicGL2 (𝓞 F) F) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)

private theorem hε0' (hε : ε = 1 ∨ ε = -1) : -ε ≠ 0 := by rcases hε with h | h <;> simp [h]

private def P : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![-ε, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hε0' ε hε])

private def g₁ : AdelicGL2 (𝓞 F) F := g₀ * archRealGLAt hw (P ε hε)

private def Fx (x : AdelicGL2 (𝓞 F) F → ℂ) (h : GL (Fin 2) ℝ) : ℂ := W D x (g₁ hw g₀ ε hε * archRealGLAt hw h)

private def φ (x : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) : ℂ := Fx hw D g₀ ε hε x (splitTorusGL2 (Real.log t / 2))

private theorem hasDerivAt_Fx_flow {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (d : ArchDir) (h : GL (Fin 2) ℝ) :
    HasDerivAt (fun s : ℝ => Fx hw D g₀ ε hε x (h * archFlowMatrix d s)) (Fx hw D g₀ ε hε (archDerivAt hw d x) h) 0 :=
  (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt F D w hw x (reg_continuous hw hx) hx.smooth
    (reg_hD1 hw hx) (reg_hD2 hw hx) (g₁ hw g₀ ε hε)).1 d h

private theorem Fx_unipotent (hg₀ : archComponent F w (glArch (𝓞 F) F g₀) = 1) {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (u : ℝ) (h : GL (Fin 2) ℝ) :
    Fx hw D g₀ ε hε x (unipotentGL2 u * h) = Complex.exp (2 * Real.pi * Complex.I * ((-ε) * u)) * Fx hw D g₀ ε hε x h := by
  classical
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he_def
  have hper' : ∀ (G : AdelicGL2 (𝓞 F) F) (β : F) (uA : (AdeleRing (𝓞 F) F)),
      x (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + uA) * G) = x (unipotentGL2 uA * G) := by
    intro G β uA; rw [unipotentGL2_add, mul_assoc, hx.per]
  dsimp only [Fx, W]
  have h1 : g₁ hw g₀ ε hε * archRealGLAt hw (unipotentGL2 u * h) =
      archRealGLAt hw (unipotentGL2 ((-ε) * u)) * (g₁ hw g₀ ε hε * archRealGLAt hw h) := by
    have hc := archRealGLAt_mul_comm_of_archComponent_eq_one hw (unipotentGL2 ((-ε) * u)) hg₀
    calc g₁ hw g₀ ε hε * archRealGLAt hw (unipotentGL2 u * h)
        = g₀ * (archRealGLAt hw (P ε hε * unipotentGL2 u)) * archRealGLAt hw h := by
          simp only [g₁, map_mul, mul_assoc]
      _ = g₀ * (archRealGLAt hw (unipotentGL2 ((-ε) * u) * P ε hε)) * archRealGLAt hw h := by
          rw [P, diagSign_mul_unipotent (-ε) (hε0' ε hε) u]
      _ = (g₀ * archRealGLAt hw (unipotentGL2 ((-ε) * u))) * archRealGLAt hw (P ε hε) * archRealGLAt hw h := by
          simp only [map_mul, mul_assoc]
      _ = (archRealGLAt hw (unipotentGL2 ((-ε) * u)) * g₀) * archRealGLAt hw (P ε hε) * archRealGLAt hw h := by rw [hc]
      _ = archRealGLAt hw (unipotentGL2 ((-ε) * u)) * (g₁ hw g₀ ε hε * archRealGLAt hw h) := by
          simp only [g₁, mul_assoc]
  obtain ⟨hE, -⟩ := NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
    F w hw 1 (by rfl) ((-ε) * u)
  rw [map_one, one_mul, mul_one] at hE
  dsimp only at hE
  rw [h1, hE]
  rw [AutomorphicForm.whittakerCoefficient_unipotentGL2_mul F D
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (NumberField.StandardAddChar.stdAddChar F)
    (NumberField.StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK.principalInvariant x _ (hper' _) 1]
  rw [map_one, one_mul]
  congr 1
  have : (((1 : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F))).1 w * e.symm ((-ε) * u) = e.symm ((-ε) * u) := by
    rw [Units.val_one]; exact one_mul _
  rw [← he_def, this]
  have hψ := NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal F w hw ((-ε) * u)
  rw [← he_def] at hψ
  rw [hψ]; push_cast; ring_nf

private theorem hasDerivAt_φ {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (φ hw D g₀ ε hε x) (((t⁻¹ / 2 : ℝ) : ℂ) * φ hw D g₀ ε hε (archDerivAt hw .H x) t) t := by

  set s₀ := Real.log t / 2 with hs₀
  have h1 : HasDerivAt (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 (s₀ + s)))
      (Fx hw D g₀ ε hε (archDerivAt hw .H x) (splitTorusGL2 s₀)) 0 := by
    have h := hasDerivAt_Fx_flow hw D g₀ ε hε hx .H (splitTorusGL2 s₀)
    have hfun : (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 s₀ * archFlowMatrix .H s)) =
        fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 (s₀ + s)) := by
      funext s; rw [show archFlowMatrix .H s = splitTorusGL2 s from rfl, ← splitTorusGL2_add]
    rwa [hfun] at h
  have h2 : HasDerivAt (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 s))
      (Fx hw D g₀ ε hε (archDerivAt hw .H x) (splitTorusGL2 s₀)) s₀ := by
    have h1' : HasDerivAt (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 (s₀ + s)))
        (Fx hw D g₀ ε hε (archDerivAt hw .H x) (splitTorusGL2 s₀)) (-s₀ + s₀) := by rwa [neg_add_cancel]
    have h := h1'.comp_const_add (-s₀) s₀
    simp only [add_neg_cancel_left] at h
    exact h
  have h3 : HasDerivAt (fun t : ℝ => Real.log t / 2) (t⁻¹ / 2) t := (Real.hasDerivAt_log ht.ne').div_const 2
  have h4 := h2.scomp t h3
  simp [Function.comp_def, φ, hs₀] at h4 ⊢
  exact h4

private theorem φ_E (hg₀ : archComponent F w (glArch (𝓞 F) F g₀) = 1) {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) {t : ℝ} (ht : 0 < t) :
    φ hw D g₀ ε hε (archDerivAt hw .E x) t = (2 * Real.pi * Complex.I * ((-ε) * t)) * φ hw D g₀ ε hε x t := by
  set s₀ := Real.log t / 2 with hs₀
  have hexp : Real.exp (2 * s₀) = t := by rw [hs₀, mul_div_cancel₀ _ (two_ne_zero), Real.exp_log ht]
  have h := hasDerivAt_Fx_flow hw D g₀ ε hε hx .E (splitTorusGL2 s₀)
  set c : ℂ := 2 * Real.pi * Complex.I * ((-ε) * t) with hc
  set Kx : ℂ := Fx hw D g₀ ε hε x (splitTorusGL2 s₀) with hKx
  have hfun : (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 s₀ * archFlowMatrix .E s)) =
      fun s : ℝ => Complex.exp (c * (s : ℂ)) * Kx := by
    funext s
    rw [show archFlowMatrix .E s = unipotentGL2 s from rfl, splitTorus_mul_unipotent, Fx_unipotent hw D g₀ ε hε hg₀ hx, hexp]
    congr 2; push_cast; ring
  rw [hfun] at h
  have h5 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c
  have h' : HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ)) * Kx) (c * Kx) 0 := by
    have h6 := (h5.cexp).mul_const Kx
    simpa using h6
  have := h.unique h'
  show Fx hw D g₀ ε hε (archDerivAt hw .E x) (splitTorusGL2 s₀) = c * Kx
  exact this

private theorem point_eq {t : ℝ} (ht : 0 < t) :
    g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]) =
      g₁ hw g₀ ε hε * archRealGLAt hw (splitTorusGL2 (Real.log t / 2)) := by
  have hsq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hA : Matrix.of (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]) =
      !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] := Equiv.apply_symm_apply _ _
  have hdet : (Matrix.of (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])).det ≠ 0 := by
    rw [hA, Matrix.det_fin_two_of]; simp [hsq, hε0' ε hε]
  have hM : Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet = P ε hε * splitTorusGL2 (Real.log t / 2) := by
    apply Units.ext
    show Matrix.of (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]) =
      (!![-ε, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (splitTorusGL2 (Real.log t / 2) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hA]
    have hexp : Real.exp (Real.log t / 2) = Real.sqrt t := by
      rw [show Real.log t / 2 = Real.log (Real.sqrt t) by rw [Real.log_sqrt ht.le], Real.exp_log (Real.sqrt_pos.2 ht)]
    have hexp' : Real.exp (-(Real.log t / 2)) = (Real.sqrt t)⁻¹ := by rw [Real.exp_neg, hexp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, splitTorusGL2, hexp, hexp']
  rw [archRealLiftAt_of_det_ne_zero hw hdet, hM, g₁, map_mul, mul_assoc]

end Torus

end Os17

namespace Os17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicHaar

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

section Lin

variable (D : Set (AdelicGL2 (𝓞 F) F)) (g₀ : AdelicGL2 (𝓞 F) F) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)

private theorem φ_smul (c : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) : φ hw D g₀ ε hε (c • x) t = c * φ hw D g₀ ε hε x t :=
  W_smul D c x _

private theorem φ_add {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous x₁) (h₂ : Continuous x₂) (t : ℝ) :
    φ hw D g₀ ε hε (x₁ + x₂) t = φ hw D g₀ ε hε x₁ t + φ hw D g₀ ε hε x₂ t :=
  W_add D h₁ h₂ _

private theorem φ_sub {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous x₁) (h₂ : Continuous x₂) (t : ℝ) :
    φ hw D g₀ ε hε (x₁ - x₂) t = φ hw D g₀ ε hε x₁ t - φ hw D g₀ ε hε x₂ t :=
  W_sub D h₁ h₂ _

private theorem φ_op {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (σ μ : ℂ)
    (hμ : archDerivAt hw .E x - archDerivAt hw .Fm x = μ • x) (t : ℝ) :
    φ hw D g₀ ε hε (op hw σ x) t = φ hw D g₀ ε hε (archDerivAt hw .H x) t +
      σ * (2 * φ hw D g₀ ε hε (archDerivAt hw .E x) t - μ * φ hw D g₀ ε hε x t) := by
  have hF : archDerivAt hw .Fm x = archDerivAt hw .E x - μ • x := by
    rw [← hμ]; abel
  have hEF : archDerivAt hw .E x + archDerivAt hw .Fm x = (2 : ℂ) • archDerivAt hw .E x - μ • x := by
    rw [hF, two_smul]; abel
  unfold op
  have c1 : Continuous ((2 : ℂ) • archDerivAt hw .E x - μ • x) := ((reg_hD1 hw hx .E).const_smul (2 : ℂ)).sub ((reg_continuous hw hx).const_smul μ)
  have c2 : Continuous (σ • ((2 : ℂ) • archDerivAt hw .E x - μ • x)) := c1.const_smul σ
  rw [hEF, φ_add hw D g₀ ε hε (x₁ := archDerivAt hw .H x) (x₂ := σ • ((2 : ℂ) • archDerivAt hw .E x - μ • x)) (reg_hD1 hw hx .H) c2,
    φ_smul, φ_sub hw D g₀ ε hε (x₁ := (2 : ℂ) • archDerivAt hw .E x) (x₂ := μ • x) ((reg_hD1 hw hx .E).const_smul (2 : ℂ))
      ((reg_continuous hw hx).const_smul μ), φ_smul, φ_smul]

end Lin

private theorem main (D : Set (AdelicGL2 (𝓞 F) F))
    (y : AdelicGL2 (𝓞 F) F → ℂ) (hyc : Continuous y)
    (hper : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F), y (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = y g)
    (hys : IsArchSmoothAt hw y)
    (hD : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) y))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (k₀ M : ℕ) (hk₀ : 1 ≤ k₀) (n : ℤ) (hn : (n : ℝ) = ε * (k₀ + 2 * M))
    (hm : archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y)
    (hΩ : archCasimirAt hw y = (((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2)) • y)
    (hlow : (fun x : AdelicGL2 (𝓞 F) F → ℂ =>
        archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M + 1] y = 0)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : archComponent F w (glArch (𝓞 F) F g₀) = 1)
    (C : ℝ) (Ngr : ℕ)
    (hgrowth : ∀ t : ℝ, 1 ≤ t →
      ‖W D (((fun x : AdelicGL2 (𝓞 F) F → ℂ =>
            archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M] y))
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]))‖ ≤ C * t ^ Ngr)
    (t : ℝ) (ht : 0 < t) :
    W D y (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])) = 0 := by

  set σR : ℂ := (ε : ℂ) * Complex.I with hσR
  set σL : ℂ := -σR with hσL
  have hL : (fun x : AdelicGL2 (𝓞 F) F → ℂ =>
      archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x)) = op hw σL := by
    funext x; simp only [op, hσL, hσR, neg_smul, sub_eq_add_neg]
  rw [hL] at hlow hgrowth
  have hε2 : (ε : ℂ) ^ 2 = 1 := by rcases hε with h | h <;> simp [h]
  have regy : Reg hw y := ⟨hD, hys, hper⟩

  set y₀ := (op hw σL)^[M] y with hy₀
  have regy₀ : Reg hw y₀ := reg_op_iter hw regy σL M
  have hLy₀ : op hw σL y₀ = 0 := by rw [hy₀, ← Function.iterate_succ_apply' (op hw σL) M y]; exact hlow

  set lam : ℂ := ((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2) with hlam
  have halg : (∀ j : ℕ, archDerivAt hw .E ((op hw σR)^[j] y₀) - archDerivAt hw .Fm ((op hw σR)^[j] y₀) =
        (Complex.I * ε * ((k₀ : ℂ) + 2 * j)) • (op hw σR)^[j] y₀) ∧
      ∃ Pc : ℂ, Pc ≠ 0 ∧ (op hw σR)^[M] y₀ = Pc • y := by
    have HA := AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul F w hw y hys (Complex.I * n) lam hm hΩ
    obtain ⟨hlo, hra, hRL, hLR⟩ := HA

    have hfac : ∀ j : ℕ, j < M → ∀ q : ℂ, q = (k₀ : ℂ) + 2 * ((M - j : ℕ) : ℂ) → -4 * lam - q ^ 2 + 2 * q ≠ 0 := by
      intro j hj q hq
      have h1 : -4 * lam - q ^ 2 + 2 * q = ((k₀ : ℂ) - q) * ((k₀ : ℂ) + q - 2) := by rw [hlam]; ring
      rw [h1, hq]
      have hMj : 1 ≤ M - j := by omega
      refine mul_ne_zero ?_ ?_
      · have : ((k₀ : ℂ) - ((k₀ : ℂ) + 2 * ((M - j : ℕ) : ℂ))) = -(2 * ((M - j : ℕ) : ℂ)) := by ring
        rw [this, neg_ne_zero]
        exact_mod_cast (show (2 * (M - j) : ℕ) ≠ 0 by omega)
      · have : ((k₀ : ℂ) + ((k₀ : ℂ) + 2 * ((M - j : ℕ) : ℂ)) - 2) = (((2 * k₀ + 2 * (M - j) - 2 : ℕ)) : ℂ) := by
          have h2 : 2 ≤ 2 * k₀ + 2 * (M - j) := by omega
          push_cast [Nat.cast_sub h2]
          ring
        rw [this]
        exact_mod_cast (show (2 * k₀ + 2 * (M - j) - 2 : ℕ) ≠ 0 by omega)
    rcases hε with rfl | rfl
    ·
      have hn1 : (n : ℝ) = ((k₀ + 2 * M : ℕ) : ℝ) := by rw [hn]; push_cast; ring
      have hn2 : n = ((k₀ + 2 * M : ℕ) : ℤ) := by exact_mod_cast hn1
      have hnZ : (n : ℂ) = (k₀ : ℂ) + 2 * M := by rw [hn2]; push_cast; ring
      have eL : op hw σL = fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x) := by
        funext x; simp only [op, hσL, hσR, Complex.ofReal_one, one_mul, neg_smul, sub_eq_add_neg]
      have eR : op hw σR = fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x) := by
        funext x; simp only [op, hσR, Complex.ofReal_one, one_mul]

      obtain ⟨hy₀s, hy₀w, hy₀Ω⟩ := hlo M
      rw [← eL] at hy₀s hy₀w hy₀Ω
      have HB := AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul F w hw y₀ hy₀s _ lam hy₀w hy₀Ω
      obtain ⟨-, hra₀, -, -⟩ := HB
      refine ⟨fun j => ?_, ⟨∏ j ∈ Finset.range M, (-4 * lam + (Complex.I * n - 2 * Complex.I * j) ^ 2 -
        2 * Complex.I * (Complex.I * n - 2 * Complex.I * j)), ?_, ?_⟩⟩
      · obtain ⟨-, hwj, -⟩ := hra₀ j
        rw [← eR] at hwj
        rw [hwj]; congr 1; rw [hnZ]; push_cast; ring
      · rw [Finset.prod_ne_zero_iff]
        intro j hj
        rw [Finset.mem_range] at hj
        have := hfac j hj ((n : ℂ) - 2 * j) (by rw [hnZ]; push_cast [Nat.cast_sub hj.le]; ring)
        convert this using 1
        ring_nf; simp only [Complex.I_sq]; ring
      · rw [← eR, ← eL] at hRL; exact hRL M
    ·
      have hn1 : (n : ℝ) = -((k₀ + 2 * M : ℕ) : ℝ) := by rw [hn]; push_cast; ring
      have hn2 : n = -((k₀ + 2 * M : ℕ) : ℤ) := by exact_mod_cast hn1
      have hnZ : (n : ℂ) = -((k₀ : ℂ) + 2 * M) := by rw [hn2]; push_cast; ring
      have eL : op hw σL = fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x) := by
        funext x; simp only [op, hσL, hσR]; push_cast; simp only [neg_mul, one_mul, neg_neg]
      have eR : op hw σR = fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x) := by
        funext x; simp only [op, hσR]; push_cast; simp only [neg_mul, one_mul, neg_smul, sub_eq_add_neg]
      obtain ⟨hy₀s, hy₀w, hy₀Ω⟩ := hra M
      rw [← eL] at hy₀s hy₀w hy₀Ω
      have HB := AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul F w hw y₀ hy₀s _ lam hy₀w hy₀Ω
      obtain ⟨hlo₀, -, -, -⟩ := HB
      refine ⟨fun j => ?_, ⟨∏ j ∈ Finset.range M, (-4 * lam + (Complex.I * n + 2 * Complex.I * j) ^ 2 +
        2 * Complex.I * (Complex.I * n + 2 * Complex.I * j)), ?_, ?_⟩⟩
      · obtain ⟨-, hwj, -⟩ := hlo₀ j
        rw [← eR] at hwj
        rw [hwj]; congr 1; rw [hnZ]; push_cast; ring
      · rw [Finset.prod_ne_zero_iff]
        intro j hj
        rw [Finset.mem_range] at hj
        have := hfac j hj (-((n : ℂ) + 2 * j)) (by rw [hnZ]; push_cast [Nat.cast_sub hj.le]; ring)
        convert this using 1
        ring_nf; simp only [Complex.I_sq]; ring
      · rw [← eR, ← eL] at hLR; exact hLR M
  obtain ⟨hwt, Pc, hPc, hRM⟩ := halg
  have hε' : ε = 1 ∨ ε = -1 := hε

  have hφE := fun (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : Reg hw x) {s : ℝ} (hs : 0 < s) => φ_E hw D g₀ ε hε' hg₀ hx hs

  have hμ₀ := hwt 0
  simp only [Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, add_zero] at hμ₀
  have hHy₀ : archDerivAt hw .H y₀ = (-σL) • (archDerivAt hw .E y₀ + archDerivAt hw .Fm y₀) := by
    have h := hLy₀
    unfold op at h
    rw [neg_smul, eq_neg_iff_add_eq_zero, h]
  have hderiv₀ : ∀ s : ℝ, 0 < s → HasDerivAt (φ hw D g₀ ε hε' y₀)
      ((((k₀ : ℂ) / 2) / (s : ℂ) + 2 * Real.pi) * φ hw D g₀ ε hε' y₀ s) s := by
    intro s hs
    have h1 := hasDerivAt_φ hw D g₀ ε hε' regy₀ hs
    have hF : archDerivAt hw .Fm y₀ = archDerivAt hw .E y₀ - (Complex.I * ε * k₀) • y₀ := by rw [← hμ₀]; abel
    have h2 : φ hw D g₀ ε hε' (archDerivAt hw .H y₀) s = (-σL) * (2 * φ hw D g₀ ε hε' (archDerivAt hw .E y₀) s
        - (Complex.I * ε * k₀) * φ hw D g₀ ε hε' y₀ s) := by
      rw [hHy₀, φ_smul, hF, show archDerivAt hw .E y₀ + (archDerivAt hw .E y₀ - (Complex.I * ε * k₀) • y₀) =
        (2 : ℂ) • archDerivAt hw .E y₀ - (Complex.I * ε * k₀) • y₀ by rw [two_smul]; abel,
        φ_sub hw D g₀ ε hε' (x₁ := (2 : ℂ) • archDerivAt hw .E y₀) (x₂ := (Complex.I * ε * k₀) • y₀)
          ((reg_hD1 hw regy₀ .E).const_smul (2 : ℂ)) ((reg_continuous hw regy₀).const_smul (Complex.I * ε * k₀)), φ_smul, φ_smul]
    rw [h2, hφE y₀ regy₀ hs] at h1
    convert h1 using 1
    rw [hσL, hσR]
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq, hε2]
    ring
  have hzero₀ : ∀ s : ℝ, 0 < s → φ hw D g₀ ε hε' y₀ s = 0 := by
    refine LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow ((k₀ : ℂ) / 2) (2 * Real.pi) (by simp [Real.pi_pos])
      (φ hw D g₀ ε hε' y₀) (fun s hs => (hderiv₀ s hs).differentiableAt.differentiableWithinAt) (fun s hs => (hderiv₀ s hs).deriv)
      C Ngr (fun s hs => ?_)
    have h := hgrowth s hs
    rwa [point_eq hw g₀ ε hε' (lt_of_lt_of_le one_pos hs)] at h

  have hzero : ∀ j : ℕ, ∀ s : ℝ, 0 < s → φ hw D g₀ ε hε' ((op hw σR)^[j] y₀) s = 0 := by
    intro j
    induction j with
    | zero => exact hzero₀
    | succ j ih =>
      intro s hs
      have regj : Reg hw ((op hw σR)^[j] y₀) := reg_op_iter hw regy₀ σR j
      rw [Function.iterate_succ_apply', φ_op hw D g₀ ε hε' regj σR _ (hwt j), hφE _ regj hs, ih s hs]

      have h1 := hasDerivAt_φ hw D g₀ ε hε' regj hs
      have h0 : HasDerivAt (φ hw D g₀ ε hε' ((op hw σR)^[j] y₀)) 0 s := by
        refine (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hs] with u hu using ih u hu
      have huniq := h1.unique h0
      have hs0 : ((s⁻¹ / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      have hH : φ hw D g₀ ε hε' (archDerivAt hw .H ((op hw σR)^[j] y₀)) s = 0 := (mul_eq_zero.mp huniq).resolve_left hs0
      rw [hH]; ring

  have hy : y = Pc⁻¹ • (op hw σR)^[M] y₀ := by rw [hRM, smul_smul, inv_mul_cancel₀ hPc, one_smul]
  have := hzero M t ht
  rw [point_eq hw g₀ ε hε' ht, hy, W_smul]
  show Pc⁻¹ * φ hw D g₀ ε hε' ((op hw σR)^[M] y₀) t = 0
  rw [this, mul_zero]

end Os17

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hyc : Continuous y)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K), y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = y g)
    (hys : IsArchSmoothAt hw y)
    (hD : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) y))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (k₀ M : ℕ) (hk₀ : 1 ≤ k₀) (n : ℤ) (hn : (n : ℝ) = ε * (k₀ + 2 * M))
    (hm : archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y)
    (hΩ : archCasimirAt hw y = (((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2)) • y)
    (hlow : (fun x : AdelicGL2 (𝓞 K) K → ℂ =>
        archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M + 1] y = 0)
    (g₀ : AdelicGL2 (𝓞 K) K) (hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (C : ℝ) (Ngr : ℕ)
    (hgrowth : ∀ t : ℝ, 1 ≤ t →
      ‖whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (((fun x : AdelicGL2 (𝓞 K) K → ℂ =>
            archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M] y)) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]))‖ ≤ C * t ^ Ngr)
    (t : ℝ) (ht : 0 < t) :
    whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (y) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])) = 0 :=
  Os17.main hw D y hyc hper hys hD ε hε k₀ M hk₀ n hn hm hΩ hlow g₀ hg₀ C Ngr hgrowth t ht

end S_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero (solution)
