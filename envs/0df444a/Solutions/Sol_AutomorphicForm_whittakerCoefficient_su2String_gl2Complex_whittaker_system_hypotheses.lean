-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/346f7c54-9a87-5d0a-8d35-006ef3270c76

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

noncomputable section

open scoped Classical

namespace E40DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

abbrev eC {w : InfinitePlace K} (hw : w.IsComplex) : w.Completion ≃+* ℂ := ringEquivComplexOfIsComplex hw

def iotaW {w : InfinitePlace K} (hw : w.IsComplex) : ℂˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (archUnitHom w).comp (Units.map (eC hw).symm.toRingHom.toMonoidHom)

def bprime (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  b * (archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹

def g0 (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) : AdelicGL2 (𝓞 K) K := diagOne (bprime w b)

abbrev W (D : Set (AdelicGL2 (𝓞 K) K)) (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  whittakerCoefficient K (productionPinsOf K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
    (NumberField.StandardAddChar.stdAddChar K) φ 1 g

def Fstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (h : GL (Fin 2) ℂ) : ℂ :=
  W D (x p) (g0 w b * archComplexGLAt hw h)

def DFstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ) : ℂ :=
  W D (archDerivAtComplex hw d (x p)) (g0 w b * archComplexGLAt hw h)

def DDstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (d' d : ArchDirComplex) (h : GL (Fin 2) ℂ) : ℂ :=
  W D (archDerivAtComplex hw d' (archDerivAtComplex hw d (x p))) (g0 w b * archComplexGLAt hw h)

def fstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (m : ℕ) (y : ℝ) : ℂ :=
  if hm : m < n + 1 then Fstr D hw b x ⟨m, hm⟩ (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)) else 0

theorem bprime_fst_self (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) :
    ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := by
  classical
  have hne : ((b : AdeleRing (𝓞 K) K)).1 w ≠ 0 := by
    intro h
    have h1 : (((b * b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by rw [mul_inv_cancel]; rfl
    have : (((b * b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w =
        ((b : AdeleRing (𝓞 K) K)).1 w * (((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w := rfl
    rw [this, h, zero_mul] at h1; exact zero_ne_one h1
  rw [bprime]
  show ((b : AdeleRing (𝓞 K) K)).1 w * ((((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K)).1 w = 1
  rw [← map_inv, archUnitHom_apply]
  show ((b : AdeleRing (𝓞 K) K)).1 w * Function.update (1 : InfiniteAdeleRing K) w _ w = 1
  rw [Function.update_self]
  show ((b : AdeleRing (𝓞 K) K)).1 w * (((infiniteUnitsComponent (𝓞 K) K w b)⁻¹ : (w.Completion)ˣ) : w.Completion) = 1
  rw [← map_inv]
  show ((b : AdeleRing (𝓞 K) K)).1 w * (((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1
  have : (((b * b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by rw [mul_inv_cancel]; rfl
  exact this

theorem bprime_fst_of_ne {w w' : InfinitePlace K} (hne : w' ≠ w) (b : (AdeleRing (𝓞 K) K)ˣ) :
    ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w' := by
  classical
  rw [bprime]
  show ((b : AdeleRing (𝓞 K) K)).1 w' * ((((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K)).1 w' = _
  rw [← map_inv, archUnitHom_apply]
  show ((b : AdeleRing (𝓞 K) K)).1 w' * Function.update (1 : InfiniteAdeleRing K) w _ w' = _
  rw [Function.update_of_ne hne]
  show ((b : AdeleRing (𝓞 K) K)).1 w' * 1 = _
  rw [mul_one]

theorem bprime_snd (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) :
    ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = ((b : AdeleRing (𝓞 K) K)).2 := by
  rw [bprime]
  show ((b : AdeleRing (𝓞 K) K)).2 * ((((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K)).2 = _
  rw [← map_inv, archUnitHom_apply]
  show ((b : AdeleRing (𝓞 K) K)).2 * 1 = _
  rw [mul_one]

theorem hasDerivAt_W_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex)
    (b : (AdeleRing (𝓞 K) K)ˣ) {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p))) :
    (∀ (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
        (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g0 w b * archComplexGLAt hw h)) 0) ∧
    (∀ (p : Fin (n + 1)) (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' (x p)) 1 (g0 w b * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
        (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (archDerivAtComplex hw d' (x p))) 1 (g0 w b * archComplexGLAt hw h)) 0) := by
  have hs : ∀ p, IsArchSmoothAtComplex hw (x p) := fun p => by simpa only [List.foldr] using (hreg p []).1
  have h1 : ∀ p (d : ArchDirComplex), Continuous (archDerivAtComplex hw d (x p)) := fun p d => by
    simpa only [List.foldr] using (hreg p [d]).2
  have h2 : ∀ p (d d' : ArchDirComplex), Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (x p))) := fun p d d' => by
    simpa only [List.foldr] using (hreg p [d, d']).2
  exact ⟨fun p => (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) (g0 w b)).1,
    fun p => (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) (g0 w b)).2⟩

section Casimir

variable {w : InfinitePlace K} (hw : w.IsComplex)

theorem archDelAt_apply' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDelAt hw d ψ g = (1 / 2 : ℂ) * (archDerivAtComplex hw d.toComplex ψ g - Complex.I * archDerivAtComplex hw d.toComplexI ψ g) := by
  simp only [archDelAt, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem archDelBarAt_apply' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDelBarAt hw d ψ g = (1 / 2 : ℂ) * (archDerivAtComplex hw d.toComplex ψ g + Complex.I * archDerivAtComplex hw d.toComplexI ψ g) := by
  simp only [archDelBarAt, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem archDerivAtComplex_sub'' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDirComplex) :
    archDerivAtComplex hw d (φ - ψ) = archDerivAtComplex hw d φ - archDerivAtComplex hw d ψ := by
  rw [sub_eq_add_neg, archDerivAtComplex_add hφ hψ.neg, ← neg_one_smul ℂ ψ, archDerivAtComplex_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem archDerivAtComplex_archDelAt' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAtComplex hw ψ)
    (d : ArchDirComplex) (d' : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d (archDelAt hw d' ψ) g =
      (1 / 2 : ℂ) * (archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplex ψ) g -
        Complex.I * archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplexI ψ) g) := by
  unfold AutomorphicForm.archDelAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_sub'' hw (hψ.archDerivAtComplex _) ((hψ.archDerivAtComplex _).smul _),
    archDerivAtComplex_smul]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem archDerivAtComplex_archDelBarAt' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAtComplex hw ψ)
    (d : ArchDirComplex) (d' : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d (archDelBarAt hw d' ψ) g =
      (1 / 2 : ℂ) * (archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplex ψ) g +
        Complex.I * archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplexI ψ) g) := by
  unfold AutomorphicForm.archDelBarAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_add (hψ.archDerivAtComplex _) ((hψ.archDerivAtComplex _).smul _),
    archDerivAtComplex_smul]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]

def casWords (φ : AdelicGL2 (𝓞 K) K → ℂ) : Fin 10 → (AdelicGL2 (𝓞 K) K → ℂ) :=
  ![archDerivAtComplex hw .H (archDerivAtComplex hw .H φ), archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ),
    archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ), archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ),
    archDerivAtComplex hw .H φ, archDerivAtComplex hw .iH φ,
    archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ), archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ),
    archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ), archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ)]

def casCoeff : Fin 10 → ℂ :=
  ![-(1 / 16 : ℂ), Complex.I / 16, Complex.I / 16, 1 / 16, 1 / 4, -(Complex.I / 4), -(1 / 4 : ℂ), Complex.I / 4, Complex.I / 4, 1 / 4]

def casBarCoeff : Fin 10 → ℂ :=
  ![-(1 / 16 : ℂ), -(Complex.I / 16), -(Complex.I / 16), 1 / 16, 1 / 4, Complex.I / 4, -(1 / 4 : ℂ), -(Complex.I / 4),
    -(Complex.I / 4), 1 / 4]

theorem archCasimirAtComplex_eq_sum {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirAtComplex hw φ = fun g => ∑ j : Fin 10, casCoeff j * casWords hw φ j g := by
  funext g
  simp only [archCasimirAtComplex, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [archDelAt_apply' hw .H (ψ := archDelAt hw .H φ), archDerivAtComplex_archDelAt' hw hφ, archDerivAtComplex_archDelAt' hw hφ,
    archDelAt_apply' hw .H (ψ := φ), archDelAt_apply' hw .E (ψ := archDelAt hw .Fm φ), archDerivAtComplex_archDelAt' hw hφ,
    archDerivAtComplex_archDelAt' hw hφ]
  simp only [casCoeff, casWords, ArchDir.toComplex, ArchDir.toComplexI, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (-(1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) g -
    (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g) * Complex.I_sq

theorem archCasimirBarAtComplex_eq_sum {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirBarAtComplex hw φ = fun g => ∑ j : Fin 10, casBarCoeff j * casWords hw φ j g := by
  funext g
  simp only [archCasimirBarAtComplex, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [archDelBarAt_apply' hw .H (ψ := archDelBarAt hw .H φ), archDerivAtComplex_archDelBarAt' hw hφ, archDerivAtComplex_archDelBarAt' hw hφ,
    archDelBarAt_apply' hw .H (ψ := φ), archDelBarAt_apply' hw .E (ψ := archDelBarAt hw .Fm φ), archDerivAtComplex_archDelBarAt' hw hφ,
    archDerivAtComplex_archDelBarAt' hw hφ]
  simp only [casBarCoeff, casWords, ArchDir.toComplex, ArchDir.toComplexI, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (-(1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) g -
    (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g) * Complex.I_sq

end Casimir

end E40DCFN

namespace E40UNI

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

theorem map_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  ext i j
  change f ((unipotentGL2 x : Matrix (Fin 2) (Fin 2) A) i j) = (unipotentGL2 (f x) : Matrix (Fin 2) (Fin 2) B) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem archComponent_glArch_unipotentGL2 (w : InfinitePlace K) (X : AdeleRing (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (unipotentGL2 X)) = unipotentGL2 (X.1 w) := by
  change Matrix.GeneralLinearGroup.map (archEval K w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) (unipotentGL2 X)) = _
  rw [map_unipotentGL2, map_unipotentGL2]
  rfl

theorem glFin_unipotentGL2 (X : AdeleRing (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 X) = unipotentGL2 X.2 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) (unipotentGL2 X) = _
  rw [map_unipotentGL2]
  rfl

theorem glEquivOfRingEquiv_unipotentGL2 {A B : Type*} [NormedField A] [NormedField B] (e : A ≃+* B) (x : A) :
    glEquivOfRingEquiv e (unipotentGL2 x) = unipotentGL2 (e x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glEquivOfRingEquiv_apply_entry, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField K] in
theorem glArch_ext' {x y : GL (Fin 2) (InfiniteAdeleRing K)}
    (h : ∀ w : InfinitePlace K, archComponent K w x = archComponent K w y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => funext fun w => ?_
  exact congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

open scoped Classical in

theorem archComplexGLAt_unipotentGL2 {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂ) :
    archComplexGLAt hw (unipotentGL2 z) =
      unipotentGL2 (show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0)) := by
  refine eq_of_glArch_eq_of_glFin_eq (glArch_ext' fun w' => ?_) ?_
  · rw [archComponent_glArch_unipotentGL2]
    have hL : glArch (𝓞 K) K (archComplexGLAt hw (unipotentGL2 z)) =
        archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm (unipotentGL2 z)) :=
      glArch_adelicArchGLIncl K _
    rw [hL, glEquivOfRingEquiv_unipotentGL2]
    by_cases hww : w' = w
    · subst hww
      rw [archComponent_archGLIncl_self]
      congr 1
      show _ = Pi.single (M := fun v : InfinitePlace K => v.Completion) w' ((ringEquivComplexOfIsComplex hw).symm z) w'
      rw [Pi.single_eq_same]
    · rw [archComponent_archGLIncl_of_ne K hww]
      have h0 : ((show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0))).1 w' = 0 := by
        show Pi.single (M := fun v : InfinitePlace K => v.Completion) w ((ringEquivComplexOfIsComplex hw).symm z) w' = 0
        exact Pi.single_eq_of_ne hww _
      rw [h0, unipotentGL2_zero]
  · rw [glFin_unipotentGL2]
    have hF : glFin (𝓞 K) K (archComplexGLAt hw (unipotentGL2 z)) = 1 := glFin_adelicArchGLIncl K _
    rw [hF]
    show (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) = unipotentGL2 0
    rw [unipotentGL2_zero]

theorem unipotentGL2_algebraMap_eq_globalPoints (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  refine Units.ext ?_
  ext i j
  simp only [unipotentGL2_coe, globalPoints, Matrix.GeneralLinearGroup.map_apply,
    Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp

end E40UNI

namespace E40DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

theorem glInf_ext {a b : GL (Fin 2) (InfiniteAdeleRing K)}
    (h : ∀ v : InfinitePlace K, archComponent K v a = archComponent K v b) : a = b := by
  apply Units.ext
  ext i j
  funext v
  have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (v.Completion) =>
    (m : Matrix (Fin 2) (Fin 2) (v.Completion))) (h v)) i) j
  rwa [archComponent_apply, archComponent_apply] at this

theorem archComplexGLAt_mul_comm_of_archComponent_eq_one {w : InfinitePlace K} (hw : w.IsComplex) (m : GL (Fin 2) ℂ)
    {k : AdelicGL2 (𝓞 K) K} (hk : archComponent K w (glArch (𝓞 K) K k) = 1) :
    archComplexGLAt hw m * k = k * archComplexGLAt hw m := by
  have hfin : glFin (𝓞 K) K (archComplexGLAt hw m) = 1 := glFin_adelicArchGLIncl K _
  have harch : glArch (𝓞 K) K (archComplexGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) := glArch_adelicArchGLIncl K _
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, harch]
    refine glInf_ext K fun v => ?_
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv; rw [hk, mul_one, one_mul, archComponent_archGLIncl_self]
    · rw [archComponent_archGLIncl_of_ne K hv, one_mul, mul_one]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

theorem archComponent_glArch_g0 (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) :
    archComponent K w (glArch (𝓞 K) K (g0 w b)) = 1 := by
  ext i j
  rw [archComponent_apply, glArch_apply]
  show ((Matrix.diagonal ![((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] i j).1 w) =
    (1 : Matrix (Fin 2) (Fin 2) (w.Completion)) i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, bprime_fst_self] <;> rfl

theorem archComplexGLAt_mul_g0 {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ) (m : GL (Fin 2) ℂ) :
    archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m :=
  archComplexGLAt_mul_comm_of_archComponent_eq_one K hw m (archComponent_glArch_g0 K w b)

section Wlemmas
variable (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)

theorem whittakerCoefficient_mul_right (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g k : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (fun y => φ (y * k)) α g := by
  unfold whittakerCoefficient
  congr 1
  funext u
  simp only [mul_assoc]

theorem whittakerCoefficient_const_mul (φ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ (fun y => c * φ y) α g = c * whittakerCoefficient K pins ψ φ α g := by
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext u
  ring

end Wlemmas

end E40DCFN

namespace E37K

variable (K : Type) [Field K] [NumberField K]

private theorem _root_.E37K.whittakerCoefficient_mul_right (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g k : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (fun y => φ (y * k)) α g := by
  letI := pins.nS
  simp only [whittakerCoefficient, mul_assoc]

p2m_export "E37K" "whittakerCoefficient_mul_right"

theorem archComplexGLAt_eq_lift_rot {w : InfinitePlace K} (hw : w.IsComplex) (s : ℝ) (k : GL (Fin 2) ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s]) :
    archComplexGLAt hw k =
      archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] := by
  have hmat : (Matrix.of !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) =
      (k : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_cos, Complex.ofReal_sin]
  have hdet : (Matrix.of !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [hmat, ← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [archComplexLiftAt_of_det_ne_zero hw hdet]
  congr 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hmat]

theorem archComplexGLAt_eq_lift_irot {w : InfinitePlace K} (hw : w.IsComplex) (s : ℝ) (k : GL (Fin 2) ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s]) :
    archComplexGLAt hw k =
      archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] := by
  have hmat : (Matrix.of !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_cos, Complex.ofReal_sin, mul_comm]
  have hdet : (Matrix.of !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [hmat, ← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [archComplexLiftAt_of_det_ne_zero hw hdet]
  congr 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hmat]

theorem hK_of_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (g₀ : AdelicGL2 (𝓞 K) K)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (hxc : ∀ p, Continuous (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) =
        ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) =
        ∑ p' : Fin (n + 1), E₂ s p' p * x p' g) :
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) =
          ∑ p' : Fin (n + 1), E₁ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) =
          ∑ p' : Fin (n + 1), E₂ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) := by
  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous
  constructor
  · intro p s h k hk
    rw [map_mul, ← mul_assoc, whittakerCoefficient_mul_right, archComplexGLAt_eq_lift_rot K hw s k hk]
    rw [show (fun y => x p (y * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)])) =
        fun y => ∑ p' : Fin (n + 1), E₁ s p' p * x p' y from funext fun y => hK₁ p s y]
    exact AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ (n + 1) x hxc (fun p' => E₁ s p' p) 1 _
  · intro p s h k hk
    rw [map_mul, ← mul_assoc, whittakerCoefficient_mul_right, archComplexGLAt_eq_lift_irot K hw s k hk]
    rw [show (fun y => x p (y * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)])) =
        fun y => ∑ p' : Fin (n + 1), E₂ s p' p * x p' y from funext fun y => hK₂ p s y]
    exact AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ (n + 1) x hxc (fun p' => E₂ s p' p) 1 _

theorem final_bound (V C B w₀ δ r : ℝ) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hsmall : r ≤ 1 → V ≤ C * r ^ w₀ * r ^ δ) (hlarge : V ≤ B * r ^ w₀) :
    V ≤ max C B * r ^ ((2 : ℝ) * w₀ / 2) * (min 1 r) ^ δ := by
  rw [show (2 : ℝ) * w₀ / 2 = w₀ by ring]
  have hrw : 0 ≤ r ^ w₀ := Real.rpow_nonneg hr.le _
  by_cases h1 : r ≤ 1
  · rw [min_eq_right h1]
    have hrδ : 0 ≤ r ^ δ := Real.rpow_nonneg hr.le _
    calc V ≤ C * r ^ w₀ * r ^ δ := hsmall h1
      _ ≤ max C B * r ^ w₀ * r ^ δ := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C B) hrw) hrδ
          exact this
  · rw [min_eq_left (le_of_lt (not_le.mp h1)), Real.one_rpow, mul_one]
    calc V ≤ B * r ^ w₀ := hlarge
      _ ≤ max C B * r ^ w₀ := mul_le_mul_of_nonneg_right (le_max_right C B) hrw

end E37K

open E40DCFN E40UNI in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (g₀ : AdelicGL2 (𝓞 K) K) (_hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₂ s p' p * x p' g)
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p) :
    (∀ (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t))) (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g₀ * archComplexGLAt hw h)) 0) ∧
    (∀ (p : Fin (n + 1)) (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d' t))) (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' (archDerivAtComplex hw d (x p))) 1 (g₀ * archComplexGLAt hw h)) 0) ∧
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g₀ * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h))))) = lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g₀ * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h))))) = lam' * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (z : ℂ) (h : GL (Fin 2) ℂ),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (unipotentGL2 z * h)) = Complex.exp (2 * Real.pi * Complex.I * ((2 * ((1 : ℂ) * z).re : ℝ) : ℂ)) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * circleGL2 ζ)) = (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) = ∑ p' : Fin (n + 1), E₁ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) = ∑ p' : Fin (n + 1), E₂ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) := by

  have hs : ∀ p, IsArchSmoothAtComplex hw (x p) := fun p => by simpa only [List.foldr] using (hreg p []).1
  have h1 : ∀ p (d : ArchDirComplex), Continuous (archDerivAtComplex hw d (x p)) := fun p d => by
    simpa only [List.foldr] using (hreg p [d]).2
  have h2 : ∀ p (d d' : ArchDirComplex), Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (x p))) := fun p d d' => by
    simpa only [List.foldr] using (hreg p [d, d']).2
  have hcomm : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * g₀ = g₀ * archComplexGLAt hw m := fun m =>
    E40DCFN.archComplexGLAt_mul_comm_of_archComponent_eq_one K hw m _hg₀

  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous

  have hcw : ∀ (p : Fin (n + 1)) (j : Fin 10), Continuous (casWords hw (x p) j) := by
    intro p j
    have h2 : ∀ a b' : ArchDirComplex, Continuous (archDerivAtComplex hw a (archDerivAtComplex hw b' (x p))) :=
      fun a b' => by simpa only [List.foldr] using (hreg p [a, b']).2
    have h1 : ∀ a : ArchDirComplex, Continuous (archDerivAtComplex hw a (x p)) :=
      fun a => by simpa only [List.foldr] using (hreg p [a]).2
    fin_cases j <;> simp only [casWords, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons,
      Fin.isValue] <;> first | exact h2 _ _ | exact h1 _
  have hsm : ∀ p : Fin (n + 1), IsArchSmoothAtComplex hw (x p) := fun p => by simpa only [List.foldr] using (hreg p []).1

  have hWsmul : ∀ (p : Fin (n + 1)) (c : ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (c • x p) 1 g = c * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
    intro p c g
    have h := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ 1 (fun _ => x p) (fun _ => hxc p) (fun _ => c) 1 g
    simp only [Fin.sum_univ_one] at h
    rw [show (c • x p) = fun g' => c * x p g' from funext fun g' => by simp [Pi.smul_apply, smul_eq_mul]]
    exact h
  have hWsum : ∀ (p : Fin (n + 1)) (cf : Fin 10 → ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (fun g' => ∑ j : Fin 10, cf j * casWords hw (x p) j g') 1 g =
        ∑ j : Fin 10, cf j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g := fun p cf g =>
    AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ 10 (casWords hw (x p)) (hcw p) cf 1 g
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) g₀).1
  · intro p d d' h
    exact (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) g₀).2 d' d h
  · intro p h
    set g : AdelicGL2 (𝓞 K) K := g₀ * archComplexGLAt hw h with hg
    have key : ∑ j : Fin 10, casCoeff j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g = lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
      rw [← hWsum, ← hWsmul, ← archCasimirAtComplex_eq_sum hw (hsm p), (hcas p).1]
    rw [← key]
    simp only [casCoeff, casWords, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    linear_combination (-(1 / 16 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 g -
      (1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 g) * Complex.I_sq
  · intro p h
    set g : AdelicGL2 (𝓞 K) K := g₀ * archComplexGLAt hw h with hg
    have key : ∑ j : Fin 10, casBarCoeff j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g = lam' * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
      rw [← hWsum, ← hWsmul, ← archCasimirBarAtComplex_eq_sum hw (hsm p), (hcas p).2]
    rw [← key]
    simp only [casBarCoeff, casWords, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    linear_combination (-(1 / 16 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 g -
      (1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 g) * Complex.I_sq
  · intro p z h
    set X : AdeleRing (𝓞 K) K := (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0))
      with hX
    have hgeom : g₀ * archComplexGLAt hw (unipotentGL2 z * h) = unipotentGL2 X * (g₀ * archComplexGLAt hw h) := by
      rw [map_mul, ← mul_assoc, ← hcomm, archComplexGLAt_unipotentGL2, mul_assoc]
    rw [hgeom]
    have hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K),
        x p (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * (g₀ * archComplexGLAt hw h)) =
          x p (unipotentGL2 u * (g₀ * archComplexGLAt hw h)) := by
      intro β u
      rw [unipotentGL2_add, mul_assoc, unipotentGL2_algebraMap_eq_globalPoints, hxG]
    have hcov := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (NumberField.StandardAddChar.stdAddChar K)
      (NumberField.StandardAddChar.adelicTraceData K).isGlobalAddChar_psiK.principalInvariant
      (x p) (g₀ * archComplexGLAt hw h) hper 1 X
    rw [map_one, one_mul] at hcov
    rw [hcov, hX, NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex K w hw z, one_mul]
  · intro p ζ hζ h
    rw [map_mul, ← mul_assoc, E40DCFN.whittakerCoefficient_mul_right]
    have hfun : (fun y => x p (y * archComplexGLAt hw (circleGL2 ζ))) = fun y => (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * x p y :=
      funext fun y => hwt p ζ hζ y
    rw [hfun, E40DCFN.whittakerCoefficient_const_mul]
  · exact (E37K.hK_of_string K D hw g₀ n x hxc E₁ E₂ hK₁ hK₂).1
  · exact (E37K.hK_of_string K D hw g₀ n x hxc E₁ E₂ hK₁ hK₂).2

end
end S_AutomorphicForm_whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses (solution)
