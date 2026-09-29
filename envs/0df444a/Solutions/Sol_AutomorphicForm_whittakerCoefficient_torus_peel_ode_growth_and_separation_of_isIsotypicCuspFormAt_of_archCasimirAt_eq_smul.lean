-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/078577b3-9721-5115-b108-26c8d05986e0

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_AdelicTraceProducer
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
import Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import Theorems.Thm_LanglandsTunnell_whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Mathlib.Tactic.Module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal
open NumberField.AdelicVolume
open scoped Real

namespace P2M
namespace TorusKit

section CoefficientFunction

variable (F : Type) [Field F] [NumberField F]

section RealUnipotent

private theorem archRealGLAt_unipotentGL2_eq {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ∃ X : InfiniteAdeleRing F, X w = (ringEquivRealOfIsReal hw).symm x ∧ (∀ v : InfinitePlace F, v ≠ w → X v = 0) ∧
      archRealGLAt hw (unipotentGL2 x) = unipotentGL2 ((⟨X, 0⟩ : AdeleRing (𝓞 F) F)) := by
  set m : GL (Fin 2) w.Completion := glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (unipotentGL2 x) with hm
  refine ⟨archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) 0 1, ?_, ?_, ?_⟩
  · rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
    simp [unipotentGL2_coe]
  · intro v hv
    rw [archMatrixUpdate_apply_of_ne F w _ 0 1 hv]
    simp [Matrix.one_apply]
  · refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
    · have h1 : AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw (unipotentGL2 x)) = archGLIncl F w m :=
        glArch_adelicArchGLIncl F _
      rw [h1]
      apply Units.ext
      ext i j
      rw [AdelicLevel.glArch_apply]
      change archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
      funext v
      by_cases hv : v = w
      · subst hv
        rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
        fin_cases i <;> fin_cases j <;>
          simp [unipotentGL2_coe, archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry] <;> rfl
      · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
        fin_cases i <;> fin_cases j <;>
          simp [unipotentGL2_coe, Matrix.one_apply,
            archMatrixUpdate_apply_of_ne F w (m : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 hv] <;> rfl
    · have h2 : AdelicLevel.glFin (𝓞 F) F (archRealGLAt hw (unipotentGL2 x)) = 1 := glFin_adelicArchGLIncl F _
      rw [h2]
      apply Units.ext
      ext i j
      rw [AdelicLevel.glFin_apply]
      fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe, Matrix.one_apply]

private theorem apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {w : InfinitePlace F} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing F, (∀ w' : InfinitePlace F, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 F) F) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (W : AdelicGL2 (𝓞 F) F → ℂ)
    (hW : ∀ (X : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 X * g) = ψ X * W g)
    (x : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    W (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * W g := by
  obtain ⟨X, hXw, hX0, hX⟩ := archRealGLAt_unipotentGL2_eq F hw x
  rw [hX]
  refine (hW ⟨X, 0⟩ g).trans ?_
  rw [hψr X hX0, hXw]
  congr 3
  rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply]

end RealUnipotent

section Periodicity

private theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  change algebraMap F (AdeleRing (𝓞 F) F) ((unipotentGL2 β : Matrix (Fin 2) (Fin 2) F) i j)
    = (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe]

variable {F}

private theorem isLsXiFunction_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ) : IsLsXiFunction (𝓞 F) F pins.Z ξ φ := by
  letI := pins.mS
  exact ((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D φ).mp h.smoothCusp.1.1).1

private theorem apply_unipotentGL2_algebraMap_add_mul_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ)
    (β : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g) := by
  have hinv := (isLsXiFunction_of_isIsotypicCuspFormAt h).left_invariant
  rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hinv]

variable (F)

private theorem whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsIsotypicCuspFormAt F pins ξ N S Φ φ)
    (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (unipotentGL2 x * g) =
      ψ x * whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 g := by
  have h := whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ.principalInvariant φ g
    (fun β u => (apply_unipotentGL2_algebraMap_add_mul_of_isIsotypicCuspFormAt hφ) β u g) 1 x
  rwa [map_one, one_mul] at h

end Periodicity

section Peeling

section CentralLaw

private theorem whittakerCoefficient_centralScalar_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {ξ : pins.Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F pins.Z ξ φ) (z : pins.Z) (α : F)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g)
      = ((ξ z : ℂˣ) : ℂ) * whittakerCoefficient F pins ψ φ α g := by
  unfold whittakerCoefficient
  have h : ∀ x : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 x * (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g))
        = ((ξ z : ℂˣ) : ℂ) * φ (unipotentGL2 x * g) := by
    intro x
    rw [← mul_assoc, mul_centralScalar_comm (F := F), mul_assoc, hφ.central_transform z]
  simp only [h, mul_assoc, integral_const_mul]

end CentralLaw

section RealUnits

variable {F}

private noncomputable def archRealUnit {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) : (w.Completion)ˣ :=
  Units.mk0 ((ringEquivRealOfIsReal hw).symm r) ((map_ne_zero_iff _ (ringEquivRealOfIsReal hw).symm.injective).mpr hr)

private theorem archRealUnit_coe {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    ((archRealUnit hw r hr : (w.Completion)ˣ) : w.Completion) = (ringEquivRealOfIsReal hw).symm r := rfl

private theorem extensionEmbedding_archRealUnit {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    extensionEmbedding w ((archRealUnit hw r hr : (w.Completion)ˣ) : w.Completion) = (r : ℂ) := by
  rw [archRealUnit_coe, ← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw,
    RingEquiv.apply_symm_apply]

private theorem norm_archRealUnit {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    ‖((archRealUnit hw r hr : (w.Completion)ˣ) : w.Completion)‖ = |r| := by
  rw [← (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), archRealUnit_coe,
    ← ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply, Real.norm_eq_abs]

private theorem archUnitHom_archRealUnit_of_isArchCompAt {μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {w : InfinitePlace F}
    (hw : w.IsReal) {u : ℂ} {a : ℤ} (h : IsArchCompAt F μ w u a) (r : ℝ) (hr : 0 < r) :
    ((μ (archUnitHom w (archRealUnit hw r hr.ne')) : ℂˣ) : ℂ) = (r : ℂ) ^ u := by
  have hx := h (archRealUnit hw r hr.ne')
  rw [archLocalChar_apply] at hx
  have hm : w.mult = 1 := InfinitePlace.mult_isReal ⟨w, hw⟩
  rw [archUnitHom_apply, hx, norm_archRealUnit, extensionEmbedding_archRealUnit, abs_of_pos hr, hm, Nat.cast_one,
    one_mul, div_self (Complex.ofReal_ne_zero.mpr hr.ne'), _root_.one_zpow, mul_one]

end RealUnits

section Naturality

private theorem archRealGLAt_diagOne {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    archRealGLAt hw (diagOne (Units.mk0 r hr)) = diagOne (archUnitHom w (archRealUnit hw r hr)) := by
  set m : GL (Fin 2) w.Completion := glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (diagOne (Units.mk0 r hr))
    with hm
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · have h1 : AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw (diagOne (Units.mk0 r hr))) = archGLIncl F w m :=
      glArch_adelicArchGLIncl F _
    rw [h1]
    apply Units.ext
    ext i j
    rw [AdelicLevel.glArch_apply, diagOne_coe_apply]
    change archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry, diagOne_coe_apply]
      fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, archRealUnit_coe] <;> rfl
    · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
      fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, Matrix.one_apply, hv] <;> rfl
  · have h2 : AdelicLevel.glFin (𝓞 F) F (archRealGLAt hw (diagOne (Units.mk0 r hr))) = 1 := glFin_adelicArchGLIncl F _
    rw [h2]
    apply Units.ext
    ext i j
    rw [AdelicLevel.glFin_apply, diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, Matrix.one_apply] <;> rfl

private theorem archRealGLAt_scalar {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr))
      = centralScalar (𝓞 F) F (archUnitHom w (archRealUnit hw r hr)) := by
  set m : GL (Fin 2) w.Completion :=
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr))
    with hm
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · have h1 : AdelicLevel.glArch (𝓞 F) F
        (archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr))) = archGLIncl F w m :=
      glArch_adelicArchGLIncl F _
    rw [h1]
    apply Units.ext
    ext i j
    rw [AdelicLevel.glArch_apply, centralScalar_val]
    change archMatrixUpdate F w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.scalar, archUnitHom_apply, archCentralUnit, archRealUnit_coe] <;> rfl
    · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
      fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, Matrix.one_apply, hv] <;> rfl
  · have h2 : AdelicLevel.glFin (𝓞 F) F
        (archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr))) = 1 :=
      glFin_adelicArchGLIncl F _
    rw [h2]
    apply Units.ext
    ext i j
    rw [AdelicLevel.glFin_apply, centralScalar_val]
    fin_cases i <;> fin_cases j <;> simp [archUnitHom_apply, archCentralUnit, Matrix.one_apply] <;> rfl

end Naturality

section Torus

private theorem sqrt_ne_zero_of_pos
    {y : ℝ} (hy : 0 < y) : (Real.sqrt y)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hy).ne'

private theorem splitTorusGL2_half_log_eq (y : ℝ) (hy : 0 < y) :
    splitTorusGL2 (Real.log y / 2)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy))
          * diagOne (Units.mk0 y hy.ne') := by
  have hsq : Real.exp (Real.log y / 2) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, div_eq_mul_one_div]
  apply Units.ext
  show (!![Real.exp (Real.log y / 2), 0; 0, Real.exp (-(Real.log y / 2))] : Matrix (Fin 2) (Fin 2) ℝ)
    = Matrix.scalar (Fin 2) (Real.sqrt y)⁻¹ * Matrix.diagonal ![y, 1]
  rw [Real.exp_neg, hsq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_eq_div, Real.div_sqrt]

private theorem whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {ξ : (productionPinsOf F D U gen B).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F (productionPinsOf F D U gen B).Z ξ φ)
    {w : InfinitePlace F} (hw : w.IsReal) (α : F) (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
        (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
      = ((ξ ⟨archUnitHom w (archRealUnit hw (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
          * whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
              (diagOne (archUnitHom w (archRealUnit hw y hy.ne')) * g) := by
  rw [splitTorusGL2_half_log_eq y hy, map_mul, archRealGLAt_scalar, archRealGLAt_diagOne, mul_assoc]
  exact whittakerCoefficient_centralScalar_mul F (productionPinsOf F D U gen B) ψ hφ
    ⟨archUnitHom w (archRealUnit hw (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy)), Subgroup.mem_top _⟩ α _

private theorem whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {ξ : (productionPinsOf F D U gen B).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F (productionPinsOf F D U gen B).Z ξ φ)
    {w : InfinitePlace F} (hw : w.IsReal) {u : ℂ} {a : ℤ}
    (hcen : IsArchCompAt F (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w u a)
    (α : F) (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
        (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
      = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u
          * whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
              (diagOne (archUnitHom w (archRealUnit hw y hy.ne')) * g) := by
  rw [whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log F D U gen B ψ hφ hw α y hy g]
  congr 1
  exact archUnitHom_archRealUnit_of_isArchCompAt hw hcen _ (inv_pos.mpr (Real.sqrt_pos.mpr hy))

end Torus

end Peeling

section NegativeSheet

private theorem J_mul_splitTorusGL2_half_log_eq (y : ℝ) (hy : 0 < y) :
    UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy))
          * diagOne (Units.mk0 (-y) (neg_ne_zero.mpr hy.ne')) := by
  have hsq : Real.exp (Real.log y / 2) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, div_eq_mul_one_div]
  apply Units.ext
  show (!![(-1 : ℝ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
        * !![Real.exp (Real.log y / 2), 0; 0, Real.exp (-(Real.log y / 2))]
      = Matrix.scalar (Fin 2) (Real.sqrt y)⁻¹ * Matrix.diagonal ![-y, 1]
  rw [Real.exp_neg, hsq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_eq_div, Real.div_sqrt]

private theorem whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {ξ : (productionPinsOf F D U gen B).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F (productionPinsOf F D U gen B).Z ξ φ)
    {w : InfinitePlace F} (hw : w.IsReal) {u : ℂ} {a : ℤ}
    (hcen : IsArchCompAt F (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w u a)
    (α : F) (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
        (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)
      = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u
          * whittakerCoefficient F (productionPinsOf F D U gen B) ψ φ α
              (diagOne (archUnitHom w (archRealUnit hw (-y) (neg_ne_zero.mpr hy.ne'))) * g) := by
  rw [J_mul_splitTorusGL2_half_log_eq y hy, map_mul, archRealGLAt_scalar, archRealGLAt_diagOne, mul_assoc,
    whittakerCoefficient_centralScalar_mul F (productionPinsOf F D U gen B) ψ hφ
      ⟨archUnitHom w (archRealUnit hw (Real.sqrt y)⁻¹ (sqrt_ne_zero_of_pos hy)), Subgroup.mem_top _⟩ α]
  congr 1
  exact archUnitHom_archRealUnit_of_isArchCompAt hw hcen _ (inv_pos.mpr (Real.sqrt_pos.mpr hy))

end NegativeSheet

section ArchUnitNorm

private theorem ideleNorm_archUnitHom_archRealUnit_rat {w : InfinitePlace ℚ} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    ideleNorm ℚ (archUnitHom w (archRealUnit hw r hr)) = |r| := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one ℚ _ rfl,
    Fintype.prod_subsingleton _ w]
  have hm : w.mult = 1 := InfinitePlace.mult_isReal ⟨w, hw⟩
  rw [hm, pow_one, archUnitHom_apply]
  rw [archCentralUnit_fst_self, norm_archRealUnit]

private theorem archUnitHom_archRealUnit_coe_snd {w : InfinitePlace ℚ} (hw : w.IsReal) (r : ℝ) (hr : r ≠ 0) :
    ((archUnitHom w (archRealUnit hw r hr) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := rfl

end ArchUnitNorm

section GrowthTransfer

private theorem norm_inv_sqrt_cpow (u : ℂ) (y : ℝ) (hy : 0 < y) :
    ‖(((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u‖ = y ^ (-(u.re / 2)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hy)), Real.sqrt_eq_rpow,
    ← Real.rpow_neg hy.le, ← Real.rpow_mul hy.le]
  congr 1
  ring

private theorem exists_forall_norm_cpow_mul_le_of_forall_norm_le (u : ℂ) (G : ℝ → ℂ) (C M : ℝ)
    (hG : ∀ y : ℝ, 0 < y → ‖G y‖ ≤ C * y ^ M) :
    ∃ C' N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖(((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u * G y‖ ≤ C' * y ^ N := by
  refine ⟨|C|, M + -(u.re / 2), fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  rw [norm_mul, norm_inv_sqrt_cpow u y hy0, Real.rpow_add hy0, mul_comm (y ^ M), ← mul_assoc, mul_comm |C|,
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hy0.le _)
  exact (hG y hy0).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hy0.le _))

end GrowthTransfer
section ReferenceDatum

variable {F}

private theorem apply_unipotentGL2_algebraMap_mul_of_isIsotypicCuspFormAt {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Φ φ) (β : F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g := by
  rw [← globalPoints_unipotentGL2, (isLsXiFunction_of_isIsotypicCuspFormAt h).left_invariant]

end ReferenceDatum

section ReferenceDatumRat

private theorem glArch_archRealGLAt_archRealProjAt_rat {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicLevel.glArch (𝓞 ℚ) ℚ (archRealGLAt hw (archRealProjAt hw g)) = AdelicLevel.glArch (𝓞 ℚ) ℚ g := by
  set m : GL (Fin 2) w.Completion := glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (archRealProjAt hw g) with hm
  have h1 : AdelicLevel.glArch (𝓞 ℚ) ℚ (archRealGLAt hw (archRealProjAt hw g)) = archGLIncl ℚ w m :=
    glArch_adelicArchGLIncl ℚ _
  rw [h1]
  apply Units.ext
  ext i j
  change archMatrixUpdate ℚ w (m : Matrix (Fin 2) (Fin 2) w.Completion) i j = _
  funext v
  rw [Subsingleton.elim v w, archMatrixUpdate_apply_self, hm, glEquivOfRingEquiv_apply_entry]
  change (ringEquivRealOfIsReal hw).symm ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
    (AdelicLevel.archComponent ℚ w (AdelicLevel.glArch (𝓞 ℚ) ℚ g)) : Matrix (Fin 2) (Fin 2) ℝ) i j) = _
  rw [glEquivOfRingEquiv_apply_entry, RingEquiv.symm_apply_apply, AdelicLevel.archComponent_apply]

private theorem glArch_inv_archRealGLAt_archRealProjAt_mul_rat
    {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicLevel.glArch (𝓞 ℚ) ℚ ((archRealGLAt hw (archRealProjAt hw g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, glArch_archRealGLAt_archRealProjAt_rat, inv_mul_cancel]

private theorem exists_eq_archRealGLAt_mul_of_glArch_eq_one_rat
    {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (p : GL (Fin 2) ℝ) (k : AdelicGL2 (𝓞 ℚ) ℚ), AdelicLevel.glArch (𝓞 ℚ) ℚ k = 1 ∧ g = archRealGLAt hw p * k :=
  ⟨archRealProjAt hw g, _, glArch_inv_archRealGLAt_archRealProjAt_mul_rat hw g, (mul_inv_cancel_left _ _).symm⟩

end ReferenceDatumRat

section RealIwasawa

private theorem det_rotMatrix (c' d' : ℝ) (h : c' ^ 2 + d' ^ 2 = 1) :
    (!![d', -c'; c', d'] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [Matrix.det_fin_two_of]
  linear_combination h

private noncomputable def rotOf (c' d' : ℝ) (h : c' ^ 2 + d' ^ 2 = 1) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![d', -c'; c', d'] (by rw [det_rotMatrix c' d' h]; exact one_ne_zero)

private theorem rotOf_coe (c' d' : ℝ) (h : c' ^ 2 + d' ^ 2 = 1) :
    ((rotOf c' d' h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![d', -c'; c', d'] := rfl

private theorem rotOf_mem_rowIsometrySubgroup₀ (c' d' : ℝ) (h : c' ^ 2 + d' ^ 2 = 1) :
    rotOf c' d' h ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [rotOf_coe]; exact det_rotMatrix c' d' h, ?_, ?_⟩
  · rw [rotOf_coe, det_rotMatrix c' d' h, norm_one]
  · intro x y
    rw [rotOf_coe]
    simp
    linear_combination (x ^ 2 + y ^ 2) * h

private theorem exists_unipotentGL2_mul_scalar_mul_diagOne_mul_eq (p : GL (Fin 2) ℝ) :
    ∃ (x : ℝ) (δ v : ℝˣ) (k : rowIsometrySubgroup₀ ℝ),
      unipotentGL2 x * Matrix.GeneralLinearGroup.scalar (Fin 2) δ * diagOne v * (k : GL (Fin 2) ℝ) = p := by
  have hdet : (p : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (p : Matrix (Fin 2) (Fin 2) ℝ)).mp p.isUnit).ne_zero
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (p : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, (p : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = d := ⟨_, rfl⟩
  have hcd : 0 < c ^ 2 + d ^ 2 := by
    by_contra hle
    have hc0 : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    have hd0 : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    apply hdet
    rw [Matrix.det_fin_two, hc, hd, hc0, hd0]
    ring
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = Real.sqrt (c ^ 2 + d ^ 2) := ⟨_, rfl⟩
  have hρ : 0 < ρ := hρdef ▸ Real.sqrt_pos.mpr hcd
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hρ2 : ρ ^ 2 = c ^ 2 + d ^ 2 := by rw [hρdef]; exact Real.sq_sqrt hcd.le
  have h1 : (c / ρ) ^ 2 + (d / ρ) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hρ2, div_self (pow_ne_zero 2 hρ0)]

  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) ℝ,
      M = (p : Matrix (Fin 2) (Fin 2) ℝ) * !![d / ρ, c / ρ; -(c / ρ), d / ρ] := ⟨_, rfl⟩
  have hM10 : M 1 0 = 0 := by
    rw [hM]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    ring
  have hM11 : M 1 1 = ρ := by
    rw [hM]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    field_simp
    linarith [hρ2]
  have hMdet : M.det = (p : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hM, Matrix.det_mul, Matrix.det_fin_two_of]
    linear_combination (p : Matrix (Fin 2) (Fin 2) ℝ).det * h1
  have hα : M 0 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [← hMdet, Matrix.det_fin_two, h0, hM10]
    ring
  refine ⟨M 0 1 / ρ, Units.mk0 ρ hρ0, Units.mk0 (M 0 0 / ρ) (div_ne_zero hα hρ0),
    ⟨rotOf (c / ρ) (d / ρ) h1, rotOf_mem_rowIsometrySubgroup₀ _ _ h1⟩, ?_⟩
  apply Units.ext
  have hkk : (!![d / ρ, c / ρ; -(c / ρ), d / ρ] : Matrix (Fin 2) (Fin 2) ℝ)
      * !![d / ρ, -(c / ρ); c / ρ, d / ρ] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination h1
  have hp : (p : Matrix (Fin 2) (Fin 2) ℝ) = M * !![d / ρ, -(c / ρ); c / ρ, d / ρ] := by
    rw [hM, Matrix.mul_assoc, hkk, Matrix.mul_one]
  show (!![(1 : ℝ), M 0 1 / ρ; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.scalar (Fin 2) ρ
      * Matrix.diagonal ![M 0 0 / ρ, 1] * !![d / ρ, -(c / ρ); c / ρ, d / ρ] = (p : Matrix (Fin 2) (Fin 2) ℝ)
  rw [hp]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hM10, hM11] <;> field_simp

end RealIwasawa

section ReferenceDatumIwasawa

variable {F}

private theorem norm_ringEquivRealOfIsReal_symm_real {w : InfinitePlace F} (hw : w.IsReal) (r : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm r‖ = ‖r‖ := by
  rw [← (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), ← ringEquivRealOfIsReal_apply hw,
    RingEquiv.apply_symm_apply]

private noncomputable def rotAt {w : InfinitePlace F} (hw : w.IsReal) :
    rowIsometrySubgroup₀ ℝ →* rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_ringEquivRealOfIsReal_symm_real hw)

private theorem archRealGLAt_coe_eq_adelicArchGLInclAt_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (k : rowIsometrySubgroup₀ ℝ) :
    archRealGLAt hw (k : GL (Fin 2) ℝ)
      = adelicArchGLInclAt F w ((rotAt hw k : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
  rfl

end ReferenceDatumIwasawa

section NegativeSheetVanishing

open Complex in

private theorem inv_sqrt_cpow_mul_sqrt_cpow (u : ℂ) {y : ℝ} (hy : 0 < y) :
    (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ u * ((Real.sqrt y : ℝ) : ℂ) ^ u = 1 := by
  rw [← mul_cpow_ofReal_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg y)) (Real.sqrt_nonneg y) u, ← ofReal_mul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hy).ne', ofReal_one, one_cpow]

end NegativeSheetVanishing
section IdeleSplit

private def archProjHom : AdeleRing (𝓞 F) F →* InfiniteAdeleRing F where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl

private def finProjHom : AdeleRing (𝓞 F) F →* FiniteAdeleRing (𝓞 F) F where
  toFun x := x.2
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def archInclHomF : InfiniteAdeleRing F →* AdeleRing (𝓞 F) F where
  toFun x := (x, (1 : FiniteAdeleRing (𝓞 F) F))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

variable {F}

private noncomputable def archPart (a : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (archInclHomF F) (Units.map (archProjHom F) a)

private noncomputable def finPart (a : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (Units.map (finProjHom F) a)

private theorem archPart_coe (a : (AdeleRing (𝓞 F) F)ˣ) :
    ((archPart a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = ((a : AdeleRing (𝓞 F) F).1, 1) := rfl

private theorem finPart_coe (a : (AdeleRing (𝓞 F) F)ˣ) :
    ((finPart a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = (1, (a : AdeleRing (𝓞 F) F).2) := rfl

private theorem finPart_coe_fst
    (a : (AdeleRing (𝓞 F) F)ˣ) : ((finPart a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 :=
  rfl

private theorem archPart_mul_finPart (a : (AdeleRing (𝓞 F) F)ˣ) : archPart a * finPart a = a := by
  apply Units.ext
  rw [Units.val_mul, archPart_coe, finPart_coe]
  exact Prod.ext (mul_one _) (one_mul _)

private theorem diagOne_mem_finiteAdelicGL2Subgroup_of_fst_eq_one (b : (AdeleRing (𝓞 F) F)ˣ)
    (hb : ((b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1) : diagOne b ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  apply Units.ext
  ext i j
  rw [glArch_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [hb] <;> rfl

private theorem diagOne_finPart_mem (a : (AdeleRing (𝓞 F) F)ˣ) : diagOne (finPart a) ∈ finiteAdelicGL2Subgroup F :=
  diagOne_mem_finiteAdelicGL2Subgroup_of_fst_eq_one _ (finPart_coe_fst a)

end IdeleSplit

section IdeleSplitRat

private theorem idele_fst_apply_ne_zero (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (w : InfinitePlace ℚ) :
    ((a : AdeleRing (𝓞 ℚ) ℚ).1 w) ≠ 0 := by
  have h : ((a : AdeleRing (𝓞 ℚ) ℚ).1 w) * (((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 w) = 1 :=
    congrArg (fun x : AdeleRing (𝓞 ℚ) ℚ => x.1 w) a.mul_inv
  exact left_ne_zero_of_mul_eq_one h

private noncomputable def archReal {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℝ :=
  ringEquivRealOfIsReal hw ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)

private theorem archReal_ne_zero
    {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : archReal hw a ≠ 0 := by
  unfold archReal
  exact (map_ne_zero_iff _ (ringEquivRealOfIsReal hw).injective).mpr (idele_fst_apply_ne_zero a w)

private theorem archPart_eq_archUnitHom_archRealUnit {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    archPart a = archUnitHom w (archRealUnit hw (archReal hw a) (archReal_ne_zero hw a)) := by
  apply Units.ext
  rw [archPart_coe, archUnitHom_apply]
  refine Prod.ext (funext fun v => ?_) rfl
  change (a : AdeleRing (𝓞 ℚ) ℚ).1 v = _
  rw [Subsingleton.elim v w, archCentralUnit_fst_self, archRealUnit_coe, archReal, RingEquiv.symm_apply_apply]

private theorem eq_archUnitHom_archRealUnit_mul_finPart
    {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    a = archUnitHom w (archRealUnit hw (archReal hw a) (archReal_ne_zero hw a)) * finPart a := by
  rw [← archPart_eq_archUnitHom_archRealUnit hw a, archPart_mul_finPart]

end IdeleSplitRat

end CoefficientFunction
section WeightTransferAndCasimirEquation

private theorem hasArchCharacterAt₀_whittakerCoefficient_fn (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (w : InfinitePlace F) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hφ : HasArchCharacterAt₀ F w χ φ) :
    HasArchCharacterAt₀ F w χ (whittakerCoefficient F pins ψ φ α) := by
  intro k g
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [show unipotentGL2 x * (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))
        = unipotentGL2 x * g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) from
      (mul_assoc _ _ _).symm,
    hφ k (unipotentGL2 x * g), mul_assoc]

private theorem whittakerCoefficient_smul_fn (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) :
    whittakerCoefficient F pins ψ (c • φ) α = c • whittakerCoefficient F pins ψ φ α := by
  funext g
  unfold whittakerCoefficient
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [mul_assoc]

private theorem isKfSmooth_of_exists_rightConv_eq (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hconv : ∃ α : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F α ∧ rightConv F φ α = φ) :
    IsKfSmooth F φ := by
  obtain ⟨α, hα, hαφ⟩ := hconv
  have h := isKfSmooth_rightConv F φ α hα
  rwa [hαφ] at h

private theorem isArchSmoothAt_and_archCasimirAt_whittakerCoefficient_eq_smul
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hsm : IsArchSmoothAt hw φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (lam : ℂ) (hΩ : archCasimirAt hw φ = lam • φ) (α : ℚ) :
    IsArchSmoothAt hw (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α) ∧
      archCasimirAt hw (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α)
        = lam • whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α := by
  obtain ⟨h₁, -, h₃⟩ := isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm D U gen ψ hψ.continuous w hw φ
    hsm (isKfSmooth_of_exists_rightConv_eq ℚ φ hconv) α
  exact ⟨h₁, by rw [h₃, hΩ, whittakerCoefficient_smul_fn]⟩

section CoefficientODE

private theorem whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    (k₀ : ℤ) (hwt : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k₀) φ)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hW : W = whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : AdelicLevel.glArch (𝓞 ℚ) ℚ g = 1) :
    (DifferentiableOn ℝ (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((k₀ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0) ∧
    (DifferentiableOn ℝ
        (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ
        (deriv (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv
              (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (((-k₀ : ℤ) : ℝ) : ℂ) * (y : ℂ)
                - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0) := by
  subst hW
  obtain ⟨hWsm, hWΩ⟩ :=
    isArchSmoothAt_and_archCasimirAt_whittakerCoefficient_eq_smul D U gen ψ hψ w hw φ hsm hconv _ hΩ 1
  have hWk := hasArchCharacterAt₀_whittakerCoefficient_fn ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 w _ hwt
  have hWψ := apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul ℚ ψ hw hψr
    (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1)
    (fun X g' => whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt ℚ D U gen ψ hψ hiso X g')
  exact LanglandsTunnell.whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq hw _ k₀ ν hWsm hWΩ hWk hWψ g hg

private theorem archCasimirAt_eq_of_laplaceEigenvalue_discrete {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (h : archCasimirAt hw φ = (RealArchParam.discrete u₀ n hn).laplaceEigenvalue • φ) :
    archCasimirAt hw φ = (1 / 4 - ((n : ℂ) / 2) ^ 2) • φ := by
  rw [h, RealArchParam.laplaceEigenvalue_discrete]
  congr 1
  ring

private theorem archCasimirAt_eq_of_laplaceEigenvalue_principal {w : InfinitePlace ℚ} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2)
    (h : archCasimirAt hw φ = (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue • φ) :
    archCasimirAt hw φ = (1 / 4 - ((u₁ - u₂) / 2) ^ 2) • φ :=
  h

end CoefficientODE

section Separation

private theorem eq_div_mul_of_whittaker_ode_of_moderateGrowth (ν : ℂ) (k : ℝ) (f g : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hg : DifferentiableOn ℝ g (Set.Ioi 0)) (hg' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv g) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y ^ N)
    (y₀ : ℝ) (hy₀ : 0 < y₀) (hf₀ : f y₀ ≠ 0) :
    ∀ y : ℝ, 0 < y → g y = g y₀ / f y₀ * f y := by
  obtain ⟨c₁, c₂, hc, hlin⟩ :=
    LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam ν k f g hf hf' hfeq hfgr hg hg'
      hgeq hggr
  have hc₂ : c₂ ≠ 0 := by
    rintro rfl
    have h₀ := hlin y₀ hy₀
    rw [zero_mul, add_zero, mul_eq_zero] at h₀
    rcases h₀ with h₀ | h₀
    · exact hc (by simp [h₀])
    · exact hf₀ h₀
  have hprop : ∀ y : ℝ, 0 < y → g y = -(c₁ / c₂) * f y := by
    intro y hy
    have h := hlin y hy
    field_simp
    linear_combination h
  intro y hy
  rw [hprop y hy, hprop y₀ hy₀, mul_div_assoc, div_self hf₀, mul_one]

end Separation

end WeightTransferAndCasimirEquation
section ReferenceDatumOverRationals

section ReferenceDatumRat₂

private theorem exists_whittakerCoefficient_one_diagOne_archRealUnit_mul_ne_zero (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    {ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    {χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ} (hwt : HasArchCharacterAt₀ ℚ w χ φ) {g₀ : AdelicGL2 (𝓞 ℚ) ℚ}
    (hg₀ : whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 g₀ ≠ 0) :
    ∃ (r : ℝ) (hr : r ≠ 0) (t : AdelicGL2 (𝓞 ℚ) ℚ), t ∈ finiteAdelicGL2Subgroup ℚ ∧
      whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1
        (diagOne (archUnitHom w (archRealUnit hw r hr)) * t) ≠ 0 := by
  obtain ⟨p, k'', hk'', hg⟩ := exists_eq_archRealGLAt_mul_of_glArch_eq_one_rat hw g₀
  obtain ⟨x, δ, v, k, hp⟩ := exists_unipotentGL2_mul_scalar_mul_diagOne_mul_eq p
  obtain ⟨X, -, -, hX⟩ := archRealGLAt_unipotentGL2_eq ℚ hw x
  refine ⟨v, v.ne_zero, k'', hk'', fun h0 => hg₀ ?_⟩
  have hW := hasArchCharacterAt₀_whittakerCoefficient_fn ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 w χ hwt
  rw [hg, ← hp, ← Units.mk0_val δ δ.ne_zero, ← Units.mk0_val v v.ne_zero, map_mul, map_mul, map_mul, hX,
    archRealGLAt_scalar, archRealGLAt_diagOne, mul_assoc _ (archRealGLAt hw (k : GL (Fin 2) ℝ)) k'',
    archRealGLAt_mul_comm_of_glArch_eq_one hw _ hk'', ← mul_assoc, archRealGLAt_coe_eq_adelicArchGLInclAt_rotAt,
    hW (rotAt hw k), mul_assoc, mul_assoc]
  erw [whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt ℚ D U gen ψ hψ hiso]
  rw [show whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1
        (centralScalar (𝓞 ℚ) ℚ (archUnitHom w (archRealUnit hw (δ : ℝ) δ.ne_zero))
          * (diagOne (archUnitHom w (archRealUnit hw (v : ℝ) v.ne_zero)) * k''))
        = ((ξ ⟨archUnitHom w (archRealUnit hw (δ : ℝ) δ.ne_zero), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
          * whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1
              (diagOne (archUnitHom w (archRealUnit hw (v : ℝ) v.ne_zero)) * k'') from
      whittakerCoefficient_centralScalar_mul ℚ _ ψ (isLsXiFunction_of_isIsotypicCuspFormAt hiso)
        ⟨archUnitHom w (archRealUnit hw (δ : ℝ) δ.ne_zero), Subgroup.mem_top _⟩ 1 _,
    h0, mul_zero, mul_zero, mul_zero]

end ReferenceDatumRat₂

end ReferenceDatumOverRationals
section SeparationOfVariables

section SeparationAtDatum

private theorem whittakerCoefficient_one_diagOne_archRealUnit_mul_eq_div_mul_pos
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    {k : InfinitePlace ℚ → ℤ}
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    {uc : ℂ} {ac : ℤ} (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (hgr : ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, t ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
        ‖whittakerCoefficient ℚ
            (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ D U gen (adelicBox ℚ))
      ψ φ 1)
    {t₀ : AdelicGL2 (𝓞 ℚ) ℚ} (ht₀ : t₀ ∈ finiteAdelicGL2Subgroup ℚ) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (href : W (diagOne (archUnitHom w (archRealUnit hw y₀ hy₀.ne')) * t₀) ≠ 0) :
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ y : ℝ, ∀ hy : 0 < y,
      W (diagOne (archUnitHom w (archRealUnit hw y hy.ne')) * h)
        = W (diagOne (archUnitHom w (archRealUnit hw y₀ hy₀.ne')) * h)
            / W (diagOne (archUnitHom w (archRealUnit hw y₀ hy₀.ne')) * t₀)
            * W (diagOne (archUnitHom w (archRealUnit hw y hy.ne')) * t₀) := by
  intro h hh y hy
  obtain ⟨α, hα, hα'⟩ := hconv

  have hpeel : ∀ (z : ℝ) (hz : 0 < z) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)
        = (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc * W (diagOne (archUnitHom w (archRealUnit hw z hz.ne')) * g) := by
    intro z hz g
    rw [hW]
    exact whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hw
      hcen 1 z hz g
  have hP : ∀ (z : ℝ), 0 < z → (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc ≠ 0 := fun z hz =>
    left_ne_zero_of_mul_eq_one (inv_sqrt_cpow_mul_sqrt_cpow uc hz)

  have hgrowth : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z → ‖W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N' := by
    intro g hg
    obtain ⟨C, M, hCM⟩ := hgr g hg
    obtain ⟨C', N', hb⟩ := exists_forall_norm_cpow_mul_le_of_forall_norm_le uc
      (fun z : ℝ => if hz : 0 < z then W (diagOne (archUnitHom w (archRealUnit hw z hz.ne')) * g) else 0) C M
      (fun z hz => by
        simp only [dif_pos hz]
        have := hCM (archUnitHom w (archRealUnit hw z hz.ne')) rfl
        rwa [ideleNorm_archUnitHom_archRealUnit_rat hw, abs_of_pos hz, ← hW] at this)
    refine ⟨C', N', fun z hz => ?_⟩
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
    have hbz := hb z hz
    simp only [dif_pos hz0] at hbz
    rw [hpeel z hz0 g]
    exact hbz

  obtain ⟨⟨hf, hf', hfeq⟩, -⟩ := whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt
    _ _ _ ψ hψ hw hψr hiso ⟨α, hα, hα'⟩ hsm ν hΩ (k w) (hwt w hw) W hW t₀ ht₀
  obtain ⟨⟨hg, hg', hgeq⟩, -⟩ := whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt
    _ _ _ ψ hψ hw hψr hiso ⟨α, hα, hα'⟩ hsm ν hΩ (k w) (hwt w hw) W hW h hh
  have hf₀ : W (archRealGLAt hw (splitTorusGL2 (Real.log y₀ / 2)) * t₀) ≠ 0 := by
    rw [hpeel y₀ hy₀ t₀]
    exact mul_ne_zero (hP y₀ hy₀) href
  have hsep : W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * h)
      = W (archRealGLAt hw (splitTorusGL2 (Real.log y₀ / 2)) * h)
          / W (archRealGLAt hw (splitTorusGL2 (Real.log y₀ / 2)) * t₀)
          * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * t₀) :=
    eq_div_mul_of_whittaker_ode_of_moderateGrowth ν ((k w : ℤ) : ℝ) _ _ hf hf' hfeq (hgrowth t₀ ht₀) hg hg' hgeq
      (hgrowth h hh) y₀ hy₀ hf₀ y hy
  rw [hpeel y hy h, hpeel y₀ hy₀ h, hpeel y₀ hy₀ t₀, hpeel y hy t₀, mul_div_mul_left _ _ (hP y₀ hy₀)] at hsep
  exact mul_left_cancel₀ (hP y hy) (hsep.trans (mul_left_comm _ _ _))

end SeparationAtDatum

section FactorizationClause

private theorem extensionEmbedding_eq_ofReal_ringEquivRealOfIsReal
    {w : InfinitePlace ℚ} (hw : w.IsReal) (x : w.Completion) :
    extensionEmbedding w x = ((ringEquivRealOfIsReal hw x : ℝ) : ℂ) := by
  rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw]

private theorem extensionEmbedding_idele_eq_ofReal_archReal
    {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w) = ((archReal hw a : ℝ) : ℂ) :=
  extensionEmbedding_eq_ofReal_ringEquivRealOfIsReal hw _

open scoped Classical in

private theorem exists_forall_whittakerCoefficient_one_diagOne_mul_eq_prod_mul
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    {w : InfinitePlace ℚ} (hw : w.IsReal) (Fref : ℂ → ℂ) (cst : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hprop : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
      whittakerCoefficient ℚ
        (productionPinsOf ℚ D U gen (adelicBox ℚ))
        ψ φ 1
        (diagOne (archUnitHom w (archRealUnit hw r hr)) * h) = cst h * Fref (r : ℂ))
    (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ
          (productionPinsOf ℚ D U gen (adelicBox ℚ))
          ψ φ 1
          (diagOne a * g)
        = (∏ w' : InfinitePlace ℚ, ρ * Fref (extensionEmbedding w' ((a : AdeleRing (𝓞 ℚ) ℚ).1 w')))
            * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g := by
  refine ⟨fun x g => if hx : IsUnit x then ρ⁻¹ * cst (diagOne (Units.map (finIncl (𝓞 ℚ) ℚ) hx.unit) * g) else 0, ?_⟩
  intro a g hg
  dsimp only
  have hunit : IsUnit (a : AdeleRing (𝓞 ℚ) ℚ).2 := ⟨Units.map (finProjHom ℚ) a, rfl⟩
  have hfin : Units.map (finIncl (𝓞 ℚ) ℚ) hunit.unit = finPart a := by
    apply Units.ext
    rw [finPart_coe]
    exact congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => ((1 : InfiniteAdeleRing ℚ), x)) hunit.unit_spec
  have hmem : diagOne (finPart a) * g ∈ finiteAdelicGL2Subgroup ℚ := mul_mem (diagOne_finPart_mem a) hg
  have hkey := hprop _ hmem (archReal hw a) (archReal_ne_zero hw a)
  rw [← mul_assoc, ← map_mul, ← eq_archUnitHom_archRealUnit_mul_finPart hw a] at hkey
  rw [hkey, Fintype.prod_subsingleton _ w, dif_pos hunit, hfin, extensionEmbedding_idele_eq_ofReal_archReal hw,
    mul_mul_mul_comm, mul_inv_cancel₀ hρ, one_mul, mul_comm]

end FactorizationClause

end SeparationOfVariables
section GrowthOfSheetFunctions

section GrowthOfSheets

private theorem exists_forall_norm_splitTorus_le_mul_rpow
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    {k : InfinitePlace ℚ → ℤ}
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    {uc : ℂ} {ac : ℤ} (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (hgr : ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, t ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
        ‖whittakerCoefficient ℚ
            (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ D U gen (adelicBox ℚ))
      ψ φ 1)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ finiteAdelicGL2Subgroup ℚ) :
    ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z → ‖W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N' := by
  obtain ⟨α, hα, hα'⟩ := hconv
  have hpeel : ∀ (z : ℝ) (hz : 0 < z),
      W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)
        = (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc * W (diagOne (archUnitHom w (archRealUnit hw z hz.ne')) * g) := by
    intro z hz
    rw [hW]
    exact whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hw
      hcen 1 z hz g
  obtain ⟨C, M, hCM⟩ := hgr g hg
  obtain ⟨C', N', hb⟩ := exists_forall_norm_cpow_mul_le_of_forall_norm_le uc
    (fun z : ℝ => if hz : 0 < z then W (diagOne (archUnitHom w (archRealUnit hw z hz.ne')) * g) else 0) C M
    (fun z hz => by
      simp only [dif_pos hz]
      have := hCM (archUnitHom w (archRealUnit hw z hz.ne')) rfl
      rwa [ideleNorm_archUnitHom_archRealUnit_rat hw, abs_of_pos hz, ← hW] at this)
  refine ⟨C', N', fun z hz => ?_⟩
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hbz := hb z hz
  simp only [dif_pos hz0] at hbz
  rw [hpeel z hz0]
  exact hbz

private theorem exists_forall_norm_J_splitTorus_le_mul_rpow
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    {ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ}
    {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ξ N S Φ φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    {k : InfinitePlace ℚ → ℤ}
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    {uc : ℂ} {ac : ℤ} (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (hgr : ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, t ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
        ‖whittakerCoefficient ℚ
            (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
      (productionPinsOf ℚ D U gen (adelicBox ℚ))
      ψ φ 1)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ finiteAdelicGL2Subgroup ℚ) :
    ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z →
      ‖W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N' := by
  obtain ⟨α, hα, hα'⟩ := hconv
  have hpeel : ∀ (z : ℝ) (hz : 0 < z),
      W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)
        = (((Real.sqrt z)⁻¹ : ℝ) : ℂ) ^ uc
            * W (diagOne (archUnitHom w (archRealUnit hw (-z) (neg_ne_zero.mpr hz.ne'))) * g) := by
    intro z hz
    rw [hW]
    exact whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ
      (isLsXiFunction_of_isIsotypicCuspFormAt hiso) hw hcen 1 z hz g
  obtain ⟨C, M, hCM⟩ := hgr g hg
  obtain ⟨C', N', hb⟩ := exists_forall_norm_cpow_mul_le_of_forall_norm_le uc
    (fun z : ℝ =>
      if hz : 0 < z then W (diagOne (archUnitHom w (archRealUnit hw (-z) (neg_ne_zero.mpr hz.ne'))) * g) else 0) C M
    (fun z hz => by
      simp only [dif_pos hz]
      have := hCM (archUnitHom w (archRealUnit hw (-z) (neg_ne_zero.mpr hz.ne'))) rfl
      rwa [ideleNorm_archUnitHom_archRealUnit_rat hw, abs_neg, abs_of_pos hz, ← hW] at this)
  refine ⟨C', N', fun z hz => ?_⟩
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hbz := hb z hz
  simp only [dif_pos hz0] at hbz
  rw [hpeel z hz0]
  exact hbz

end GrowthOfSheets

end GrowthOfSheetFunctions

end P2M.TorusKit

open P2M.TorusKit in

theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ D U gen (adelicBox ℚ))
        ξ N S Φ φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    (k : ℤ) (hwt : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k) φ)
    (uc : ℂ) (ac : ℤ) (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
        (productionPinsOf ℚ D U gen (adelicBox ℚ))
        ψ φ 1)
    (hgr : ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, t ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
        ‖W (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M) :

    ((∀ (X : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), W (unipotentGL2 X * g) = ψ X * W g) ∧
      ∀ (x : ℝ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        W (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * W g) ∧

    (∀ (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
        = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ uc * W (archRealGLAt hw (diagOne (Units.mk0 y hy.ne')) * g)) ∧

    (∀ (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)
        = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ uc
            * W (archRealGLAt hw (diagOne (Units.mk0 (-y) (neg_ne_zero.mpr hy.ne'))) * g)) ∧

    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, AdelicLevel.glArch (𝓞 ℚ) ℚ g = 1 →
      (DifferentiableOn ℝ (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
        DifferentiableOn ℝ (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)))
          (Set.Ioi 0) ∧
        ∀ y : ℝ, 0 < y →
          (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))) y
              + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((k : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
                * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0) ∧
      (DifferentiableOn ℝ
          (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
        DifferentiableOn ℝ
          (deriv (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)))
          (Set.Ioi 0) ∧
        ∀ y : ℝ, 0 < y →
          (y : ℂ) ^ 2 * deriv (deriv
                (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) y
              + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (((-k : ℤ) : ℝ) : ℂ) * (y : ℂ)
                  - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
                * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0)) ∧

    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z → ‖W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N') ∧

    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z →
        ‖W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N') ∧

    (∀ g₀ : AdelicGL2 (𝓞 ℚ) ℚ, W g₀ ≠ 0 →
      ∃ (r : ℝ) (hr : r ≠ 0) (t : AdelicGL2 (𝓞 ℚ) ℚ), t ∈ finiteAdelicGL2Subgroup ℚ ∧
        W (archRealGLAt hw (diagOne (Units.mk0 r hr)) * t) ≠ 0) ∧

    (∀ t₀ : AdelicGL2 (𝓞 ℚ) ℚ, t₀ ∈ finiteAdelicGL2Subgroup ℚ → ∀ (y₀ : ℝ) (hy₀ : 0 < y₀),
      W (archRealGLAt hw (diagOne (Units.mk0 y₀ hy₀.ne')) * t₀) ≠ 0 →
        ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (y : ℝ) (hy : 0 < y),
          W (archRealGLAt hw (diagOne (Units.mk0 y hy.ne')) * h)
            = W (archRealGLAt hw (diagOne (Units.mk0 y₀ hy₀.ne')) * h)
                / W (archRealGLAt hw (diagOne (Units.mk0 y₀ hy₀.ne')) * t₀)
                * W (archRealGLAt hw (diagOne (Units.mk0 y hy.ne')) * t₀)) ∧

    (∀ (Fref : ℂ → ℂ) (cst : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      (∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
        W (archRealGLAt hw (diagOne (Units.mk0 r hr)) * h) = cst h * Fref (r : ℂ)) →
      ∀ ρ : ℂ, ρ ≠ 0 →
        ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
          ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
            W (diagOne a * g)
              = (∏ w' : InfinitePlace ℚ, ρ * Fref (extensionEmbedding w' ((a : AdeleRing (𝓞 ℚ) ℚ).1 w')))
                  * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) := by
  have hLs := isLsXiFunction_of_isIsotypicCuspFormAt hiso

  have hdiag : ∀ (r : ℝ) (hr : r ≠ 0), archRealGLAt hw (diagOne (Units.mk0 r hr))
      = diagOne (archUnitHom w (archRealUnit hw r hr)) := fun r hr => archRealGLAt_diagOne ℚ hw r hr
  have hgr' : ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, t ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
        ‖whittakerCoefficient ℚ
            (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1 (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M := by
    intro t ht
    rw [← hW]
    exact hgr t ht
  have hwt' : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal),
      HasArchCharacterAt₀ ℚ w' (archWeightCharAt hw' ((fun _ : InfinitePlace ℚ => k) w')) φ := by
    intro w' hw'
    obtain rfl : w' = w := Subsingleton.elim _ _
    exact hwt
  have huni : ∀ (X : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), W (unipotentGL2 X * g) = ψ X * W g := by
    intro X g
    rw [hW]
    exact whittakerCoefficient_one_unipotentGL2_mul_of_isIsotypicCuspFormAt ℚ _ _ _ ψ hψ hiso X g
  refine ⟨⟨huni, apply_archRealGLAt_unipotentGL2_mul_of_forall_unipotentGL2_mul ℚ ψ hw hψr W huni⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy g
    rw [hW, hdiag]
    exact whittakerCoefficient_archRealGLAt_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ hLs hw hcen 1 y hy g
  ·
    intro y hy g
    rw [hW, hdiag]
    exact whittakerCoefficient_archRealGLAt_J_mul_splitTorusGL2_half_log_of_isArchCompAt ℚ _ _ _ _ ψ hLs hw hcen 1 y
      hy g
  ·
    intro g hg
    exact whittaker_ode_splitTorus_whittakerCoefficient_one_of_isIsotypicCuspFormAt _ _ _ ψ hψ hw hψr hiso hconv hsm
      ν hΩ k hwt W hW g hg
  ·
    intro g hg
    exact exists_forall_norm_splitTorus_le_mul_rpow D U gen ψ hψ hw hψr hiso hconv hsm ν hΩ hwt' hcen
      hgr' W hW g hg
  ·
    intro g hg
    exact exists_forall_norm_J_splitTorus_le_mul_rpow D U gen ψ hψ hw hψr hiso hconv hsm ν hΩ hwt' hcen
      hgr' W hW g hg
  ·
    intro g₀ hg₀
    rw [hW] at hg₀
    obtain ⟨r, hr, t, ht, hne⟩ :=
      exists_whittakerCoefficient_one_diagOne_archRealUnit_mul_ne_zero _ _ _ ψ hψ hw hiso hwt hg₀
    refine ⟨r, hr, t, ht, ?_⟩
    rw [hW, hdiag]
    exact hne
  ·
    intro t₀ ht₀ y₀ hy₀ href h hh y hy
    simp only [hdiag] at href ⊢
    exact whittakerCoefficient_one_diagOne_archRealUnit_mul_eq_div_mul_pos D U gen ψ hψ hw hψr hiso hconv
      hsm ν hΩ hwt' hcen hgr' W hW ht₀ hy₀ href h hh y hy
  ·
    intro Fref cst hprop ρ hρ
    have hprop' : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
        whittakerCoefficient ℚ
            (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ 1
            (diagOne (archUnitHom w (archRealUnit hw r hr)) * h) = cst h * Fref (r : ℂ) := by
      intro h hh r hr
      rw [← hdiag, ← hW]
      exact hprop h hh r hr
    obtain ⟨C, hC⟩ := exists_forall_whittakerCoefficient_one_diagOne_mul_eq_prod_mul D U gen ψ φ hw Fref cst
      hprop' ρ hρ
    refine ⟨C, fun a g hg => ?_⟩
    rw [hW]
    exact hC a g hg

end S_AutomorphicForm_whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul (solution)
