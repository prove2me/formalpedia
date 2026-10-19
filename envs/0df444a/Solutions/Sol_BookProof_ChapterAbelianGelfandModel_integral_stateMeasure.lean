-- Prove2me | solution 1 for BookProof.ChapterAbelianGelfandModel.integral_stateMeasure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:39:14.930892+00:00
-- url     : https://prove2.me/submissions/97033e26-b504-4682-9599-750bcb42299a

-- Generated from ChapterAbelianGelfandModel.lean — solution of BookProof.ChapterAbelianGelfandModel.integral_stateMeasure
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_integral_stateMeasure_ofReal
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterA3b
open BookProof.ChapterAbelianGelfandModel



open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder


open BookProof.ChapterLinftyMultiplication

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {X : Type*} [TopologicalSpace X]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g))

set_option maxHeartbeats 1000000 in
theorem solution (g : C(X, ℂ)) :
    psi g = ∫ x, g x ∂(stateMeasure psi hpos) := by

  classical
  set mu := stateMeasure psi hpos with hmu
  set gre : C(X, ℝ) := ⟨fun x => (g x).re, Complex.continuous_re.comp g.continuous⟩ with hgre
  set gim : C(X, ℝ) := ⟨fun x => (g x).im, Complex.continuous_im.comp g.continuous⟩ with hgim
  have hg : g = toC gre + Complex.I • toC gim := by
    ext x
    simp only [hgre, hgim, ContinuousMap.add_apply, ContinuousMap.smul_apply, toC_apply,
      ContinuousMap.coe_mk, smul_eq_mul]
    apply Complex.ext <;> simp
  have hint : ∀ f : C(X, ℂ), Integrable (fun x => f x) mu := by
    intro f
    have hm : AEStronglyMeasurable (fun x => f x) mu := (map_continuous f).aestronglyMeasurable
    obtain ⟨C, hC⟩ := (isCompact_range (map_continuous f)).isBounded.subset_closedBall 0
    have hb : MemLp (fun x => f x) ⊤ mu := by
      refine memLp_top_of_bound hm C (.of_forall fun x => ?_)
      simpa using hC (Set.mem_range_self x)
    exact hb.integrable le_top
  calc psi g = psi (toC gre) + Complex.I * psi (toC gim) := by
        rw [hg, map_add, map_smul]
        simp
    _ = (∫ x, (toC gre) x ∂mu) + Complex.I * ∫ x, (toC gim) x ∂mu := by
        rw [integral_stateMeasure_ofReal psi hpos gre, integral_stateMeasure_ofReal psi hpos gim]
    _ = ∫ x, ((toC gre) x + Complex.I * (toC gim) x) ∂mu := by
        rw [integral_add (hint _) ((hint _).const_mul _), integral_const_mul]
    _ = ∫ x, g x ∂mu := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [hgre, hgim, toC_apply, ContinuousMap.coe_mk]
        apply Complex.ext <;> simp
