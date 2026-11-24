-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.lintegral_eq_of_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:57.945446+00:00
-- url     : https://prove2.me/submissions/b27e1ad6-33cb-4472-8cfa-116fb1da0fee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.CovariantRepresentation
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
namespace Formalism.L2.SG.CovariantRepresentation
theorem _root_.solution (μ : Measure H) [μ.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ]
    {f g : H → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, ∑' γ : Γ, f ((γ : H) * x) = 1) (hg1 : ∀ x, ∑' γ : Γ, g ((γ : H) * x) = 1) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ := by
  calc ∫⁻ x, f x ∂μ = ∫⁻ x, ∑' γ : Γ, f x * g ((γ : H) * x) ∂μ := by
        congr 1; funext x; rw [ENNReal.tsum_mul_left, hg1, mul_one]
    _ = ∑' γ : Γ, ∫⁻ x, f x * g ((γ : H) * x) ∂μ :=
        lintegral_tsum fun γ => (hf.mul (hg.comp (measurable_const_mul _))).aemeasurable
    _ = ∑' γ : Γ, ∫⁻ y, f ((γ : H)⁻¹ * y) * g y ∂μ := by
        congr 1; funext γ
        have := lintegral_mul_left_eq_self (μ := μ) (fun y => f ((γ : H)⁻¹ * y) * g y) (γ : H)
        simpa only [inv_mul_cancel_left] using this
    _ = ∫⁻ y, ∑' γ : Γ, f ((γ : H)⁻¹ * y) * g y ∂μ :=
        (lintegral_tsum fun γ => ((hf.comp (measurable_const_mul _)).mul hg).aemeasurable).symm
    _ = ∫⁻ y, g y ∂μ := by
        congr 1; funext y
        rw [ENNReal.tsum_mul_right]
        have := (Equiv.inv Γ).tsum_eq (fun γ : Γ => f ((γ : H) * y))
        simp only [Equiv.inv_apply, Subgroup.coe_inv] at this
        rw [this, hf1, one_mul]
end Formalism.L2.SG.CovariantRepresentation
