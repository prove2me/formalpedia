-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.modular_eq_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:50.368721+00:00
-- url     : https://prove2.me/submissions/e32cc366-6ab9-438a-90c5-4cb9cac910aa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_measurable_lwt
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_tsum_lwt
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_lwt_le
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_lintegral_eq_of_tsum
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_map_mul_right_eq_modular

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
theorem _root_.solution (μ : Measure H) [IsHaarMeasure μ] (Γ : Subgroup H) [Countable Γ]
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K)
    {δ : H} (hδ : δ ∈ Γ) : modularCharacterFun δ = 1 := by
  set I := ∫⁻ x, lwt Γ K x ∂μ with hI
  have hw := measurable_lwt Γ hK
  have hItop : I ≠ ∞ := by
    refine ne_top_of_le_ne_top (hK.measure_lt_top (μ := μ)).ne ?_
    calc I ≤ ∫⁻ x, K.indicator 1 x ∂μ := lintegral_mono fun x => lwt_le Γ hcov x
      _ = μ K := lintegral_indicator_one hK.measurableSet
  have hI0 : I ≠ 0 := by
    intro h0
    have huniv : μ univ = ∑' γ : Γ, I := by
      calc μ univ = ∫⁻ _x, 1 ∂μ := (lintegral_one).symm
        _ = ∫⁻ x, ∑' γ : Γ, lwt Γ K ((γ : H) * x) ∂μ := by
            congr 1; funext x; rw [tsum_lwt Γ hK hcov x]
        _ = ∑' γ : Γ, ∫⁻ x, lwt Γ K ((γ : H) * x) ∂μ :=
            lintegral_tsum fun γ => (hw.comp (measurable_const_mul _)).aemeasurable
        _ = ∑' γ : Γ, I := by
            congr 1; funext γ; exact lintegral_mul_left_eq_self _ _
    rw [h0, tsum_zero, Measure.measure_univ_eq_zero] at huniv
    exact NeZero.ne μ huniv
  have hshift : ∫⁻ x, lwt Γ K (x * δ) ∂μ = I :=
    (lintegral_eq_of_tsum μ Γ (hw.comp (measurable_mul_const δ)) hw
      (fun x => by simpa [mul_assoc] using tsum_lwt Γ hK hcov (x * δ)) (tsum_lwt Γ hK hcov)).trans rfl
  have hmap : ∫⁻ x, lwt Γ K (x * δ) ∂μ = (modularCharacterFun δ : ℝ≥0∞) * I := by
    rw [← lintegral_map hw (measurable_mul_const δ), map_mul_right_eq_modular μ δ, lintegral_smul_measure]
    all_goals first | rfl | simp [hI]
  have : (modularCharacterFun δ : ℝ≥0∞) * I = 1 * I := by rw [← hmap, hshift, one_mul]
  exact ENNReal.coe_eq_one.1 ((ENNReal.mul_left_inj hI0 hItop).1 this)
end Formalism.L2.SG.CovariantRepresentation
