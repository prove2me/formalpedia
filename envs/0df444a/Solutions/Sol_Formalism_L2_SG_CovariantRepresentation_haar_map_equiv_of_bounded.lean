-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.haar_map_equiv_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:03.791929+00:00
-- url     : https://prove2.me/submissions/bc0c7195-d763-4956-8349-54915328ffd1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_one_le_of_iterate_bounded

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
theorem _root_.solution (μ : Measure H) [IsHaarMeasure μ] (α : H ≃ₜ* H) {V L : Set H}
    (hV : IsCompact V) (hV1 : V ∈ 𝓝 (1 : H)) (hL : IsCompact L)
    (hb : ∀ n : ℕ, (⇑α)^[n] '' V ⊆ L ∧ (⇑α.symm)^[n] '' V ⊆ L) : μ.map α = μ := by
  have hc : μ.map α = (haarScalarFactor (μ.map α) μ : ℝ≥0∞) • μ := by
    rw [← ENNReal.smul_def]; exact isMulLeftInvariant_eq_smul _ μ
  have hc' : μ.map α.symm = (haarScalarFactor (μ.map α.symm) μ : ℝ≥0∞) • μ := by
    rw [← ENNReal.smul_def]; exact isMulLeftInvariant_eq_smul _ μ
  set c : ℝ≥0∞ := (haarScalarFactor (μ.map α) μ : ℝ≥0∞)
  set c' : ℝ≥0∞ := (haarScalarFactor (μ.map α.symm) μ : ℝ≥0∞)
  have h1 : 1 ≤ c := one_le_of_iterate_bounded μ α.continuous α.injective hc hV hV1 hL fun n => (hb n).1
  have h2 : 1 ≤ c' :=
    one_le_of_iterate_bounded μ α.symm.continuous α.symm.injective hc' hV hV1 hL fun n => (hb n).2
  have hid : μ = (c * c') • μ := by
    have e : μ.map (⇑α.symm ∘ ⇑α) = μ := by
      have : (⇑α.symm ∘ ⇑α) = id := funext fun x => α.symm_apply_apply x
      rw [this, Measure.map_id]
    rw [← map_map (show Measurable (⇑α.symm) from α.symm.continuous.measurable)
      (show Measurable (⇑α) from α.continuous.measurable), hc, Measure.map_smul, hc',
      smul_smul] at e
    exact e.symm
  obtain ⟨W, hW, hW1⟩ := exists_compact_mem_nhds (1 : H)
  have hWpos : 0 < μ W := measure_pos_of_mem_nhds μ hW1
  have e : c * c' * μ W = 1 * μ W := by
    conv_rhs => rw [hid]
    simp
  have hcc : c * c' = 1 := (ENNReal.mul_left_inj hWpos.ne' hW.measure_lt_top.ne).1 e
  have hc1 : c = 1 := le_antisymm (by
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * c' := by gcongr
      _ = 1 := hcc) h1
  rw [hc, hc1, one_smul]
end Formalism.L2.SG.CovariantRepresentation
