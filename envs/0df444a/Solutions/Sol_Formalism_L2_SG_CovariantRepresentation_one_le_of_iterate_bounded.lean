-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.one_le_of_iterate_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:43.642783+00:00
-- url     : https://prove2.me/submissions/21121f91-b8af-4a11-bf68-47ed9d703fab

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
theorem _root_.solution (μ : Measure H) [IsHaarMeasure μ] {f : H → H} (hf : Continuous f)
    (hinj : Function.Injective f) {c : ℝ≥0∞} (hc : μ.map f = c • μ) {V L : Set H} (hV : IsCompact V)
    (hV1 : V ∈ 𝓝 (1 : H)) (hL : IsCompact L) (hb : ∀ n : ℕ, f^[n] '' V ⊆ L) : 1 ≤ c := by
  have hpow : ∀ n : ℕ, μ.map (f^[n]) = c ^ n • μ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ, ← map_map (hf.iterate n).measurable hf.measurable, hc, Measure.map_smul,
        ih, smul_smul, pow_succ']
  have hVpos : 0 < μ V := measure_pos_of_mem_nhds μ hV1
  have hLtop : μ L ≠ ∞ := hL.measure_lt_top.ne
  have hle : ∀ n : ℕ, μ V ≤ c ^ n * μ L := by
    intro n
    have hcpt : IsCompact (f^[n] '' V) := hV.image (hf.iterate n)
    have e := congrArg (fun m : Measure H => m (f^[n] '' V)) (hpow n)
    simp only [Measure.smul_apply, smul_eq_mul] at e
    rw [Measure.map_apply (hf.iterate n).measurable hcpt.measurableSet,
      Set.preimage_image_eq _ (hinj.iterate n)] at e
    rw [e]
    gcongr
    exact hb n
  by_contra h
  push_neg at h
  have ht : Tendsto (fun n : ℕ => c ^ n * μ L) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h) (Or.inr hLtop)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hVpos)).exists
  exact absurd (hle n) (not_le.2 hn)
end Formalism.L2.SG.CovariantRepresentation
