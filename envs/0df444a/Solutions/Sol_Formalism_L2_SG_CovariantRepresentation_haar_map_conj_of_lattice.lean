-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.haar_map_conj_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:15:32.811158+00:00
-- url     : https://prove2.me/submissions/237cc649-ed7b-44de-89e9-ae05d527153f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_haar_map_mul_right_of_lattice

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
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (n : H) :
    μ.map (fun x => n⁻¹ * x * n) = μ := by
  have e : (fun x => n⁻¹ * x * n) = (· * n) ∘ (n⁻¹ * ·) := rfl
  rw [e, ← map_map (measurable_mul_const n) (measurable_const_mul n⁻¹), map_mul_left_eq_self μ n⁻¹,
    haar_map_mul_right_of_lattice μ Γ hK hcov n]
end Formalism.L2.SG.CovariantRepresentation
