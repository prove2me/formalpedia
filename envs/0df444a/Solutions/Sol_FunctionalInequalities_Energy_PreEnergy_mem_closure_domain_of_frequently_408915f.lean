-- Prove2me | solution 1 for FunctionalInequalities.Energy.PreEnergy.mem_closure_domain_of_frequently_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:54:26.068786+00:00
-- url     : https://prove2.me/submissions/5e3e39a6-f334-4aab-a0a9-c06b4d5600d6

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Theorems.Thm_FunctionalInequalities_Energy_exists_mem_of_isClosed_of_frequently_norm_le_408915f

noncomputable section
open Filter Topology Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section PreEnergy
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
variable (T : X →ₗ.[ℝ] H)
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities.Energy.PreEnergy in
/-- Any approximating sequence with frequently bounded energies forces membership in the domain
of the closure, with the corresponding norm bound. -/
theorem solution (hT : T.IsClosable) {x : X}
    (f : (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap T).ApproximatingSequence x) {L : NNReal}
    (hL : ∃ᶠ n in atTop, ‖T (f.1 n)‖₊ ≤ L) :
    ∃ hx : x ∈ T.closure.domain, ‖T.closure ⟨x, hx⟩‖₊ ≤ L := by
  have hG : IsClosed (T.closure.graph : Set (X × H)) := hT.closure_isClosed
  let g : ℕ → T.domain := f.1
  have hxy : ∀ n, ((g n : X), T (g n)) ∈ T.closure.graph := fun n ↦
    (LinearPMap.le_graph_of_le (T.le_closure)) (T.mem_graph (g n))
  have hx : Tendsto (fun n ↦ (g n : X)) atTop (𝓝 x) := f.2
  have hL' : ∃ᶠ n in atTop, ‖T (g n)‖ ≤ (L : ℝ) := by
    refine hL.mono fun n hn ↦ ?_
    exact_mod_cast hn
  obtain ⟨y₀, hy₀, hy₀L⟩ := FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le_408915f hG hxy hx hL'
  have hxdom : x ∈ T.closure.domain := LinearPMap.mem_domain_of_mem_graph hy₀
  refine ⟨hxdom, ?_⟩
  have : y₀ = T.closure ⟨x, hxdom⟩ := (LinearPMap.image_iff hxdom).mpr hy₀
  rw [← this]
  exact_mod_cast hy₀L
