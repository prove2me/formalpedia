-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_conc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:52.073286+00:00
-- url     : https://prove2.me/submissions/a058bf9e-7178-45ee-b985-da846d0283d5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LintegralFinProd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.ProductExactness Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
variable {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
theorem _root_.solution (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (S : ∀ i, Set (α i))
    (h : ∀ i, μ i (S i)ᶜ = 0) : Measure.pi μ (Set.univ.pi S)ᶜ = 0 := by
  have hsub : (Set.univ.pi S)ᶜ ⊆ ⋃ i, Function.eval i ⁻¹' (S i)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_univ_pi, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  exact measure_mono_null hsub (measure_iUnion_null fun i => Measure.pi_eval_preimage_null (μ := μ) (h i))
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
