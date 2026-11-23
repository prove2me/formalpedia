-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:48.74563+00:00
-- url     : https://prove2.me/submissions/bd1587fb-a3a4-4601-8da7-523dc885dc6f

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
theorem _root_.solution (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (h : ∀ i, μ i ≠ 0) : Measure.pi μ ≠ 0 := by
  intro h0
  have h1 := congrArg (fun ν : Measure (∀ i, α i) => ν Set.univ) h0
  simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply] at h1
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 h1
  exact h i (Measure.measure_univ_eq_zero.1 hi)
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
