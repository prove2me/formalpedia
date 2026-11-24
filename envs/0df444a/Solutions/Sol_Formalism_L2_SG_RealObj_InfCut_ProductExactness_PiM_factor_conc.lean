-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.factor_conc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:12.583816+00:00
-- url     : https://prove2.me/submissions/b50bb63a-15ae-4755-bb65-0d2f890f04f6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_ExistsBox
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_pi_box_eval

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
theorem _root_.solution (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) (N : ∀ i, Set (α i))
    (hc : Measure.pi μ (Set.univ.pi N)ᶜ = 0) (v : ι) : μ v (N v)ᶜ = 0 := by
  have hsub : Set.univ.pi (Function.update (fun w => (Set.univ : Set (α w))) v (N v)ᶜ) ⊆
      (Set.univ.pi N)ᶜ := by
    intro x hx hxN
    have hv := hx v (Set.mem_univ v)
    rw [Function.update_self] at hv
    exact hv (hxN v (Set.mem_univ v))
  have h0 := measure_mono_null hsub hc
  rw [pi_box_eval] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exfalso
    obtain ⟨w, -, hw⟩ := Finset.prod_eq_zero_iff.mp h
    exact hne w (Measure.measure_univ_eq_zero.mp hw)
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
