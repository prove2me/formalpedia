-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.factor_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:29.58596+00:00
-- url     : https://prove2.me/submissions/cfe482b7-1d41-4565-9a09-4a539f6810fd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_ExistsBox
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_exists_box_alt
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
theorem _root_.solution (μ μ' : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μ' i)]
    (hne : ∀ i, μ i ≠ 0) (v : ι) (hw : ∀ w, w ≠ v → μ' w = μ w) (h : Measure.pi μ' = Measure.pi μ) : μ' v = μ v := by
  obtain ⟨S, -, hS0, hSt⟩ := exists_box_alt μ hne
  ext A _
  have h1 := pi_box_eval μ' S v A
  have h2 := pi_box_eval μ S v A
  have hP : ∏ w ∈ Finset.univ.erase v, μ' w (S w) = ∏ w ∈ Finset.univ.erase v, μ w (S w) :=
    Finset.prod_congr rfl fun w hm => by rw [hw w (Finset.ne_of_mem_erase hm)]
  rw [h, h2, hP] at h1
  have hP0 : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hS0 w
  have hPt : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ ∞ := ENNReal.prod_ne_top fun w _ => hSt w
  exact ((ENNReal.mul_left_inj hP0 hPt).mp h1).symm
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
