-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.exists_pos_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:08.303511+00:00
-- url     : https://prove2.me/submissions/385b36df-44bc-48fc-bd4c-c8215d237a38

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
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
theorem _root_.solution {β : Type*} [MeasurableSpace β] (ν : Measure β) [SigmaFinite ν] (h : ν ≠ 0) :
    ∃ t, MeasurableSet t ∧ ν t ≠ 0 ∧ ν t ≠ ∞ := by
  by_contra hne
  push_neg at hne
  apply h
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
  refine measure_iUnion_null fun n => ?_
  by_contra hn
  exact (measure_spanningSets_lt_top ν n).ne (hne _ (measurableSet_spanningSets ν n) hn)
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
