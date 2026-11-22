-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.cls_leftRel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:43.218116+00:00
-- url     : https://prove2.me/submissions/84af11a7-bf11-472b-8731-57eae9353445

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_cls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {G : Type} [Group G]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (K₀ : Subgroup G) (q : G ⧸ K₀) :
    cls (QuotientGroup.leftRel K₀) q = (fun z => q.out⁻¹ * z) ⁻¹' (K₀ : Set G) := by
  ext y
  simp only [Set.mem_preimage, SetLike.mem_coe]
  rw [mem_cls]
  constructor
  · intro h
    have h' : (y : G ⧸ K₀) = ((q.out : G) : G ⧸ K₀) := h.trans (Quotient.out_eq q).symm
    rw [QuotientGroup.eq] at h'
    simpa using K₀.inv_mem h'
  · intro h
    have h' : ((q.out : G) : G ⧸ K₀) = (y : G ⧸ K₀) := by
      rw [QuotientGroup.eq]; exact h
    exact h'.symm.trans (Quotient.out_eq q)
end Formalism.DoubleCosetMeasures.P
