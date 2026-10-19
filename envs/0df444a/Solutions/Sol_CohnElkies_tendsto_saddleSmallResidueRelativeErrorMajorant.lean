-- Prove2me | solution 1 for CohnElkies.tendsto_saddleSmallResidueRelativeErrorMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/ece2ad6a-492a-46db-b266-95075468c931

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_saddleSmallResidueTailMajorant
import Theorems.Thm_CohnElkies_tendsto_saddleSmallResidueCoefficientMajorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (K C : ℝ) :
    Tendsto (saddleSmallResidueRelativeErrorMajorant K C)
      atTop (𝓝 0) := by
  have h :=
    (tendsto_saddleSmallResidueCoefficientMajorant K C).add
      ((tendsto_saddleSmallResidueTailMajorant C).const_mul 2)
  simpa [saddleSmallResidueRelativeErrorMajorant] using! h
end CohnElkies
