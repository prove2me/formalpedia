-- Prove2me | solution 1 for FD1D.DyadicMass.haarTerms_width_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:38.932432+00:00
-- url     : https://prove2.me/submissions/c5f1443d-8912-468c-a4fe-c63f1f2e9490

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_DyadicMass_haarTermsAt_width_pos

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
namespace DyadicMass
theorem _root_.solution
    {L : ℕ} (q : DyadicMass L) {t : HaarTerm} (ht : t ∈ q.haarTerms) :
    0 < t.width := by
  exact q.haarTermsAt_width_pos (by norm_num) ht
end DyadicMass
end FD1D
