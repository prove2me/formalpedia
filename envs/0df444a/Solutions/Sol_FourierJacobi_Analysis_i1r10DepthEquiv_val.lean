-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r10DepthEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:45.761833+00:00
-- url     : https://prove2.me/submissions/c99bc1e6-e4a9-4b82-9a01-8166b1c4b768

import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Definitions.Def_FourierJacobi_Analysis_I1Partition

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (p : I1R10Row × ℕ) :
    (i1r10DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
end FourierJacobi.Analysis
