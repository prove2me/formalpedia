-- Prove2me | solution 1 for GaussianSynthesis.dirty_center_difference_is_fresh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/c1126481-b6e1-4190-a6cb-ca1231a3be9c

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (old produced : Int) :
    (old+produced)-old = produced := by omega
end GaussianSynthesis
