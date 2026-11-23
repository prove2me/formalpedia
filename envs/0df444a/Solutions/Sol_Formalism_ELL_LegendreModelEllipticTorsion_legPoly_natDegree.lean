-- Prove2me | solution 1 for Formalism.ELL.LegendreModelEllipticTorsion.legPoly_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:56.106879+00:00
-- url     : https://prove2.me/submissions/356275fa-f1ce-4409-aa1f-6057063a2705

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Legendre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ELL
open Formalism.ELL.LegendreModelEllipticTorsion
open Polynomial
namespace Formalism.ELL.LegendreModelEllipticTorsion
theorem _root_.solution {K : Type*} [Field K] (h : (256 : K) ≠ 0) (j : K) :
    (legPoly j).natDegree = 6 := by
  unfold legPoly
  compute_degree!
end Formalism.ELL.LegendreModelEllipticTorsion
