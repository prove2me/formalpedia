-- Prove2me | solution 1 for Formalism.ELL.LegendreModelEllipticTorsion.norm_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:56.645959+00:00
-- url     : https://prove2.me/submissions/ec8529e1-dda6-4db4-8ed2-b36c57b59de8

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
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] {t : K} (ht : ‖t‖ ≠ 1) :
    ‖1 + t‖ = max 1 ‖t‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : K)) (y := t)
    (by rw [norm_one]; exact fun h => ht h.symm)
  simpa using this
end Formalism.ELL.LegendreModelEllipticTorsion
