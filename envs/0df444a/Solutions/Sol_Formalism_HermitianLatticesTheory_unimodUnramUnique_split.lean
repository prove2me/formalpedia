-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:02.637512+00:00
-- url     : https://prove2.me/submissions/6e44d130-65aa-4bd7-9361-ff7b631ba2a7

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {S : Type*} [CommRing S] [HenselianLocalRing S]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (T N d r : S) (hr : r ^ 2 + T * r + N = 0)
    (hu : IsUnit (T + 2 * r)) : ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨1 + r * ((d - 1) * v), (d - 1) * v, ?_⟩
  linear_combination ((d - 1) * v) ^ 2 * hr + (d - 1) * hv
end Formalism.HermitianLatticesTheory
