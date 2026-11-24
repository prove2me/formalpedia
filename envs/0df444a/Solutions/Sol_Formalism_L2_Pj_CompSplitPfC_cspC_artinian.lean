-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfC.cspC_artinian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:14:46.877359+00:00
-- url     : https://prove2.me/submissions/57274701-c39c-46d1-a16f-7b1cc1fff151

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfC
open TensorProduct
variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]
namespace Formalism.L2.Pj.CompSplitPfC
theorem _root_.solution : IsArtinianRing (S ⊗[P] FractionRing P) := by
  haveI : Algebra.Etale (FractionRing P) (FractionRing P ⊗[P] S) := inferInstance
  haveI : Module.Finite (FractionRing P) (FractionRing P ⊗[P] S) :=
    Algebra.FormallyUnramified.finite_of_free (FractionRing P) _
  haveI : IsArtinianRing (FractionRing P ⊗[P] S) := IsArtinianRing.of_finite (FractionRing P) _
  exact Function.Surjective.isArtinianRing (f := (Algebra.TensorProduct.comm P (FractionRing P) S))
    (Algebra.TensorProduct.comm P (FractionRing P) S).surjective
end Formalism.L2.Pj.CompSplitPfC
