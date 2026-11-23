-- Prove2me | solution 1 for Formalism.ELL.QuadraticDifferenceHypotheses.sum1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:06.694538+00:00
-- url     : https://prove2.me/submissions/1216eab3-3a41-49d1-a1c7-2d8209f4f833

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ELL Formalism.ELL.QuadraticDifferenceHypotheses
universe u
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]
namespace Formalism.ELL.QuadraticDifferenceHypotheses
theorem _root_.solution {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (b : M) :
    quadDiff ψ (∑ e ∈ s, x e) b = ∑ e ∈ s, quadDiff ψ (x e) b :=
  map_sum (AddMonoidHom.mk' (fun a => quadDiff ψ a b) (fun a a' => H.add1 a a' b)) x s
end Formalism.ELL.QuadraticDifferenceHypotheses
