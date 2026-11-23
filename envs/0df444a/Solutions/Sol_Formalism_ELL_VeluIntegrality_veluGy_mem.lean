-- Prove2me | solution 1 for Formalism.ELL.VeluIntegrality.veluGy_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:51.55831+00:00
-- url     : https://prove2.me/submissions/73bca019-a0aa-481b-8bd7-8ef9fd73ccab

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.VeluIntegrality
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.VeluIntegrality
theorem _root_.solution (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGy W x y ∈ (ball : Subring K) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  unfold veluGy
  exact sub_mem (sub_mem (mul_mem (neg_mem (ofNat_mem _ 2)) hy) (mul_mem h1 hx)) h3
end Formalism.ELL.VeluIntegrality
