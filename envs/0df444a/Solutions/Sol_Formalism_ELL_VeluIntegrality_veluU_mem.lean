-- Prove2me | solution 1 for Formalism.ELL.VeluIntegrality.veluU_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:11.274244+00:00
-- url     : https://prove2.me/submissions/1a6a1f09-ac3c-495a-94e8-d09e747780f5

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluInt
import Theorems.Thm_Formalism_ELL_VeluIntegrality_veluGy_mem

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
    veluU W x y ∈ (ball : Subring K) := by
  unfold veluU
  exact pow_mem (veluGy_mem W hW hx hy) 2
end Formalism.ELL.VeluIntegrality
