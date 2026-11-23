-- Prove2me | solution 1 for Formalism.ELL.VeluIntegrality.veluV_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:25.01972+00:00
-- url     : https://prove2.me/submissions/905a8ece-62da-4ae7-a95d-0128250a8b01

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluInt
import Theorems.Thm_Formalism_ELL_VeluIntegrality_veluGx_mem
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
    veluV W x y ∈ (ball : Subring K) := by
  have gx := veluGx_mem W hW hx hy
  have gy := veluGy_mem W hW hx hy
  unfold veluV
  split_ifs
  · exact gx
  · exact sub_mem (mul_mem (ofNat_mem _ 2) gx) (mul_mem hW.1 gy)
end Formalism.ELL.VeluIntegrality
