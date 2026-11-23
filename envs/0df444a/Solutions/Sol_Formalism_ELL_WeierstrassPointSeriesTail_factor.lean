-- Prove2me | solution 1 for Formalism.ELL.WeierstrassPointSeriesTail.factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:52.415119+00:00
-- url     : https://prove2.me/submissions/0eb04690-064f-4cd7-a19b-aee06a91cb43

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Theorems.Thm_Formalism_ELL_WeierstrassPointSeriesTail_wTail_dvd

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
open Formalism.ELL.WeierstrassPointSeriesTail
namespace Formalism.ELL.WeierstrassPointSeriesTail
theorem _root_.solution {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (hw : WFixed W w) : ∃ e : PowerSeries R, w = X ^ 3 * (1 + X * e) := by
  have hsplit : w = X ^ 3 + wTail W w := by
    unfold wTail
    conv_lhs => rw [hw.2]
    ring
  have d1 : (X : PowerSeries R) ^ 1 ∣ w := by
    rw [pow_one, PowerSeries.X_dvd_iff]
    exact hw.1
  have d2 : (X : PowerSeries R) ^ 2 ∣ w := by
    rw [hsplit]
    exact dvd_add (pow_dvd_pow X (by norm_num)) (wTail_dvd W w 1 le_rfl d1)
  have d3 : (X : PowerSeries R) ^ 3 ∣ w := by
    rw [hsplit]
    exact dvd_add dvd_rfl (wTail_dvd W w 2 (by norm_num) d2)
  obtain ⟨e, he⟩ := wTail_dvd W w 3 (by norm_num) d3
  exact ⟨e, by rw [hsplit, he]; ring⟩
end Formalism.ELL.WeierstrassPointSeriesTail
