-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.map_int_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:21:50.887608+00:00
-- url     : https://prove2.me/submissions/60d97d32-5c99-47be-a25a-31efe17a2f66

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_map_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (hR : RowInvUpSt) (K : Type) [Field K] [CharZero K] (z : MvPolynomial (Letter Ty r n) ℤ)
    (hz : map (Int.castRingHom ℚ) z ∈ HHa r n ℚ cc isX a) : map (Int.castRingHom K) z ∈ HHa r n K cc isX a := by
  have e : map (Int.castRingHom K) z = map (algebraMap ℚ K) (map (Int.castRingHom ℚ) z) := by
    rw [map_map, RingHom.ext_int (Int.castRingHom K) ((algebraMap ℚ K).comp (Int.castRingHom ℚ))]
  rw [e]
  exact map_mem hR K _ hz
end Formalism.L2.FormalSeriesBounds.HaP
