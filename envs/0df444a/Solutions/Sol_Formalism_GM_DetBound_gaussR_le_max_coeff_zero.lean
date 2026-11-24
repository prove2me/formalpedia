-- Prove2me | solution 1 for Formalism.GM.DetBound.gaussR_le_max_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:24.8438+00:00
-- url     : https://prove2.me/submissions/fddc3e13-1f97-472a-8574-8b24d8e18bc6

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_gaussR_le_iff
import Theorems.Thm_Formalism_GM_DetBound_coeff_le_gaussR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DetBound
open Finset Polynomial
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.GM.DetBound
theorem _root_.solution {ρ : NNReal} (hρ : ρ ≤ 1) (P : K[X]) (hP : gaussR 1 P ≤ 1) :
    gaussR ρ P ≤ max ‖P.coeff 0‖₊ ρ := by
  rw [gaussR_le_iff]; intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have h1 : ‖P.coeff k‖₊ ≤ 1 := by simpa using (coeff_le_gaussR 1 P k).trans hP
    calc ‖P.coeff k‖₊ * ρ ^ k ≤ 1 * ρ := mul_le_mul' h1 (pow_le_of_le_one ρ.2 hρ hk.ne')
      _ = ρ := one_mul _
      _ ≤ _ := le_max_right _ _
end Formalism.GM.DetBound
