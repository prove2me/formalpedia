-- Prove2me | solution 1 for Formalism.GM.DetBound.gaussR_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:20.691825+00:00
-- url     : https://prove2.me/submissions/fce42890-334a-4b5c-a90a-cff053061b45

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_gaussR_le_iff
import Theorems.Thm_Formalism_GM_DetBound_coeff_le_gaussR
import Theorems.Thm_Formalism_GM_DetBound_nnnorm_sum_mul_le

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
theorem _root_.solution (ρ : NNReal) (P Q : K[X]) : gaussR ρ (P * Q) ≤ gaussR ρ P * gaussR ρ Q := by
  rw [gaussR_le_iff]; intro k
  rw [coeff_mul]
  apply nnnorm_sum_mul_le
  intro x hx
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  rw [nnnorm_mul, ← hx, pow_add]
  calc ‖P.coeff x.1‖₊ * ‖Q.coeff x.2‖₊ * (ρ ^ x.1 * ρ ^ x.2)
      = (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by ring
    _ ≤ _ := mul_le_mul' (coeff_le_gaussR _ _ _) (coeff_le_gaussR _ _ _)
end Formalism.GM.DetBound
