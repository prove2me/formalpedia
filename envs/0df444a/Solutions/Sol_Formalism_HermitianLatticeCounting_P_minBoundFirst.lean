-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minBoundFirst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:37.422952+00:00
-- url     : https://prove2.me/submissions/66b6c483-35b6-40d3-bbc6-85b356a95f9d

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_minBoundFirst__4de30799fb86

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MinI := by
  intro k r C G T g v t Dr loss loss' JHS Jop dim hk hC hG hT hg hv ht hDr hl' hdim hJop hJHS
    heπ hloss hVF hABS hrank
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hv0 : 0 < v := by linarith
  have h1 : Real.exp 1 * Real.pi / (k * v) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have h2 : v⁻¹ ≤ 1 := by have := inv_anti₀ one_pos hv; simpa using this
  have hAV : (Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * (k - 2 - r)) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (by positivity) h1) (pow_le_one₀ (by positivity) h2)
          (by positivity) zero_le_one
      _ = 1 := one_mul 1
  exact minBoundFirst' k r C G T g v t Dr loss loss' JHS Jop dim (by omega) hC hG hT hg hv0 ht hDr
    hl' hdim hJop hJHS hAV hloss hVF hABS hrank
end Formalism.HermitianLatticeCounting.P
