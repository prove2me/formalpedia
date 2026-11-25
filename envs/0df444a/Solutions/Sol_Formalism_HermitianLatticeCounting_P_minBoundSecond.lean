-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minBoundSecond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:41.739712+00:00
-- url     : https://prove2.me/submissions/27c5f8be-07eb-4f27-a5c7-d07f7cfd0070

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_minBoundSecond__fa09391593a9

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
theorem _root_.solution : MinII := by
  intro k r C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim hr hk hC hCk hG hT hT' hg hv ht hDr
    hl' hdim hJop hJHS hloss hsh hch hc hGeq hCT hkt hVF hABS hrank
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hv0 : 0 < v := by linarith
  have h1 : C / (k * v) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have h2 : v⁻¹ ≤ 1 := by have := inv_anti₀ one_pos hv; simpa using this
  have hAV : v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * (k - 2 - r)) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (by positivity) h2) (pow_le_one₀ (by positivity) h1)
          (by positivity) zero_le_one
      _ = 1 := one_mul 1
  exact minBoundSecond' k r C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim hr hk hC hG hT hT' hg
    hv0 ht hDr hl' hdim hJop hJHS hAV hloss hsh hch hc hGeq hCT hkt hVF hABS hrank
end Formalism.HermitianLatticeCounting.P
