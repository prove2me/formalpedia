-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership04_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:49.835751+00:00
-- url     : https://prove2.me/submissions/9b656b2d-dfca-4c63-8aea-8a1f864bb945

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice04_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([2495,2503,2519,2543,2551,2559,2567,2591,2599,2607,2615,2623,2631,2639,2647,2663,2671,2679,2687,2703,2711,2719,2735,2743,2751,2759,2767,2791,2807,2815,2823,2831,2839,2847,2855,2863,2879,2887,2895,2903,2911,2919,2927,2935,2951,2959,2967,2983,2991,2999,3007,3023,3031,3039,3047,3055,3063,3071,3079,3095,3103,3111,3119,3127] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice04_20261024.map Sigma.fst = ([2495,2503,2519,2543,2551,2559,2567,2591,2599,2607,2615,2623,2631,2639,2647,2663,2671,2679,2687,2703,2711,2719,2735,2743,2751,2759,2767,2791,2807,2815,2823,2831,2839,2847,2855,2863,2879,2887,2895,2903,2911,2919,2927,2935,2951,2959,2967,2983,2991,2999,3007,3023,3031,3039,3047,3055,3063,3071,3079,3095,3103,3111,3119,3127] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
