-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership08_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:34.982056+00:00
-- url     : https://prove2.me/submissions/461dfda6-9056-417c-bacf-563f8dedf2fa

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice08_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([5023,5039,5055,5063,5071,5079,5087,5095,5111,5119,5127,5135,5143,5151,5159,5167,5183,5191,5199,5207,5215,5223,5231,5255,5263,5271,5279,5287,5295,5303,5311,5327,5335,5343,5351,5359,5367,5383,5399,5407,5423,5431,5447,5455,5471,5479,5487,5495,5503,5511,5519,5527,5543,5551,5559,5567,5583,5591,5599,5615,5623,5631,5639,5647] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice08_20261024.map Sigma.fst = ([5023,5039,5055,5063,5071,5079,5087,5095,5111,5119,5127,5135,5143,5151,5159,5167,5183,5191,5199,5207,5215,5223,5231,5255,5263,5271,5279,5287,5295,5303,5311,5327,5335,5343,5351,5359,5367,5383,5399,5407,5423,5431,5447,5455,5471,5479,5487,5495,5503,5511,5519,5527,5543,5551,5559,5567,5583,5591,5599,5615,5623,5631,5639,5647] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
