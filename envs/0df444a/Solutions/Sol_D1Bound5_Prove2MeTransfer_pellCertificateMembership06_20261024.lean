-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership06_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:33.790425+00:00
-- url     : https://prove2.me/submissions/1a9bf0a7-1950-497f-aaa4-c97f13320074

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice06_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([3759,3767,3783,3791,3799,3815,3823,3831,3839,3847,3855,3863,3895,3903,3911,3919,3927,3935,3943,3959,3967,3983,3991,3999,4007,4015,4031,4039,4047,4055,4063,4071,4079,4087,4103,4111,4119,4127,4135,4143,4151,4159,4183,4191,4199,4207,4215,4223,4231,4247,4255,4271,4279,4287,4295,4303,4319,4327,4343,4351,4359,4367,4391,4399] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice06_20261024.map Sigma.fst = ([3759,3767,3783,3791,3799,3815,3823,3831,3839,3847,3855,3863,3895,3903,3911,3919,3927,3935,3943,3959,3967,3983,3991,3999,4007,4015,4031,4039,4047,4055,4063,4071,4079,4087,4103,4111,4119,4127,4135,4143,4151,4159,4183,4191,4199,4207,4215,4223,4231,4247,4255,4271,4279,4287,4295,4303,4319,4327,4343,4351,4359,4367,4391,4399] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
