-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership05_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:33.117808+00:00
-- url     : https://prove2.me/submissions/5504fa6d-f576-4299-94d9-7abdb0757393

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice05_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([3135,3143,3151,3167,3183,3191,3199,3207,3215,3223,3239,3247,3255,3263,3271,3279,3287,3295,3311,3319,3327,3335,3343,3351,3359,3367,3383,3391,3399,3407,3415,3423,3431,3439,3455,3463,3471,3487,3495,3503,3511,3527,3535,3543,3551,3559,3567,3583,3599,3607,3615,3623,3631,3639,3647,3655,3671,3679,3687,3695,3711,3719,3727,3743] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice05_20261024.map Sigma.fst = ([3135,3143,3151,3167,3183,3191,3199,3207,3215,3223,3239,3247,3255,3263,3271,3279,3287,3295,3311,3319,3327,3335,3343,3351,3359,3367,3383,3391,3399,3407,3415,3423,3431,3439,3455,3463,3471,3487,3495,3503,3511,3527,3535,3543,3551,3559,3567,3583,3599,3607,3615,3623,3631,3639,3647,3655,3671,3679,3687,3695,3711,3719,3727,3743] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
