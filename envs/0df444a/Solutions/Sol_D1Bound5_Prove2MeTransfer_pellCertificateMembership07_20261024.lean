-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership07_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:34.377071+00:00
-- url     : https://prove2.me/submissions/b7fdea88-2580-4cec-9478-8a00f20b917e

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice07_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([4407,4415,4423,4431,4439,4447,4463,4471,4479,4487,4495,4503,4511,4519,4535,4543,4551,4559,4567,4583,4591,4607,4615,4623,4631,4639,4647,4663,4679,4687,4695,4703,4711,4727,4735,4751,4759,4767,4783,4791,4799,4807,4823,4831,4839,4847,4855,4863,4871,4879,4895,4903,4911,4919,4927,4935,4943,4951,4967,4983,4991,4999,5007,5015] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice07_20261024.map Sigma.fst = ([4407,4415,4423,4431,4439,4447,4463,4471,4479,4487,4495,4503,4511,4519,4535,4543,4551,4559,4567,4583,4591,4607,4615,4623,4631,4639,4647,4663,4679,4687,4695,4703,4711,4727,4735,4751,4759,4767,4783,4791,4799,4807,4823,4831,4839,4847,4855,4863,4871,4879,4895,4903,4911,4919,4927,4935,4943,4951,4967,4983,4991,4999,5007,5015] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
