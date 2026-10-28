-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership10_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:36.159788+00:00
-- url     : https://prove2.me/submissions/345b48cb-162a-436d-b439-588f64077e40

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice10_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([6295,6303,6311,6319,6335,6343,6351,6359,6367,6383,6391,6407,6415,6423,6431,6439,6447,6455,6463,6479,6487,6495,6503,6511,6519,6527,6535,6551,6559,6567,6583,6599,6607,6623,6631,6639,6663,6671,6679,6695,6703,6711,6719,6735,6743,6751,6767,6783,6791,6799,6807,6815,6823,6839,6847,6855,6863,6871,6879,6887,6895,6911,6919,6927] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice10_20261024.map Sigma.fst = ([6295,6303,6311,6319,6335,6343,6351,6359,6367,6383,6391,6407,6415,6423,6431,6439,6447,6455,6463,6479,6487,6495,6503,6511,6519,6527,6535,6551,6559,6567,6583,6599,6607,6623,6631,6639,6663,6671,6679,6695,6703,6711,6719,6735,6743,6751,6767,6783,6791,6799,6807,6815,6823,6839,6847,6855,6863,6871,6879,6887,6895,6911,6919,6927] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
