-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership15_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:39.434616+00:00
-- url     : https://prove2.me/submissions/adc4afc1-7505-4e11-9bc1-5ec98672c56c

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice15_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([9447,9455,9463,9471,9479,9487,9503,9511,9519,9527,9535,9543,9551,9591,9599,9607,9615,9623,9631,9647,9655,9663,9671,9679,9687,9695,9703,9719,9727,9735,9743,9759,9767,9791,9799,9807,9815,9823,9831,9839,9847,9863,9871,9879,9887,9895,9903,9911,9919,9935,9943,9951,9959,9967,9983,9991] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice15_20261024.map Sigma.fst = ([9447,9455,9463,9471,9479,9487,9503,9511,9519,9527,9535,9543,9551,9591,9599,9607,9615,9623,9631,9647,9655,9663,9671,9679,9687,9695,9703,9719,9727,9735,9743,9759,9767,9791,9799,9807,9815,9823,9831,9839,9847,9863,9871,9879,9887,9895,9903,9911,9919,9935,9943,9951,9959,9967,9983,9991] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
