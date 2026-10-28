-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership09_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:35.539886+00:00
-- url     : https://prove2.me/submissions/53944277-08c8-4d25-87b5-197f088c7632

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice09_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([5655,5663,5671,5695,5703,5711,5719,5727,5735,5743,5759,5767,5783,5791,5799,5807,5815,5839,5847,5855,5863,5871,5879,5903,5911,5919,5927,5935,5943,5951,5959,5983,5991,5999,6007,6015,6023,6031,6047,6055,6063,6071,6079,6087,6095,6103,6119,6127,6135,6143,6151,6159,6167,6191,6199,6207,6215,6231,6239,6247,6263,6271,6279,6287] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice09_20261024.map Sigma.fst = ([5655,5663,5671,5695,5703,5711,5719,5727,5735,5743,5759,5767,5783,5791,5799,5807,5815,5839,5847,5855,5863,5871,5879,5903,5911,5919,5927,5935,5943,5951,5959,5983,5991,5999,6007,6015,6023,6031,6047,6055,6063,6071,6079,6087,6095,6103,6119,6127,6135,6143,6151,6159,6167,6191,6199,6207,6215,6231,6239,6247,6263,6271,6279,6287] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
