-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership14_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:38.851652+00:00
-- url     : https://prove2.me/submissions/14916c61-36eb-416f-b3fc-82a6f697963f

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice14_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([8807,8815,8823,8831,8839,8855,8863,8871,8879,8887,8895,8903,8911,8927,8935,8943,8951,8983,8999,9007,9015,9023,9031,9039,9047,9055,9071,9079,9087,9095,9103,9111,9119,9127,9143,9151,9159,9167,9183,9191,9199,9215,9223,9231,9239,9247,9255,9263,9271,9287,9303,9311,9319,9327,9335,9343,9367,9383,9391,9399,9407,9415,9431,9439] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice14_20261024.map Sigma.fst = ([8807,8815,8823,8831,8839,8855,8863,8871,8879,8887,8895,8903,8911,8927,8935,8943,8951,8983,8999,9007,9015,9023,9031,9039,9047,9055,9071,9079,9087,9095,9103,9111,9119,9127,9143,9151,9159,9167,9183,9191,9199,9215,9223,9231,9239,9247,9255,9263,9271,9287,9303,9311,9319,9327,9335,9343,9367,9383,9391,9399,9407,9415,9431,9439] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
