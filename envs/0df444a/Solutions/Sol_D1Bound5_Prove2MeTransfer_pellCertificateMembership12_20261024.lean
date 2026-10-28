-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership12_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:37.624688+00:00
-- url     : https://prove2.me/submissions/c4baa8cd-c189-4aad-983b-25b36f8be008

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice12_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([7543,7559,7567,7583,7591,7599,7607,7615,7631,7639,7647,7655,7663,7671,7679,7687,7703,7711,7719,7727,7735,7743,7751,7759,7783,7799,7807,7815,7823,7831,7847,7855,7863,7871,7879,7887,7895,7903,7919,7927,7951,7959,7967,7991,7999,8007,8015,8023,8031,8039,8047,8063,8071,8079,8087,8095,8103,8111,8119,8135,8143,8151,8159,8167] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice12_20261024.map Sigma.fst = ([7543,7559,7567,7583,7591,7599,7607,7615,7631,7639,7647,7655,7663,7671,7679,7687,7703,7711,7719,7727,7735,7743,7751,7759,7783,7799,7807,7815,7823,7831,7847,7855,7863,7871,7879,7887,7895,7903,7919,7927,7951,7959,7967,7991,7999,8007,8015,8023,8031,8039,8047,8063,8071,8079,8087,8095,8103,8111,8119,8135,8143,8151,8159,8167] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
