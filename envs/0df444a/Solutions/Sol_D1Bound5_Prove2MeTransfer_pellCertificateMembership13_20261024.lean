-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership13_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:38.144194+00:00
-- url     : https://prove2.me/submissions/6572f745-4953-4819-8648-f6206b0d1d48

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice13_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([8191,8207,8215,8223,8231,8239,8247,8255,8263,8279,8287,8295,8311,8319,8327,8335,8351,8359,8367,8383,8391,8399,8407,8423,8431,8439,8447,8455,8463,8471,8479,8495,8503,8511,8519,8527,8535,8543,8551,8567,8583,8599,8607,8615,8623,8639,8647,8655,8663,8671,8679,8687,8695,8711,8719,8727,8735,8743,8751,8759,8767,8783,8791,8799] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice13_20261024.map Sigma.fst = ([8191,8207,8215,8223,8231,8239,8247,8255,8263,8279,8287,8295,8311,8319,8327,8335,8351,8359,8367,8383,8391,8399,8407,8423,8431,8439,8447,8455,8463,8471,8479,8495,8503,8511,8519,8527,8535,8543,8551,8567,8583,8599,8607,8615,8623,8639,8647,8655,8663,8671,8679,8687,8695,8711,8719,8727,8735,8743,8751,8759,8767,8783,8791,8799] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
