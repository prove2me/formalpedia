-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership11_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:36.900122+00:00
-- url     : https://prove2.me/submissions/596dcbaa-79a8-4136-ac3e-7a95d599edef

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice11_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([6935,6943,6951,6959,6967,6983,6991,6999,7015,7023,7031,7039,7055,7063,7071,7079,7087,7095,7103,7111,7127,7135,7143,7151,7159,7167,7183,7199,7207,7215,7223,7231,7239,7247,7255,7271,7279,7287,7295,7303,7311,7319,7327,7343,7351,7359,7367,7383,7391,7415,7423,7431,7439,7447,7455,7463,7471,7487,7495,7503,7511,7519,7527,7535] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice11_20261024.map Sigma.fst = ([6935,6943,6951,6959,6967,6983,6991,6999,7015,7023,7031,7039,7055,7063,7071,7079,7087,7095,7103,7111,7127,7135,7143,7151,7159,7167,7183,7199,7207,7215,7223,7231,7239,7247,7255,7271,7279,7287,7295,7303,7311,7319,7327,7343,7351,7359,7367,7383,7391,7415,7423,7431,7439,7447,7455,7463,7471,7487,7495,7503,7511,7519,7527,7535] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
