-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership00_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:31.864368+00:00
-- url     : https://prove2.me/submissions/abc08293-cdf8-410c-9c20-0bbf9522e45b

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice00_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([7,15,23,31,39,47,55,71,79,87,95,103,111,119,127,143,151,159,167,183,191,199,215,223,231,239,247,255,263,271,287,295,303,311,319,327,335,359,367,383,391,399,407,415,431,439,447,455,463,471,479,487,503,511,519,527,535,543,551,559,583,591,599,607] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice00_20261024.map Sigma.fst = ([7,15,23,31,39,47,55,71,79,87,95,103,111,119,127,143,151,159,167,183,191,199,215,223,231,239,247,255,263,271,287,295,303,311,319,327,335,359,367,383,391,399,407,415,431,439,447,455,463,471,479,487,503,511,519,527,535,543,551,559,583,591,599,607] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
