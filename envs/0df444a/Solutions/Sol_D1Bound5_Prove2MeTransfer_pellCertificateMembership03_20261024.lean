-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership03_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:31:38.489661+00:00
-- url     : https://prove2.me/submissions/6d6468ba-6ce0-49ee-981d-d9bcd6486107

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice03_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([1871,1879,1887,1895,1903,1919,1927,1943,1951,1959,1967,1983,1991,1999,2015,2031,2039,2047,2055,2063,2071,2087,2095,2103,2111,2119,2127,2135,2143,2159,2167,2183,2191,2199,2207,2215,2231,2239,2247,2255,2263,2271,2279,2287,2311,2319,2327,2335,2343,2351,2359,2383,2391,2399,2407,2415,2423,2431,2447,2455,2463,2471,2479,2487] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice03_20261024.map Sigma.fst = ([1871,1879,1887,1895,1903,1919,1927,1943,1951,1959,1967,1983,1991,1999,2015,2031,2039,2047,2055,2063,2071,2087,2095,2103,2111,2119,2127,2135,2143,2159,2167,2183,2191,2199,2207,2215,2231,2239,2247,2255,2263,2271,2279,2287,2311,2319,2327,2335,2343,2351,2359,2383,2391,2399,2407,2415,2423,2431,2447,2455,2463,2471,2479,2487] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
