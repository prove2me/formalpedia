-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCertificateMembership02_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:32.473604+00:00
-- url     : https://prove2.me/submissions/e4d5bf32-a308-497f-8738-8c21954e111d

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice02_20261024

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution (d : ℤ) (hd : d ∈ ([1255,1263,1271,1279,1295,1303,1311,1319,1327,1335,1343,1351,1367,1383,1391,1399,1407,1415,1423,1439,1447,1455,1463,1471,1479,1487,1495,1511,1527,1535,1543,1551,1559,1567,1583,1591,1599,1607,1615,1623,1631,1639,1655,1663,1671,1679,1687,1695,1703,1711,1727,1735,1743,1751,1759,1767,1783,1799,1807,1823,1831,1839,1847,1855] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : D1Bound5.Prove2MeTransfer.pellCertifiedFieldsSlice02_20261024.map Sigma.fst = ([1255,1263,1271,1279,1295,1303,1311,1319,1327,1335,1343,1351,1367,1383,1391,1399,1407,1415,1423,1439,1447,1455,1463,1471,1479,1487,1495,1511,1527,1535,1543,1551,1559,1567,1583,1591,1599,1607,1615,1623,1631,1639,1655,1663,1671,1679,1687,1695,1703,1711,1727,1735,1743,1751,1759,1767,1783,1799,1807,1823,1831,1839,1847,1855] : List ℤ) := by rfl
  rw [← he] at hd
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
  cases hr
  exact ⟨r.2⟩

end D1Bound5
end
