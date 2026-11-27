-- Prove2me | solution 1 for Esgk.general_position_six_exact
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T03:03:30.201944+00:00
-- url     : https://prove2.me/submissions/cba60029-eac7-417e-8a59-793739cab6ca

import Definitions.Def_Esgk_Foundation
import Theorems.Thm_Esgk_general_position_five_exact

open EuclideanGeometry
open scoped EuclideanGeometry

namespace Esgk

set_option maxHeartbeats 0

private def xy (a b : ℝ) : Point :=
  WithLp.toLp 2 ![a, b]

@[simp] private theorem xy_zero (a b : ℝ) : xy a b 0 = a := rfl
@[simp] private theorem xy_one (a b : ℝ) : xy a b 1 = b := rfl

private theorem dist_sq_xy (a b : Point) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

private def area (o a b : Point) : ℝ :=
  (a 0 - o 0) * (b 1 - o 1) - (a 1 - o 1) * (b 0 - o 0)

private noncomputable def liftedArea (o a b c : Point) : ℝ :=
  area o a b * dist c o ^ 2 - area o a c * dist b o ^ 2
    + area o b c * dist a o ^ 2

private theorem area_zero_of_collinear {o a b : Point}
    (h : Collinear ℝ ({o, a, b} : Set Point)) : area o a b = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (p₀ := o) (by simp : o ∈ ({o,a,b} : Set Point))).mp h
  obtain ⟨s, hs⟩ := hv a (by simp)
  obtain ⟨t, ht⟩ := hv b (by simp)
  have ha (i : Fin 2) : a i = s * v i + o i := by
    simpa using congrFun (congrArg WithLp.ofLp hs) i
  have hb (i : Fin 2) : b i = t * v i + o i := by
    simpa using congrFun (congrArg WithLp.ofLp ht) i
  unfold area
  rw [ha 0, ha 1, hb 0, hb 1]
  ring

private theorem liftedArea_zero_of_dist_eq {o a b c center : Point} (radius : ℝ)
    (ho : dist o center = radius) (ha : dist a center = radius)
    (hb : dist b center = radius) (hc : dist c center = radius) :
    liftedArea o a b c = 0 := by
  have same (p : Point) (h : dist p center = radius) :
      dist p o ^ 2 = 2 * ((p 0 - o 0) * (center 0 - o 0) + (p 1 - o 1) * (center 1 - o 1)) := by
    have eq : dist p center ^ 2 = dist o center ^ 2 := by rw [h, ho]
    rw [dist_sq_xy, dist_sq_xy] at eq
    rw [dist_sq_xy]
    linarith only [eq]
  unfold liftedArea
  rw [same a ha, same b hb, same c hc]
  unfold area
  ring


private theorem image_contains {n : ℕ} (p : Config n) (i : Fin n) :
    p i ∈ Config.toFinset p := by
  classical
  simp [Config.toFinset, Finset.mem_image]

private theorem gp_of_area {n : ℕ} (p : Config n) (hp : Function.Injective p)
    (htri : ∀ i j k : Fin n, i < j → j < k → area (p i) (p j) (p k) ≠ 0)
    (hquad : ∀ i j k l : Fin n, i < j → j < k → k < l →
      liftedArea (p i) (p j) (p k) (p l) ≠ 0) :
    InGeneralPosition (p.toFinset) := by
  classical
  constructor
  · intro o ho a ha b hb hoa hab hob hcol
    have preimage (q : Point) (hq : q ∈ (p.toFinset : Set Point)) :
        ∃ i, p i = q := by simpa [Config.toFinset, Finset.mem_image] using hq
    obtain ⟨i, rfl⟩ := preimage o ho
    obtain ⟨j, rfl⟩ := preimage a ha
    obtain ⟨k, rfl⟩ := preimage b hb
    let T : Finset (Fin n) := {i,j,k}
    have hcard : T.card = 3 := by
      refine Finset.card_eq_three.mpr ⟨i,j,k,?_,?_,?_,rfl⟩
      all_goals solve | exact fun h => hoa (congrArg p h) | exact fun h => hob (congrArg p h) | exact fun h => hab (congrArg p h)
    let e := T.orderEmbOfFin hcard
    have point_mem (u : Fin 3) : p (e u) ∈ ({p i,p j,p k} : Set Point) := by
      have hu : e u ∈ T := T.orderEmbOfFin_mem hcard u
      simp [T] at hu
      rcases hu with h | h | h <;> simp [h]
    apply htri (e 0) (e 1) (e 2) (e.strictMono (by decide)) (e.strictMono (by decide))
    refine area_zero_of_collinear (hcol.subset ?_)
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact point_mem 0
    · exact point_mem 1
    · exact point_mem 2
  · intro T hT hc hcos
    let U := Finset.univ.filter (fun i : Fin n ↦ p i ∈ T)
    have hmem (i : Fin n) : i ∈ U ↔ p i ∈ T := by simp [U]
    have him : U.image p = T := by
      ext q
      constructor
      · intro hq
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
        exact (hmem i).mp hi
      · intro hq
        have hq' : q ∈ p.toFinset := hT hq
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq'
        exact Finset.mem_image.mpr ⟨i,(hmem i).mpr hq,rfl⟩
    have hcU : U.card = 4 := by
      rw [← Finset.card_image_of_injective U hp, him, hc]
    let e := U.orderEmbOfFin hcU
    obtain ⟨center, radius, hd⟩ := hcos
    have at_radius (u : Fin 4) : dist (p (e u)) center = radius :=
      hd _ ((hmem (e u)).mp (U.orderEmbOfFin_mem hcU u))
    exact hquad (e 0) (e 1) (e 2) (e 3) (e.strictMono (by decide))
      (e.strictMono (by decide)) (e.strictMono (by decide))
      (liftedArea_zero_of_dist_eq radius (at_radius 0) (at_radius 1) (at_radius 2) (at_radius 3))


set_option maxRecDepth 16384
set_option linter.unusedVariables false

private def squaredGram (d : Fin 5 → Fin 5 → ℝ) (o i j : Fin 5) : ℝ :=
  d o i + d o j - d i j

private def trianglePolynomial (a b c : ℝ) : ℝ := 4 * a * b - (a + b - c)^2

private def circlePolynomial (a b c d e f : ℝ) : ℝ :=
  (a*f)^2 + (b*e)^2 + (c*d)^2 - 2*(a*f*b*e + b*e*c*d + c*d*a*f)

private structure StandardDistanceData (d : Fin 5 → Fin 5 → ℝ) : Prop where
  gram : ∀ o i j k l,
    (squaredGram d o i i * squaredGram d o j j - (squaredGram d o i j)^2) *
      squaredGram d o k l -
    squaredGram d o j j * squaredGram d o i k * squaredGram d o i l +
    squaredGram d o i j * (squaredGram d o j k * squaredGram d o i l +
      squaredGram d o i k * squaredGram d o j l) -
    squaredGram d o i i * squaredGram d o j k * squaredGram d o j l = 0
  triangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    trianglePolynomial (d i j) (d i k) (d j k) ≠ 0
  circle : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    circlePolynomial (d i j) (d i k) (d i l) (d j k) (d j l) (d k l) ≠ 0

private def edgeIndex (i j : Fin 5) : Fin 10 :=
  ![![0,0,1,2,3], ![0,0,4,5,6], ![1,4,0,7,8], ![2,5,7,0,9], ![3,6,8,9,0]] i j

private def fromColor (c : Fin 10 → Bool) (s a : ℝ) (i j : Fin 5) : ℝ :=
  if i = j then 0 else if c (edgeIndex i j) then a else s


private def twoPatterns : Fin 34 → Fin 10 → Bool := ![
  ![false, false, false, false, false, false, false, false, false, false],
  ![false, false, false, false, false, false, false, false, false, true],
  ![false, false, false, false, false, false, false, false, true, true],
  ![false, false, false, false, false, false, false, true, true, true],
  ![false, false, false, false, false, false, true, false, true, true],
  ![false, false, false, false, false, false, true, true, false, false],
  ![false, false, false, false, false, false, true, true, false, true],
  ![false, false, false, false, false, false, true, true, true, true],
  ![false, false, false, false, false, true, true, true, true, false],
  ![false, false, false, false, false, true, true, true, true, true],
  ![false, false, false, false, true, true, true, true, true, true],
  ![false, false, false, true, false, false, true, false, true, true],
  ![false, false, false, true, false, false, true, true, false, false],
  ![false, false, false, true, false, false, true, true, false, true],
  ![false, false, false, true, false, false, true, true, true, true],
  ![false, false, false, true, false, true, false, true, true, false],
  ![false, false, false, true, false, true, false, true, true, true],
  ![false, false, false, true, false, true, true, true, true, false],
  ![false, false, false, true, false, true, true, true, true, true],
  ![false, false, false, true, true, true, false, true, false, false],
  ![false, false, false, true, true, true, false, true, false, true],
  ![false, false, false, true, true, true, false, true, true, true],
  ![false, false, false, true, true, true, true, true, true, true],
  ![false, false, true, true, false, true, true, true, true, false],
  ![false, false, true, true, false, true, true, true, true, true],
  ![false, false, true, true, true, false, true, false, true, true],
  ![false, false, true, true, true, false, true, true, false, false],
  ![false, false, true, true, true, false, true, true, false, true],
  ![false, false, true, true, true, false, true, true, true, true],
  ![false, false, true, true, true, true, true, true, true, false],
  ![false, false, true, true, true, true, true, true, true, true],
  ![false, true, true, true, true, true, true, false, true, true],
  ![false, true, true, true, true, true, true, true, true, true],
  ![true, true, true, true, true, true, true, true, true, true]]


private def permutationCodes : Array Nat := #[2930, 2430, 2830, 1830, 2230, 1730, 2910, 2410, 2710, 1210, 2110, 1110, 2790, 1790, 2690, 1190, 1490, 990, 2170, 1670, 2070, 1070, 1470, 970, 2926, 2426, 2826, 1826, 2226, 1726, 2886, 2386, 2586, 586, 1986, 486, 2766, 1766, 2566, 566, 1366, 366, 2146, 1646, 1946, 446, 1346, 346, 2902, 2402, 2702, 1202, 2102, 1102, 2882, 2382, 2582, 582, 1982, 482, 2642, 1142, 2542, 542, 742, 242, 2022, 1022, 1922, 422, 722, 222, 2778, 1778, 2678, 1178, 1478, 978, 2758, 1758, 2558, 558, 1358, 358, 2638, 1138, 2538, 538, 738, 238, 1398, 898, 1298, 298, 698, 198, 2154, 1654, 2054, 1054, 1454, 954, 2134, 1634, 1934, 434, 1334, 334, 2014, 1014, 1914, 414, 714, 214, 1394, 894, 1294, 294, 694, 194]

private def caseWitnesses : Array (Array Nat) := #[
  #[0, 184, 160, 333, 154, 309, 285, 585, 152, 303, 279, 561, 273, 537, 513, 1353, 136, 331, 330, 450, 696, 832, 826, 957, 672, 808, 802, 933, 1533, 1655, 1653, 1773],
  #[130, 307, 697, 833, 306, 426, 824, 951, 648, 784, 1509, 1631, 778, 909, 1629, 1749, 261, 579, 820, 955, 818, 949, 1056, 1192, 1501, 1624, 1894, 2014, 1870, 1990, 2153, 2273],
  #[128, 301, 673, 809, 649, 785, 1503, 1625, 300, 420, 800, 927, 776, 903, 1623, 1743, 255, 555, 796, 931, 1507, 1630, 1895, 2015, 794, 925, 1032, 1168, 1864, 1984, 2129, 2249],
  #[249, 531, 1531, 1654, 772, 907, 1871, 1991, 770, 901, 1865, 1985, 1008, 1144, 2105, 2225, 489, 1329, 1651, 1771, 1627, 1747, 2152, 2272, 1621, 1741, 2128, 2248, 2104, 2224, 2824, 2944],
  #[124, 699, 283, 827, 282, 825, 402, 945, 624, 1485, 760, 1607, 754, 1605, 885, 1725, 259, 821, 577, 954, 816, 1058, 943, 1186, 1477, 1892, 1600, 2012, 1846, 2147, 1966, 2267],
  #[258, 819, 817, 1060, 576, 948, 942, 1184, 1471, 1868, 1844, 2145, 1594, 1988, 1964, 2265, 378, 939, 937, 1180, 936, 1178, 1176, 1296, 2280, 2513, 2507, 2637, 2505, 2631, 2625, 2745],
  #[600, 1461, 1453, 1890, 1447, 1866, 2304, 2512, 1440, 2329, 1836, 2482, 1830, 2458, 2432, 3033, 736, 1583, 1576, 2010, 1820, 2139, 2501, 2635, 1812, 2476, 2113, 2610, 3120, 3352, 3322, 3453],
  #[730, 1581, 1822, 2141, 1570, 1986, 2499, 2629, 1806, 2452, 3122, 3353, 2089, 2586, 3298, 3429, 861, 1701, 1942, 2261, 1940, 2259, 2619, 2739, 2408, 3009, 3316, 3451, 3292, 3427, 3592, 3712],
  #[122, 675, 277, 803, 625, 1479, 761, 1601, 276, 801, 396, 921, 752, 1599, 879, 1719, 253, 797, 553, 930, 1483, 1893, 1606, 2013, 792, 1034, 919, 1162, 1840, 2123, 1960, 2243],
  #[601, 1455, 1459, 1891, 1441, 2328, 1842, 2506, 1446, 1860, 2305, 2488, 1831, 2456, 2434, 3035, 737, 1577, 1582, 2011, 1818, 2500, 2137, 2634, 1814, 2115, 2477, 2611, 3121, 3328, 3346, 3455],
  #[252, 795, 793, 1036, 1470, 1862, 1838, 2121, 552, 924, 918, 1160, 1592, 1982, 1958, 2241, 372, 915, 913, 1156, 2281, 2489, 2483, 2613, 912, 1154, 1152, 1272, 2481, 2607, 2601, 2721],
  #[728, 1575, 1816, 2117, 1807, 2450, 3124, 3329, 1568, 1980, 2475, 2605, 2088, 2580, 3296, 3423, 855, 1695, 1936, 2237, 2410, 3011, 3340, 3454, 1934, 2235, 2595, 2715, 3290, 3421, 3568, 3688],
  #[243, 1530, 507, 1652, 748, 1847, 883, 1967, 746, 1841, 877, 1961, 984, 2081, 1120, 2201, 483, 1650, 1323, 1770, 1603, 2146, 1723, 2266, 1597, 2122, 1717, 2242, 2080, 2800, 2200, 2920],
  #[724, 1823, 1579, 2140, 1564, 2497, 1962, 2623, 1800, 3128, 2428, 3347, 2065, 3274, 2562, 3405, 859, 1943, 1699, 2260, 1938, 2617, 2257, 2737, 2402, 3317, 3003, 3450, 3268, 3586, 3403, 3706],
  #[722, 1817, 1573, 2116, 1801, 3130, 2426, 3323, 1562, 2473, 1956, 2599, 2064, 3272, 2556, 3399, 853, 1937, 1693, 2236, 2404, 3341, 3005, 3452, 1932, 2593, 2233, 2713, 3266, 3562, 3397, 3682],
  #[960, 2057, 2056, 2776, 2041, 3250, 3244, 3580, 2040, 3248, 3242, 3556, 2760, 3528, 3504, 3753, 1096, 2177, 2176, 2896, 2538, 3381, 3379, 3700, 2532, 3375, 3373, 3676, 3480, 3729, 3723, 3930],
  #[120, 651, 627, 1473, 271, 779, 755, 1595, 270, 777, 753, 1593, 390, 897, 873, 1713, 603, 1449, 1443, 2352, 1458, 1867, 1843, 2504, 1452, 1861, 1837, 2480, 2307, 2464, 2440, 3041],
  #[247, 773, 1482, 1869, 529, 906, 1604, 1989, 768, 1010, 1834, 2099, 895, 1138, 1954, 2219, 731, 1571, 1819, 2498, 1580, 1987, 2136, 2628, 1808, 2091, 3123, 3304, 2453, 2587, 3344, 3431],
  #[246, 771, 1476, 1863, 769, 1012, 1832, 2097, 528, 900, 1598, 1983, 894, 1136, 1952, 2217, 729, 1569, 1813, 2474, 1810, 2093, 3125, 3305, 1574, 1981, 2112, 2604, 2451, 2581, 3320, 3425],
  #[366, 891, 2283, 2465, 889, 1132, 2459, 2589, 888, 1130, 2457, 2583, 1128, 1248, 2577, 2697, 849, 1689, 2416, 3017, 1930, 2213, 3338, 3430, 1928, 2211, 3314, 3424, 2571, 2691, 3544, 3664],
  #[241, 1506, 749, 1845, 505, 1628, 882, 1965, 744, 1835, 986, 2075, 871, 1955, 1114, 2195, 725, 1821, 1565, 2496, 1578, 2138, 1963, 2622, 1802, 3129, 2067, 3280, 2429, 3345, 2563, 3407],
  #[481, 1626, 1602, 2144, 1321, 1746, 1722, 2264, 1591, 2098, 2074, 2794, 1711, 2218, 2194, 2914, 858, 1941, 1939, 2616, 1698, 2258, 2256, 2736, 2400, 3293, 3269, 3584, 3001, 3426, 3402, 3704],
  #[720, 1811, 1803, 3136, 1567, 2092, 2424, 3299, 1560, 2449, 2066, 3273, 1950, 2575, 2550, 3393, 962, 2051, 2043, 3256, 2050, 2770, 3245, 3578, 2042, 3249, 2762, 3552, 3240, 3532, 3506, 3759],
  #[847, 1931, 2405, 3339, 1687, 2212, 3004, 3428, 1926, 2569, 3264, 3538, 2209, 2689, 3391, 3658, 1090, 2171, 2539, 3383, 2170, 2890, 3378, 3698, 2526, 3369, 3482, 3735, 3367, 3652, 3721, 3906],
  #[240, 1500, 747, 1839, 745, 1833, 988, 2073, 504, 1622, 876, 1959, 870, 1953, 1112, 2193, 723, 1815, 1563, 2472, 1804, 3131, 2069, 3281, 1572, 2114, 1957, 2598, 2427, 3321, 2557, 3401],
  #[721, 1809, 1805, 3137, 1561, 2448, 2068, 3275, 1566, 2090, 2425, 3297, 1951, 2574, 2551, 3395, 964, 2049, 2045, 3257, 2044, 3251, 2764, 3576, 2048, 2768, 3243, 3554, 3241, 3530, 3508, 3765],
  #[480, 1620, 1596, 2120, 1590, 2096, 2072, 2792, 1320, 1740, 1716, 2240, 1710, 2216, 2192, 2912, 852, 1935, 1933, 2592, 2401, 3291, 3267, 3560, 1692, 2234, 2232, 2712, 3000, 3420, 3396, 3680],
  #[846, 1929, 2403, 3315, 1927, 2568, 3265, 3536, 1686, 2210, 3002, 3422, 2208, 2688, 3390, 3656, 1088, 2169, 2533, 3377, 2527, 3371, 3484, 3741, 2168, 2888, 3372, 3674, 3366, 3650, 3720, 3900],
  #[360, 2289, 867, 2441, 865, 2435, 1108, 2565, 864, 2433, 1106, 2559, 1104, 2553, 1224, 2673, 843, 2417, 1683, 3016, 1924, 3336, 2189, 3406, 1922, 3312, 2187, 3400, 2547, 3520, 2667, 3640],
  #[841, 2411, 1925, 3337, 1681, 3010, 2188, 3404, 1920, 3288, 2545, 3514, 2185, 3394, 2665, 3634, 1084, 2541, 2165, 3382, 2164, 3380, 2884, 3696, 2520, 3488, 3363, 3733, 3361, 3727, 3628, 3882],
  #[840, 2409, 1923, 3313, 1921, 3289, 2544, 3512, 1680, 3008, 2186, 3398, 2184, 3392, 2664, 3632, 1082, 2535, 2163, 3376, 2521, 3490, 3365, 3739, 2162, 3374, 2882, 3672, 3360, 3726, 3626, 3876],
  #[1080, 2529, 2523, 3496, 2161, 3370, 3364, 3738, 2160, 3368, 3362, 3732, 2880, 3648, 3624, 3870, 1200, 2649, 2643, 3616, 2641, 3610, 3604, 3858, 2640, 3608, 3602, 3852, 3600, 3846, 3840, 3960]]

private def decode (m : Nat) (i : Fin 10) : Bool := m.testBit i

private def packBits (c : Fin 10 → Bool) : List (Fin 10) → Nat
  | [] => 0
  | k :: ks => 2 * packBits c ks + if c k then 1 else 0

private theorem packBits_lt (c : Fin 10 → Bool) (ks : List (Fin 10)) :
    packBits c ks < 2^ks.length := by
  induction ks with
  | nil => simp [packBits]
  | cons k ks ih =>
    simp only [packBits, List.length_cons, pow_succ]
    split <;> omega

private theorem packBits_bit (c : Fin 10 → Bool) (ks : List (Fin 10))
    (j : Nat) (hj : j < ks.length) : (packBits c ks).testBit j = c (ks[j]'hj) := by
  induction ks generalizing j with
  | nil => simp at hj
  | cons k ks ih =>
    cases j with
    | zero =>
      cases h : c k <;> simp [packBits, h, Nat.testBit_eq_decide_div_mod_eq]
    | succ j =>
      rw [Nat.testBit_succ, packBits]
      have hd : (2 * packBits c ks + (if c k then 1 else 0))/2 = packBits c ks := by
        split <;> omega
      rw [hd]
      exact ih j (by simpa using hj)

private def encode (c : Fin 10 → Bool) : Fin 1024 :=
  ⟨packBits c (List.finRange 10), by simpa using packBits_lt c (List.finRange 10)⟩

private theorem encode_correct (c : Fin 10 → Bool) (i : Fin 10) : decode (encode c) i = c i := by
  simpa [decode,encode] using packBits_bit c (List.finRange 10) i
    (by simpa using i.isLt)

private def packed (m : Fin 1024) : Nat :=
  (caseWitnesses.getD (m.val / 32) #[]).getD (m.val % 32) 0

private def caseId (m : Fin 1024) : Fin 34 :=
  ⟨packed m / 120 % 34, Nat.mod_lt _ (by decide)⟩

private def permutationValue (k : Fin 120) (i : Fin 5) : Fin 5 :=
  ⟨permutationCodes.getD k 0 / (5^(i : Nat)) % 5, Nat.mod_lt _ (by decide)⟩

private def renumber (m : Fin 1024) (i : Fin 5) : Fin 5 :=
  permutationValue ⟨packed m % 120,Nat.mod_lt _ (by decide)⟩ i

private def edgePair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

private theorem edgePair_eq : ∀ i j : Fin 5, i ≠ j →
    edgePair (edgeIndex i j) = (i,j) ∨ edgePair (edgeIndex i j) = (j,i) := by decide

private theorem edge_symm : ∀ i j : Fin 5, edgeIndex i j = edgeIndex j i := by decide

private theorem permutationValuesInjective : ∀ (k : Fin 120) (i j : Fin 5),
    permutationValue k i = permutationValue k j → i = j := by
  decide +kernel

private theorem correctLabels : ∀ (m : Fin 1024) (k : Fin 10),
    decode m (edgeIndex (renumber m (edgePair k).1) (renumber m (edgePair k).2))
      = twoPatterns (caseId m) k := by
  decide +kernel

private theorem coloring_coverage (m : Fin 1024) :
    (∀ i j : Fin 5, renumber m i = renumber m j → i = j) ∧
    (∀ i j : Fin 5, i ≠ j →
      decode m (edgeIndex (renumber m i) (renumber m j)) = twoPatterns (caseId m) (edgeIndex i j)) := by
  refine ⟨permutationValuesInjective _,?_⟩
  intro i j hij
  have h := correctLabels m (edgeIndex i j)
  rcases edgePair_eq i j hij with hpair | hpair
  · simpa only [hpair] using h
  · simpa only [hpair,edge_symm (renumber m j) (renumber m i)] using h


private theorem collinear_of_area_zero {o a b : Point} (hoa : a ≠ o)
    (h : area o a b = 0) : Collinear ℝ ({o,a,b} : Set Point) := by
  have param : ∃ s : ℝ, b 0 = s*(a 0-o 0)+o 0 ∧ b 1 = s*(a 1-o 1)+o 1 := by
    unfold area at h
    by_cases hx : a 0 = o 0
    · have hy : a 1 ≠ o 1 := by
        intro h'
        apply hoa
        ext i
        fin_cases i
        · exact hx
        · exact h'
      have he : b 0 = o 0 := by
        have hv : (a 1-o 1)*(b 0-o 0) = 0 := by simpa [hx] using h
        exact sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_left (sub_ne_zero.mpr hy))
      refine ⟨(b 1-o 1)/(a 1-o 1), ?_, ?_⟩
      · simp [hx, he]
      · field_simp [sub_ne_zero.mpr hy]
        ring
    · refine ⟨(b 0-o 0)/(a 0-o 0), ?_, ?_⟩
      · field_simp [sub_ne_zero.mpr hx]
        ring
      · field_simp [sub_ne_zero.mpr hx]
        linear_combination h
  obtain ⟨r,hx,hy⟩ := param
  apply (collinear_iff_of_mem (p₀ := o) (by simp : o ∈ ({o,a,b} : Set Point))).mpr
  refine ⟨a-o, ?_⟩
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨r, ?_⟩
    ext i
    fin_cases i
    · exact hx
    · exact hy

private theorem center_of_liftedArea_zero {o a b c : Point}
    (hn : area o a b ≠ 0) (hc : liftedArea o a b c = 0) :
    ∃ z : Point, (∀ p ∈ ({o,a,b,c} : Set Point), dist p z = dist o z) := by
  let A := area o a b
  let xx := (dist a o ^ 2 * (b 1 - o 1) - dist b o ^ 2 * (a 1 - o 1)) / (2*A)
  let yy := ((a 0 - o 0) * dist b o ^ 2 - (b 0 - o 0) * dist a o ^ 2) / (2*A)
  let z := xy (o 0 + xx) (o 1 + yy)
  have hz (p : Point) (hp : dist p o ^ 2 = 2*((p 0-o 0)*xx + (p 1-o 1)*yy)) :
      dist p z = dist o z := by
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [dist_sq_xy, dist_sq_xy]
    simp only [z, xy_zero, xy_one]
    rw [dist_sq_xy] at hp
    linear_combination hp
  have hclaim (p : Point) (hp : liftedArea o a b p = 0) :
      dist p o ^ 2 = 2*((p 0-o 0)*xx + (p 1-o 1)*yy) := by
    dsimp [xx,yy]
    have hA : A ≠ 0 := hn
    field_simp [hA]
    dsimp [A]
    unfold liftedArea area at hp
    unfold area
    linear_combination hp
  refine ⟨z, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h | h | h | h
  · rw [h]
  · rw [h]
    apply hz; apply hclaim
    unfold liftedArea area
    ring
  · rw [h]
    apply hz; apply hclaim
    unfold liftedArea area
    ring
  · rw [h]
    exact hz c (hclaim c hc)

private theorem triangle_formula (o a b : Point) :
    trianglePolynomial (dist o a ^ 2) (dist o b ^ 2) (dist a b ^ 2) =
      4 * area o a b ^ 2 := by
  simp only [trianglePolynomial, area, dist_sq_xy]
  ring

private theorem circle_formula (o a b c : Point) :
    circlePolynomial (dist o a ^ 2) (dist o b ^ 2) (dist o c ^ 2)
      (dist a b ^ 2) (dist a c ^ 2) (dist b c ^ 2) =
      -4 * liftedArea o a b c ^ 2 := by
  simp only [circlePolynomial, liftedArea, area, dist_sq_xy]
  ring

private theorem data_of_points (p : Config 5) (hi : Function.Injective p)
    (hgp : InGeneralPosition p.toFinset) (d0 : ℝ) (hd0 : d0 ≠ 0) :
    StandardDistanceData (fun i j => dist (p i) (p j) ^ 2 / d0) := by
  classical
  let d := fun i j => dist (p i) (p j) ^ 2
  let d' : Fin 5 → Fin 5 → ℝ := fun i j => d i j / d0
  change StandardDistanceData d'
  have hc (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      area (p i) (p j) (p k) ≠ 0 := by
    intro h
    exact hgp.1 (image_contains p i) (image_contains p j) (image_contains p k)
      (fun h => hij (hi h)) (fun h => hjk (hi h)) (fun h => hik (hi h))
      (collinear_of_area_zero (fun h => hij (hi h.symm)) h)
  have gscale (o i j : Fin 5) :
      squaredGram d' o i j = squaredGram d o i j / d0 := by
    unfold squaredGram d' 
    ring
  have gdot (o i j : Fin 5) :
      squaredGram d o i j = 2 * ((p i 0 - p o 0)*(p j 0 - p o 0) +
        (p i 1 - p o 1)*(p j 1 - p o 1)) := by
    simp only [squaredGram, d, dist_sq_xy]
    ring
  constructor
  · intro o i j k l
    simp only [gscale, gdot, div_eq_mul_inv]
    ring
  · intro i j k hij hik hjk hz
    unfold trianglePolynomial d' d at hz
    field_simp [hd0] at hz
    have hz' : trianglePolynomial (dist (p i) (p j)^2)
        (dist (p i) (p k)^2) (dist (p j) (p k)^2) = 0 := by
      unfold trianglePolynomial
      linear_combination hz
    rw [triangle_formula] at hz'
    exact hc i j k hij hik hjk (by nlinarith only [hz'])
  · intro i j k l hij hik hil hjk hjl hkl hz
    unfold circlePolynomial d' d at hz
    field_simp [hd0] at hz
    have hz' : circlePolynomial (dist (p i) (p j)^2)
        (dist (p i) (p k)^2) (dist (p i) (p l)^2)
        (dist (p j) (p k)^2) (dist (p j) (p l)^2) (dist (p k) (p l)^2) = 0 := by
      unfold circlePolynomial
      linear_combination hz
    rw [circle_formula] at hz'
    have hlift : liftedArea (p i) (p j) (p k) (p l) = 0 := by
      nlinarith only [hz']
    obtain ⟨z, hz⟩ := center_of_liftedArea_zero (hc i j k hij hik hjk) hlift
    have hne (a b : Fin 5) (hab : a ≠ b) : p a ≠ p b := fun h => hab (hi h)
    let U : Finset Point := {p i,p j,p k,p l}
    have hU : U ⊆ p.toFinset := by
      intro y hy
      simp [U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> exact image_contains p _
    have hcard : U.card = 4 :=
      Finset.card_eq_four.mpr ⟨_,_,_,_,hne _ _ hij,hne _ _ hik,hne _ _ hil,
        hne _ _ hjk,hne _ _ hjl,hne _ _ hkl,rfl⟩
    apply hgp.2 U hU hcard
    refine ⟨z,dist (p i) z,?_⟩
    intro y hy
    exact hz y (by simpa [U] using hy)


private def readThree (code : Nat) (i : Fin 10) : Fin 3 :=
  ⟨code/(3^(i : Nat))%3, Nat.mod_lt _ (by decide)⟩

private def fromThree (c : Fin 10 → Fin 3) (a b : ℝ) (i j : Fin 5) : ℝ :=
  if i = j then 0 else if c (edgeIndex i j) = 0 then 1 else
    if c (edgeIndex i j) = 1 then a else b


private def threeCodeRows : Array (Array Nat) := #[#[48114, 46656, 42282, 48843, 55404, 24786, 31347, 51030, 29889, 49572, 32076, 49086, 16281, 35964, 55647, 18468, 38151, 57834, 36693, 56376, 12636, 32319, 52002, 38880, 55728, 57915, 56457, 32400, 52083, 58644, 39204, 46683], #[53244, 42309, 48870, 55431, 5130, 24813, 44496, 31374, 51057, 57618, 3672, 23355, 43038, 29916, 49599, 56160, 25542, 32103, 51786, 48384, 15579, 35262, 54945, 17766, 37449, 57132, 16308, 55674, 5373, 25056, 44739, 11934], #[51300, 18495, 38178, 57861, 17037, 36720, 56403, 6102, 25785, 45468, 12663, 32346, 52029, 19224, 38907, 58590, 24570, 11448, 31131, 50814, 37692, 12177, 31860, 51543, 18738, 38421, 58104, 39150, 41904, 55026, 4725, 24408], #[44091, 50652, 57213, 49194, 5454, 44820, 31698, 57942, 56484, 6183, 25866, 45549, 52110, 58671, 4968, 24651, 44334, 11529, 31212, 50895, 18090, 37773, 57456, 12258, 51624, 18819, 38502, 58185, 19548, 39231, 58914, 24732], #[31293, 50976, 32022, 51705, 58266, 29943, 49626, 32130, 9774, 49140, 16335, 36018, 55701, 5400, 25083, 44766, 11961, 31644, 51327, 18522, 38205, 57888, 17064, 36747, 56430, 25812, 12690, 32373, 52056, 38934, 12204, 31887], #[51570, 38448, 2565, 22248, 41931, 48492, 55053, 4752, 24435, 44118, 30996, 50679, 57240, 29538, 55782, 5481, 25164, 44847, 51408, 57969, 56511, 6210, 25893, 45576, 32454, 52137, 58698, 24678, 11556, 31239, 50922, 37800], #[12285, 31968, 51651, 18846, 38529, 58212, 39258, 31320, 32049, 51732, 49122, 36000, 18504, 57870, 17046, 56412, 12672, 52038, 19233, 38916, 58599, 19476, 39159, 58842, 53334, 48960, 5220, 44586, 31464, 57708, 34380, 54063], #[30006, 16884, 56250, 5949, 25632, 45315, 12510, 51876, 19071, 38754, 58437, 49203, 16398, 36081, 55764, 38268, 36810, 32436, 19314, 58680, 19557, 39240, 58923, 46854, 33732, 53415, 42480, 29358, 55602, 5301, 24984, 44667], #[11862, 51228, 18423, 38106, 57789, 34461, 54144, 10404, 49770, 16965, 36648, 56331, 6030, 25713, 45396, 12591, 32274, 51957, 19152, 38835, 58518, 9918, 29601, 49284, 36162, 18666, 58032, 17208, 56574, 12834, 52200, 19395], #[39078, 58761, 19638, 39321, 59004, 17073, 36756, 56439, 12699, 32382, 52065, 19260, 38943, 58626, 18774, 38457, 58140, 39186, 54090, 49716, 56277, 5976, 25659, 45342, 32220, 51903, 58464, 9864, 29547, 49230, 36108, 5490], #[44856, 31734, 18612, 57978, 17154, 56520, 6219, 25902, 45585, 12780, 52146, 19341, 39024, 58707, 24687, 44370, 11565, 31248, 50931, 18126, 37809, 57492, 12294, 51660, 18855, 38538, 58221, 19584, 39267, 58950, 23553, 43236], #[30114, 49797, 36675, 56358, 25740, 12618, 32301, 51984, 38862, 22338, 42021, 48582, 35460, 55143, 44208, 50769, 57330, 29628, 16506, 55872, 5571, 25254, 44937, 12132, 51498, 18693, 38376, 58059, 17235, 36918, 56601, 6300], #[25983, 45666, 12861, 32544, 52227, 19422, 39105, 58788, 24768, 11646, 31329, 51012, 37890, 12375, 32058, 51741, 18936, 38619, 58302, 39348, 29556, 16434, 55800, 18621, 38304, 57987, 17163, 36846, 56529, 12789, 32472, 52155], #[19350, 39033, 58716, 39276, 30123, 49806, 32310, 9954, 49320, 16515, 36198, 55881, 18702, 38385, 58068, 17244, 36927, 56610, 12870, 32553, 52236, 39114, 47019, 53580, 49206, 55767, 57954, 47748, 23691, 43374, 30252, 49935], #[56496, 25878, 32439, 52122, 54552, 10812, 30495, 50178, 37056, 19560, 58926, 48072, 54633, 30576, 56820, 59007, 54336, 30279, 49962, 45588, 32466, 58710, 53850, 10110, 29793, 49476, 36354, 18858, 58224, 54579, 30522, 17400], #[56766, 26148, 45831, 13026, 52392, 19587, 39270, 58953, 53931, 42996, 29874, 56118, 25500, 45183, 51744, 58305, 54660, 43725, 50286, 56847, 26229, 45912, 32790, 52473, 59034, 10848, 50214, 17409, 37092, 56775, 19596, 39279], #[58962, 54426, 50052, 56613, 25995, 45678, 32556, 52239, 58800, 30612, 50295, 17490, 37173, 56856, 39360, 30615, 50298]]

private def threeChoiceRows : Array (Array (Array Nat)) := #[
  #[],
  #[],
  #[#[0, 4380, 636, 9800, 630, 9776, 1842, 18033, 152, 4622, 878, 10040, 872, 10016, 2313, 18273], #[612, 9794, 9672, 15312, 16938, 32256, 17683, 32983, 5832, 10644, 10158, 15560, 22600, 42201, 22840, 42681], #[606, 9770, 16939, 32257, 9648, 15288, 17682, 32982, 5808, 10620, 22594, 42177, 10134, 15536, 22834, 42657], #[1818, 18009, 17659, 32977, 17658, 32976, 25656, 34896, 18968, 35941, 46045, 46765, 46021, 46741, 51402, 59625], #[128, 4620, 5838, 10646, 5814, 10622, 18992, 35943, 3900, 4980, 6080, 10886, 6056, 10862, 19232, 36183], #[854, 10034, 10152, 15554, 22570, 42171, 46047, 46767, 6074, 10884, 10992, 15924, 43981, 44221, 46287, 47007], #[848, 10010, 22576, 42195, 10128, 15530, 46023, 46743, 6050, 10860, 43983, 44223, 10968, 15900, 46263, 46983], #[2289, 18249, 22816, 42675, 22810, 42651, 51378, 59619, 19208, 36181, 46285, 47005, 46261, 46981, 61264, 61504], #[4, 20061, 1109, 20327, 1108, 20325, 2082, 20685, 1224, 21765, 2797, 22007, 2791, 22005, 3525, 22365], #[1085, 20303, 16085, 31537, 17178, 32496, 17923, 33223, 18397, 42799, 18877, 43279, 23446, 49967, 23686, 50207], #[1084, 20301, 17179, 32497, 16084, 31536, 17922, 33222, 18391, 42775, 23444, 49965, 18871, 43255, 23684, 50205], #[2058, 20661, 17899, 33217, 17898, 33216, 25896, 35136, 23880, 51729, 50549, 60227, 50548, 60225, 51642, 60585], #[1200, 21741, 18373, 42793, 18367, 42769, 23904, 51753, 16200, 47089, 19356, 47599, 19350, 47575, 24152, 51993], #[2773, 21983, 18853, 43273, 23420, 49941, 50525, 60221, 19332, 47593, 36673, 48433, 50640, 62813, 52477, 63083], #[2767, 21981, 23422, 49943, 18847, 43249, 50524, 60219, 19326, 47569, 50642, 62819, 36649, 48409, 52471, 63059], #[3501, 22341, 23662, 50183, 23660, 50181, 51618, 60579, 24128, 51969, 52453, 63077, 52447, 63053, 63364, 0]],
  #[#[0, 19449, 987, 19721, 985, 19715, 1962, 19965, 984, 19713, 1956, 19959, 1950, 19953, 3153, 21633], #[963, 19697, 15963, 31393, 17058, 32376, 17803, 33103, 17052, 32352, 17797, 33079, 23080, 49241, 23320, 49481], #[961, 19691, 17059, 32377, 15961, 31369, 17802, 33102, 17046, 32328, 23074, 49235, 17791, 33055, 23314, 49475], #[1938, 19941, 17779, 33097, 17778, 33096, 25776, 35016, 23048, 49209, 50403, 59717, 50401, 59693, 51522, 59985], #[960, 19689, 17053, 32353, 17047, 32329, 23072, 49233, 15960, 31368, 17796, 33078, 17790, 33054, 23312, 49473], #[1932, 19935, 17773, 33073, 23050, 49211, 50405, 59723, 17772, 33072, 25752, 34992, 50400, 59691, 51516, 59961], #[1926, 19929, 23056, 49217, 17767, 33049, 50404, 59699, 17766, 33048, 50402, 59697, 25728, 34968, 51510, 59937], #[3129, 21609, 23296, 49457, 23290, 49451, 51498, 59979, 23288, 49449, 51492, 59955, 51486, 59931, 63240, 0]],
  #[#[0, 4500, 4476, 10280, 4470, 10256, 10232, 35193, 3752, 4862, 4838, 10520, 4832, 10496, 10472, 35433], #[732, 9914, 9912, 15432, 21018, 42051, 42027, 45681, 5952, 10764, 10758, 15800, 43521, 43887, 43881, 45921], #[726, 9890, 21019, 42075, 9888, 15408, 42025, 45657, 5928, 10740, 43497, 43863, 10734, 15776, 43857, 45897], #[2169, 18129, 21262, 42555, 21260, 42531, 48858, 55299, 19088, 36061, 46165, 46885, 46141, 46861, 60905, 61145], #[720, 21021, 9866, 42073, 9864, 42049, 15384, 45633, 5904, 43473, 10716, 43839, 10710, 43833, 15752, 45873], #[2163, 21263, 18123, 42553, 21258, 48860, 42507, 55297, 19082, 46159, 36037, 46879, 46117, 60881, 46837, 61121], #[2161, 21261, 21259, 48862, 18121, 42529, 42505, 55296, 19080, 46135, 46111, 60875, 36031, 46855, 46831, 61115], #[3018, 21501, 21499, 49102, 21498, 49100, 49098, 55656, 24000, 51849, 51843, 62716, 51841, 62692, 62668, 0]],
  #[#[0, 5139, 5113, 6690, 5089, 6666, 13232, 13552, 5064, 13258, 6636, 13522, 6630, 13498, 13472, 36753], #[256, 5381, 5356, 6930, 8629, 9349, 14038, 14278, 8599, 14012, 9319, 14252, 37173, 37439, 37413, 37773], #[250, 5379, 8635, 9355, 5332, 6906, 14032, 14272, 8575, 13988, 37149, 37433, 9295, 14228, 37389, 37749], #[501, 5739, 8875, 9595, 8869, 9589, 14992, 15232, 22448, 40313, 40799, 41039, 40793, 41033, 41753, 41993], #[242, 8610, 5353, 9330, 8550, 37119, 13958, 37403, 5306, 14002, 6876, 14242, 9270, 37359, 14198, 37719], #[493, 8850, 5713, 9570, 22444, 40773, 40283, 41013, 8839, 14962, 9559, 15202, 40763, 41723, 41003, 41963], #[2401, 18497, 18502, 36331, 18481, 47208, 42865, 48114, 18486, 42888, 47185, 48091, 36271, 48054, 48031, 61595], #[2657, 18737, 18742, 36571, 22938, 47500, 43180, 48354, 22934, 43157, 47477, 48331, 52081, 62135, 62157, 62495], #[240, 8586, 8556, 37113, 5329, 9306, 13952, 37379, 5304, 13978, 9276, 37353, 6870, 14218, 14192, 37713], #[2403, 18491, 18483, 47232, 18500, 36307, 42867, 48108, 18492, 42893, 36277, 48078, 47187, 48067, 48037, 61601], #[487, 8826, 22445, 40749, 5689, 9546, 40259, 40989, 8815, 14938, 40739, 41699, 9535, 15178, 40979, 41939], #[2651, 18731, 22939, 47498, 18740, 36547, 43178, 48348, 22928, 43133, 52083, 62111, 47453, 48307, 62151, 62471], #[480, 22449, 8796, 40719, 8790, 40713, 14912, 41673, 5664, 40233, 9516, 40959, 9510, 40953, 15152, 41913], #[2643, 22935, 18723, 47472, 22924, 52091, 43107, 62081, 18732, 43152, 36517, 48318, 47427, 62121, 48277, 62441], #[2641, 22929, 22925, 52097, 18721, 47448, 43105, 62075, 18726, 43128, 47425, 62097, 36511, 48294, 48271, 62435], #[3604, 23769, 23765, 52337, 23764, 52331, 50284, 63216, 23768, 50288, 52323, 63194, 52321, 63170, 63148, 0]],
  #[#[0, 7266, 7236, 30438, 5209, 7866, 13592, 31068, 5184, 13618, 7836, 31038, 6750, 13858, 13832, 36993], #[1453, 16581, 16573, 31873, 17300, 25309, 32618, 34549, 17292, 32592, 25279, 34519, 44677, 45307, 45277, 57323], #[370, 7506, 20179, 30708, 5572, 8106, 29988, 31308, 8695, 14588, 39189, 39789, 9415, 14828, 39429, 40029], #[1701, 16821, 20542, 32139, 17540, 25549, 32858, 34789, 22688, 42413, 51013, 57953, 44947, 45547, 58313, 58553], #[362, 20175, 7476, 30678, 8670, 39159, 14558, 39759, 5546, 29958, 8076, 31278, 9390, 39399, 14798, 39999], #[1693, 20537, 16813, 32113, 22684, 51021, 42387, 57923, 17532, 32832, 25519, 34759, 44917, 58283, 45517, 58523], #[2521, 21855, 21859, 49577, 18601, 47328, 42985, 60097, 18606, 43008, 47305, 60075, 36391, 48174, 48151, 61835], #[3377, 22217, 22222, 49817, 23538, 51261, 50059, 60460, 23534, 50055, 51253, 60437, 52201, 62931, 62909, 0]],
  #[#[0, 19569, 7356, 30558, 7350, 30534, 14312, 38913, 5424, 29814, 7956, 31158, 7950, 31134, 14432, 39033], #[1573, 19817, 16693, 31993, 21138, 48621, 42267, 55180, 17412, 32712, 25399, 34639, 44797, 57563, 45397, 57683], #[1567, 19811, 21139, 48623, 16687, 31969, 42265, 55178, 17406, 32688, 44791, 57539, 25375, 34615, 45391, 57659], #[2901, 20901, 21382, 48743, 21380, 48741, 48978, 55539, 23168, 49329, 51133, 59837, 51127, 59813, 62548, 0]],
  #[#[0, 16337, 16336, 24570, 16321, 31609, 31585, 33834, 16320, 31608, 31584, 33810, 24510, 33774, 33750, 55713], #[1336, 16457, 16456, 24690, 20418, 31781, 31780, 33954, 20412, 31757, 31756, 33930, 50760, 56135, 56133, 56373], #[1320, 20409, 20403, 50776, 16441, 31729, 31705, 56075, 16440, 31728, 31704, 56073, 24630, 33894, 33870, 56313], #[3243, 22089, 22083, 50896, 22098, 49691, 49685, 60336, 22092, 49689, 49683, 60312, 50880, 60291, 60267, 0]],
  #[],
  #[#[0, 20769, 20763, 48496, 20761, 48490, 48484, 55416, 20760, 48488, 48482, 55392, 48480, 55368, 55344, 0]],
  #[#[0, 4740, 4716, 10400, 4710, 10376, 10352, 35313, 4692, 10394, 10392, 15672, 43321, 43741, 43717, 45801], #[4686, 10370, 43323, 43743, 10368, 15648, 43711, 45777, 10328, 35289, 43693, 45795, 43687, 45771, 60604, 60784], #[4680, 43329, 10346, 43719, 10344, 43713, 15624, 45753, 10322, 43695, 35283, 45793, 43681, 60610, 45747, 60760], #[10320, 43689, 43683, 60616, 35281, 45769, 45745, 60754, 15600, 45729, 45723, 60736, 45721, 60730, 60724, 0]],
  #[#[0, 11346, 6319, 11612, 6295, 11588, 13352, 26873, 6313, 11610, 8233, 11850, 27352, 27592, 27959, 28199], #[6289, 11586, 27353, 27593, 8209, 11826, 27953, 28193, 13328, 26872, 27958, 28198, 27952, 28192, 29392, 29632], #[3962, 12690, 6559, 12932, 8910, 37239, 14078, 37643, 6553, 12930, 8473, 13170, 40403, 41373, 40643, 41613], #[8886, 37215, 40397, 41371, 35521, 47688, 46345, 59276, 14054, 37637, 40637, 41611, 46321, 59274, 58674, 59514], #[3960, 12666, 8916, 37233, 6535, 12908, 14072, 37619, 8892, 37209, 35523, 47712, 40373, 41347, 46347, 59270], #[6529, 12906, 40379, 41349, 8449, 13146, 40619, 41589, 14048, 37613, 46323, 59268, 40613, 41587, 58668, 59508], #[4200, 40089, 9156, 40839, 9150, 40833, 15032, 41793, 9132, 40815, 35763, 47952, 44041, 61971, 46587, 62321], #[9126, 40809, 44043, 61977, 35761, 47928, 46585, 62315, 15008, 41769, 46563, 62297, 46561, 62291, 61324, 0]],
  #[#[0, 12066, 7596, 30798, 6415, 12188, 13712, 36899, 7572, 30792, 24793, 34033, 38347, 38707, 44437, 54353], #[6409, 12186, 38349, 38709, 8329, 12426, 38469, 38829, 13688, 36893, 44413, 54352, 38467, 38827, 54952, 55072], #[4082, 29712, 7716, 30918, 9030, 39279, 14678, 39879, 7692, 30912, 24913, 34153, 43587, 58043, 44557, 58163], #[9006, 39255, 43563, 58037, 35641, 47808, 46465, 61715, 14654, 39855, 44533, 58157, 46441, 61691, 60965, 0]],
  #[],
  #[#[0, 26250, 11442, 26396, 6991, 27107, 11684, 27227, 11412, 26370, 26010, 26610, 27706, 29157, 27826, 29277], #[6966, 27077, 27676, 29131, 25009, 34249, 45030, 56495, 11654, 27197, 27796, 29251, 45007, 56518, 57095, 57215], #[6120, 30048, 12762, 39515, 7111, 30295, 13004, 39635, 12732, 39489, 37443, 59112, 40469, 57773, 41443, 59384], #[7086, 30288, 40443, 57777, 25129, 34369, 45150, 58377, 12974, 39609, 41413, 59354, 45127, 58373, 62165, 0]],
  #[],
  #[],
  #[#[0, 30168, 30144, 54436, 24391, 33655, 33631, 55955, 12252, 38175, 38173, 54676, 44281, 57413, 57389, 0]],
  #[#[0, 11153, 11147, 11277, 11145, 11271, 11265, 12585, 11048, 26693, 27436, 28051, 27412, 28027, 41152, 41272], #[11042, 27437, 26669, 28050, 27388, 41146, 28003, 41266, 11172, 28037, 28036, 29476, 41041, 58730, 58706, 59013], #[11040, 27413, 27389, 41144, 26668, 28026, 28002, 41264, 11166, 28013, 41043, 58751, 28012, 29452, 58704, 58989], #[11160, 41049, 27989, 58727, 27988, 58725, 29428, 58965, 12480, 41169, 41163, 58992, 41161, 58968, 58944, 0]],
  #[],
  #[#[0, 37809, 26909, 53507, 26908, 53505, 28722, 53865, 11888, 38049, 38533, 54797, 38527, 54773, 58824, 0]],
  #[#[0, 37929, 37923, 54556, 37921, 54532, 54508, 0]],
  #[#[0, 33288, 33264, 52773, 33240, 52771, 52770, 53130, 24240, 33528, 33504, 56193, 33480, 56169, 56163, 0]],
  #[#[0, 33408, 33384, 55833, 33360, 55809, 55803, 0]],
  #[#[0, 26460, 26436, 28881, 26406, 28851, 56525, 56825, 26400, 56531, 28827, 56801, 28801, 56771, 56765, 0]],
  #[],
  #[#[0, 28387, 28357, 53243, 26092, 28627, 53991, 54233, 26066, 53961, 28597, 54203, 28921, 56889, 56885, 0]],
  #[#[0, 53331, 28477, 53723, 28447, 53693, 56645, 0]],
  #[#[0, 52654, 52652, 53013, 28200, 54051, 54027, 0]],
  #[#[0, 53571, 53547, 0]],
  #[#[0, 52864, 52804, 0]],
  #[],
  #[]]


private def ones (c : Fin 10 → Bool) : Nat :=
  ((Finset.univ : Finset (Fin 10)).filter (fun k => c k = true)).card

private def complementEdges (i : Fin 34) : List (Fin 10) :=
  (List.finRange 10).filter (fun k => !(twoPatterns i k))

private def packEdges (c : Fin 10 → Bool) : List (Fin 10) → Nat
  | [] => 0
  | k :: ks => 2 * packEdges c ks + if c k then 1 else 0

private theorem packEdges_lt (c : Fin 10 → Bool) (ks : List (Fin 10)) :
    packEdges c ks < 2^ks.length := by
  induction ks with
  | nil => simp [packEdges]
  | cons k ks ih =>
    simp only [packEdges, List.length_cons, pow_succ]
    split <;> omega

private theorem packEdges_bit (c : Fin 10 → Bool) (ks : List (Fin 10))
    (j : Nat) (hj : j < ks.length) : (packEdges c ks).testBit j = c (ks[j]'hj) := by
  induction ks generalizing j with
  | nil => simp at hj
  | cons k ks ih =>
    cases j with
    | zero =>
      cases h : c k <;>
        simp [packEdges, h, Nat.testBit_eq_decide_div_mod_eq]
    | succ j =>
      rw [Nat.testBit_succ, packEdges]
      have hd : (2 * packEdges c ks + (if c k then 1 else 0))/2 = packEdges c ks := by
        split <;> omega
      rw [hd]
      exact ih j (by simpa using hj)

private def unpackThree (i : Fin 34) (m : Nat) (k : Fin 10) : Fin 3 :=
  if twoPatterns i k then 1 else
  if m.testBit ((complementEdges i).idxOf k) then 2 else 0

private def hasAllThree (c : Fin 10 → Fin 3) : Prop :=
  (∃ k, c k = 0) ∧ (∃ k, c k = 1) ∧ (∃ k, c k = 2)

private theorem packThree (i : Fin 34) (c : Fin 10 → Fin 3)
    (hc : ∀ k, (c k = 1) ↔ twoPatterns i k = true) :
    ∃ m : Fin (2^(complementEdges i).length), ∀ k, unpackThree i m k = c k := by
  let paint : Fin 10 → Bool := fun k => decide (c k = 2)
  let ks := complementEdges i
  let m := packEdges paint ks
  refine ⟨⟨m, packEdges_lt paint ks⟩,?_⟩
  intro k
  by_cases hh : twoPatterns i k = true
  · simp [unpackThree,hh,(hc k).mpr hh]
  · have hn : c k ≠ 1 := fun hz => hh ((hc k).mp hz)
    have hm : k ∈ ks := by
      simp [ks, complementEdges, Bool.not_eq_true', Bool.eq_false_iff.mpr hh]
    have hidx : ks.idxOf k < ks.length := List.idxOf_lt_length_of_mem hm
    have hbits := packEdges_bit paint ks (ks.idxOf k) hidx
    rw [List.getElem_idxOf hidx] at hbits
    have hh' : (↑(⟨m, packEdges_lt paint ks⟩ : Fin (2^ks.length)) : ℕ).testBit
        ((complementEdges i).idxOf k) = paint k := hbits
    have hv : c k = 0 ∨ c k = 1 ∨ c k = 2 := by omega
    rcases hv with h | h | h
    · simp [unpackThree, hh,hh',paint,h]
    · exact (hn h).elim
    · simp [unpackThree, hh,hh',paint,h]

private def lookupThreeCode (i : Nat) : Nat :=
  (threeCodeRows.getD (i / 32) #[]).getD (i % 32) 0

private def jointChoice (i : Fin 34) (m : Nat) : Nat :=
  ((threeChoiceRows.getD i #[]).getD (m / 16) #[]).getD (m % 16) 0

private def caseNumThree (i : Fin 34) (m : Nat) : Fin 529 :=
  ⟨jointChoice i m / 120 % 529,Nat.mod_lt _ (by decide)⟩

private def permThree (i : Fin 34) (m : Nat) : Fin 5 → Fin 5 :=
  permutationValue ⟨jointChoice i m % 120,Nat.mod_lt _ (by decide)⟩

private def checkedThreeLabels (i : Fin 34) : Prop :=
  0 < ones (twoPatterns i) →
  ones (twoPatterns i) % 4 ≠ 1 →
  ∀ m : Fin (2^(complementEdges i).length), hasAllThree (unpackThree i m) →
    ∀ k : Fin 10,
      unpackThree i m (edgeIndex (permThree i m (edgePair k).1) (permThree i m (edgePair k).2)) =
        readThree (lookupThreeCode (caseNumThree i m)) k

private theorem three_labels (i : Fin 34) : checkedThreeLabels i := by
  fin_cases i <;> unfold checkedThreeLabels hasAllThree <;> decide +kernel

private def checkedThree (i : Fin 34) : Prop :=
  0 < ones (twoPatterns i) →
  ones (twoPatterns i) % 4 ≠ 1 →
  ∀ m : Fin (2^(complementEdges i).length), hasAllThree (unpackThree i m) →
    (∀ j k : Fin 5, permThree i m j = permThree i m k → j = k) ∧
    (∀ j k : Fin 5, j ≠ k →
      unpackThree i m (edgeIndex (permThree i m j) (permThree i m k)) =
        readThree (lookupThreeCode (caseNumThree i m)) (edgeIndex j k))

private theorem three_coverage (i : Fin 34) : checkedThree i := by
  intro hpos hno m hall
  refine ⟨permutationValuesInjective _, ?_⟩
  intro j k hjk
  have hh := three_labels i hpos hno m hall (edgeIndex j k)
  rcases edgePair_eq j k hjk with h|h
  · simpa only [h] using hh
  · simpa only [h,edge_symm (permThree i m k) (permThree i m j)] using hh

private structure Monomial where
  x : ℕ
  y : ℕ
  value : ℤ
  deriving DecidableEq

private abbrev SparsePoly := List Monomial

private def evalMonomial (a b : ℝ) (m : Monomial) : ℝ :=
  (m.value : ℝ)*a^m.x*b^m.y

private def evalSparse (a b : ℝ) (p : SparsePoly) : ℝ :=
  (p.map (evalMonomial a b)).sum

private def insertMonomial (m : Monomial) : SparsePoly → SparsePoly
  | [] => if m.value = 0 then [] else [m]
  | n :: p =>
    if m.value = 0 then n :: p
    else if m.x = n.x ∧ m.y = n.y then
      if m.value + n.value = 0 then p else ⟨m.x,m.y,m.value+n.value⟩ :: p
    else if m.x < n.x ∨ (m.x = n.x ∧ m.y < n.y) then m :: n :: p
    else n :: insertMonomial m p

private def normalizeSparse (p : SparsePoly) : SparsePoly :=
  p.foldr insertMonomial []

private theorem eval_insert_sparse (a b : ℝ) (m : Monomial) (p : SparsePoly) :
    evalSparse a b (insertMonomial m p) = evalMonomial a b m + evalSparse a b p := by
  induction p with
  | nil => by_cases h : m.value = 0 <;> simp [insertMonomial,evalSparse,evalMonomial,h]
  | cons n p ih =>
    by_cases h : m.value = 0
    · simp [insertMonomial,evalSparse,evalMonomial,h]
    · by_cases he : m.x = n.x ∧ m.y = n.y
      · have eqTerm : evalMonomial a b ⟨m.x,m.y,m.value+n.value⟩ =
            evalMonomial a b m + evalMonomial a b n := by
          simp [evalMonomial, he.1,he.2,Int.cast_add]
          ring
        rw [insertMonomial,if_neg h,if_pos he]
        by_cases hz : m.value + n.value = 0
        · rw [if_pos hz]
          have hz' : evalMonomial a b ⟨m.x,m.y,m.value+n.value⟩ = 0 := by simp [evalMonomial,hz]
          have hh : evalMonomial a b m + evalMonomial a b n = 0 := eqTerm.symm.trans hz'
          change evalSparse a b p = evalMonomial a b m + (evalMonomial a b n + evalSparse a b p)
          linear_combination -hh
        · rw [if_neg hz]
          change evalMonomial a b ⟨m.x,m.y,m.value+n.value⟩ + evalSparse a b p =
            evalMonomial a b m + (evalMonomial a b n + evalSparse a b p)
          rw [eqTerm]
          ring
      · by_cases ha : m.x < n.x ∨ (m.x = n.x ∧ m.y < n.y)
        · simp [insertMonomial,h,he,ha,evalSparse]
        · simp only [insertMonomial,h,he,ha,if_false,evalSparse,List.map_cons,List.sum_cons]
          change evalMonomial a b n + evalSparse a b (insertMonomial m p) =
            evalMonomial a b m + (evalMonomial a b n + evalSparse a b p)
          rw [ih]
          ring

private theorem eval_normalize_sparse (a b : ℝ) (p : SparsePoly) :
    evalSparse a b (normalizeSparse p) = evalSparse a b p := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    change evalSparse a b (insertMonomial m (normalizeSparse p)) = _
    rw [eval_insert_sparse,ih]
    rfl

private def literalSparse (c : ℤ) : SparsePoly := [⟨0,0,c⟩]
private def xSparse : SparsePoly := [⟨1,0,1⟩]
private def ySparse : SparsePoly := [⟨0,1,1⟩]

private def addSparse (p q : SparsePoly) : SparsePoly := normalizeSparse (p ++ q)
private def negateSparse (p : SparsePoly) : SparsePoly := p.map (fun m => ⟨m.x,m.y,-m.value⟩)
private def subSparse (p q : SparsePoly) : SparsePoly := addSparse p (negateSparse q)
private def multiplyMonomial (m n : Monomial) := Monomial.mk (m.x+n.x) (m.y+n.y) (m.value*n.value)
private def multiplyByMonomial (m : Monomial) (p : SparsePoly) := p.map (multiplyMonomial m)
private def multiplySparseRaw (p q : SparsePoly) : SparsePoly := p.flatMap (fun m => multiplyByMonomial m q)
private def mulSparse (p q : SparsePoly) : SparsePoly := normalizeSparse (multiplySparseRaw p q)

@[simp] private theorem eval_literal (a b : ℝ) (c : ℤ) :
    evalSparse a b (literalSparse c) = c := by simp [evalSparse,literalSparse,evalMonomial]

@[simp] private theorem eval_x_sparse (a b : ℝ) : evalSparse a b xSparse = a := by
  simp [evalSparse,xSparse,evalMonomial]
@[simp] private theorem eval_y_sparse (a b : ℝ) : evalSparse a b ySparse = b := by
  simp [evalSparse,ySparse,evalMonomial]

@[simp] private theorem eval_add_sparse (a b : ℝ) (p q : SparsePoly) :
    evalSparse a b (addSparse p q) = evalSparse a b p + evalSparse a b q := by
  rw [addSparse,eval_normalize_sparse]
  simp [evalSparse,List.map_append,List.sum_append]

@[simp] private theorem eval_negate_sparse (a b : ℝ) (p : SparsePoly) :
    evalSparse a b (negateSparse p) = -evalSparse a b p := by
  induction p with
  | nil => simp [negateSparse,evalSparse]
  | cons m p ih =>
    change evalMonomial a b ⟨m.x,m.y,-m.value⟩ + evalSparse a b (negateSparse p) =
      -(evalMonomial a b m + evalSparse a b p)
    simp [ih,evalMonomial]
    ring

@[simp] private theorem eval_sub_sparse (a b : ℝ) (p q : SparsePoly) :
    evalSparse a b (subSparse p q) = evalSparse a b p - evalSparse a b q := by
  simp [subSparse,sub_eq_add_neg]

private theorem eval_monomial_mul (a b : ℝ) (m n : Monomial) :
    evalMonomial a b (multiplyMonomial m n) = evalMonomial a b m * evalMonomial a b n := by
  simp [evalMonomial,multiplyMonomial,pow_add]
  ring

private theorem eval_mul_by_monomial (a b : ℝ) (m : Monomial) (p : SparsePoly) :
    evalSparse a b (multiplyByMonomial m p) = evalMonomial a b m * evalSparse a b p := by
  induction p with
  | nil => simp [multiplyByMonomial,evalSparse]
  | cons n p ih =>
    change evalMonomial a b (multiplyMonomial m n) + evalSparse a b (multiplyByMonomial m p) =
      evalMonomial a b m * (evalMonomial a b n + evalSparse a b p)
    rw [eval_monomial_mul,ih,mul_add]

@[simp] private theorem eval_mul_sparse (a b : ℝ) (p q : SparsePoly) :
    evalSparse a b (mulSparse p q) = evalSparse a b p * evalSparse a b q := by
  rw [mulSparse,eval_normalize_sparse]
  induction p with
  | nil => simp [multiplySparseRaw,evalSparse]
  | cons m p ih =>
    change evalSparse a b (multiplyByMonomial m q ++ multiplySparseRaw p q) =
      (evalMonomial a b m + evalSparse a b p) * evalSparse a b q
    have happ : evalSparse a b (multiplyByMonomial m q ++ multiplySparseRaw p q) =
      evalSparse a b (multiplyByMonomial m q) + evalSparse a b (multiplySparseRaw p q) := by
      simp [evalSparse,List.map_append,List.sum_append]
    rw [happ,eval_mul_by_monomial,ih,add_mul]

private theorem eval_of_normal_forms_eq (a b : ℝ) {p q : SparsePoly}
    (h : normalizeSparse p = normalizeSparse q) : evalSparse a b p = evalSparse a b q := by
  simpa only [eval_normalize_sparse] using congrArg (evalSparse a b) h

local infixl:65 " +ₛ " => addSparse
local infixl:65 " -ₛ " => subSparse
local infixl:70 " *ₛ " => mulSparse
local notation "L" => literalSparse

private def basicSparse (code : Nat) (i j : Fin 5) : SparsePoly :=
  if i = j then L 0 else
  if readThree code (edgeIndex i j) = 0 then L 1 else
  if readThree code (edgeIndex i j) = 1 then xSparse else ySparse

@[simp] private theorem eval_basic_sparse (code : Nat) (a b : ℝ) (i j : Fin 5) :
    evalSparse a b (basicSparse code i j) = fromThree (readThree code) a b i j := by
  unfold basicSparse fromThree
  split
  · exact (eval_literal a b 0).trans (Int.cast_zero : ((0 : ℤ) : ℝ) = 0)
  · split
    · exact (eval_literal a b 1).trans (Int.cast_one : ((1 : ℤ) : ℝ) = 1)
    · split
      · exact eval_x_sparse a b
      · exact eval_y_sparse a b

private def gramSparse (code : Nat) (i j : Fin 5) : SparsePoly :=
  basicSparse code 0 i +ₛ basicSparse code 0 j -ₛ basicSparse code i j

private def gramDetSparse (code : Nat) (k l : Fin 5) : SparsePoly :=
  let F := gramSparse code
  (F 1 1 *ₛ F 2 2 -ₛ F 1 2 *ₛ F 1 2) *ₛ F k l -ₛ
    F 2 2 *ₛ F 1 k *ₛ F 1 l +ₛ
    F 1 2 *ₛ (F 2 k *ₛ F 1 l +ₛ F 1 k *ₛ F 2 l) -ₛ
    F 1 1 *ₛ F 2 k *ₛ F 2 l

private theorem eval_gram_sparse_zero (code : Nat) (a b : ℝ) (k l : Fin 5)
    (hd : StandardDistanceData (fromThree (readThree code) a b)) :
    evalSparse a b (gramDetSparse code k l) = 0 := by
  simpa [gramDetSparse,gramSparse,squaredGram,pow_two] using hd.gram 0 1 2 k l

private def triangleSparse (u v w : SparsePoly) : SparsePoly :=
  let t := u +ₛ v -ₛ w
  L 4 *ₛ u *ₛ v -ₛ t *ₛ t

private def circleSparse (a b c d e f : SparsePoly) : SparsePoly :=
  let u := a *ₛ f
  let v := b *ₛ e
  let w := c *ₛ d
  u *ₛ u +ₛ v *ₛ v +ₛ w *ₛ w -ₛ L 2 *ₛ (u *ₛ v +ₛ v *ₛ w +ₛ w *ₛ u)

private def trianglePos : Fin 10 → Fin 5 × Fin 5 × Fin 5 :=
  ![(0,1,2),(0,1,3),(0,1,4),(0,2,3),(0,2,4),(0,3,4),
    (1,2,3),(1,2,4),(1,3,4),(2,3,4)]

private def quadPos : Fin 5 → Fin 5 × Fin 5 × Fin 5 × Fin 5 :=
  ![(0,1,2,3),(0,1,2,4),(0,1,3,4),(0,2,3,4),(1,2,3,4)]

private theorem tri_pos_distinct : ∀ i : Fin 10,
    (trianglePos i).1 ≠ (trianglePos i).2.1 ∧
    (trianglePos i).1 ≠ (trianglePos i).2.2 ∧
    (trianglePos i).2.1 ≠ (trianglePos i).2.2 := by decide

private theorem quad_pos_distinct : ∀ i : Fin 5,
    (quadPos i).1 ≠ (quadPos i).2.1 ∧ (quadPos i).1 ≠ (quadPos i).2.2.1 ∧
    (quadPos i).1 ≠ (quadPos i).2.2.2 ∧ (quadPos i).2.1 ≠ (quadPos i).2.2.1 ∧
    (quadPos i).2.1 ≠ (quadPos i).2.2.2 ∧ (quadPos i).2.2.1 ≠ (quadPos i).2.2.2 := by decide

private inductive Guard
  | aOrder
  | bOrder
  | triangle (i : Fin 10)
  | circle (i : Fin 5)

private def guardSparse (code : Nat) : Guard → SparsePoly
  | .aOrder => xSparse -ₛ L 1
  | .bOrder => ySparse -ₛ xSparse
  | .triangle i =>
    let (o,p,q) := trianglePos i
    let D := basicSparse code
    triangleSparse (D o p) (D o q) (D p q)
  | .circle i =>
    let (o,p,q,r) := quadPos i
    let D := basicSparse code
    circleSparse (D o p) (D o q) (D o r) (D p q) (D p r) (D q r)

private theorem guard_eval_ne_zero (code : Nat) (a b : ℝ) (ha : 1<a) (hb : a<b)
    (hd : StandardDistanceData (fromThree (readThree code) a b)) (g : Guard) :
    evalSparse a b (guardSparse code g) ≠ 0 := by
  cases g with
  | aOrder => simpa [guardSparse] using (sub_ne_zero.mpr ha.ne' : a - 1 ≠ 0)
  | bOrder => simpa [guardSparse] using (sub_ne_zero.mpr hb.ne' : b - a ≠ 0)
  | triangle i =>
    obtain ⟨h1,h2,h3⟩ := tri_pos_distinct i
    simpa [guardSparse,triangleSparse,trianglePolynomial,pow_two] using
      hd.triangle _ _ _ h1 h2 h3
  | circle i =>
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := quad_pos_distinct i
    have h := hd.circle _ _ _ _ h1 h2 h3 h4 h5 h6
    intro hn
    apply h
    simp [guardSparse,circleSparse] at hn
    unfold circlePolynomial
    linear_combination hn

private def guardsSparse (code : Nat) : List Guard → SparsePoly
  | [] => L 1
  | x :: xs => guardSparse code x *ₛ guardsSparse code xs

private theorem guards_eval_ne_zero (code : Nat) (a b : ℝ) (ha : 1<a) (hb : a<b)
    (hd : StandardDistanceData (fromThree (readThree code) a b)) (gs : List Guard) :
    evalSparse a b (guardsSparse code gs) ≠ 0 := by
  induction gs with
  | nil => norm_num [guardsSparse]
  | cons x xs ih =>
    simp only [guardsSparse,eval_mul_sparse]
    exact mul_ne_zero (guard_eval_ne_zero code a b ha hb hd x) ih

private structure PolynomialIdentity where
  scale : ℤ
  guards : List Guard
  first : SparsePoly
  second : SparsePoly
  third : SparsePoly

private def certificateLeft (code : Nat) (target : SparsePoly) (d : PolynomialIdentity) : SparsePoly :=
  L d.scale *ₛ target *ₛ guardsSparse code d.guards

private def certificateRight (code : Nat) (d : PolynomialIdentity) : SparsePoly :=
  d.first *ₛ gramDetSparse code 3 3 +ₛ d.second *ₛ gramDetSparse code 3 4 +ₛ
    d.third *ₛ gramDetSparse code 4 4

private def validIdentity (code : Nat) (target : SparsePoly) (d : PolynomialIdentity) : Bool :=
  decide (certificateLeft code target d = certificateRight code d) && decide (d.scale ≠ 0)

private theorem identity_vanishes (code : Nat) (target : SparsePoly) (d : PolynomialIdentity)
    (a b : ℝ) (ha : 1<a) (hb : a<b) (hd : StandardDistanceData (fromThree (readThree code) a b))
    (h : validIdentity code target d = true) : evalSparse a b target = 0 := by
  unfold validIdentity at h
  obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
  have heq : certificateLeft code target d = certificateRight code d := of_decide_eq_true h₁
  have hscale : d.scale ≠ 0 := of_decide_eq_true h₂
  have hh := congrArg (evalSparse a b) heq
  simp only [certificateLeft,certificateRight,eval_add_sparse,eval_mul_sparse,eval_literal,
    eval_gram_sparse_zero code a b _ _ hd,mul_zero,add_zero] at hh
  have hh' := (mul_eq_zero.mp hh).resolve_right (guards_eval_ne_zero code a b ha hb hd d.guards)
  exact (mul_eq_zero.mp hh').resolve_left (by exact_mod_cast hscale)

private inductive LabelExclusion
  | constant (d : PolynomialIdentity)
  | belowTwo (ba bb : PolynomialIdentity)
  | half (d : PolynomialIdentity)

private def belowTwoA : SparsePoly := xSparse *ₛ xSparse -ₛ L 4 *ₛ xSparse +ₛ L 1
private def belowTwoB : SparsePoly := ySparse -ₛ L 2
private def halfB : SparsePoly := L 2 *ₛ ySparse -ₛ L 1

private def validExclusion (code : Nat) : LabelExclusion → Bool
  | .constant d => validIdentity code (L 1) d
  | .belowTwo a b => validIdentity code belowTwoA a && validIdentity code belowTwoB b
  | .half d => validIdentity code halfB d

private theorem label_excluded (code : Nat) (d : LabelExclusion)
    (a b : ℝ) (ha : 1<a) (hb : a<b) (hd : StandardDistanceData (fromThree (readThree code) a b))
    (h : validExclusion code d = true) : False := by
  cases d with
  | constant d =>
    have hz := identity_vanishes code (L 1) d a b ha hb hd h
    norm_num at hz
  | belowTwo d₁ d₂ =>
    unfold validExclusion at h
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
    have ha2 := identity_vanishes code belowTwoA d₁ a b ha hb hd h₁
    have hb2 := identity_vanishes code belowTwoB d₂ a b ha hb hd h₂
    norm_num [belowTwoA] at ha2
    norm_num [belowTwoB] at hb2
    have hp : 0 < a := by linarith
    have hx : a < 2 := by linarith
    have hm := mul_pos hp (sub_pos.mpr hx)
    nlinarith only [ha2,ha,hm]
  | half d =>
    have hz := identity_vanishes code halfB d a b ha hb hd h
    norm_num [halfB] at hz
    linarith only [hz,ha,hb]

private def exclusionRow0 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨3, [Guard.triangle 5], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,1⟩], []⟩,
  LabelExclusion.constant ⟨4, [], [⟨0,0,1⟩], [], []⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 4], [⟨0,0,-5⟩, ⟨0,1,5⟩, ⟨1,0,-4⟩, ⟨2,0,-3⟩], [⟨0,0,2⟩, ⟨0,1,-2⟩, ⟨1,0,10⟩], []⟩,
  LabelExclusion.constant ⟨8, [], [⟨0,0,7⟩, ⟨0,1,-3⟩, ⟨1,0,-1⟩], [⟨0,0,-2⟩, ⟨1,0,2⟩], [⟨0,0,-4⟩, ⟨0,1,3⟩]⟩,
  LabelExclusion.constant ⟨9, [Guard.triangle 2], [⟨0,0,7⟩, ⟨0,1,-1⟩, ⟨1,0,-1⟩], [⟨0,0,-1⟩, ⟨0,1,-2⟩, ⟨1,0,2⟩], [⟨1,0,2⟩]⟩,
  LabelExclusion.constant ⟨36, [], [⟨2,0,-2⟩, ⟨3,0,1⟩], [⟨0,0,12⟩, ⟨1,0,-6⟩, ⟨1,1,-4⟩, ⟨2,1,2⟩], [⟨0,0,9⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 3], [⟨0,0,3⟩], [⟨0,0,4⟩, ⟨1,0,-2⟩], [⟨0,1,1⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,4⟩, ⟨1,0,7⟩, ⟨2,0,2⟩, ⟨3,0,-1⟩], [⟨0,0,24⟩, ⟨0,1,-8⟩, ⟨1,0,-6⟩, ⟨1,1,-6⟩, ⟨2,1,2⟩], [⟨0,0,-9⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.circle 4], [⟨0,1,-2⟩, ⟨0,2,-1⟩], [⟨0,1,6⟩], []⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,16⟩, ⟨0,1,5⟩, ⟨0,2,-7⟩, ⟨0,3,1⟩, ⟨1,0,-10⟩, ⟨1,1,12⟩, ⟨1,2,-2⟩], [⟨0,0,-12⟩, ⟨0,1,6⟩, ⟨1,0,10⟩, ⟨1,1,-12⟩, ⟨1,2,2⟩], [⟨0,0,-9⟩]⟩,
  LabelExclusion.constant ⟨9, [Guard.triangle 2], [⟨0,0,7⟩, ⟨0,1,-1⟩, ⟨1,0,-1⟩], [⟨0,0,-1⟩, ⟨0,1,2⟩, ⟨1,0,-2⟩], [⟨0,1,2⟩]⟩,
  LabelExclusion.constant ⟨3, [Guard.triangle 5], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,1⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 4], [⟨0,0,43⟩, ⟨0,1,8⟩, ⟨0,2,-3⟩, ⟨1,0,-40⟩, ⟨1,1,6⟩, ⟨2,0,-3⟩], [⟨0,0,-10⟩, ⟨0,1,-24⟩, ⟨1,0,56⟩], [⟨0,0,-21⟩]⟩,
  LabelExclusion.constant ⟨108, [], [⟨0,0,65⟩, ⟨0,1,-150⟩, ⟨0,2,31⟩, ⟨1,0,-48⟩, ⟨1,1,13⟩, ⟨1,2,-20⟩, ⟨2,0,10⟩, ⟨2,1,40⟩], [⟨0,0,-264⟩, ⟨0,1,238⟩, ⟨0,2,-62⟩, ⟨1,0,278⟩, ⟨1,1,-48⟩, ⟨1,2,40⟩, ⟨2,0,-10⟩, ⟨2,1,-40⟩], [⟨0,0,145⟩, ⟨0,1,-62⟩, ⟨1,0,-76⟩, ⟨1,1,71⟩, ⟨2,0,-5⟩, ⟨2,1,-20⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,23⟩, ⟨0,1,-9⟩, ⟨0,2,1⟩, ⟨1,0,-2⟩, ⟨1,1,1⟩], [⟨0,0,-26⟩, ⟨0,1,10⟩, ⟨1,0,4⟩, ⟨1,1,-2⟩], [⟨0,0,-6⟩]⟩,
  LabelExclusion.constant ⟨3, [], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩]

private def exclusionRow1 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨3, [Guard.triangle 1], [⟨0,0,4⟩, ⟨1,0,-1⟩], [⟨0,0,-4⟩, ⟨1,0,1⟩], []⟩,
  LabelExclusion.constant ⟨3, [Guard.triangle 3], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,1⟩], []⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,7⟩, ⟨0,1,-16⟩, ⟨0,2,4⟩], [⟨0,0,-28⟩, ⟨0,1,8⟩, ⟨1,0,14⟩, ⟨1,1,-4⟩], [⟨0,0,12⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,16⟩, ⟨0,1,-16⟩, ⟨0,2,4⟩], [⟨0,0,-28⟩, ⟨0,1,14⟩, ⟨1,0,8⟩, ⟨1,1,-4⟩], [⟨0,0,3⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 4], [⟨0,0,7⟩, ⟨0,1,-4⟩, ⟨0,2,-3⟩, ⟨1,0,-4⟩, ⟨2,0,-3⟩], [⟨0,0,-4⟩, ⟨0,1,4⟩, ⟨1,0,4⟩, ⟨1,1,6⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 4], [⟨0,0,2⟩, ⟨0,1,-4⟩, ⟨0,2,-3⟩, ⟨1,0,1⟩, ⟨2,0,-3⟩], [⟨0,0,-2⟩, ⟨0,1,4⟩, ⟨1,0,2⟩, ⟨1,1,6⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 4], [⟨0,0,2⟩, ⟨0,1,1⟩, ⟨0,2,-3⟩, ⟨1,0,-4⟩, ⟨2,0,-3⟩], [⟨0,0,-2⟩, ⟨0,1,2⟩, ⟨1,0,4⟩, ⟨1,1,6⟩], []⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,-7⟩, ⟨0,1,2⟩, ⟨1,0,-1⟩, ⟨1,1,-1⟩], [⟨0,0,-26⟩, ⟨0,1,8⟩, ⟨1,0,6⟩, ⟨1,1,-4⟩, ⟨2,0,2⟩], [⟨0,0,24⟩, ⟨0,1,-6⟩, ⟨1,0,-6⟩, ⟨1,1,3⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,1⟩, ⟨0,1,2⟩, ⟨1,0,-9⟩, ⟨2,0,2⟩], [⟨0,1,-4⟩, ⟨1,0,14⟩, ⟨2,0,-4⟩], [⟨1,0,4⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 9], [⟨0,0,3⟩], [⟨0,0,-6⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,-3⟩], [⟨0,0,12⟩, ⟨0,1,-6⟩], [⟨1,0,3⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.circle 4], [⟨0,1,-4⟩, ⟨0,2,-1⟩], [⟨0,1,-4⟩, ⟨1,0,16⟩, ⟨1,1,2⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.circle 4], [⟨0,2,-2⟩, ⟨1,1,4⟩, ⟨1,2,-1⟩, ⟨2,0,-4⟩, ⟨2,1,-3⟩, ⟨3,0,-1⟩], [⟨0,2,-2⟩, ⟨1,1,8⟩, ⟨1,2,2⟩, ⟨3,0,2⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,1⟩, ⟨1,0,-2⟩], [⟨0,1,2⟩, ⟨1,0,8⟩, ⟨1,1,-4⟩], [⟨0,1,-1⟩, ⟨1,1,2⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.triangle 0], [⟨0,0,8⟩, ⟨0,1,-8⟩, ⟨0,2,2⟩, ⟨1,0,4⟩, ⟨2,0,-1⟩], [⟨0,0,-8⟩, ⟨0,1,8⟩, ⟨0,2,-2⟩], []⟩,
  LabelExclusion.constant ⟨4, [], [⟨0,0,1⟩], [], []⟩]

private def exclusionRow2 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨4, [], [⟨0,0,1⟩], [], []⟩,
  LabelExclusion.constant ⟨20, [], [⟨0,0,16⟩, ⟨0,1,-3⟩, ⟨1,0,2⟩], [⟨0,0,-2⟩, ⟨1,0,2⟩], [⟨0,0,-13⟩, ⟨0,1,3⟩]⟩,
  LabelExclusion.constant ⟨64, [], [⟨0,0,36⟩], [⟨0,0,-6⟩, ⟨1,0,18⟩], [⟨0,0,-32⟩, ⟨0,1,9⟩]⟩,
  LabelExclusion.constant ⟨66, [Guard.triangle 3], [⟨0,0,47⟩, ⟨0,1,-4⟩, ⟨1,0,4⟩], [⟨0,0,-10⟩, ⟨0,1,-4⟩, ⟨1,0,8⟩], [⟨1,0,4⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 3], [⟨0,0,3⟩], [⟨0,0,-14⟩, ⟨1,0,4⟩], [⟨0,1,4⟩]⟩,
  LabelExclusion.constant ⟨36, [], [⟨0,0,16⟩, ⟨0,1,-7⟩, ⟨1,0,-16⟩, ⟨1,1,16⟩, ⟨2,0,4⟩, ⟨2,1,-4⟩], [⟨0,0,18⟩, ⟨0,1,-32⟩, ⟨0,2,14⟩, ⟨1,0,-6⟩, ⟨1,1,10⟩, ⟨1,2,-4⟩], [⟨0,0,9⟩, ⟨0,1,-9⟩]⟩,
  LabelExclusion.constant ⟨99, [], [⟨0,0,40⟩, ⟨1,0,-56⟩, ⟨2,0,26⟩, ⟨3,0,-4⟩], [⟨0,0,45⟩, ⟨0,1,-20⟩, ⟨1,0,-48⟩, ⟨1,1,18⟩, ⟨2,0,12⟩, ⟨2,1,-4⟩], [⟨0,0,18⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,1⟩], [⟨0,0,2⟩], []⟩,
  LabelExclusion.constant ⟨10, [], [⟨0,0,4⟩], [⟨0,0,10⟩, ⟨0,1,-4⟩], [⟨0,0,-5⟩, ⟨0,1,2⟩]⟩,
  LabelExclusion.constant ⟨54, [Guard.triangle 3], [⟨0,0,37⟩, ⟨0,1,4⟩, ⟨1,0,-4⟩], [⟨0,0,2⟩, ⟨0,1,-8⟩, ⟨1,0,4⟩], [⟨0,1,4⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 2], [⟨0,0,2⟩, ⟨0,1,1⟩, ⟨1,0,-2⟩], [⟨0,0,10⟩, ⟨0,1,2⟩, ⟨1,0,-2⟩], [⟨0,0,9⟩, ⟨1,0,1⟩]⟩,
  LabelExclusion.constant ⟨72, [], [⟨0,0,16⟩, ⟨0,1,11⟩, ⟨0,2,-7⟩, ⟨0,3,1⟩, ⟨1,0,2⟩, ⟨1,1,-3⟩, ⟨1,2,1⟩], [⟨0,0,18⟩, ⟨0,1,12⟩, ⟨0,2,-6⟩, ⟨1,0,4⟩, ⟨1,1,-6⟩, ⟨1,2,2⟩], [⟨0,0,-9⟩]⟩,
  LabelExclusion.constant ⟨54, [Guard.triangle 2], [⟨0,0,23⟩, ⟨0,1,17⟩, ⟨0,2,-4⟩, ⟨1,0,-2⟩, ⟨1,1,8⟩], [⟨0,0,-26⟩, ⟨0,1,34⟩, ⟨0,2,-8⟩, ⟨1,0,-2⟩, ⟨1,1,8⟩], [⟨0,0,-12⟩, ⟨0,1,12⟩, ⟨1,0,1⟩, ⟨1,1,-4⟩]⟩,
  LabelExclusion.constant ⟨12, [Guard.triangle 3], [⟨0,0,8⟩, ⟨0,1,-1⟩, ⟨1,0,1⟩], [⟨0,0,2⟩, ⟨0,1,2⟩, ⟨1,0,-4⟩], [⟨1,0,1⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,15⟩, ⟨0,1,-6⟩, ⟨0,2,3⟩, ⟨1,0,-6⟩, ⟨1,1,-1⟩, ⟨1,2,-1⟩, ⟨2,1,1⟩], [⟨0,0,-12⟩, ⟨0,1,12⟩, ⟨0,2,-6⟩, ⟨1,0,6⟩, ⟨1,1,8⟩, ⟨1,2,2⟩, ⟨2,1,-4⟩], [⟨0,0,-9⟩, ⟨0,1,9⟩, ⟨1,0,3⟩, ⟨1,1,-6⟩, ⟨2,1,1⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 2], [⟨0,0,4⟩, ⟨0,1,-1⟩, ⟨1,0,1⟩], [⟨0,0,-4⟩, ⟨0,1,-2⟩, ⟨1,0,4⟩], [⟨0,0,9⟩, ⟨1,0,1⟩]⟩]

private def exclusionRow3 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨54, [Guard.aOrder], [⟨0,0,-5⟩, ⟨0,1,2⟩, ⟨1,0,4⟩, ⟨1,1,1⟩, ⟨2,0,1⟩], [⟨0,0,-18⟩, ⟨0,1,4⟩, ⟨1,1,2⟩], []⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 2], [⟨0,0,4⟩, ⟨0,1,1⟩, ⟨1,0,-1⟩], [⟨0,0,-4⟩, ⟨0,1,4⟩, ⟨1,0,-2⟩], [⟨0,0,9⟩, ⟨0,1,1⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,7⟩, ⟨0,1,-8⟩, ⟨1,0,14⟩, ⟨1,1,9⟩, ⟨2,0,-10⟩, ⟨2,1,-1⟩, ⟨3,0,1⟩], [⟨0,0,12⟩, ⟨0,1,-16⟩, ⟨1,0,-6⟩, ⟨1,1,18⟩, ⟨2,1,-2⟩], [⟨0,0,-9⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 2], [⟨0,0,-3⟩, ⟨0,1,5⟩, ⟨1,0,-6⟩, ⟨2,0,-3⟩], [⟨0,1,-2⟩, ⟨1,0,12⟩], []⟩,
  LabelExclusion.constant ⟨108, [], [⟨0,0,-84⟩, ⟨0,1,18⟩, ⟨0,2,12⟩, ⟨1,0,67⟩, ⟨1,1,-78⟩, ⟨1,2,8⟩, ⟨2,0,44⟩, ⟨2,1,-4⟩], [⟨0,0,-36⟩, ⟨0,1,66⟩, ⟨0,2,12⟩, ⟨1,0,-234⟩, ⟨1,1,-52⟩, ⟨1,2,8⟩, ⟨2,0,88⟩, ⟨2,1,-8⟩], [⟨0,0,66⟩, ⟨0,1,12⟩, ⟨1,0,-37⟩, ⟨1,1,2⟩, ⟨2,0,44⟩, ⟨2,1,-4⟩]⟩,
  LabelExclusion.constant ⟨36, [], [⟨0,0,24⟩, ⟨0,1,30⟩, ⟨0,2,-17⟩, ⟨0,3,2⟩, ⟨1,0,-15⟩, ⟨1,1,9⟩, ⟨1,2,-1⟩], [⟨0,0,54⟩, ⟨0,1,-6⟩, ⟨0,2,-12⟩, ⟨0,3,2⟩, ⟨1,0,-30⟩, ⟨1,1,18⟩, ⟨1,2,-2⟩], [⟨0,0,-15⟩, ⟨0,1,-9⟩, ⟨0,2,2⟩, ⟨1,0,-15⟩, ⟨1,1,9⟩, ⟨1,2,-1⟩]⟩,
  LabelExclusion.constant ⟨36, [], [⟨0,0,-2⟩, ⟨0,1,-8⟩, ⟨0,2,-8⟩, ⟨1,0,-1⟩, ⟨1,1,-11⟩, ⟨1,2,6⟩, ⟨2,0,18⟩, ⟨2,1,-3⟩], [⟨0,0,84⟩, ⟨0,1,-28⟩, ⟨0,2,-8⟩, ⟨1,0,-128⟩, ⟨1,1,8⟩, ⟨1,2,6⟩, ⟨2,0,36⟩, ⟨2,1,-6⟩], [⟨0,0,26⟩, ⟨0,1,4⟩, ⟨1,0,-19⟩, ⟨1,1,1⟩, ⟨2,0,18⟩, ⟨2,1,-3⟩]⟩,
  LabelExclusion.constant ⟨3, [Guard.circle 2], [⟨1,0,-2⟩, ⟨2,0,-1⟩], [⟨1,0,2⟩, ⟨2,0,1⟩], []⟩,
  LabelExclusion.constant ⟨3, [Guard.circle 2], [⟨0,0,-1⟩, ⟨1,0,-1⟩, ⟨2,0,-1⟩], [⟨0,0,1⟩, ⟨1,0,1⟩, ⟨2,0,1⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 2], [⟨0,0,-3⟩, ⟨0,1,1⟩, ⟨0,2,2⟩, ⟨1,0,-2⟩, ⟨1,1,-2⟩, ⟨2,0,-3⟩], [⟨0,1,2⟩, ⟨0,2,-2⟩, ⟨1,0,8⟩, ⟨1,1,2⟩], []⟩,
  LabelExclusion.constant ⟨144, [], [⟨0,0,37⟩, ⟨0,1,90⟩, ⟨0,2,-18⟩, ⟨0,3,1⟩, ⟨1,0,-1⟩, ⟨1,1,10⟩, ⟨1,2,-1⟩], [⟨0,0,-24⟩, ⟨0,1,-82⟩, ⟨0,2,-8⟩, ⟨0,3,2⟩, ⟨1,0,-4⟩, ⟨1,1,40⟩, ⟨1,2,-4⟩], [⟨0,0,-61⟩, ⟨0,1,-11⟩, ⟨0,2,2⟩, ⟨1,0,-1⟩, ⟨1,1,10⟩, ⟨1,2,-1⟩]⟩,
  LabelExclusion.constant ⟨72, [], [⟨0,0,90⟩, ⟨0,1,-30⟩, ⟨0,2,11⟩, ⟨0,3,-1⟩, ⟨1,0,9⟩, ⟨1,1,-6⟩, ⟨1,2,1⟩], [⟨0,0,-144⟩, ⟨0,1,90⟩, ⟨0,3,-2⟩, ⟨1,0,36⟩, ⟨1,1,-24⟩, ⟨1,2,4⟩], [⟨0,0,-54⟩, ⟨0,1,3⟩, ⟨0,2,1⟩, ⟨1,0,9⟩, ⟨1,1,-6⟩, ⟨1,2,1⟩]⟩,
  LabelExclusion.constant ⟨36, [], [⟨0,0,-3⟩, ⟨1,0,7⟩, ⟨2,0,-2⟩], [⟨0,0,-18⟩, ⟨0,1,6⟩, ⟨1,0,-38⟩, ⟨1,1,-2⟩, ⟨2,0,12⟩], [⟨0,0,3⟩, ⟨0,1,-3⟩, ⟨1,0,10⟩, ⟨1,1,11⟩, ⟨2,0,-4⟩]⟩,
  LabelExclusion.belowTwo ⟨2, [], [], [], [⟨0,0,-1⟩]⟩ ⟨6, [], [⟨0,0,2⟩, ⟨1,0,-4⟩], [⟨0,0,-14⟩, ⟨0,1,-4⟩, ⟨1,0,8⟩], [⟨0,0,-3⟩, ⟨0,1,6⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,28⟩, ⟨1,0,-8⟩], [⟨0,0,28⟩, ⟨0,1,-16⟩, ⟨1,0,-6⟩, ⟨1,1,4⟩], [⟨0,0,-23⟩, ⟨0,1,-8⟩, ⟨0,2,4⟩, ⟨1,0,11⟩, ⟨1,1,-2⟩]⟩,
  LabelExclusion.constant ⟨32, [], [⟨0,0,-12⟩], [⟨0,0,-6⟩, ⟨0,1,-24⟩, ⟨1,0,-6⟩], [⟨0,0,8⟩, ⟨0,1,21⟩]⟩]

private def exclusionRow4 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨2, [], [⟨0,0,-12⟩], [⟨0,0,-24⟩, ⟨0,1,12⟩, ⟨1,0,-6⟩], [⟨0,0,23⟩, ⟨0,1,-6⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,1⟩, ⟨0,1,1⟩, ⟨1,0,-5⟩, ⟨1,1,-1⟩, ⟨2,0,1⟩], [⟨0,0,-8⟩, ⟨0,1,-4⟩, ⟨1,0,4⟩, ⟨1,1,4⟩, ⟨2,0,-2⟩], [⟨0,0,6⟩, ⟨0,1,3⟩, ⟨1,0,3⟩, ⟨1,1,-3⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,33⟩, ⟨0,1,-7⟩, ⟨0,2,-4⟩, ⟨1,0,-9⟩, ⟨1,1,4⟩], [⟨0,0,-12⟩, ⟨0,1,-24⟩, ⟨0,2,8⟩, ⟨1,0,6⟩], [⟨0,0,-36⟩, ⟨0,1,31⟩, ⟨0,2,-4⟩, ⟨1,0,6⟩, ⟨1,1,-4⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 9], [⟨0,0,-3⟩], [⟨0,0,-6⟩], [⟨0,0,6⟩]⟩,
  LabelExclusion.constant ⟨432, [], [⟨0,0,204⟩, ⟨0,1,-488⟩, ⟨0,2,68⟩, ⟨1,0,30⟩, ⟨1,1,176⟩, ⟨1,2,-34⟩, ⟨2,0,-57⟩, ⟨2,1,34⟩], [⟨0,0,-300⟩, ⟨0,1,56⟩, ⟨0,2,68⟩, ⟨1,0,396⟩, ⟨1,1,-164⟩, ⟨1,2,-34⟩, ⟨2,0,-114⟩, ⟨2,1,68⟩], [⟨0,0,180⟩, ⟨0,1,136⟩, ⟨1,0,24⟩, ⟨1,1,-136⟩, ⟨2,0,-57⟩, ⟨2,1,34⟩]⟩,
  LabelExclusion.constant ⟨81, [], [⟨0,0,63⟩, ⟨0,1,-1856⟩, ⟨0,2,332⟩, ⟨1,0,528⟩, ⟨1,1,326⟩, ⟨1,2,-112⟩, ⟨2,0,-210⟩, ⟨2,1,112⟩], [⟨0,0,-1083⟩, ⟨0,1,-196⟩, ⟨0,2,332⟩, ⟨1,0,1602⟩, ⟨1,1,-566⟩, ⟨1,2,-112⟩, ⟨2,0,-420⟩, ⟨2,1,224⟩], [⟨0,0,438⟩, ⟨0,1,664⟩, ⟨1,0,444⟩, ⟨1,1,-556⟩, ⟨2,0,-210⟩, ⟨2,1,112⟩]⟩,
  LabelExclusion.constant ⟨36, [], [⟨0,0,253⟩, ⟨0,1,-321⟩, ⟨0,2,50⟩, ⟨1,0,-292⟩, ⟨1,1,517⟩, ⟨1,2,-70⟩, ⟨2,0,-287⟩, ⟨2,1,70⟩], [⟨0,0,-496⟩, ⟨0,1,4⟩, ⟨0,2,50⟩, ⟨1,0,1642⟩, ⟨1,1,12⟩, ⟨1,2,-70⟩, ⟨2,0,-574⟩, ⟨2,1,140⟩], [⟨0,0,-23⟩, ⟨0,1,25⟩, ⟨1,0,212⟩, ⟨1,1,-85⟩, ⟨2,0,-287⟩, ⟨2,1,70⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 2], [⟨0,0,11⟩, ⟨0,1,1⟩, ⟨1,0,1⟩], [⟨0,0,-2⟩, ⟨0,1,2⟩, ⟨1,0,2⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 2], [⟨0,0,3⟩, ⟨1,0,1⟩], [⟨1,0,2⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 1], [⟨0,0,4⟩, ⟨1,0,-1⟩], [⟨0,0,8⟩, ⟨1,0,-2⟩], []⟩,
  LabelExclusion.constant ⟨36, [Guard.aOrder], [⟨0,0,-19⟩, ⟨0,1,2⟩, ⟨1,0,-2⟩], [⟨0,0,8⟩, ⟨0,1,-2⟩, ⟨1,0,-2⟩], [⟨0,0,21⟩, ⟨0,1,-3⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.aOrder], [⟨0,0,-21⟩, ⟨0,1,3⟩, ⟨1,0,-3⟩], [⟨0,0,10⟩, ⟨0,1,-2⟩, ⟨1,0,-4⟩], [⟨0,0,25⟩, ⟨0,1,-4⟩, ⟨1,0,-1⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,84⟩, ⟨0,1,-82⟩, ⟨0,2,11⟩, ⟨1,0,27⟩, ⟨1,1,-11⟩], [⟨0,0,18⟩, ⟨0,1,66⟩, ⟨0,2,-22⟩, ⟨1,0,-12⟩], [⟨0,0,-102⟩, ⟨0,1,115⟩, ⟨0,2,-22⟩, ⟨1,0,-39⟩, ⟨1,1,11⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 1], [⟨0,0,25⟩, ⟨0,1,-10⟩, ⟨1,0,10⟩], [⟨0,0,-8⟩, ⟨0,1,8⟩, ⟨1,0,2⟩], [⟨0,0,-9⟩, ⟨0,1,6⟩, ⟨1,0,-9⟩]⟩,
  LabelExclusion.constant ⟨558, [], [⟨0,0,2163⟩, ⟨0,1,-1068⟩, ⟨0,2,126⟩, ⟨1,0,-481⟩, ⟨1,1,330⟩, ⟨1,2,-56⟩, ⟨2,0,-148⟩, ⟨2,1,56⟩], [⟨0,0,498⟩, ⟨0,1,-438⟩, ⟨0,2,126⟩, ⟨1,0,740⟩, ⟨1,1,-132⟩, ⟨1,2,-56⟩, ⟨2,0,-296⟩, ⟨2,1,112⟩], [⟨0,0,-2691⟩, ⟨0,1,1476⟩, ⟨0,2,-189⟩, ⟨1,0,999⟩, ⟨1,1,-600⟩, ⟨1,2,84⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 1], [⟨0,0,34⟩, ⟨0,1,-10⟩, ⟨1,0,10⟩], [⟨0,0,-24⟩, ⟨1,0,10⟩], [⟨0,0,-22⟩, ⟨0,1,10⟩, ⟨1,0,-5⟩]⟩]

private def exclusionRow5 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨99, [], [⟨0,0,18⟩, ⟨1,0,-30⟩, ⟨1,1,12⟩, ⟨2,0,10⟩, ⟨2,1,-4⟩], [⟨0,0,45⟩, ⟨0,1,-48⟩, ⟨0,2,12⟩, ⟨1,0,-20⟩, ⟨1,1,18⟩, ⟨1,2,-4⟩], [⟨0,0,30⟩, ⟨0,1,-12⟩]⟩,
  LabelExclusion.constant ⟨54, [], [⟨0,0,13⟩, ⟨0,1,-2⟩, ⟨1,0,2⟩, ⟨1,1,-1⟩, ⟨2,0,-2⟩, ⟨2,1,1⟩], [⟨0,0,-52⟩, ⟨0,1,34⟩, ⟨0,2,-4⟩, ⟨1,0,20⟩, ⟨1,1,-14⟩, ⟨1,2,2⟩], [⟨0,0,12⟩, ⟨0,1,-6⟩]⟩,
  LabelExclusion.constant ⟨54, [], [⟨0,0,1⟩, ⟨0,1,10⟩, ⟨1,0,-28⟩, ⟨1,1,8⟩, ⟨2,0,7⟩, ⟨2,1,-2⟩], [⟨0,0,98⟩, ⟨0,1,-98⟩, ⟨0,2,20⟩, ⟨1,0,-28⟩, ⟨1,1,22⟩, ⟨1,2,-4⟩], [⟨0,0,21⟩, ⟨0,1,-6⟩]⟩,
  LabelExclusion.constant ⟨54, [], [⟨0,0,29⟩, ⟨0,1,-10⟩, ⟨1,0,-14⟩, ⟨1,1,7⟩, ⟨2,0,2⟩, ⟨2,1,-1⟩], [⟨0,0,88⟩, ⟨0,1,-64⟩, ⟨0,2,10⟩, ⟨1,0,-20⟩, ⟨1,1,14⟩, ⟨1,2,-2⟩], [⟨0,0,-12⟩, ⟨0,1,6⟩]⟩,
  LabelExclusion.constant ⟨54, [], [⟨0,0,-55⟩, ⟨0,1,75⟩, ⟨0,2,-14⟩, ⟨1,0,-84⟩, ⟨1,1,10⟩, ⟨1,2,4⟩, ⟨2,0,28⟩, ⟨2,1,-8⟩], [⟨0,0,112⟩, ⟨0,1,-130⟩, ⟨0,2,28⟩, ⟨1,0,-56⟩, ⟨1,1,44⟩, ⟨1,2,-8⟩], [⟨0,0,84⟩, ⟨0,1,-24⟩]⟩,
  LabelExclusion.constant ⟨22, [], [⟨0,0,4⟩], [⟨0,0,-10⟩, ⟨0,1,4⟩], [⟨0,0,5⟩, ⟨0,1,-2⟩]⟩,
  LabelExclusion.constant ⟨3, [], [⟨0,0,2⟩], [⟨0,0,-7⟩, ⟨0,1,2⟩], []⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,-1⟩], [⟨0,0,-8⟩, ⟨0,1,2⟩], [⟨0,0,4⟩, ⟨0,1,-1⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,15⟩, ⟨0,1,-18⟩, ⟨0,2,3⟩, ⟨1,0,32⟩, ⟨1,1,-12⟩, ⟨1,2,1⟩, ⟨2,0,4⟩, ⟨2,1,-1⟩], [⟨0,1,24⟩, ⟨0,2,-6⟩, ⟨1,0,-40⟩, ⟨1,1,18⟩, ⟨1,2,-2⟩], [⟨0,0,-24⟩, ⟨0,1,6⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,27⟩, ⟨0,1,-33⟩, ⟨0,2,6⟩, ⟨1,0,16⟩, ⟨1,2,-1⟩, ⟨2,0,-4⟩, ⟨2,1,1⟩], [⟨0,0,-48⟩, ⟨0,1,60⟩, ⟨0,2,-12⟩, ⟨1,0,16⟩, ⟨1,1,-12⟩, ⟨1,2,2⟩], [⟨0,0,-12⟩, ⟨0,1,3⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,3⟩, ⟨0,1,-3⟩, ⟨1,0,-8⟩, ⟨1,1,6⟩, ⟨1,2,-1⟩, ⟨2,0,-4⟩, ⟨2,1,1⟩], [⟨0,0,-72⟩, ⟨0,1,18⟩, ⟨1,0,40⟩, ⟨1,1,-18⟩, ⟨1,2,2⟩], [⟨0,0,24⟩, ⟨0,1,-6⟩]⟩,
  LabelExclusion.constant ⟨27, [], [⟨0,0,53⟩, ⟨0,1,-66⟩, ⟨0,2,16⟩, ⟨1,0,42⟩, ⟨1,1,2⟩, ⟨1,2,-4⟩, ⟨2,0,-14⟩, ⟨2,1,4⟩], [⟨0,0,-49⟩, ⟨0,1,70⟩, ⟨0,2,-16⟩, ⟨1,0,28⟩, ⟨1,1,-22⟩, ⟨1,2,4⟩], [⟨0,0,-42⟩, ⟨0,1,12⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 6], [⟨0,0,6⟩], [], [⟨0,0,-3⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,3⟩, ⟨0,1,-2⟩, ⟨1,0,-5⟩, ⟨2,0,2⟩], [⟨0,0,4⟩, ⟨0,1,-4⟩, ⟨1,0,-6⟩, ⟨2,0,4⟩], [⟨1,0,4⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,1⟩], [⟨0,0,2⟩], []⟩,
  LabelExclusion.constant ⟨26568, [Guard.triangle 0], [⟨1,0,15456⟩, ⟨2,0,-2668⟩, ⟨2,1,3864⟩, ⟨3,0,10264⟩, ⟨3,1,-12512⟩], [⟨0,0,26568⟩, ⟨0,2,7728⟩, ⟨1,0,35424⟩, ⟨1,1,11052⟩, ⟨1,2,-25024⟩, ⟨2,0,-72052⟩, ⟨2,1,89056⟩, ⟨3,0,20528⟩, ⟨3,1,-25024⟩], [⟨0,0,-4428⟩, ⟨0,1,-24303⟩, ⟨0,2,16675⟩, ⟨1,0,52631⟩, ⟨1,1,-47668⟩, ⟨1,2,-10948⟩, ⟨2,0,-33409⟩, ⟨2,1,41032⟩, ⟨3,0,5132⟩, ⟨3,1,-6256⟩]⟩]

private def exclusionRow6 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨336, [Guard.triangle 0], [⟨1,0,-608⟩, ⟨1,1,-64⟩, ⟨2,0,672⟩, ⟨2,1,32⟩, ⟨3,0,-176⟩], [⟨0,0,336⟩, ⟨0,1,336⟩, ⟨0,2,32⟩, ⟨1,0,-1256⟩, ⟨1,1,-296⟩, ⟨2,0,980⟩, ⟨2,1,32⟩, ⟨3,0,-176⟩], [⟨0,0,628⟩, ⟨0,1,86⟩, ⟨0,2,4⟩, ⟨1,0,-333⟩, ⟨1,1,-30⟩, ⟨2,0,44⟩]⟩,
  LabelExclusion.constant ⟨269613595350, [], [⟨0,0,-25476158228⟩, ⟨0,1,-77696061520⟩, ⟨1,0,102450462884⟩, ⟨1,1,352649928984⟩, ⟨2,0,-200541659348⟩, ⟨2,1,-443432452008⟩, ⟨3,0,120128522328⟩, ⟨3,1,133517536968⟩, ⟨4,0,6972238084⟩, ⟨4,1,14541880096⟩, ⟨5,0,-8760486864⟩, ⟨5,1,-7197679104⟩], [⟨0,0,562294818702⟩, ⟨0,1,-20905801668⟩, ⟨0,2,-77696061520⟩, ⟨1,0,3975157336⟩, ⟨1,1,357396963228⟩, ⟨1,2,119561744424⟩, ⟨2,0,-413945621084⟩, ⟨2,1,-521337098212⟩, ⟨2,2,-7051157216⟩, ⟨3,0,123705019888⟩, ⟨3,1,110068648120⟩, ⟨3,2,-7197679104⟩, ⟨4,0,24493211812⟩, ⟨4,1,28937238304⟩, ⟨5,0,-8760486864⟩, ⟨5,1,-7197679104⟩], [⟨0,0,-134806797675⟩, ⟨0,1,562294818702⟩, ⟨0,2,4570356560⟩, ⟨1,0,-269613595350⟩, ⟨1,1,-660224294278⟩, ⟨1,2,16020372388⟩, ⟨2,0,315748851354⟩, ⟨2,1,334031180886⟩, ⟨2,2,-39807017904⟩, ⟨3,0,-46119784996⟩, ⟨3,1,-24534277996⟩, ⟨3,2,10796518656⟩, ⟨4,0,-21007092770⟩, ⟨4,1,-21666298256⟩, ⟨5,0,4380243432⟩, ⟨5,1,3598839552⟩]⟩,
  LabelExclusion.constant ⟨324, [Guard.triangle 3], [⟨0,0,1252⟩, ⟨0,1,-2158⟩, ⟨0,2,420⟩, ⟨1,0,-2504⟩, ⟨1,1,560⟩, ⟨2,0,1216⟩, ⟨2,1,-315⟩], [⟨0,0,3080⟩, ⟨0,1,-1324⟩, ⟨0,2,210⟩, ⟨1,0,-5008⟩, ⟨1,1,1120⟩, ⟨2,0,2432⟩, ⟨2,1,-630⟩], [⟨0,1,2432⟩, ⟨0,2,-630⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨0,0,11⟩, ⟨1,0,-3⟩], [], [⟨0,0,-8⟩, ⟨1,0,3⟩]⟩,
  LabelExclusion.constant ⟨50, [Guard.triangle 3], [⟨0,0,25⟩], [⟨0,0,-148⟩, ⟨1,0,-26⟩, ⟨2,0,32⟩], [⟨0,1,48⟩]⟩,
  LabelExclusion.constant ⟨3298193304500, [], [⟨0,0,2877140808859⟩, ⟨0,1,1093218597246⟩, ⟨1,0,503522664612⟩, ⟨1,1,1570009394901⟩, ⟨2,0,-4045680200037⟩, ⟨2,1,-985441397832⟩, ⟨3,0,1307783869984⟩, ⟨3,1,-986966121813⟩, ⟨4,0,591448252407⟩, ⟨4,1,475266073674⟩, ⟨5,0,-186613557417⟩], [⟨0,0,3425140244056⟩, ⟨0,1,-2694937709318⟩, ⟨0,2,-1093218597246⟩, ⟨1,0,-9528887362⟩, ⟨1,1,2836543868170⟩, ⟨1,2,-1023400096278⟩, ⟨2,0,-7184526657726⟩, ⟨2,1,4102605910652⟩, ⟨2,2,950532147348⟩, ⟨3,0,-538822939536⟩, ⟨3,1,-4881911751388⟩, ⟨4,0,2178168811038⟩, ⟨4,1,950532147348⟩, ⟨5,0,-373227114834⟩], [⟨0,0,-1649096652250⟩, ⟨0,1,-3425140244056⟩, ⟨0,2,-182203099541⟩, ⟨1,0,3552087183612⟩, ⟨1,1,-2434633905978⟩, ⟨1,2,-170566682713⟩, ⟨2,0,2074353165972⟩, ⟨2,1,3339819363955⟩, ⟨2,2,158422024558⟩, ⟨3,0,-1462311520353⟩, ⟨3,1,-537470592813⟩, ⟨4,0,186613557417⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,1⟩], [⟨1,0,2⟩], []⟩,
  LabelExclusion.constant ⟨162, [Guard.triangle 6], [⟨0,0,105⟩, ⟨0,1,-40⟩], [⟨0,0,-24⟩, ⟨0,1,-20⟩, ⟨1,0,-10⟩, ⟨2,0,40⟩], [⟨0,1,60⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,2⟩, ⟨0,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,-2⟩, ⟨1,0,4⟩], [⟨1,0,1⟩]⟩,
  LabelExclusion.constant ⟨1458, [Guard.triangle 3], [⟨0,0,-33313⟩, ⟨0,1,31126⟩, ⟨1,0,15453⟩, ⟨1,1,-24201⟩, ⟨2,0,31170⟩, ⟨2,1,-3910⟩, ⟨3,0,-10632⟩, ⟨3,1,5674⟩, ⟨4,0,-2698⟩, ⟨4,1,-992⟩, ⟨5,0,992⟩], [⟨0,0,-14406⟩, ⟨0,1,42616⟩, ⟨1,0,-133432⟩, ⟨1,1,-9916⟩, ⟨2,0,54188⟩, ⟨2,1,-7380⟩, ⟨3,0,25556⟩, ⟨3,1,1984⟩, ⟨4,0,-15316⟩, ⟨5,0,1984⟩], [⟨0,1,11490⟩, ⟨1,1,-7023⟩, ⟨2,1,1488⟩]⟩,
  LabelExclusion.constant ⟨890867160, [Guard.aOrder], [⟨0,0,6517359090⟩, ⟨0,1,-11881052375⟩, ⟨0,2,6688296740⟩, ⟨0,3,-879169875⟩, ⟨1,0,4353819440⟩, ⟨1,1,-4283842067⟩, ⟨1,2,586539922⟩, ⟨1,3,177580725⟩, ⟨2,0,-4009952996⟩, ⟨2,1,1801943151⟩, ⟨2,2,-750838851⟩, ⟨3,0,1919828440⟩, ⟨3,1,-86173409⟩, ⟨3,2,114905175⟩, ⟨4,0,-273822514⟩, ⟨4,1,-83567400⟩], [⟨0,0,-9168016140⟩, ⟨0,1,10931691920⟩, ⟨0,2,-2014777140⟩, ⟨1,0,-5483727884⟩, ⟨1,1,-10068852232⟩, ⟨1,2,3499069908⟩, ⟨2,0,22107519780⟩, ⟨2,1,-6482782348⟩, ⟨2,2,-584971800⟩, ⟨3,0,-9492047628⟩, ⟨3,1,3605936796⟩, ⟨4,0,1739316152⟩, ⟨4,1,-584971800⟩], [⟨0,0,445433580⟩, ⟨0,1,10058883300⟩, ⟨0,2,-6944734130⟩, ⟨0,3,879169875⟩, ⟨1,0,-18781465860⟩, ⟨1,1,11269608294⟩, ⟨1,2,48077606⟩, ⟨1,3,-177580725⟩, ⟨2,0,13288885322⟩, ⟨2,1,-8802553262⟩, ⟨2,2,884994747⟩, ⟨3,0,-3894913540⟩, ⟨3,1,2202489338⟩, ⟨3,2,-177580725⟩, ⟨4,0,434829038⟩, ⟨4,1,-146242950⟩]⟩,
  LabelExclusion.constant ⟨19365127691838347286, [], [⟨0,0,398100574699766361141⟩, ⟨0,1,233632256266159387772⟩, ⟨0,2,-1173667930460296862812⟩, ⟨0,3,532252535648451940256⟩, ⟨1,0,-2236794087545531192399⟩, ⟨1,1,2594436402488698141965⟩, ⟨1,2,1188521856226287801246⟩, ⟨1,3,-1584894426553131445384⟩, ⟨2,0,1404841867755191723162⟩, ⟨2,1,-3538760126126269440718⟩, ⟨2,2,-472844863325139934482⟩, ⟨2,3,1936607686742001354748⟩, ⟨3,0,-3474377401537803882946⟩, ⟨3,1,5384027583650853833764⟩, ⟨3,2,-1330646801949340942872⟩, ⟨3,3,-1017252767148692526944⟩, ⟨4,0,2544297369436519720852⟩, ⟨4,1,-4083031788221790743240⟩, ⟨4,2,1464808149226946024068⟩, ⟨4,3,189320481729959109192⟩, ⟨5,0,-441270439842016596864⟩, ⟨5,1,950074288410918950448⟩, ⟨5,2,-378640963459918218384⟩], [⟨0,0,35142662103485044186⟩, ⟨0,1,-462290928341008926256⟩, ⟨0,2,-641415394811844922556⟩, ⟨0,3,532252535648451940256⟩, ⟨1,0,287218034783215422128⟩, ⟨1,1,3851271354119697645264⟩, ⟨1,2,-1914648472941782970992⟩, ⟨1,3,-1318768158728905475256⟩, ⟨2,0,-332040097494376501140⟩, ⟨2,1,-3581791482059183612732⟩, ⟨2,2,4538172015382911134608⟩, ⟨2,3,1277223607377548617120⟩, ⟨3,0,-749291465651768164156⟩, ⟨3,1,7827808459862154735104⟩, ⟨3,2,-5856229263288099211672⟩, ⟨3,3,-378640963459918218384⟩, ⟨4,0,1206696348665406911608⟩, ⟨4,1,-5210751025822632470432⟩, ⟨4,2,2791787461217221490656⟩, ⟨5,0,-441270439842016596864⟩, ⟨5,1,950074288410918950448⟩, ⟨5,2,-378640963459918218384⟩], [⟨0,0,-9682563845919173643⟩, ⟨0,1,-54507789795323391472⟩, ⟨1,0,70285324206970088372⟩, ⟨1,1,468459062592544780389⟩, ⟨1,2,-133063133912112985064⟩, ⟨2,0,527817046976930801234⟩, ⟨2,1,-592804884326980710538⟩, ⟨2,2,329692039682226368814⟩, ⟨3,0,-577468112067612100942⟩, ⟨3,1,731254431504657385544⟩, ⟨3,2,-319305901844387154280⟩, ⟨4,0,110317609960504149216⟩, ⟨4,1,-237518572102729737612⟩, ⟨4,2,94660240864979554596⟩]⟩,
  LabelExclusion.constant ⟨113022, [Guard.triangle 0], [⟨0,0,213486⟩, ⟨0,1,-269997⟩, ⟨0,2,114194⟩, ⟨0,3,3419⟩, ⟨1,0,608370⟩, ⟨1,1,-159279⟩, ⟨1,2,-121501⟩, ⟨2,0,-361302⟩, ⟨2,1,238959⟩, ⟨2,2,27352⟩, ⟨3,0,34716⟩, ⟨3,1,-51285⟩], [⟨0,0,-12558⟩, ⟨0,1,-62790⟩, ⟨0,2,68174⟩, ⟨1,0,436770⟩, ⟨1,1,-200108⟩, ⟨1,2,-54704⟩, ⟨2,0,-383778⟩, ⟨2,1,277192⟩, ⟨3,0,72588⟩, ⟨3,1,-54704⟩], [⟨0,0,-226044⟩, ⟨0,1,207207⟩, ⟨0,2,-46020⟩, ⟨0,3,-3419⟩, ⟨1,0,-420693⟩, ⟨1,1,142266⟩, ⟨1,2,36129⟩, ⟨2,0,264477⟩, ⟨2,1,-155428⟩, ⟨2,2,-3419⟩, ⟨3,0,-36294⟩, ⟨3,1,27352⟩]⟩,
  LabelExclusion.constant ⟨50, [Guard.triangle 6], [⟨0,0,25⟩, ⟨1,0,7⟩, ⟨1,1,-7⟩, ⟨2,0,2⟩, ⟨3,0,-2⟩, ⟨3,1,2⟩, ⟨4,0,-2⟩], [⟨0,0,10⟩, ⟨0,1,4⟩, ⟨1,0,-26⟩, ⟨1,1,-10⟩, ⟨2,0,24⟩, ⟨2,1,-4⟩, ⟨3,0,16⟩, ⟨4,0,-4⟩], [⟨0,1,5⟩, ⟨1,1,5⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.circle 1], [⟨1,1,4⟩, ⟨2,0,-2⟩], [⟨0,1,-16⟩, ⟨0,2,4⟩, ⟨1,0,4⟩], [⟨0,0,-2⟩, ⟨1,0,-1⟩]⟩,
  LabelExclusion.constant ⟨224, [Guard.triangle 0], [⟨2,0,-112⟩, ⟨3,0,72⟩], [⟨0,0,224⟩, ⟨1,0,24⟩, ⟨1,1,-112⟩, ⟨2,0,-108⟩, ⟨2,1,72⟩], [⟨0,0,100⟩, ⟨1,0,119⟩, ⟨2,0,-36⟩]⟩]

private def exclusionRow7 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨96, [Guard.triangle 0], [⟨0,0,64⟩, ⟨1,0,64⟩, ⟨2,0,-204⟩, ⟨3,0,90⟩], [⟨0,0,96⟩, ⟨0,1,-32⟩, ⟨1,0,152⟩, ⟨1,1,-56⟩, ⟨2,0,-212⟩, ⟨2,1,60⟩, ⟨3,0,20⟩], [⟨0,0,-60⟩, ⟨1,0,123⟩, ⟨2,0,-7⟩, ⟨3,0,-5⟩]⟩,
  LabelExclusion.constant ⟨250, [], [⟨0,0,56⟩, ⟨1,0,144⟩, ⟨2,0,101⟩, ⟨3,0,-6⟩, ⟨4,0,-19⟩], [⟨0,0,-224⟩, ⟨0,1,112⟩, ⟨1,0,-800⟩, ⟨1,1,176⟩, ⟨2,0,-196⟩, ⟨2,1,26⟩, ⟨3,0,292⟩, ⟨3,1,-38⟩, ⟨4,0,-38⟩], [⟨0,0,-125⟩, ⟨1,0,-26⟩, ⟨2,0,218⟩, ⟨3,0,-127⟩, ⟨4,0,19⟩]⟩,
  LabelExclusion.constant ⟨100, [], [⟨0,0,50⟩, ⟨1,0,-461⟩, ⟨1,1,-173⟩, ⟨2,0,544⟩, ⟨2,1,-8⟩, ⟨3,0,-560⟩, ⟨3,1,165⟩, ⟨4,0,75⟩], [⟨0,0,-254⟩, ⟨0,1,100⟩, ⟨1,0,1112⟩, ⟨1,1,1054⟩, ⟨1,2,-346⟩, ⟨2,0,520⟩, ⟨2,1,-1600⟩, ⟨2,2,330⟩, ⟨3,0,-150⟩, ⟨3,1,150⟩], [⟨0,0,-50⟩, ⟨1,0,-354⟩, ⟨1,1,173⟩, ⟨2,0,635⟩, ⟨2,1,-165⟩, ⟨3,0,-75⟩]⟩,
  LabelExclusion.constant ⟨250, [], [⟨0,0,171⟩, ⟨1,0,-66⟩, ⟨2,0,-194⟩, ⟨3,0,144⟩, ⟨4,0,-24⟩], [⟨0,0,380⟩, ⟨0,1,-114⟩, ⟨1,0,18⟩, ⟨1,1,-32⟩, ⟨2,0,-406⟩, ⟨2,1,108⟩, ⟨3,0,144⟩, ⟨3,1,-24⟩, ⟨4,0,-12⟩], [⟨0,0,-125⟩, ⟨1,0,130⟩, ⟨2,0,47⟩, ⟨3,0,-42⟩, ⟨4,0,6⟩]⟩,
  LabelExclusion.constant ⟨2646, [Guard.triangle 0], [⟨0,0,2468⟩, ⟨0,1,-704⟩, ⟨1,0,1420⟩, ⟨1,1,-329⟩, ⟨2,0,1834⟩, ⟨2,1,-223⟩, ⟨3,0,-603⟩, ⟨3,1,219⟩, ⟨4,0,-292⟩], [⟨0,0,-4240⟩, ⟨0,1,1408⟩, ⟨1,0,-1608⟩, ⟨1,1,658⟩, ⟨2,0,-2114⟩, ⟨2,1,446⟩, ⟨3,0,2390⟩, ⟨3,1,-438⟩, ⟨4,0,-292⟩], [⟨1,0,-1052⟩, ⟨2,0,463⟩, ⟨3,0,-342⟩, ⟨4,0,73⟩]⟩,
  LabelExclusion.constant ⟨98, [Guard.triangle 0], [⟨0,0,517⟩, ⟨0,1,-607⟩, ⟨0,2,106⟩, ⟨1,0,612⟩, ⟨1,1,-640⟩, ⟨1,2,118⟩, ⟨2,0,812⟩, ⟨2,1,6⟩, ⟨2,2,-52⟩, ⟨3,0,-432⟩, ⟨3,1,104⟩], [⟨0,0,-696⟩, ⟨0,1,982⟩, ⟨0,2,-212⟩, ⟨1,0,-1056⟩, ⟨1,1,1196⟩, ⟨1,2,-236⟩, ⟨2,0,648⟩, ⟨2,1,-588⟩, ⟨2,2,104⟩], [⟨1,0,-892⟩, ⟨1,1,222⟩, ⟨2,0,216⟩, ⟨2,1,-52⟩]⟩,
  LabelExclusion.constant ⟨882, [Guard.triangle 0], [⟨0,0,-718⟩, ⟨0,1,1306⟩, ⟨1,0,-1166⟩, ⟨1,1,83⟩, ⟨2,0,-3463⟩, ⟨2,1,-1826⟩, ⟨3,0,5766⟩, ⟨3,1,670⟩, ⟨4,0,-1742⟩], [⟨0,0,6008⟩, ⟨0,1,-2612⟩, ⟨1,0,-328⟩, ⟨1,1,-166⟩, ⟨2,0,-11316⟩, ⟨2,1,3652⟩, ⟨3,0,5856⟩, ⟨3,1,-1340⟩, ⟨4,0,-536⟩], [⟨1,0,4244⟩, ⟨2,0,-2173⟩, ⟨3,0,-258⟩, ⟨4,0,134⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,-15⟩, ⟨0,1,16⟩, ⟨0,2,-4⟩, ⟨1,0,4⟩], [⟨0,1,-40⟩, ⟨0,2,26⟩, ⟨0,3,-4⟩], [⟨0,0,-4⟩, ⟨0,1,20⟩, ⟨0,2,-13⟩, ⟨0,3,2⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,4⟩, ⟨1,0,-4⟩, ⟨2,0,1⟩], [⟨0,0,16⟩, ⟨0,1,-4⟩, ⟨1,0,-14⟩, ⟨1,1,2⟩, ⟨2,0,2⟩], [⟨0,0,-4⟩, ⟨1,0,5⟩, ⟨2,0,-1⟩]⟩,
  LabelExclusion.constant ⟨8, [Guard.triangle 0], [⟨0,0,-6⟩, ⟨0,1,15⟩, ⟨0,2,-5⟩, ⟨1,0,2⟩, ⟨1,1,1⟩, ⟨1,2,1⟩, ⟨2,0,-5⟩, ⟨2,1,6⟩, ⟨2,2,-1⟩], [⟨0,0,-8⟩, ⟨0,1,-20⟩, ⟨0,2,10⟩, ⟨1,0,-4⟩, ⟨1,1,-2⟩, ⟨1,2,-2⟩, ⟨2,0,12⟩, ⟨2,1,-12⟩, ⟨2,2,2⟩, ⟨3,0,-2⟩, ⟨3,1,2⟩], [⟨1,0,10⟩, ⟨1,1,-5⟩, ⟨2,0,-6⟩, ⟨2,1,5⟩, ⟨3,0,1⟩, ⟨3,1,-1⟩]⟩,
  LabelExclusion.constant ⟨32, [Guard.triangle 6], [⟨0,0,8⟩, ⟨0,1,-26⟩, ⟨1,0,52⟩, ⟨1,1,-10⟩, ⟨2,0,4⟩, ⟨2,1,3⟩, ⟨3,0,-3⟩], [⟨0,0,16⟩, ⟨0,1,52⟩, ⟨1,0,-58⟩, ⟨1,1,20⟩, ⟨2,0,12⟩, ⟨2,1,-6⟩], [⟨1,0,-16⟩, ⟨2,0,3⟩]⟩,
  LabelExclusion.constant ⟨32, [Guard.triangle 6], [⟨0,0,16⟩, ⟨0,1,4⟩, ⟨0,2,11⟩, ⟨1,1,-19⟩, ⟨1,2,-10⟩, ⟨2,1,15⟩], [⟨0,1,44⟩, ⟨0,2,-22⟩, ⟨1,1,-76⟩, ⟨1,2,20⟩, ⟨2,1,10⟩], [⟨1,1,18⟩, ⟨2,1,-5⟩]⟩,
  LabelExclusion.constant ⟨162, [Guard.triangle 0], [⟨0,0,96⟩, ⟨0,1,12⟩, ⟨1,0,-119⟩, ⟨1,1,4⟩, ⟨2,0,79⟩, ⟨2,1,-16⟩, ⟨3,0,4⟩], [⟨0,0,-240⟩, ⟨0,1,-12⟩, ⟨1,0,186⟩, ⟨1,1,-4⟩, ⟨2,0,-124⟩, ⟨2,1,16⟩, ⟨3,0,16⟩], [⟨0,0,156⟩, ⟨1,0,-75⟩, ⟨2,0,25⟩, ⟨3,0,-4⟩]⟩,
  LabelExclusion.constant ⟨54, [Guard.triangle 0], [⟨0,0,204⟩, ⟨0,1,-104⟩, ⟨1,0,-65⟩, ⟨1,1,144⟩, ⟨2,0,-104⟩, ⟨2,1,-40⟩, ⟨3,0,40⟩], [⟨0,0,-200⟩, ⟨0,1,104⟩, ⟨1,0,206⟩, ⟨1,1,-144⟩, ⟨2,0,-60⟩, ⟨2,1,40⟩], [⟨0,0,-108⟩, ⟨1,0,107⟩, ⟨2,0,-20⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 0], [⟨0,0,100⟩, ⟨0,1,-88⟩, ⟨1,0,35⟩, ⟨1,1,94⟩, ⟨2,0,-93⟩, ⟨2,1,-24⟩, ⟨3,0,27⟩], [⟨0,0,-328⟩, ⟨0,1,88⟩, ⟨1,0,378⟩, ⟨1,1,-94⟩, ⟨2,0,-134⟩, ⟨2,1,24⟩, ⟨3,0,12⟩], [⟨0,0,-36⟩, ⟨1,0,1⟩, ⟨2,0,14⟩, ⟨3,0,-3⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 0], [⟨0,0,16⟩, ⟨0,1,-4⟩, ⟨1,0,-15⟩, ⟨1,1,10⟩, ⟨2,0,6⟩, ⟨2,1,-4⟩], [⟨0,0,18⟩, ⟨0,1,-24⟩, ⟨0,2,8⟩, ⟨1,0,-6⟩, ⟨1,1,10⟩, ⟨1,2,-4⟩], [⟨0,0,12⟩, ⟨0,1,-8⟩]⟩]

private def exclusionRow8 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨4, [Guard.triangle 6], [⟨1,0,5⟩, ⟨2,0,-1⟩], [⟨0,0,-2⟩, ⟨0,1,6⟩, ⟨1,0,2⟩, ⟨1,1,-2⟩], [⟨0,1,-2⟩]⟩,
  LabelExclusion.constant ⟨8, [Guard.triangle 0], [⟨0,0,-2⟩, ⟨0,1,10⟩, ⟨0,2,5⟩, ⟨0,3,-2⟩, ⟨1,0,-2⟩, ⟨1,1,-2⟩], [⟨0,0,12⟩, ⟨0,1,22⟩, ⟨0,2,6⟩, ⟨0,3,-4⟩, ⟨1,0,-4⟩, ⟨1,1,-4⟩], [⟨0,1,-4⟩, ⟨0,2,-4⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 6], [], [⟨0,0,3⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,8⟩, ⟨0,1,-2⟩], [⟨0,0,-4⟩, ⟨0,1,1⟩]⟩,
  LabelExclusion.constant ⟨10, [Guard.triangle 6], [⟨0,0,9⟩, ⟨0,1,-6⟩], [⟨0,1,-54⟩, ⟨0,2,12⟩, ⟨1,0,12⟩], [⟨0,1,12⟩]⟩,
  LabelExclusion.constant ⟨54, [Guard.triangle 3], [⟨0,0,37⟩, ⟨0,1,-4⟩, ⟨1,0,4⟩], [⟨0,0,2⟩, ⟨0,1,4⟩, ⟨1,0,-8⟩], [⟨1,0,4⟩]⟩,
  LabelExclusion.constant ⟨90, [], [⟨0,0,67⟩, ⟨0,1,31⟩, ⟨0,2,-62⟩, ⟨0,3,12⟩, ⟨1,0,-56⟩, ⟨1,1,68⟩, ⟨1,2,-12⟩], [⟨0,0,-78⟩, ⟨0,1,66⟩, ⟨0,2,-18⟩, ⟨1,0,56⟩, ⟨1,1,-68⟩, ⟨1,2,12⟩], [⟨0,0,-45⟩, ⟨0,1,27⟩]⟩,
  LabelExclusion.constant ⟨66, [Guard.triangle 3], [⟨0,0,47⟩, ⟨0,1,4⟩, ⟨1,0,-4⟩], [⟨0,0,-10⟩, ⟨0,1,8⟩, ⟨1,0,-4⟩], [⟨0,1,4⟩]⟩,
  LabelExclusion.constant ⟨108, [], [⟨0,0,31⟩, ⟨0,1,-19⟩, ⟨0,2,2⟩, ⟨0,3,4⟩, ⟨1,0,-4⟩, ⟨1,1,8⟩, ⟨1,2,-4⟩], [⟨0,0,-50⟩, ⟨0,1,28⟩, ⟨0,2,-14⟩, ⟨1,0,4⟩, ⟨1,1,-8⟩, ⟨1,2,4⟩], [⟨0,0,15⟩, ⟨0,1,3⟩]⟩,
  LabelExclusion.constant ⟨27, [], [⟨0,0,53⟩, ⟨0,1,4⟩, ⟨0,2,-38⟩, ⟨0,3,8⟩, ⟨1,0,-38⟩, ⟨1,1,46⟩, ⟨1,2,-8⟩], [⟨0,0,-49⟩, ⟨0,1,56⟩, ⟨0,2,-16⟩, ⟨1,0,38⟩, ⟨1,1,-46⟩, ⟨1,2,8⟩], [⟨0,0,-42⟩, ⟨0,1,24⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,101⟩, ⟨0,1,17⟩, ⟨0,2,-1⟩, ⟨1,0,-89⟩, ⟨1,1,-14⟩, ⟨1,2,-5⟩, ⟨2,0,5⟩, ⟨2,1,5⟩], [⟨0,0,-44⟩, ⟨0,1,-42⟩, ⟨0,2,2⟩, ⟨1,0,206⟩, ⟨1,1,-14⟩, ⟨1,2,10⟩, ⟨2,0,-20⟩, ⟨2,1,-20⟩], [⟨0,0,-22⟩, ⟨0,1,1⟩, ⟨1,0,-29⟩, ⟨1,1,6⟩, ⟨2,0,5⟩, ⟨2,1,5⟩]⟩,
  LabelExclusion.constant ⟨54, [], [⟨0,0,-36⟩, ⟨0,1,31⟩, ⟨0,2,-22⟩, ⟨1,0,36⟩, ⟨1,1,77⟩, ⟨1,2,-10⟩, ⟨2,0,-45⟩, ⟨2,1,10⟩], [⟨0,0,-96⟩, ⟨0,1,26⟩, ⟨0,2,44⟩, ⟨1,0,-294⟩, ⟨1,1,-158⟩, ⟨1,2,20⟩, ⟨2,0,180⟩, ⟨2,1,-40⟩], [⟨0,0,57⟩, ⟨0,1,22⟩, ⟨1,0,-24⟩, ⟨1,1,32⟩, ⟨2,0,-45⟩, ⟨2,1,10⟩]⟩,
  LabelExclusion.constant ⟨54, [], [⟨0,0,63⟩, ⟨0,1,-33⟩, ⟨0,2,14⟩, ⟨0,3,-2⟩, ⟨1,0,9⟩, ⟨1,1,-12⟩, ⟨1,2,2⟩], [⟨0,0,-108⟩, ⟨0,1,90⟩, ⟨0,2,-32⟩, ⟨0,3,4⟩, ⟨1,0,-36⟩, ⟨1,1,48⟩, ⟨1,2,-8⟩], [⟨0,0,-36⟩, ⟨0,1,24⟩, ⟨0,2,-4⟩, ⟨1,0,9⟩, ⟨1,1,-12⟩, ⟨1,2,2⟩]⟩,
  LabelExclusion.constant ⟨3, [Guard.circle 3], [⟨0,1,-2⟩, ⟨0,2,-1⟩], [⟨0,1,2⟩, ⟨0,2,1⟩], []⟩,
  LabelExclusion.constant ⟨3, [Guard.circle 3], [⟨0,0,-1⟩, ⟨0,1,-2⟩, ⟨0,2,-1⟩, ⟨1,0,1⟩], [⟨0,0,1⟩, ⟨0,1,2⟩, ⟨0,2,1⟩, ⟨1,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨3, [Guard.circle 3], [⟨0,0,-1⟩, ⟨0,1,-1⟩, ⟨0,2,-1⟩], [⟨0,0,1⟩, ⟨0,1,1⟩, ⟨0,2,1⟩], []⟩]

private def exclusionRow9 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨18, [Guard.aOrder], [⟨0,0,-6⟩], [⟨0,0,4⟩, ⟨0,1,-2⟩, ⟨1,0,2⟩], [⟨0,0,7⟩, ⟨0,1,-1⟩, ⟨1,0,-1⟩]⟩,
  LabelExclusion.constant ⟨9, [Guard.triangle 2], [⟨0,0,7⟩, ⟨0,1,-2⟩, ⟨1,0,2⟩], [⟨0,0,1⟩, ⟨0,1,2⟩, ⟨1,0,-4⟩], [⟨0,0,-3⟩, ⟨0,1,3⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,63⟩, ⟨0,1,-1⟩, ⟨0,2,-10⟩, ⟨1,0,-24⟩, ⟨1,1,10⟩], [⟨0,0,12⟩, ⟨0,1,30⟩, ⟨0,2,-10⟩, ⟨1,0,-6⟩], [⟨0,0,-78⟩, ⟨0,1,16⟩, ⟨0,2,5⟩, ⟨1,0,27⟩, ⟨1,1,-10⟩]⟩,
  LabelExclusion.constant ⟨36, [], [⟨0,0,27⟩, ⟨0,1,3⟩, ⟨0,2,-6⟩, ⟨1,0,-14⟩, ⟨1,1,3⟩, ⟨1,2,2⟩, ⟨2,0,4⟩, ⟨2,1,-2⟩], [⟨0,0,-18⟩, ⟨0,1,12⟩, ⟨0,2,-6⟩, ⟨1,0,16⟩, ⟨1,1,-12⟩, ⟨1,2,2⟩, ⟨2,0,-4⟩, ⟨2,1,2⟩], [⟨0,0,-9⟩, ⟨0,1,-9⟩, ⟨0,2,9⟩, ⟨1,1,6⟩, ⟨1,2,-3⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 8], [⟨0,0,-3⟩], [⟨0,0,-6⟩], [⟨0,0,6⟩]⟩,
  LabelExclusion.constant ⟨90, [], [⟨0,0,84⟩, ⟨0,1,651⟩, ⟨0,2,-108⟩, ⟨1,0,-301⟩, ⟨1,1,-23⟩, ⟨1,2,18⟩, ⟨2,0,86⟩, ⟨2,1,-18⟩], [⟨0,0,-168⟩, ⟨0,1,246⟩, ⟨0,2,-108⟩, ⟨1,0,344⟩, ⟨1,1,-158⟩, ⟨1,2,18⟩, ⟨2,0,-86⟩, ⟨2,1,18⟩], [⟨0,0,-45⟩, ⟨0,1,-612⟩, ⟨0,2,162⟩, ⟨1,1,129⟩, ⟨1,2,-27⟩]⟩,
  LabelExclusion.constant ⟨22, [], [⟨0,0,4⟩], [⟨0,0,-8⟩, ⟨0,1,-6⟩, ⟨1,0,4⟩], [⟨0,0,1⟩, ⟨0,1,3⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,-1⟩], [⟨0,0,-10⟩, ⟨0,1,6⟩, ⟨1,0,2⟩], [⟨0,0,5⟩, ⟨0,1,-3⟩]⟩,
  LabelExclusion.constant ⟨3, [], [⟨0,0,2⟩], [⟨0,0,-7⟩, ⟨1,0,2⟩], []⟩,
  LabelExclusion.constant ⟨108, [], [⟨0,0,26⟩, ⟨0,1,97⟩, ⟨0,2,-28⟩, ⟨1,0,26⟩, ⟨1,1,19⟩, ⟨1,2,-7⟩], [⟨0,0,208⟩, ⟨0,1,-264⟩, ⟨0,2,56⟩, ⟨1,1,-52⟩, ⟨1,2,14⟩, ⟨2,0,-52⟩, ⟨2,1,14⟩], [⟨0,0,24⟩, ⟨0,1,-81⟩, ⟨0,2,84⟩, ⟨1,0,-78⟩, ⟨1,1,-57⟩, ⟨1,2,21⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 1], [⟨0,0,39⟩, ⟨0,1,3⟩, ⟨1,0,-3⟩], [⟨0,0,-4⟩, ⟨0,1,4⟩, ⟨1,0,2⟩], [⟨0,0,-31⟩, ⟨0,1,1⟩, ⟨1,0,4⟩]⟩,
  LabelExclusion.constant ⟨4338, [], [⟨0,0,7578⟩, ⟨0,1,32487⟩, ⟨0,2,1620⟩, ⟨1,0,-12506⟩, ⟨1,1,-3289⟩, ⟨1,2,-108⟩, ⟨2,0,481⟩, ⟨2,1,108⟩], [⟨0,0,10818⟩, ⟨0,1,-15852⟩, ⟨0,2,6480⟩, ⟨1,0,-962⟩, ⟨1,1,-2140⟩, ⟨1,2,-432⟩, ⟨2,0,962⟩, ⟨2,1,216⟩], [⟨0,0,-15156⟩, ⟨0,1,-28899⟩, ⟨0,2,4860⟩, ⟨1,0,12987⟩, ⟨1,1,1473⟩, ⟨1,2,-324⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 1], [⟨0,0,46⟩, ⟨0,1,5⟩, ⟨1,0,-5⟩], [⟨0,0,-8⟩, ⟨0,1,8⟩, ⟨1,0,2⟩], [⟨0,0,-42⟩, ⟨0,1,3⟩, ⟨1,0,6⟩]⟩,
  LabelExclusion.constant ⟨1, [], [⟨0,0,-6⟩], [⟨0,0,-15⟩, ⟨0,1,6⟩, ⟨1,0,6⟩], [⟨0,0,13⟩, ⟨0,1,-6⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,3⟩, ⟨0,1,6⟩, ⟨1,0,-16⟩, ⟨1,1,-4⟩, ⟨2,0,4⟩], [⟨0,0,-12⟩, ⟨0,1,6⟩, ⟨1,0,8⟩, ⟨1,1,-4⟩], [⟨0,0,12⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,15⟩, ⟨0,1,18⟩, ⟨0,2,-6⟩, ⟨1,0,-40⟩, ⟨1,1,-6⟩, ⟨1,2,4⟩, ⟨2,0,16⟩, ⟨2,1,-4⟩], [⟨0,0,-72⟩, ⟨0,1,42⟩, ⟨0,2,-6⟩, ⟨1,0,56⟩, ⟨1,1,-30⟩, ⟨1,2,4⟩], [⟨0,0,12⟩, ⟨0,1,-3⟩]⟩]

private def exclusionRow10 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨9, [], [⟨0,0,-27⟩, ⟨0,1,78⟩, ⟨0,2,-24⟩, ⟨1,0,-120⟩, ⟨1,1,2⟩, ⟨1,2,8⟩, ⟨2,0,30⟩, ⟨2,1,-8⟩], [⟨0,0,-135⟩, ⟨0,1,126⟩, ⟨0,2,-24⟩, ⟨1,0,60⟩, ⟨1,1,-46⟩, ⟨1,2,8⟩], [⟨0,0,90⟩, ⟨0,1,-24⟩]⟩,
  LabelExclusion.constant ⟨54, [], [⟨0,0,71⟩, ⟨0,1,-3⟩, ⟨0,2,-2⟩, ⟨1,0,-21⟩, ⟨1,1,-1⟩, ⟨1,2,2⟩, ⟨2,0,7⟩, ⟨2,1,-2⟩], [⟨0,0,-112⟩, ⟨0,1,46⟩, ⟨0,2,-4⟩, ⟨1,0,70⟩, ⟨1,1,-34⟩, ⟨1,2,4⟩], [⟨0,0,-42⟩, ⟨0,1,12⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 2], [], [⟨0,1,1⟩], [⟨0,0,2⟩]⟩,
  LabelExclusion.constant ⟨16, [Guard.triangle 0], [⟨0,0,24⟩, ⟨0,1,-24⟩, ⟨0,2,4⟩, ⟨1,0,-14⟩, ⟨1,1,2⟩, ⟨1,2,1⟩, ⟨2,0,2⟩, ⟨2,1,1⟩], [⟨0,0,16⟩, ⟨0,1,-32⟩, ⟨0,2,8⟩, ⟨1,0,-20⟩, ⟨1,1,8⟩, ⟨1,2,2⟩, ⟨2,0,4⟩, ⟨2,1,2⟩], [⟨0,0,16⟩, ⟨1,0,-4⟩, ⟨1,1,4⟩, ⟨2,0,2⟩, ⟨2,1,1⟩]⟩,
  LabelExclusion.constant ⟨72, [Guard.triangle 0], [⟨0,0,20⟩, ⟨0,1,-16⟩, ⟨1,0,-5⟩, ⟨1,1,18⟩], [⟨0,0,72⟩, ⟨0,1,-152⟩, ⟨0,2,32⟩, ⟨1,0,-30⟩, ⟨1,1,168⟩, ⟨1,2,-36⟩, ⟨2,0,10⟩, ⟨2,1,-36⟩], [⟨0,0,112⟩, ⟨0,1,-64⟩, ⟨1,0,-96⟩, ⟨1,1,104⟩, ⟨2,0,10⟩, ⟨2,1,-36⟩]⟩,
  LabelExclusion.constant ⟨512, [], [⟨0,0,1670⟩, ⟨0,1,-316⟩, ⟨1,0,-1617⟩, ⟨1,1,-60⟩, ⟨1,2,882⟩, ⟨1,3,-252⟩, ⟨2,0,270⟩, ⟨2,1,27⟩, ⟨2,2,-189⟩, ⟨2,3,54⟩], [⟨0,0,-1580⟩, ⟨0,1,632⟩, ⟨1,0,1590⟩, ⟨1,1,3144⟩, ⟨1,2,-2772⟩, ⟨1,3,504⟩, ⟨2,0,-270⟩, ⟨2,1,-702⟩, ⟨2,2,594⟩, ⟨2,3,-108⟩], [⟨0,0,-256⟩, ⟨1,0,-2092⟩, ⟨1,1,3024⟩, ⟨1,2,-1008⟩, ⟨2,0,1092⟩, ⟨2,1,-2160⟩, ⟨2,2,720⟩, ⟨3,0,-135⟩, ⟨3,1,324⟩, ⟨3,2,-108⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 6], [⟨0,0,1⟩, ⟨0,1,2⟩, ⟨1,0,-2⟩], [⟨1,0,8⟩, ⟨1,1,-2⟩, ⟨2,0,6⟩, ⟨3,0,-2⟩], [⟨2,0,2⟩, ⟨3,0,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.circle 3], [⟨0,0,4⟩, ⟨0,2,-1⟩], [⟨0,0,-8⟩, ⟨0,2,2⟩], [⟨0,0,-4⟩, ⟨0,2,1⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.aOrder, Guard.triangle 0], [⟨1,0,2⟩], [⟨0,0,-6⟩, ⟨0,1,2⟩], [⟨0,0,-1⟩, ⟨0,1,1⟩, ⟨1,0,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [], [⟨0,0,2⟩], [⟨0,0,1⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 2], [⟨0,0,3⟩, ⟨1,0,2⟩, ⟨2,0,-1⟩], [⟨0,0,12⟩, ⟨1,0,-2⟩, ⟨1,1,-4⟩, ⟨2,0,-2⟩, ⟨2,1,2⟩], [⟨1,1,-2⟩, ⟨2,1,1⟩]⟩,
  LabelExclusion.constant ⟨111119688, [], [⟨0,0,-362890210⟩, ⟨0,1,883300848⟩, ⟨1,0,444620330⟩, ⟨1,1,-441245900⟩, ⟨1,2,36804202⟩, ⟨2,0,2177560349⟩, ⟨2,1,-814785466⟩, ⟨2,2,-4138904⟩, ⟨3,0,1442610373⟩, ⟨3,1,203521996⟩, ⟨3,2,-30517247⟩, ⟨4,0,-104362378⟩, ⟨4,1,140471348⟩, ⟨5,0,-146758821⟩], [⟨0,0,-851648456⟩, ⟨0,1,41956012⟩, ⟨0,2,883300848⟩, ⟨1,0,852020172⟩, ⟨1,1,-782313056⟩, ⟨1,2,121491516⟩, ⟨2,0,828079444⟩, ⟨2,1,-175118146⟩, ⟨2,2,-757247352⟩, ⟨3,0,-595732836⟩, ⟨3,1,428632958⟩, ⟨3,2,-183103482⟩, ⟨4,0,-195678428⟩, ⟨4,1,293517642⟩], [⟨0,0,-55559844⟩, ⟨0,1,-851648456⟩, ⟨0,2,404846222⟩, ⟨1,0,-111119688⟩, ⟨1,1,85428256⟩, ⟨1,2,64884662⟩, ⟨2,0,-1869976444⟩, ⟨2,1,760624158⟩, ⟨2,2,-348106429⟩, ⟨3,0,-1498968628⟩, ⟨3,1,-148053406⟩, ⟨3,2,-91551741⟩, ⟨4,0,102187990⟩, ⟨4,1,85724327⟩, ⟨5,0,97839214⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,1⟩, ⟨0,1,-2⟩, ⟨1,1,1⟩], [⟨0,0,4⟩, ⟨1,0,-2⟩], [⟨0,0,-1⟩, ⟨0,1,2⟩, ⟨1,1,-1⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 6], [⟨0,0,3⟩, ⟨0,1,-3⟩], [⟨0,1,6⟩, ⟨1,0,-6⟩], [⟨1,0,3⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,3⟩, ⟨0,1,3⟩, ⟨1,0,-15⟩, ⟨2,0,3⟩], [⟨0,1,-6⟩, ⟨1,0,30⟩, ⟨2,0,-6⟩], [⟨1,0,6⟩, ⟨2,0,-3⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 2], [⟨0,0,-1⟩, ⟨1,0,3⟩, ⟨2,0,-1⟩], [⟨0,0,-8⟩, ⟨0,1,4⟩, ⟨1,0,-10⟩, ⟨1,1,2⟩, ⟨2,0,2⟩], [⟨0,0,3⟩, ⟨0,1,2⟩, ⟨1,1,1⟩]⟩]

private def exclusionRow11 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨1566, [Guard.aOrder], [⟨0,0,-1860⟩, ⟨0,1,568⟩, ⟨1,0,-7842⟩, ⟨1,1,5931⟩, ⟨1,2,-2514⟩, ⟨1,3,912⟩, ⟨2,0,-2024⟩, ⟨2,1,17236⟩, ⟨2,2,-10879⟩, ⟨2,3,1020⟩, ⟨3,0,-7856⟩, ⟨3,1,2211⟩, ⟨3,2,1054⟩, ⟨4,0,1564⟩, ⟨4,1,-782⟩], [⟨0,0,462⟩, ⟨0,1,1910⟩, ⟨0,2,344⟩, ⟨1,0,4186⟩, ⟨1,1,2638⟩, ⟨1,2,-4952⟩, ⟨2,0,1904⟩, ⟨2,1,17678⟩, ⟨2,2,-2040⟩, ⟨3,0,-8638⟩, ⟨3,1,-2108⟩, ⟨4,0,1564⟩], [⟨0,0,783⟩, ⟨0,1,-462⟩, ⟨0,2,-50⟩, ⟨0,3,-912⟩, ⟨1,0,1707⟩, ⟨1,1,-5688⟩, ⟨1,2,8991⟩, ⟨1,3,-1020⟩, ⟨2,0,9848⟩, ⟨2,1,-30656⟩, ⟨2,2,1094⟩, ⟨3,0,11563⟩, ⟨3,1,12783⟩, ⟨3,2,-1020⟩, ⟨4,0,-6665⟩, ⟨4,1,-1054⟩, ⟨5,0,782⟩]⟩,
  LabelExclusion.constant ⟨918, [], [⟨0,0,3522⟩, ⟨0,1,3212⟩, ⟨1,0,-11364⟩, ⟨1,1,-5720⟩, ⟨2,0,5580⟩, ⟨2,1,2640⟩, ⟨3,0,-744⟩, ⟨3,1,-352⟩], [⟨0,0,3114⟩, ⟨0,1,-1916⟩, ⟨0,2,-3212⟩, ⟨1,0,-6156⟩, ⟨1,1,5876⟩, ⟨1,2,4664⟩, ⟨2,0,4092⟩, ⟨2,1,-2900⟩, ⟨2,2,-2288⟩, ⟨3,0,-744⟩, ⟨3,1,392⟩, ⟨3,2,352⟩], [⟨0,0,-459⟩, ⟨0,1,-3114⟩, ⟨0,2,-1606⟩, ⟨1,0,5310⟩, ⟨1,1,7250⟩, ⟨1,2,2332⟩, ⟨2,0,-2790⟩, ⟨2,1,-3738⟩, ⟨2,2,-1144⟩, ⟨3,0,372⟩, ⟨3,1,548⟩, ⟨3,2,176⟩]⟩,
  LabelExclusion.constant ⟨1800, [Guard.triangle 0], [⟨1,0,4182⟩, ⟨1,1,76625⟩, ⟨1,2,-33729⟩, ⟨2,0,-17979⟩, ⟨2,1,-14791⟩, ⟨2,2,8456⟩, ⟨3,0,4077⟩, ⟨3,1,-1057⟩], [⟨0,0,-12600⟩, ⟨0,1,-2400⟩, ⟨0,2,-31450⟩, ⟨0,3,-4228⟩, ⟨1,0,34224⟩, ⟨1,1,129352⟩, ⟨1,2,26906⟩, ⟨2,0,-23448⟩, ⟨2,1,-73154⟩, ⟨2,2,-4228⟩, ⟨3,0,3624⟩, ⟨3,1,10570⟩], [⟨0,0,-3600⟩, ⟨0,1,11700⟩, ⟨0,2,20118⟩, ⟨0,3,-2114⟩, ⟨1,0,-31500⟩, ⟨1,1,-82608⟩, ⟨1,2,2883⟩, ⟨2,0,15348⟩, ⟨2,1,41258⟩, ⟨2,2,-2114⟩, ⟨3,0,-1812⟩, ⟨3,1,-5285⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,6⟩, ⟨0,1,-1⟩, ⟨1,0,-1⟩], [⟨0,0,-2⟩], [⟨0,0,-4⟩, ⟨0,1,1⟩, ⟨1,0,1⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 6], [], [⟨0,0,3⟩], []⟩,
  LabelExclusion.constant ⟨14, [], [⟨0,0,9⟩, ⟨0,2,-16⟩], [⟨0,0,-22⟩, ⟨0,1,-24⟩, ⟨1,0,4⟩, ⟨1,1,16⟩], [⟨0,0,-7⟩, ⟨0,1,8⟩, ⟨0,2,16⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,-27⟩, ⟨0,1,-19⟩, ⟨0,2,52⟩, ⟨0,3,-7⟩, ⟨1,0,-14⟩, ⟨1,1,-39⟩, ⟨1,2,-31⟩, ⟨1,3,7⟩, ⟨2,0,56⟩, ⟨2,1,96⟩, ⟨2,2,-28⟩, ⟨3,0,-14⟩, ⟨3,1,-24⟩, ⟨3,2,7⟩], [⟨0,0,28⟩, ⟨0,1,48⟩, ⟨0,2,-14⟩], [⟨0,0,-1⟩, ⟨0,1,-30⟩, ⟨0,2,-52⟩, ⟨0,3,7⟩, ⟨1,0,56⟩, ⟨1,1,111⟩, ⟨1,2,10⟩, ⟨1,3,-7⟩, ⟨2,0,-70⟩, ⟨2,1,-120⟩, ⟨2,2,35⟩, ⟨3,0,14⟩, ⟨3,1,24⟩, ⟨3,2,-7⟩]⟩,
  LabelExclusion.constant ⟨20, [], [⟨0,0,74⟩, ⟨0,1,-84⟩, ⟨1,0,192⟩, ⟨1,1,34⟩, ⟨2,0,-113⟩, ⟨2,1,-3⟩, ⟨3,0,15⟩], [⟨0,0,-136⟩, ⟨0,1,32⟩, ⟨1,0,30⟩, ⟨1,1,-6⟩], [⟨0,0,-10⟩, ⟨0,1,116⟩, ⟨1,0,-272⟩, ⟨1,1,-40⟩, ⟨2,0,128⟩, ⟨2,1,3⟩, ⟨3,0,-15⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 0], [⟨0,0,16⟩, ⟨0,1,-2⟩, ⟨1,0,-3⟩], [⟨0,0,4⟩, ⟨1,0,-2⟩], [⟨0,0,-12⟩, ⟨0,1,2⟩, ⟨1,0,3⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,6⟩, ⟨0,1,1⟩, ⟨1,0,-6⟩, ⟨2,0,1⟩], [⟨0,0,2⟩], [⟨0,0,-4⟩, ⟨0,1,-1⟩, ⟨1,0,5⟩, ⟨2,0,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨1,0,-1⟩], [⟨0,0,32⟩, ⟨0,1,-2⟩, ⟨1,0,-8⟩], [⟨0,0,-4⟩, ⟨1,0,1⟩]⟩,
  LabelExclusion.constant ⟨216, [Guard.triangle 0], [⟨0,0,-812⟩, ⟨0,1,-48⟩, ⟨1,0,623⟩, ⟨1,1,80⟩, ⟨2,0,-145⟩, ⟨2,1,-10⟩, ⟨3,0,10⟩], [⟨0,0,216⟩, ⟨0,1,-48⟩, ⟨1,0,-190⟩, ⟨1,1,80⟩, ⟨2,0,20⟩, ⟨2,1,-10⟩], [⟨0,0,836⟩, ⟨1,0,-469⟩, ⟨2,0,85⟩, ⟨3,0,-5⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,-1⟩, ⟨1,0,4⟩, ⟨1,1,8⟩, ⟨2,0,-4⟩], [⟨0,0,-2⟩, ⟨1,0,-4⟩], [⟨0,0,-1⟩, ⟨1,1,-8⟩, ⟨2,0,4⟩]⟩,
  LabelExclusion.constant ⟨14, [], [⟨0,0,-5⟩, ⟨0,1,-12⟩, ⟨1,0,-3⟩, ⟨1,1,27⟩, ⟨1,2,-6⟩, ⟨2,0,1⟩, ⟨2,1,-7⟩, ⟨2,2,2⟩], [⟨0,0,48⟩, ⟨0,1,-12⟩, ⟨1,0,-18⟩, ⟨1,1,4⟩], [⟨0,0,-7⟩, ⟨1,0,34⟩, ⟨1,1,-29⟩, ⟨1,2,6⟩, ⟨2,0,-10⟩, ⟨2,1,9⟩, ⟨2,2,-2⟩]⟩,
  LabelExclusion.constant ⟨4, [], [⟨0,0,4⟩, ⟨1,0,-1⟩, ⟨1,1,-7⟩, ⟨2,0,2⟩, ⟨2,1,3⟩, ⟨3,0,-1⟩], [⟨0,0,2⟩, ⟨1,0,4⟩, ⟨2,0,-2⟩], [⟨0,0,-2⟩, ⟨1,0,-2⟩, ⟨1,1,7⟩, ⟨2,0,-1⟩, ⟨2,1,-3⟩, ⟨3,0,1⟩]⟩,
  LabelExclusion.constant ⟨162, [Guard.triangle 0], [⟨0,0,411⟩, ⟨0,1,-249⟩, ⟨1,0,418⟩, ⟨1,1,-166⟩, ⟨1,2,-57⟩, ⟨2,0,-60⟩, ⟨2,1,85⟩, ⟨3,0,-32⟩, ⟨3,1,10⟩, ⟨3,2,3⟩, ⟨4,1,-4⟩, ⟨5,0,1⟩], [⟨0,0,-240⟩, ⟨0,1,186⟩, ⟨1,0,-238⟩, ⟨1,1,352⟩, ⟨1,2,-114⟩, ⟨2,0,-20⟩, ⟨2,1,20⟩, ⟨3,0,10⟩, ⟨3,1,-16⟩, ⟨3,2,6⟩, ⟨4,0,2⟩, ⟨4,1,-2⟩], [⟨1,0,-564⟩, ⟨1,1,342⟩, ⟨2,0,32⟩, ⟨2,1,-57⟩, ⟨3,0,37⟩, ⟨3,1,-18⟩, ⟨4,0,1⟩, ⟨4,1,3⟩, ⟨5,0,-1⟩]⟩]

private def exclusionRow12 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨18, [Guard.triangle 0], [⟨0,0,14⟩, ⟨0,1,-2⟩, ⟨1,1,30⟩, ⟨2,0,-59⟩, ⟨2,1,-12⟩, ⟨3,0,18⟩], [⟨0,0,-4⟩, ⟨0,1,-2⟩, ⟨1,0,-74⟩, ⟨1,1,30⟩, ⟨2,0,28⟩, ⟨2,1,-12⟩], [⟨0,0,-28⟩, ⟨1,0,79⟩, ⟨2,0,-18⟩]⟩,
  LabelExclusion.constant ⟨10, [Guard.triangle 0], [⟨0,0,100⟩, ⟨0,1,88⟩, ⟨1,0,-187⟩, ⟨1,1,-56⟩, ⟨2,0,82⟩, ⟨2,1,8⟩, ⟨3,0,-10⟩], [⟨0,0,-360⟩, ⟨0,1,88⟩, ⟨1,0,270⟩, ⟨1,1,-56⟩, ⟨2,0,-60⟩, ⟨2,1,8⟩, ⟨3,0,4⟩], [⟨0,0,-20⟩, ⟨1,0,45⟩, ⟨2,0,-18⟩, ⟨3,0,2⟩]⟩,
  LabelExclusion.constant ⟨54, [Guard.triangle 0], [⟨0,0,124⟩, ⟨0,1,-88⟩, ⟨1,0,-3⟩, ⟨1,1,82⟩, ⟨2,0,-72⟩, ⟨2,1,-20⟩, ⟨3,0,20⟩], [⟨0,0,280⟩, ⟨0,1,-88⟩, ⟨1,0,-230⟩, ⟨1,1,82⟩, ⟨2,0,50⟩, ⟨2,1,-20⟩], [⟨0,0,-108⟩, ⟨1,0,107⟩, ⟨2,0,-20⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 0], [⟨0,0,5⟩, ⟨0,1,2⟩, ⟨1,0,-8⟩], [⟨0,0,-6⟩, ⟨0,1,4⟩, ⟨1,0,-8⟩], [⟨1,0,8⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.bOrder, Guard.triangle 0], [⟨0,0,-2⟩, ⟨0,1,-1⟩, ⟨1,0,2⟩], [⟨0,0,10⟩, ⟨0,1,-2⟩], [⟨1,0,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder, Guard.triangle 0], [⟨0,0,1⟩, ⟨0,1,1⟩, ⟨1,0,-1⟩], [⟨0,0,-6⟩, ⟨0,1,2⟩], []⟩,
  LabelExclusion.constant ⟨12, [Guard.triangle 0], [⟨0,0,36⟩, ⟨1,0,-12⟩, ⟨2,0,1⟩], [⟨0,0,-16⟩, ⟨0,1,12⟩, ⟨1,0,2⟩, ⟨1,1,-2⟩], [⟨0,0,-24⟩, ⟨1,0,10⟩, ⟨2,0,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,3⟩, ⟨0,1,-5⟩, ⟨0,2,2⟩, ⟨1,0,-2⟩], [⟨0,0,4⟩, ⟨0,1,-6⟩, ⟨0,2,4⟩, ⟨1,0,-4⟩], [⟨0,1,4⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,2⟩, ⟨1,0,-1⟩], [⟨0,0,-4⟩, ⟨0,1,4⟩, ⟨1,0,-2⟩], [⟨0,1,1⟩]⟩,
  LabelExclusion.constant ⟨22, [Guard.triangle 0], [⟨0,0,53⟩, ⟨0,1,-78⟩, ⟨0,2,24⟩, ⟨1,0,77⟩, ⟨1,1,-6⟩, ⟨1,2,-8⟩, ⟨2,0,-22⟩, ⟨2,1,8⟩], [⟨0,0,44⟩, ⟨0,1,-82⟩, ⟨0,2,24⟩, ⟨1,0,-22⟩, ⟨1,1,30⟩, ⟨1,2,-8⟩], [⟨0,0,-44⟩, ⟨0,1,16⟩]⟩,
  LabelExclusion.constant ⟨9, [Guard.triangle 5], [⟨0,0,4⟩, ⟨0,1,3⟩], [⟨0,0,-4⟩, ⟨0,1,3⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 9], [⟨0,1,1⟩], [⟨0,1,-1⟩], []⟩,
  LabelExclusion.constant ⟨3, [], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 3], [⟨0,0,5⟩], [⟨0,0,-2⟩], []⟩,
  LabelExclusion.constant ⟨9, [], [⟨0,0,2⟩, ⟨0,1,-8⟩, ⟨1,0,2⟩], [⟨0,0,-5⟩, ⟨0,1,6⟩], [⟨0,0,6⟩]⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,14⟩, ⟨0,1,-2⟩, ⟨1,0,-1⟩], [⟨0,0,-20⟩, ⟨0,1,6⟩], [⟨0,0,-3⟩]⟩]

private def exclusionRow13 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨18, [Guard.circle 0], [⟨0,0,-10⟩, ⟨0,1,-1⟩, ⟨1,0,-2⟩], [⟨0,0,4⟩, ⟨0,1,-2⟩, ⟨1,0,-4⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 4], [⟨0,0,2⟩, ⟨0,1,3⟩, ⟨0,2,-3⟩, ⟨1,0,-4⟩, ⟨1,1,-2⟩, ⟨2,0,-3⟩], [⟨0,0,-2⟩, ⟨1,0,4⟩, ⟨1,1,8⟩], []⟩,
  LabelExclusion.constant ⟨6, [], [⟨0,0,5⟩, ⟨0,1,-2⟩, ⟨1,0,-1⟩], [⟨0,0,-2⟩, ⟨0,1,-2⟩, ⟨1,0,2⟩], [⟨0,0,-3⟩, ⟨0,1,3⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,-1⟩], [⟨0,0,-2⟩], [⟨0,0,2⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,2⟩], [⟨0,0,-2⟩], [⟨0,0,-1⟩]⟩,
  LabelExclusion.constant ⟨3, [], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 1], [⟨0,0,5⟩], [⟨0,0,-2⟩], []⟩,
  LabelExclusion.constant ⟨3, [Guard.triangle 5], [⟨0,1,-1⟩, ⟨1,0,4⟩], [⟨0,1,1⟩, ⟨1,0,-4⟩], []⟩,
  LabelExclusion.constant ⟨4, [Guard.circle 0], [⟨0,0,-2⟩, ⟨1,0,-1⟩], [], []⟩,
  LabelExclusion.constant ⟨12, [], [⟨0,0,-6⟩, ⟨1,0,-47⟩, ⟨2,0,13⟩], [], [⟨0,0,35⟩, ⟨1,0,21⟩, ⟨2,0,-13⟩]⟩,
  LabelExclusion.constant ⟨900, [Guard.circle 0], [⟨0,0,-1284⟩, ⟨0,1,336⟩, ⟨1,0,1951⟩, ⟨1,1,-504⟩], [⟨0,0,558⟩, ⟨0,1,666⟩, ⟨0,2,-336⟩, ⟨1,0,-1664⟩, ⟨1,1,224⟩, ⟨2,0,-928⟩, ⟨2,1,336⟩], [⟨0,0,1392⟩, ⟨0,1,-1896⟩, ⟨0,2,504⟩, ⟨1,0,-2784⟩, ⟨1,1,1008⟩, ⟨2,0,1392⟩, ⟨2,1,-504⟩]⟩,
  LabelExclusion.constant ⟨36352800, [], [⟨0,0,74941805⟩, ⟨0,1,-1750570⟩, ⟨1,0,-51626601⟩, ⟨1,1,1220019⟩, ⟨2,0,-65261345⟩, ⟨2,1,1922937⟩, ⟨3,0,46088020⟩, ⟨3,1,-1047652⟩, ⟨4,0,8148964⟩, ⟨5,0,-5476050⟩], [⟨0,0,52770390⟩, ⟨0,1,-50806040⟩, ⟨0,2,1750570⟩, ⟨1,0,25095212⟩, ⟨1,1,4283128⟩, ⟨1,2,-2095304⟩, ⟨2,0,-12598538⟩, ⟨2,1,34694750⟩, ⟨3,0,-10165512⟩, ⟨3,1,-8856796⟩, ⟨4,0,-27250028⟩, ⟨5,0,10952100⟩], [⟨0,0,-40347815⟩, ⟨0,1,48057750⟩, ⟨0,2,-25886335⟩, ⟨1,0,-83129402⟩, ⟨1,1,20654060⟩, ⟨1,2,18692702⟩, ⟨2,0,177587335⟩, ⟨2,1,-48446867⟩, ⟨3,0,-104177800⟩, ⟨3,1,4428398⟩, ⟨4,0,35529214⟩, ⟨5,0,-5476050⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.circle 0], [⟨0,0,-2⟩, ⟨1,0,-1⟩], [⟨0,0,2⟩, ⟨0,1,-2⟩], []⟩,
  LabelExclusion.constant ⟨108, [Guard.circle 0], [⟨0,0,-54⟩, ⟨0,1,-78⟩, ⟨1,0,109⟩, ⟨2,0,-16⟩], [⟨0,0,-78⟩, ⟨0,1,86⟩, ⟨1,0,-160⟩, ⟨2,0,16⟩], [⟨0,0,8⟩, ⟨0,1,-8⟩, ⟨1,0,-16⟩, ⟨2,0,8⟩]⟩,
  LabelExclusion.constant ⟨8, [Guard.triangle 5], [⟨0,0,4⟩, ⟨0,1,-3⟩, ⟨1,0,2⟩], [⟨0,1,4⟩, ⟨1,0,-8⟩], [⟨1,0,4⟩]⟩,
  LabelExclusion.constant ⟨96, [Guard.triangle 0], [⟨0,0,448⟩, ⟨0,1,-684⟩, ⟨0,2,168⟩, ⟨1,0,-60⟩, ⟨1,1,179⟩, ⟨1,2,-66⟩, ⟨2,0,-38⟩, ⟨2,1,33⟩], [⟨0,0,-360⟩, ⟨0,1,432⟩, ⟨0,2,-168⟩, ⟨1,0,-278⟩, ⟨1,1,172⟩, ⟨1,2,66⟩, ⟨2,0,152⟩, ⟨2,1,-132⟩], [⟨0,0,-192⟩, ⟨0,1,336⟩, ⟨1,0,376⟩, ⟨1,1,-384⟩, ⟨2,0,-114⟩, ⟨2,1,99⟩]⟩]

private def exclusionRow14 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨312000, [], [⟨0,0,-156000⟩, ⟨0,1,196690238⟩, ⟨0,2,-159282773⟩, ⟨0,3,69441477⟩, ⟨1,0,-121181658⟩, ⟨1,1,-492519332⟩, ⟨1,2,260762635⟩, ⟨1,3,-92174733⟩, ⟨2,0,319601940⟩, ⟨2,1,167962116⟩, ⟨2,2,-61449822⟩, ⟨3,0,-198186282⟩, ⟨3,1,184349466⟩], [⟨0,0,-196690238⟩, ⟨0,1,136758234⟩, ⟨0,2,225976910⟩, ⟨0,3,-138882954⟩, ⟨1,0,1022235572⟩, ⟨1,1,-1280230098⟩, ⟨1,2,18023236⟩, ⟨1,3,184349466⟩, ⟨2,0,-1374757146⟩, ⟨2,1,1749733356⟩, ⟨2,2,-430148754⟩, ⟨3,0,396372564⟩, ⟨3,1,-368698932⟩], [⟨0,0,22524539⟩, ⟨0,1,-295418387⟩, ⟨0,2,138882954⟩, ⟨1,0,-6110392⟩, ⟨1,1,899207201⟩, ⟨1,2,-392673897⟩, ⟨2,0,-28595931⟩, ⟨2,1,-674129862⟩, ⟨2,2,276524199⟩]⟩,
  LabelExclusion.constant ⟨87000, [], [⟨0,0,-43500⟩, ⟨1,0,1841175⟩, ⟨1,1,-541341⟩, ⟨1,2,104277⟩, ⟨1,3,-6759⟩, ⟨2,0,-2130436⟩, ⟨2,1,-524512⟩, ⟨2,2,-516516⟩, ⟨2,3,28152⟩, ⟨3,0,1023552⟩, ⟨3,1,984576⟩, ⟨3,2,-64320⟩, ⟨4,0,-392832⟩, ⟨4,1,35712⟩], [⟨0,0,-733164⟩, ⟨0,1,-9012⟩, ⟨1,0,773666⟩, ⟨1,1,564502⟩, ⟨1,2,-78530⟩, ⟨1,3,4506⟩, ⟨2,0,2436652⟩, ⟨2,1,-420296⟩, ⟨2,2,378876⟩, ⟨2,3,-18768⟩, ⟨3,0,-693216⟩, ⟨3,1,-913152⟩, ⟨3,2,55392⟩, ⟨4,0,392832⟩, ⟨4,1,-35712⟩], [⟨0,0,-95265⟩, ⟨0,1,6759⟩, ⟨1,0,1035017⟩, ⟨1,1,-87694⟩, ⟨1,2,2253⟩, ⟨2,0,-1582063⟩, ⟨2,1,245894⟩, ⟨2,2,-7131⟩, ⟨3,0,204552⟩, ⟨3,1,174720⟩, ⟨3,2,-9384⟩, ⟨4,0,-98208⟩, ⟨4,1,8928⟩]⟩,
  LabelExclusion.constant ⟨62113500, [], [⟨0,0,-31056750⟩, ⟨1,0,488074221⟩, ⟨1,1,-898437825⟩, ⟨1,2,692220681⟩, ⟨1,3,-46378089⟩, ⟨2,0,-2859412490⟩, ⟨2,1,3437673925⟩, ⟨2,2,-1705721494⟩, ⟨2,3,164380911⟩, ⟨3,0,-336294674⟩, ⟨3,1,984434434⟩, ⟨3,2,-121888000⟩, ⟨4,0,-57403388⟩, ⟨4,1,8200484⟩], [⟨0,0,-86958792⟩, ⟨0,1,-61837452⟩, ⟨1,0,-832075378⟩, ⟨1,1,709733474⟩, ⟨1,2,-440867970⟩, ⟨1,3,30918726⟩, ⟨2,0,5669194476⟩, ⟨2,1,-1720797594⟩, ⟨2,2,1022864512⟩, ⟨2,3,-109587274⟩, ⟨3,0,344569988⟩, ⟨3,1,-1804859188⟩, ⟨3,2,227375032⟩, ⟨4,0,114806776⟩, ⟨4,1,-16400968⟩], [⟨0,0,-506708325⟩, ⟨0,1,46378089⟩, ⟨1,0,2915192095⟩, ⟨1,1,295949325⟩, ⟨1,2,-46378089⟩, ⟨2,0,-2731909458⟩, ⟨2,1,-1293766183⟩, ⟨2,2,195299637⟩, ⟨3,0,-32876766⟩, ⟨3,1,853226690⟩, ⟨3,2,-109587274⟩, ⟨4,0,-57403388⟩, ⟨4,1,8200484⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 4], [⟨1,0,-1⟩, ⟨1,1,-2⟩, ⟨1,2,-1⟩, ⟨2,0,1⟩], [⟨1,0,1⟩, ⟨1,1,2⟩, ⟨1,2,1⟩, ⟨2,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨2640, [Guard.triangle 0, Guard.circle 0], [⟨0,0,266⟩, ⟨0,1,-414⟩, ⟨0,2,54⟩, ⟨0,3,70⟩, ⟨0,4,24⟩, ⟨1,0,-1461⟩, ⟨1,1,-6817⟩, ⟨1,2,3045⟩, ⟨1,3,-35⟩, ⟨1,4,-12⟩, ⟨2,0,-2150⟩, ⟨2,1,3896⟩, ⟨2,2,-1394⟩, ⟨2,3,24⟩, ⟨3,0,2673⟩, ⟨3,1,2895⟩, ⟨3,2,-36⟩, ⟨4,0,-4608⟩], [⟨0,0,266⟩, ⟨0,1,-414⟩, ⟨0,2,54⟩, ⟨0,3,70⟩, ⟨0,4,24⟩, ⟨1,0,3952⟩, ⟨1,1,-7024⟩, ⟨1,2,3072⟩, ⟨2,0,-2558⟩, ⟨2,1,-620⟩, ⟨2,2,-190⟩, ⟨2,3,-24⟩, ⟨3,0,-7804⟩, ⟨3,1,-2836⟩, ⟨3,2,48⟩, ⟨4,0,6144⟩], []⟩,
  LabelExclusion.constant ⟨16, [Guard.triangle 0, Guard.circle 4], [⟨0,0,-32⟩, ⟨0,1,62⟩, ⟨0,2,-26⟩, ⟨0,3,-6⟩, ⟨0,4,2⟩, ⟨1,0,4⟩, ⟨1,1,-7⟩, ⟨1,2,5⟩, ⟨1,3,-1⟩, ⟨1,4,-1⟩, ⟨2,0,-98⟩, ⟨2,1,-42⟩, ⟨2,2,1⟩, ⟨2,3,3⟩, ⟨3,0,76⟩, ⟨3,1,10⟩, ⟨3,2,-4⟩, ⟨4,0,-8⟩], [⟨0,0,-32⟩, ⟨0,1,62⟩, ⟨0,2,-26⟩, ⟨0,3,-6⟩, ⟨0,4,2⟩, ⟨1,0,20⟩, ⟨1,1,24⟩, ⟨1,2,20⟩, ⟨2,0,96⟩, ⟨2,1,22⟩, ⟨2,2,-4⟩, ⟨2,3,-2⟩, ⟨3,0,-76⟩, ⟨3,1,-8⟩, ⟨3,2,4⟩, ⟨4,0,8⟩], []⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 2], [⟨0,0,9⟩, ⟨0,1,16⟩, ⟨0,2,2⟩, ⟨1,0,-4⟩, ⟨1,1,-8⟩, ⟨1,2,-1⟩, ⟨2,1,3⟩, ⟨3,0,-2⟩], [⟨0,0,-16⟩, ⟨0,1,4⟩, ⟨1,0,14⟩, ⟨1,1,2⟩, ⟨2,0,-8⟩, ⟨2,1,-2⟩, ⟨3,0,4⟩], [⟨0,0,10⟩, ⟨0,1,-8⟩, ⟨0,2,-2⟩, ⟨1,0,-13⟩, ⟨1,2,1⟩, ⟨2,0,14⟩, ⟨2,1,-1⟩, ⟨3,0,-2⟩]⟩,
  LabelExclusion.constant ⟨42359598, [], [⟨0,0,-21179799⟩, ⟨0,1,-79615272⟩, ⟨0,2,241909656⟩, ⟨1,0,154637260⟩, ⟨1,1,-232491493⟩, ⟨1,2,-631171104⟩, ⟨2,0,-1412883985⟩, ⟨2,1,1343781379⟩, ⟨2,2,518072106⟩, ⟨3,0,1904736223⟩, ⟨3,1,-1263971039⟩, ⟨3,2,-131481984⟩, ⟨4,0,-339617429⟩, ⟨4,1,395815556⟩, ⟨5,0,-167776490⟩], [⟨0,0,37255674⟩, ⟨0,1,-206695304⟩, ⟨0,2,-120954828⟩, ⟨1,0,-521815364⟩, ⟨1,1,710410414⟩, ⟨1,2,255108138⟩, ⟨2,0,1510350756⟩, ⟨2,1,-1483501912⟩, ⟨2,2,-131481984⟩, ⟨3,0,-1404164216⟩, ⟨3,1,1234736792⟩, ⟨4,0,258271824⟩, ⟨4,1,-262963968⟩, ⟨5,0,134221192⟩], [⟨0,0,-136009423⟩, ⟨0,1,477694108⟩, ⟨0,2,-362864484⟩, ⟨1,0,909557245⟩, ⟨1,1,-1317884583⟩, ⟨1,2,946756656⟩, ⟨2,0,-48587475⟩, ⟨2,1,375668804⟩, ⟨2,2,-777108159⟩, ⟨3,0,-1358523413⟩, ⟨3,1,660625413⟩, ⟨3,2,197222976⟩, ⟨4,0,392493016⟩, ⟨4,1,-363629862⟩, ⟨5,0,134221192⟩]⟩,
  LabelExclusion.constant ⟨168, [Guard.triangle 0], [⟨1,0,68⟩, ⟨1,1,-43⟩, ⟨1,2,-5⟩, ⟨2,0,-10⟩, ⟨2,1,14⟩, ⟨3,0,-16⟩, ⟨3,1,-6⟩, ⟨4,0,12⟩], [⟨0,0,-212⟩, ⟨0,1,88⟩, ⟨0,2,-44⟩, ⟨1,0,-154⟩, ⟨1,1,112⟩, ⟨1,2,10⟩, ⟨2,0,52⟩, ⟨2,1,-52⟩, ⟨3,0,44⟩, ⟨3,1,12⟩, ⟨4,0,-24⟩], [⟨0,0,126⟩, ⟨0,1,-1⟩, ⟨0,2,27⟩, ⟨1,0,95⟩, ⟨1,1,-82⟩, ⟨1,2,-5⟩, ⟨2,0,-10⟩, ⟨2,1,32⟩, ⟨3,0,-34⟩, ⟨3,1,-6⟩, ⟨4,0,12⟩]⟩,
  LabelExclusion.constant ⟨8, [Guard.triangle 5], [⟨1,0,-3⟩], [⟨0,0,-18⟩, ⟨0,1,6⟩], [⟨0,0,12⟩, ⟨0,1,-3⟩, ⟨1,0,3⟩]⟩,
  LabelExclusion.constant ⟨1008, [Guard.triangle 0], [⟨1,0,-10050⟩, ⟨1,1,8358⟩, ⟨1,2,-1104⟩, ⟨2,0,7455⟩, ⟨2,1,-1434⟩, ⟨3,0,-330⟩], [⟨0,0,2768⟩, ⟨0,1,-8560⟩, ⟨0,2,4784⟩, ⟨1,0,5612⟩, ⟨1,1,-27508⟩, ⟨1,2,3312⟩, ⟨2,0,11830⟩, ⟨2,1,-1218⟩, ⟨3,0,-660⟩], [⟨0,0,6650⟩, ⟨0,1,-13646⟩, ⟨0,2,-1288⟩, ⟨1,0,10463⟩, ⟨1,1,15556⟩, ⟨1,2,-1656⟩, ⟨2,0,-19615⟩, ⟨2,1,2817⟩, ⟨3,0,990⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.circle 4], [⟨0,0,16⟩, ⟨0,1,31⟩, ⟨0,2,-2⟩, ⟨1,0,-60⟩, ⟨1,1,4⟩], [⟨0,0,-16⟩, ⟨0,1,1⟩, ⟨1,0,60⟩, ⟨1,1,-4⟩], []⟩,
  LabelExclusion.constant ⟨12, [Guard.triangle 0], [⟨0,0,24⟩, ⟨0,1,4⟩, ⟨1,0,-20⟩, ⟨1,1,-2⟩, ⟨2,0,5⟩], [⟨0,0,-16⟩, ⟨0,1,-4⟩, ⟨1,0,20⟩, ⟨1,1,2⟩, ⟨2,0,-6⟩], [⟨1,0,-2⟩, ⟨2,0,1⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨0,0,20⟩, ⟨0,1,8⟩, ⟨0,2,-3⟩, ⟨1,0,-20⟩, ⟨1,1,3⟩, ⟨2,0,3⟩], [⟨0,0,-28⟩, ⟨0,1,-22⟩, ⟨0,2,6⟩, ⟨1,0,74⟩, ⟨1,1,-12⟩, ⟨2,0,-6⟩], [⟨1,0,-14⟩, ⟨1,1,3⟩]⟩,
  LabelExclusion.constant ⟨198, [Guard.triangle 0], [⟨0,0,-124⟩, ⟨0,1,-846⟩, ⟨0,2,120⟩, ⟨1,0,3608⟩, ⟨1,1,-370⟩, ⟨2,0,-1252⟩, ⟨2,1,90⟩, ⟨3,0,105⟩], [⟨0,0,-272⟩, ⟨0,1,1254⟩, ⟨0,2,-180⟩, ⟨1,0,-3136⟩, ⟨1,1,210⟩, ⟨2,0,490⟩], [⟨1,0,-1821⟩, ⟨1,1,270⟩, ⟨2,0,972⟩, ⟨2,1,-90⟩, ⟨3,0,-105⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 0], [⟨0,0,4⟩, ⟨1,0,-1⟩], [⟨0,0,-4⟩, ⟨1,0,1⟩], []⟩]

private def exclusionRow15 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨6, [Guard.triangle 0], [⟨0,0,-6⟩, ⟨0,1,-8⟩, ⟨0,2,2⟩, ⟨1,0,9⟩, ⟨1,1,-2⟩], [⟨0,0,-24⟩, ⟨0,1,24⟩, ⟨0,2,-4⟩, ⟨1,0,-18⟩, ⟨1,1,4⟩], [⟨0,0,18⟩, ⟨0,1,-4⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 4], [⟨1,2,-1⟩, ⟨2,1,-2⟩], [⟨1,2,1⟩, ⟨2,1,2⟩], []⟩,
  LabelExclusion.constant ⟨42, [Guard.triangle 0], [⟨1,0,-2⟩, ⟨1,1,-10⟩, ⟨2,0,19⟩, ⟨2,1,2⟩, ⟨3,0,-4⟩], [⟨0,0,-44⟩, ⟨0,1,8⟩, ⟨1,0,4⟩, ⟨1,1,20⟩, ⟨2,0,-38⟩, ⟨2,1,-4⟩, ⟨3,0,8⟩], [⟨0,0,48⟩, ⟨0,1,6⟩, ⟨1,0,-25⟩, ⟨1,1,-12⟩, ⟨2,0,23⟩, ⟨2,1,2⟩, ⟨3,0,-4⟩]⟩,
  LabelExclusion.constant ⟨120, [Guard.triangle 0], [⟨1,0,1817⟩, ⟨1,1,-304⟩, ⟨1,2,15⟩, ⟨2,0,-1056⟩, ⟨2,1,88⟩, ⟨3,0,112⟩], [⟨0,0,-336⟩, ⟨0,1,-368⟩, ⟨0,2,-180⟩, ⟨1,0,-2⟩, ⟨1,1,2224⟩, ⟨1,2,-150⟩, ⟨2,0,-2244⟩, ⟨2,1,-100⟩, ⟨3,0,336⟩], [⟨0,0,96⟩, ⟨0,1,728⟩, ⟨0,2,75⟩, ⟨1,0,-2403⟩, ⟨1,1,-1050⟩, ⟨1,2,75⟩, ⟨2,0,2435⟩, ⟨2,1,-25⟩, ⟨3,0,-308⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 0], [⟨0,0,4⟩, ⟨1,0,-1⟩], [⟨0,0,-4⟩, ⟨1,0,1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 5], [⟨0,1,-1⟩, ⟨1,0,4⟩], [⟨0,1,1⟩, ⟨1,0,-4⟩], []⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 0], [⟨0,0,42⟩, ⟨0,1,-10⟩, ⟨1,0,-12⟩, ⟨1,1,4⟩], [⟨1,0,-2⟩, ⟨2,0,-4⟩], [⟨0,0,-36⟩, ⟨0,1,9⟩, ⟨1,0,24⟩, ⟨1,1,-6⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.circle 0], [⟨0,0,-1⟩], [⟨0,0,2⟩, ⟨0,1,-1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 5], [⟨0,0,1⟩, ⟨1,0,-1⟩], [⟨1,0,2⟩], [⟨0,1,1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.circle 4], [⟨0,1,-4⟩, ⟨0,2,1⟩, ⟨0,3,6⟩, ⟨0,4,-1⟩, ⟨1,2,-8⟩, ⟨1,3,2⟩, ⟨2,1,-4⟩, ⟨2,2,1⟩], [⟨0,3,-2⟩, ⟨1,1,8⟩, ⟨1,2,6⟩, ⟨1,3,-2⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,1,-1⟩], [⟨0,0,-28⟩, ⟨0,1,8⟩, ⟨1,0,2⟩], [⟨0,0,11⟩, ⟨0,1,-3⟩, ⟨1,0,-1⟩]⟩,
  LabelExclusion.constant ⟨3294, [], [⟨0,0,-1647⟩, ⟨0,1,-97347⟩, ⟨0,2,264887⟩, ⟨0,3,-108129⟩, ⟨0,4,11620⟩, ⟨1,0,84038⟩, ⟨1,1,-182828⟩, ⟨1,2,137928⟩, ⟨1,3,-42322⟩, ⟨1,4,4648⟩, ⟨2,0,-9570⟩, ⟨2,1,20671⟩, ⟨2,2,-13608⟩, ⟨2,3,2324⟩], [⟨0,0,-87332⟩, ⟨0,1,117306⟩, ⟨0,2,-32536⟩, ⟨1,0,38280⟩, ⟨1,1,-82684⟩, ⟨1,2,54432⟩, ⟨1,3,-9296⟩], [⟨0,0,53681⟩, ⟨0,1,-31570⟩, ⟨0,2,-186417⟩, ⟨0,3,112105⟩, ⟨0,4,-16268⟩, ⟨1,0,-64898⟩, ⟨1,1,141486⟩, ⟨1,2,-110712⟩, ⟨1,3,37674⟩, ⟨1,4,-4648⟩, ⟨2,0,9570⟩, ⟨2,1,-20671⟩, ⟨2,2,13608⟩, ⟨2,3,-2324⟩]⟩,
  LabelExclusion.constant ⟨100, [Guard.circle 2], [⟨0,0,323⟩, ⟨0,1,-114⟩, ⟨1,0,-148⟩, ⟨2,0,-25⟩], [⟨0,0,152⟩, ⟨0,1,-114⟩, ⟨1,0,296⟩, ⟨2,0,50⟩], [⟨0,0,-221⟩, ⟨0,1,114⟩, ⟨1,0,-50⟩, ⟨2,0,-50⟩]⟩,
  LabelExclusion.constant ⟨350465321250, [], [⟨0,0,232375247255⟩, ⟨0,1,6985030902⟩, ⟨0,2,7465390368⟩, ⟨1,0,-189447373964⟩, ⟨1,1,-263422596382⟩, ⟨1,2,38138139422⟩, ⟨1,3,2488463456⟩, ⟨2,0,-172922255692⟩, ⟨2,1,322828943648⟩, ⟨2,2,-153562018141⟩, ⟨2,3,14736119984⟩, ⟨3,0,-84662627024⟩, ⟨3,1,-8628988496⟩, ⟨3,2,15930697628⟩, ⟨3,3,6745944128⟩, ⟨4,0,39424348800⟩, ⟨4,1,-55194088320⟩, ⟨4,2,17740956960⟩], [⟨0,0,475628340418⟩, ⟨0,1,18946988716⟩, ⟨0,2,14930780736⟩, ⟨1,0,79184296878⟩, ⟨1,1,-983934229394⟩, ⟨1,2,93091770596⟩, ⟨1,3,-4976926912⟩, ⟨2,0,208941025300⟩, ⟨2,1,-18796756014⟩, ⟨2,2,345111237594⟩, ⟨2,3,-29472239968⟩, ⟨3,0,-92746942576⟩, ⟨3,1,135822374824⟩, ⟨3,2,-45353283512⟩, ⟨3,3,-13491888256⟩, ⟨4,0,-39424348800⟩, ⟨4,1,74906262720⟩, ⟨4,2,-35481913920⟩], [⟨0,0,68020432538⟩, ⟨0,1,-236730058303⟩, ⟨0,2,-1546107948⟩, ⟨0,3,-4976926912⟩, ⟨1,0,-70955804500⟩, ⟨1,1,379667958845⟩, ⟨1,2,267324095112⟩, ⟨1,3,-26983776512⟩, ⟨2,0,92746942576⟩, ⟨2,1,-74319754270⟩, ⟨2,2,-203172782325⟩, ⟨2,3,1244231728⟩, ⟨3,0,39424348800⟩, ⟨3,1,36417661192⟩, ⟨3,2,-6059328036⟩, ⟨3,3,6745944128⟩, ⟨4,1,-19712174400⟩, ⟨4,2,17740956960⟩]⟩,
  LabelExclusion.constant ⟨550941000, [], [⟨0,0,1115500585⟩, ⟨0,1,-59081531⟩, ⟨0,2,-640393718⟩, ⟨0,3,157438992⟩, ⟨1,0,-1150300188⟩, ⟨1,1,1230391882⟩, ⟨1,2,-499223981⟩, ⟨1,3,77876328⟩, ⟨2,0,-228748503⟩, ⟨2,1,500202680⟩, ⟨2,2,-123972110⟩, ⟨3,0,-25001068⟩, ⟨3,1,-55297789⟩, ⟨4,0,13078674⟩], [⟨0,0,647756398⟩, ⟨0,1,-965909452⟩, ⟨0,2,314877984⟩, ⟨1,0,1154373974⟩, ⟨1,1,-759898018⟩, ⟨1,2,-1686336⟩, ⟨2,0,-64702718⟩, ⟨2,1,54187262⟩, ⟨2,2,-77876328⟩, ⟨3,0,-80784604⟩, ⟨3,1,162910274⟩, ⟨4,0,-26157348⟩], [⟨0,0,-743214687⟩, ⟨0,1,352538652⟩, ⟨0,2,198837636⟩, ⟨0,3,-78719496⟩, ⟨1,0,170488390⟩, ⟨1,1,-319702996⟩, ⟨1,2,228942069⟩, ⟨1,3,-38938164⟩, ⟨2,0,93863278⟩, ⟨2,1,-222636268⟩, ⟨2,2,81455137⟩, ⟨3,0,26157348⟩, ⟨3,1,-13078674⟩]⟩]

private def exclusionRow16 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨72, [], [⟨0,0,-36⟩, ⟨0,1,38⟩, ⟨0,2,-4⟩], [⟨0,0,-86⟩, ⟨0,1,44⟩, ⟨0,2,-4⟩, ⟨1,0,36⟩, ⟨1,1,-38⟩, ⟨1,2,4⟩], [⟨0,0,105⟩, ⟨0,1,-80⟩, ⟨0,2,8⟩, ⟨1,0,-36⟩, ⟨1,1,38⟩, ⟨1,2,-4⟩]⟩,
  LabelExclusion.constant ⟨8, [], [⟨0,0,-4⟩, ⟨0,1,-10⟩, ⟨0,2,-13⟩, ⟨0,3,5⟩, ⟨1,1,-26⟩, ⟨1,2,23⟩, ⟨1,3,-5⟩], [⟨0,0,-48⟩, ⟨0,1,-46⟩, ⟨0,2,10⟩, ⟨1,0,100⟩, ⟨1,1,104⟩, ⟨1,2,-40⟩, ⟨2,1,-26⟩, ⟨2,2,10⟩], [⟨0,0,26⟩, ⟨0,1,92⟩, ⟨0,2,19⟩, ⟨0,3,-15⟩, ⟨1,0,-76⟩, ⟨1,1,-55⟩, ⟨1,2,12⟩, ⟨1,3,5⟩, ⟨2,1,13⟩, ⟨2,2,-5⟩]⟩,
  LabelExclusion.constant ⟨1782, [], [⟨0,0,-891⟩, ⟨0,1,-1412⟩, ⟨0,2,944⟩, ⟨1,1,350⟩, ⟨1,2,-2284⟩, ⟨1,3,944⟩, ⟨2,0,370⟩, ⟨2,1,-372⟩, ⟨2,2,150⟩, ⟨2,3,-400⟩, ⟨3,0,871⟩, ⟨3,1,-1855⟩, ⟨3,2,1215⟩, ⟨3,3,-231⟩, ⟨4,0,252⟩, ⟨4,1,-588⟩, ⟨4,2,336⟩], [⟨0,1,-4002⟩, ⟨0,2,2360⟩, ⟨1,1,-5226⟩, ⟨1,2,4066⟩, ⟨1,3,-1888⟩, ⟨2,1,-772⟩, ⟨2,2,500⟩, ⟨2,3,800⟩, ⟨3,1,1742⟩, ⟨3,2,-1968⟩, ⟨3,3,462⟩, ⟨4,1,504⟩, ⟨4,2,-672⟩], [⟨0,0,-370⟩, ⟨0,1,3126⟩, ⟨0,2,-240⟩, ⟨0,3,-944⟩, ⟨1,0,-871⟩, ⟨1,1,4219⟩, ⟨1,2,-2014⟩, ⟨1,3,1344⟩, ⟨2,0,-252⟩, ⟨2,1,1593⟩, ⟨2,2,-1234⟩, ⟨2,3,-169⟩, ⟨3,1,-619⟩, ⟨3,2,648⟩, ⟨3,3,-231⟩, ⟨4,1,-252⟩, ⟨4,2,336⟩]⟩,
  LabelExclusion.constant ⟨42, [], [⟨0,0,-21⟩, ⟨0,1,-376⟩, ⟨0,2,256⟩, ⟨1,0,134⟩, ⟨1,1,5⟩, ⟨1,2,-200⟩, ⟨2,0,-49⟩, ⟨2,1,133⟩, ⟨2,2,34⟩, ⟨3,0,-8⟩, ⟨3,1,-17⟩], [⟨0,0,-134⟩, ⟨0,1,1264⟩, ⟨0,2,-512⟩, ⟨1,0,-218⟩, ⟨1,1,-346⟩, ⟨1,2,400⟩, ⟨2,0,114⟩, ⟨2,1,-232⟩, ⟨2,2,-68⟩, ⟨3,0,16⟩, ⟨3,1,34⟩], [⟨0,0,267⟩, ⟨0,1,-288⟩, ⟨1,0,-106⟩, ⟨1,1,217⟩, ⟨2,0,-16⟩, ⟨2,1,-34⟩]⟩,
  LabelExclusion.constant ⟨30080372354474, [], [⟨0,0,-15040186177237⟩, ⟨0,1,-75468081073953⟩, ⟨0,2,-51628653072919⟩, ⟨0,3,11149280204504⟩, ⟨1,0,44736105357128⟩, ⟨1,1,-564634398918762⟩, ⟨1,2,-142413294035857⟩, ⟨1,3,52246952152824⟩, ⟨2,0,708291925915607⟩, ⟨2,1,415496766912907⟩, ⟨2,2,-115329111659447⟩, ⟨2,3,7765602404456⟩, ⟨3,0,-641664444818203⟩, ⟨3,1,364025151676317⟩, ⟨3,2,124492553672498⟩, ⟨3,3,-35635791985696⟩, ⟨4,0,-3990273877396⟩, ⟨4,1,24267147443692⟩, ⟨4,2,-36703085807568⟩, ⟨4,3,2498033277312⟩, ⟨5,0,5382275646840⟩, ⟨5,1,-6121824972360⟩, ⟨5,2,739549325520⟩], [⟨0,0,-44736105357128⟩, ⟨0,1,-29793155604026⟩, ⟨0,2,-1715273877616⟩, ⟨1,0,-731311581956522⟩, ⟨1,1,-222251264079024⟩, ⟨1,2,144328756273252⟩, ⟨1,3,-24013834286624⟩, ⟨2,0,432387170315068⟩, ⟨2,1,890721056306426⟩, ⟨2,2,270852308610978⟩, ⟨2,3,-86802788780304⟩, ⟨3,0,284378102798816⟩, ⟨3,1,-999768923410566⟩, ⟨3,2,-241127561879492⟩, ⟨3,3,76267650526016⟩, ⟨4,0,21529102587360⟩, ⟨4,1,10590357530488⟩, ⟨4,2,69889203711552⟩, ⟨4,3,-4996066554624⟩, ⟨5,1,10764551293680⟩, ⟨5,2,-1479098651040⟩], [⟨0,0,23019656040915⟩, ⟨0,1,12676362693057⟩, ⟨0,2,12318694116304⟩, ⟨0,3,63318820373954⟩, ⟨0,4,-12006917143312⟩, ⟨1,0,209277274503135⟩, ⟨1,1,404430332035585⟩, ⟨1,2,391764237011404⟩, ⟨1,3,101533643781337⟩, ⟨1,4,-43401394390152⟩, ⟨2,0,-280387828921420⟩, ⟨2,1,-868237545997724⟩, ⟨2,2,-700330561968518⟩, ⟨2,3,-39028561286586⟩, ⟨2,4,38133825263008⟩, ⟨3,0,-26911378234200⟩, ⟨3,1,579917000871599⟩, ⟨3,2,155807495006142⟩, ⟨3,3,-5687256684544⟩, ⟨3,4,-2498033277312⟩, ⟨4,1,-1392001769444⟩, ⟨4,2,-30301875534456⟩, ⟨4,3,1758483951792⟩, ⟨5,1,-5382275646840⟩, ⟨5,2,739549325520⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 0], [⟨0,0,-4⟩, ⟨0,1,-1⟩], [⟨0,0,4⟩, ⟨0,1,-2⟩], []⟩,
  LabelExclusion.constant ⟨174, [Guard.triangle 0], [⟨0,0,516⟩, ⟨0,1,291⟩, ⟨0,2,-90⟩, ⟨1,0,-864⟩, ⟨1,1,12⟩, ⟨1,2,40⟩, ⟨2,0,288⟩, ⟨2,1,-64⟩], [⟨0,0,-384⟩, ⟨0,1,246⟩, ⟨0,2,-36⟩, ⟨1,0,936⟩, ⟨1,1,-280⟩, ⟨1,2,16⟩, ⟨2,0,-288⟩, ⟨2,1,64⟩], [⟨0,0,-348⟩, ⟨0,1,159⟩, ⟨0,2,-18⟩, ⟨1,0,216⟩, ⟨1,1,-84⟩, ⟨1,2,8⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 3], [⟨0,0,-3⟩, ⟨0,1,82⟩, ⟨0,2,-16⟩, ⟨1,0,-32⟩], [⟨0,0,-26⟩, ⟨0,1,16⟩, ⟨1,0,32⟩], [⟨0,0,9⟩, ⟨0,1,-66⟩, ⟨0,2,16⟩]⟩,
  LabelExclusion.constant ⟨11502, [], [⟨0,0,-5751⟩, ⟨0,1,-55436⟩, ⟨0,2,-31729⟩, ⟨0,3,5230⟩, ⟨1,0,-10804⟩, ⟨1,1,200024⟩, ⟨1,2,18222⟩, ⟨1,3,-6200⟩, ⟨2,0,-73432⟩, ⟨2,1,-94240⟩, ⟨2,2,8680⟩, ⟨3,0,34720⟩], [⟨0,0,698⟩, ⟨0,1,-10460⟩, ⟨1,0,-2488⟩, ⟨1,1,-8520⟩, ⟨2,0,108152⟩, ⟨2,1,24800⟩, ⟨3,0,-34720⟩], [⟨0,0,54389⟩, ⟨0,1,46372⟩, ⟨0,2,10809⟩, ⟨0,3,-5230⟩, ⟨1,0,-60140⟩, ⟨1,1,-90792⟩, ⟨1,2,6578⟩, ⟨1,3,6200⟩, ⟨2,1,34720⟩, ⟨2,2,-8680⟩]⟩,
  LabelExclusion.constant ⟨12, [Guard.aOrder, Guard.circle 3], [⟨0,0,6⟩, ⟨0,1,150⟩, ⟨0,2,-51⟩, ⟨0,3,-51⟩, ⟨0,4,15⟩, ⟨1,0,6⟩, ⟨1,1,-42⟩, ⟨1,2,-6⟩, ⟨1,3,24⟩, ⟨1,4,-6⟩, ⟨2,0,-6⟩, ⟨2,1,-6⟩, ⟨2,2,6⟩, ⟨3,0,-6⟩], [⟨0,0,-28⟩, ⟨0,1,-94⟩, ⟨0,2,86⟩, ⟨0,3,14⟩, ⟨0,4,-24⟩, ⟨0,5,4⟩, ⟨1,0,52⟩, ⟨1,1,98⟩, ⟨1,2,18⟩, ⟨1,3,-26⟩, ⟨1,4,4⟩], [⟨0,0,-80⟩, ⟨0,1,98⟩, ⟨0,2,18⟩, ⟨0,3,-26⟩, ⟨0,4,4⟩, ⟨1,0,-26⟩, ⟨1,1,-49⟩, ⟨1,2,-9⟩, ⟨1,3,13⟩, ⟨1,4,-2⟩]⟩,
  LabelExclusion.constant ⟨8, [Guard.triangle 7], [⟨0,1,-15⟩, ⟨0,2,3⟩], [⟨0,0,12⟩, ⟨0,1,24⟩, ⟨0,2,-6⟩, ⟨1,0,-24⟩, ⟨1,1,6⟩], [⟨0,0,9⟩, ⟨0,1,-3⟩, ⟨1,0,12⟩, ⟨1,1,-3⟩]⟩,
  LabelExclusion.constant ⟨352, [Guard.triangle 0], [⟨0,1,-7060⟩, ⟨0,2,2801⟩, ⟨0,3,5690⟩, ⟨0,4,-2100⟩, ⟨1,1,16592⟩, ⟨1,2,-17680⟩, ⟨1,3,4200⟩], [⟨0,0,9000⟩, ⟨0,1,-12644⟩, ⟨0,2,3738⟩, ⟨1,0,-16944⟩, ⟨1,1,-1820⟩, ⟨1,2,14530⟩, ⟨1,3,-4200⟩, ⟨2,0,8296⟩, ⟨2,1,-8840⟩, ⟨2,2,2100⟩], [⟨0,0,1856⟩, ⟨0,1,-6091⟩, ⟨0,2,1869⟩, ⟨1,0,8472⟩, ⟨1,1,-7386⟩, ⟨1,2,1575⟩, ⟨2,0,-4148⟩, ⟨2,1,4420⟩, ⟨2,2,-1050⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 4], [⟨0,1,-1⟩, ⟨0,2,-1⟩, ⟨0,3,-1⟩], [⟨0,1,1⟩, ⟨0,2,1⟩, ⟨0,3,1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.circle 4], [⟨0,0,-2⟩, ⟨0,1,3⟩, ⟨0,2,-8⟩, ⟨0,3,-1⟩, ⟨1,1,-2⟩, ⟨1,2,1⟩, ⟨2,1,2⟩], [⟨0,0,-2⟩, ⟨0,1,6⟩, ⟨0,2,2⟩, ⟨0,3,2⟩, ⟨1,1,6⟩, ⟨1,2,-2⟩, ⟨2,1,-2⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 4], [⟨0,1,-1⟩, ⟨0,2,-2⟩], [⟨0,1,1⟩, ⟨0,2,2⟩], []⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,-9⟩, ⟨0,1,-11⟩, ⟨0,2,18⟩, ⟨0,3,-4⟩, ⟨1,0,-16⟩, ⟨1,1,16⟩, ⟨2,0,-17⟩, ⟨2,1,39⟩, ⟨2,2,-26⟩, ⟨2,3,4⟩], [⟨0,0,-16⟩, ⟨1,0,32⟩, ⟨1,1,-66⟩, ⟨1,2,44⟩, ⟨1,3,-8⟩, ⟨2,0,34⟩, ⟨2,1,-78⟩, ⟨2,2,52⟩, ⟨2,3,-8⟩], [⟨0,0,49⟩, ⟨0,1,-71⟩, ⟨0,2,59⟩, ⟨0,3,-26⟩, ⟨0,4,4⟩, ⟨1,0,34⟩, ⟨1,1,-78⟩, ⟨1,2,69⟩, ⟨1,3,-30⟩, ⟨1,4,4⟩]⟩]

private def exclusionRow17 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨6, [], [⟨0,0,-3⟩, ⟨0,1,12⟩, ⟨0,2,22⟩, ⟨0,3,-5⟩, ⟨1,0,-32⟩, ⟨1,1,4⟩, ⟨1,2,-36⟩, ⟨1,3,7⟩, ⟨2,0,8⟩, ⟨2,1,23⟩, ⟨2,2,8⟩, ⟨2,3,-2⟩, ⟨3,1,-6⟩], [⟨0,0,-32⟩, ⟨0,1,10⟩, ⟨1,0,38⟩, ⟨1,1,-130⟩, ⟨1,2,74⟩, ⟨1,3,-10⟩, ⟨2,0,42⟩, ⟨2,1,-18⟩, ⟨2,2,-20⟩, ⟨2,3,4⟩, ⟨3,0,-12⟩, ⟨3,1,12⟩], [⟨0,0,30⟩, ⟨0,1,-74⟩, ⟨0,2,73⟩, ⟨0,3,-37⟩, ⟨0,4,5⟩, ⟨1,0,42⟩, ⟨1,1,-38⟩, ⟨1,2,37⟩, ⟨1,3,5⟩, ⟨1,4,-2⟩, ⟨2,0,-12⟩, ⟨2,1,-11⟩, ⟨2,2,-14⟩, ⟨2,3,2⟩, ⟨3,1,6⟩]⟩,
  LabelExclusion.constant ⟨6, [], [⟨0,0,-3⟩, ⟨0,1,-22⟩, ⟨0,2,-10⟩, ⟨1,1,-17⟩, ⟨1,2,66⟩, ⟨1,3,-10⟩, ⟨2,0,16⟩, ⟨2,1,16⟩, ⟨2,2,-44⟩, ⟨2,3,8⟩], [⟨0,1,-72⟩, ⟨0,2,40⟩, ⟨1,0,32⟩, ⟨1,1,122⟩, ⟨1,2,-148⟩, ⟨1,3,20⟩, ⟨2,0,-32⟩, ⟨2,1,-32⟩, ⟨2,2,88⟩, ⟨2,3,-16⟩], [⟨0,0,16⟩, ⟨0,1,77⟩, ⟨0,2,-58⟩, ⟨0,3,10⟩, ⟨1,0,-32⟩, ⟨1,1,-48⟩, ⟨1,2,44⟩, ⟨1,3,-8⟩]⟩,
  LabelExclusion.constant ⟨58482, [], [⟨0,0,-29241⟩, ⟨0,1,483062⟩, ⟨0,2,15414⟩, ⟨0,3,-52136⟩, ⟨1,1,-479976⟩, ⟨1,2,-22304⟩, ⟨1,3,29792⟩, ⟨2,1,165856⟩, ⟨2,2,-13764⟩, ⟨3,1,-15804⟩, ⟨3,2,112⟩, ⟨4,1,-112⟩], [⟨0,0,-301654⟩, ⟨0,1,655596⟩, ⟨0,2,-477708⟩, ⟨0,3,104272⟩, ⟨1,0,31440⟩, ⟨1,1,294064⟩, ⟨1,2,163776⟩, ⟨1,3,-59584⟩, ⟨2,0,224⟩, ⟨2,1,-268496⟩, ⟨2,2,27528⟩, ⟨3,1,32056⟩, ⟨3,2,-224⟩, ⟨4,1,224⟩], [⟨0,0,212591⟩, ⟨0,1,-686338⟩, ⟨0,2,343126⟩, ⟨0,3,-52136⟩, ⟨1,0,-15300⟩, ⟨1,1,121016⟩, ⟨1,2,-141472⟩, ⟨1,3,29792⟩, ⟨2,0,-112⟩, ⟨2,1,102192⟩, ⟨2,2,-13764⟩, ⟨3,1,-16252⟩, ⟨3,2,112⟩, ⟨4,1,-112⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 5], [⟨1,1,2⟩, ⟨2,0,-3⟩], [⟨0,0,-2⟩, ⟨0,1,2⟩, ⟨1,0,-16⟩, ⟨1,1,2⟩, ⟨2,0,4⟩], [⟨0,0,1⟩, ⟨0,1,-1⟩, ⟨1,0,7⟩, ⟨1,1,-1⟩, ⟨2,0,-1⟩]⟩,
  LabelExclusion.constant ⟨54, [], [⟨0,0,-27⟩, ⟨0,1,-537⟩, ⟨0,2,168⟩, ⟨0,3,3⟩, ⟨1,1,1439⟩, ⟨1,2,-301⟩, ⟨1,3,-45⟩, ⟨2,1,-1254⟩, ⟨2,2,200⟩, ⟨2,3,56⟩, ⟨3,1,552⟩, ⟨3,2,-122⟩, ⟨3,3,-14⟩, ⟨4,1,-92⟩, ⟨4,2,28⟩], [⟨0,0,-60⟩, ⟨0,1,54⟩, ⟨0,2,-12⟩, ⟨1,0,414⟩, ⟨1,1,-714⟩, ⟨1,2,186⟩, ⟨2,0,-138⟩, ⟨2,1,1066⟩, ⟨2,2,-314⟩, ⟨3,1,-552⟩, ⟨3,2,168⟩, ⟨4,1,92⟩, ⟨4,2,-28⟩], [⟨0,0,513⟩, ⟨0,1,-156⟩, ⟨0,2,-3⟩, ⟨1,0,-851⟩, ⟨1,1,115⟩, ⟨1,2,45⟩, ⟨2,0,230⟩, ⟨2,1,114⟩, ⟨2,2,-56⟩, ⟨3,1,-46⟩, ⟨3,2,14⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,-8⟩, ⟨0,1,2⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.circle 4], [⟨0,0,-4⟩, ⟨0,1,-9⟩, ⟨1,0,16⟩, ⟨2,1,2⟩, ⟨3,0,-4⟩], [⟨0,0,4⟩, ⟨0,1,1⟩, ⟨1,0,-16⟩, ⟨3,0,4⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,-2⟩, ⟨0,1,-8⟩, ⟨1,0,11⟩, ⟨1,1,3⟩, ⟨2,0,-3⟩], [⟨0,0,-2⟩, ⟨1,0,-22⟩, ⟨2,0,6⟩], [⟨0,1,8⟩, ⟨1,1,-3⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 0], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,1⟩], []⟩,
  LabelExclusion.constant ⟨27, [Guard.triangle 0], [⟨0,0,-15⟩, ⟨0,1,-24⟩, ⟨1,0,39⟩, ⟨1,1,4⟩, ⟨2,0,-6⟩], [⟨0,0,-25⟩, ⟨0,1,24⟩, ⟨1,0,-32⟩, ⟨1,1,-4⟩, ⟨2,0,6⟩], [⟨0,0,36⟩, ⟨1,0,-6⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,10⟩, ⟨0,1,-17⟩, ⟨0,3,1⟩, ⟨1,0,-2⟩, ⟨1,1,8⟩, ⟨1,2,-2⟩], [⟨0,0,-12⟩, ⟨0,1,18⟩, ⟨0,2,-4⟩, ⟨1,0,2⟩, ⟨1,1,-8⟩, ⟨1,2,2⟩], [⟨0,0,-2⟩, ⟨0,1,8⟩, ⟨0,2,-2⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.circle 4], [⟨0,2,8⟩, ⟨0,3,-7⟩, ⟨0,4,1⟩, ⟨1,2,-6⟩, ⟨2,1,-4⟩, ⟨2,2,1⟩], [⟨0,2,-4⟩, ⟨0,3,2⟩, ⟨1,2,14⟩, ⟨1,3,-2⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.circle 4], [⟨0,2,2⟩, ⟨1,2,-6⟩, ⟨2,1,-4⟩, ⟨2,2,1⟩], [⟨0,2,-2⟩, ⟨1,2,14⟩, ⟨1,3,-2⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,1,-4⟩, ⟨0,2,17⟩, ⟨0,3,-8⟩, ⟨0,4,1⟩], [⟨0,0,8⟩, ⟨0,1,-18⟩, ⟨0,2,4⟩, ⟨1,0,-24⟩, ⟨1,1,-2⟩, ⟨1,2,10⟩, ⟨1,3,-2⟩, ⟨2,0,16⟩, ⟨2,1,-12⟩, ⟨2,2,2⟩], [⟨0,0,-28⟩, ⟨0,1,19⟩, ⟨0,2,-3⟩, ⟨1,0,36⟩, ⟨1,1,-25⟩, ⟨1,2,4⟩, ⟨2,0,-8⟩, ⟨2,1,6⟩, ⟨2,2,-1⟩]⟩]

private def exclusionRow18 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,1,-4⟩, ⟨0,2,1⟩], [⟨0,0,-8⟩, ⟨0,1,-6⟩, ⟨0,2,10⟩, ⟨0,3,-2⟩, ⟨1,0,8⟩, ⟨1,1,-10⟩, ⟨1,2,2⟩], [⟨0,0,4⟩, ⟨0,1,7⟩, ⟨0,2,-6⟩, ⟨0,3,1⟩, ⟨1,0,-4⟩, ⟨1,1,5⟩, ⟨1,2,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,1,-68⟩, ⟨0,2,65⟩, ⟨0,3,-20⟩, ⟨0,4,2⟩], [⟨0,0,-24⟩, ⟨0,1,110⟩, ⟨0,2,-106⟩, ⟨0,3,36⟩, ⟨0,4,-4⟩, ⟨1,0,-40⟩, ⟨1,1,74⟩, ⟨1,2,-32⟩, ⟨1,3,4⟩], [⟨0,0,20⟩, ⟨0,1,11⟩, ⟨0,2,-12⟩, ⟨0,3,2⟩, ⟨1,0,20⟩, ⟨1,1,-37⟩, ⟨1,2,16⟩, ⟨1,3,-2⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.triangle 1], [⟨0,0,4⟩, ⟨0,1,1⟩], [⟨0,1,-2⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 0], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,1⟩], []⟩,
  LabelExclusion.constant ⟨6, [], [⟨0,0,1⟩], [⟨0,0,-2⟩], [⟨0,0,1⟩]⟩,
  LabelExclusion.constant ⟨2, [], [], [⟨0,0,-2⟩], [⟨0,0,1⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,1⟩], [⟨0,0,-2⟩], []⟩,
  LabelExclusion.constant ⟨42, [], [⟨0,0,35⟩, ⟨0,1,-56⟩, ⟨1,0,8⟩], [⟨0,0,-14⟩, ⟨0,1,-8⟩, ⟨1,0,8⟩], [⟨0,0,-21⟩, ⟨0,1,48⟩]⟩,
  LabelExclusion.constant ⟨8, [], [⟨0,0,8⟩, ⟨0,1,-33⟩, ⟨1,0,6⟩], [⟨0,0,-8⟩, ⟨0,1,-6⟩, ⟨1,0,6⟩], [⟨0,0,-4⟩, ⟨0,1,27⟩]⟩,
  LabelExclusion.constant ⟨14, [], [⟨0,0,26⟩, ⟨0,1,-33⟩, ⟨1,0,6⟩], [⟨0,0,-14⟩, ⟨0,1,-6⟩, ⟨1,0,6⟩], [⟨0,0,-19⟩, ⟨0,1,27⟩]⟩,
  LabelExclusion.constant ⟨3, [], [⟨0,0,2⟩], [⟨0,0,1⟩, ⟨0,1,-8⟩, ⟨1,0,2⟩], [⟨0,0,-6⟩, ⟨0,1,6⟩]⟩,
  LabelExclusion.constant ⟨6, [], [⟨0,0,-1⟩], [⟨0,0,-8⟩, ⟨0,1,4⟩, ⟨1,0,2⟩], [⟨0,0,6⟩, ⟨0,1,-3⟩]⟩,
  LabelExclusion.constant ⟨6, [], [⟨0,0,4⟩], [⟨0,0,-4⟩, ⟨0,1,-10⟩, ⟨1,0,4⟩], [⟨0,0,-3⟩, ⟨0,1,3⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.circle 0], [⟨0,0,-10⟩, ⟨0,1,-2⟩, ⟨1,0,-1⟩], [⟨0,0,4⟩, ⟨0,1,-4⟩, ⟨1,0,-2⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 2], [⟨0,0,2⟩, ⟨0,1,-4⟩, ⟨0,2,-3⟩, ⟨1,0,3⟩, ⟨1,1,-2⟩, ⟨2,0,-3⟩], [⟨0,0,-2⟩, ⟨0,1,4⟩, ⟨1,1,8⟩], []⟩]

private def exclusionRow19 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨6, [Guard.circle 2], [⟨0,0,2⟩, ⟨0,1,1⟩, ⟨0,2,-3⟩, ⟨1,0,-2⟩, ⟨1,1,-2⟩, ⟨2,0,-3⟩], [⟨0,0,-2⟩, ⟨0,1,2⟩, ⟨1,0,2⟩, ⟨1,1,8⟩], []⟩,
  LabelExclusion.constant ⟨6, [], [⟨0,0,-4⟩], [⟨0,0,-8⟩, ⟨0,1,2⟩, ⟨1,0,4⟩], [⟨0,0,9⟩, ⟨0,1,-3⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.circle 0], [⟨0,0,-2⟩, ⟨1,0,-1⟩], [], []⟩,
  LabelExclusion.constant ⟨2178000, [], [⟨0,0,-1089000⟩, ⟨0,1,29614114⟩, ⟨0,2,44502360⟩, ⟨1,0,-22188761⟩, ⟨1,1,-229311868⟩, ⟨1,2,-12514515⟩, ⟨2,0,92411233⟩, ⟨2,1,61384442⟩, ⟨3,0,43146117⟩, ⟨3,1,6745224⟩, ⟨4,0,-20235672⟩], [⟨0,0,-29614114⟩, ⟨0,1,-49706064⟩, ⟨0,2,-243841570⟩, ⟨1,0,16249900⟩, ⟨1,1,1294749098⟩, ⟨1,2,142539330⟩, ⟨2,0,-154268590⟩, ⟨2,1,-872197852⟩, ⟨3,0,-295250950⟩, ⟨3,1,102067986⟩, ⟨4,0,248177610⟩, ⟨5,0,-40471344⟩], [⟨0,0,5203704⟩, ⟨0,1,243841570⟩, ⟨1,0,-145648862⟩, ⟨1,1,-386380900⟩, ⟨2,0,29378482⟩, ⟨2,1,264460115⟩, ⟨3,0,88779363⟩, ⟨3,1,-71269665⟩, ⟨4,0,-70127013⟩, ⟨5,0,20235672⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.circle 0], [⟨0,0,-1⟩, ⟨1,0,-1⟩], [⟨0,0,2⟩], []⟩,
  LabelExclusion.constant ⟨20, [Guard.circle 0], [⟨0,0,-8⟩, ⟨0,1,-2⟩, ⟨1,0,-5⟩], [⟨0,0,2⟩, ⟨0,1,-2⟩], []⟩,
  LabelExclusion.constant ⟨3570, [Guard.triangle 0], [⟨0,0,6384⟩, ⟨0,1,-2812⟩, ⟨0,2,-1312⟩, ⟨1,0,1717⟩, ⟨1,1,2008⟩, ⟨2,0,-420⟩], [⟨0,0,5128⟩, ⟨0,1,280⟩, ⟨0,2,-2624⟩, ⟨1,0,2554⟩, ⟨1,1,10576⟩, ⟨2,0,-11068⟩, ⟨2,1,-1312⟩, ⟨3,0,1680⟩], [⟨0,0,-1256⟩, ⟨0,1,3092⟩, ⟨0,2,-1312⟩, ⟨1,0,-8867⟩, ⟨1,1,-1928⟩, ⟨2,0,6448⟩, ⟨2,1,1312⟩, ⟨3,0,-1680⟩]⟩,
  LabelExclusion.constant ⟨66690, [Guard.triangle 0], [⟨0,0,-2516⟩, ⟨0,1,27616⟩, ⟨0,2,1408⟩, ⟨1,0,-41103⟩, ⟨1,1,-7232⟩, ⟨2,0,19839⟩, ⟨2,1,616⟩, ⟨3,0,-2240⟩], [⟨0,0,95416⟩, ⟨0,1,-23040⟩, ⟨0,2,-1408⟩, ⟨1,0,76738⟩, ⟨1,1,9872⟩, ⟨2,0,-65916⟩, ⟨2,1,-2464⟩, ⟨3,0,8960⟩], [⟨0,0,97932⟩, ⟨0,1,-50656⟩, ⟨0,2,-2816⟩, ⟨1,0,-63247⟩, ⟨1,1,7952⟩, ⟨2,0,44797⟩, ⟨2,1,1848⟩, ⟨3,0,-6720⟩]⟩,
  LabelExclusion.constant ⟨1764, [Guard.circle 0], [⟨0,0,-882⟩, ⟨0,1,-398⟩, ⟨1,0,-17⟩, ⟨2,0,-72⟩], [⟨0,0,398⟩, ⟨0,1,-614⟩, ⟨1,0,1552⟩, ⟨2,0,-288⟩], [⟨0,0,216⟩, ⟨0,1,-216⟩, ⟨1,0,-432⟩, ⟨2,0,216⟩]⟩,
  LabelExclusion.constant ⟨51174914, [], [⟨0,0,-25587457⟩, ⟨0,1,39809650⟩, ⟨0,2,685136970⟩, ⟨1,0,166847409⟩, ⟨1,1,-2135216918⟩, ⟨1,2,-381655869⟩, ⟨2,0,-184654964⟩, ⟨2,1,865772793⟩, ⟨3,0,246556840⟩, ⟨3,1,54177474⟩, ⟨4,0,-108354948⟩], [⟨0,0,-90984564⟩, ⟨0,1,-458575086⟩, ⟨0,2,-858287294⟩, ⟨1,0,-506758478⟩, ⟨1,1,5668538006⟩, ⟨1,2,1324754670⟩, ⟨2,0,2135597008⟩, ⟨2,1,-8818106450⟩, ⟨3,0,-1710449076⟩, ⟨3,1,1689155898⟩, ⟨4,0,1034888420⟩, ⟨5,0,-216709896⟩], [⟨0,0,-212339691⟩, ⟨0,1,1730176498⟩, ⟨0,2,-1543424264⟩, ⟨1,0,-236471210⟩, ⟨1,1,-1572289157⟩, ⟨1,2,1706410539⟩, ⟨2,0,866200327⟩, ⟨2,1,843500998⟩, ⟨3,0,501067708⟩, ⟨3,1,-1115465319⟩, ⟨4,0,-84024418⟩, ⟨5,0,108354948⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.circle 0], [⟨0,0,-2⟩, ⟨1,0,-1⟩], [⟨0,0,2⟩, ⟨0,1,-2⟩], []⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨0,0,-3⟩, ⟨0,1,15⟩, ⟨0,2,1⟩, ⟨0,3,-1⟩, ⟨1,0,6⟩, ⟨1,1,-10⟩, ⟨1,2,2⟩], [⟨0,0,-2⟩, ⟨0,1,-2⟩, ⟨0,2,-8⟩, ⟨0,3,2⟩, ⟨1,0,-6⟩, ⟨1,1,10⟩, ⟨1,2,-2⟩], [⟨0,0,1⟩, ⟨0,1,-9⟩, ⟨0,2,2⟩, ⟨1,0,-3⟩, ⟨1,1,5⟩, ⟨1,2,-1⟩]⟩,
  LabelExclusion.constant ⟨8, [Guard.triangle 0], [⟨0,0,6⟩, ⟨0,1,-41⟩, ⟨0,2,22⟩, ⟨0,3,-3⟩], [⟨0,0,-52⟩, ⟨0,1,58⟩, ⟨0,2,-12⟩, ⟨1,0,36⟩, ⟨1,1,-32⟩, ⟨1,2,6⟩], [⟨0,0,30⟩, ⟨0,1,-9⟩]⟩,
  LabelExclusion.constant ⟨22, [Guard.triangle 0], [⟨0,0,90⟩, ⟨0,1,-44⟩, ⟨0,2,6⟩, ⟨1,0,-3⟩], [⟨0,0,-100⟩, ⟨0,1,64⟩, ⟨0,2,-12⟩, ⟨1,0,6⟩], [⟨0,0,-34⟩, ⟨0,1,12⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨0,0,-30⟩, ⟨0,1,-11⟩, ⟨1,0,31⟩, ⟨1,1,3⟩, ⟨2,0,-6⟩], [⟨0,0,22⟩, ⟨0,1,44⟩, ⟨1,0,-204⟩, ⟨1,1,-12⟩, ⟨2,0,98⟩, ⟨3,0,-12⟩], [⟨1,0,66⟩, ⟨2,0,-40⟩, ⟨3,0,6⟩]⟩,
  LabelExclusion.constant ⟨789056889156, [Guard.aOrder], [⟨0,0,1398938293025⟩, ⟨0,1,-664969390500⟩, ⟨1,0,-6303932250189⟩, ⟨1,1,-1130597740397⟩, ⟨1,2,1935918951375⟩, ⟨2,0,8735967404622⟩, ⟨2,1,-617071378648⟩, ⟨2,2,-2206113546738⟩, ⟨3,0,-3850121796878⟩, ⟨3,1,2239356555327⟩], [⟨0,0,-201284659214⟩, ⟨0,1,204495963100⟩, ⟨0,2,664969390500⟩, ⟨1,0,3817356236816⟩, ⟨1,1,-423329840146⟩, ⟨1,2,-2116318229392⟩, ⟨2,0,-7471687014000⟩, ⟨2,1,-58506246094⟩, ⟨2,2,1548149857360⟩, ⟨3,0,5611538769668⟩, ⟨3,1,-100735919948⟩, ⟨4,0,-1492904370218⟩], [⟨0,0,394528444578⟩, ⟨0,1,201284659214⟩, ⟨0,2,-1603434256125⟩, ⟨1,0,-702482859626⟩, ⟨1,1,1820627092236⟩, ⟨1,2,1147954432042⟩, ⟨2,0,1274353328364⟩, ⟨2,1,480126454940⟩, ⟨2,2,774074928680⟩, ⟨3,0,-2558015805447⟩, ⟨3,1,-2372592746014⟩, ⟨4,0,1610765241551⟩]⟩]

private def exclusionRow20 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨1069363680848945395715736, [], [⟨0,0,7474257984902278504516064⟩, ⟨0,1,-3636304194335473841206400⟩, ⟨1,0,-10062726836660165721517260⟩, ⟨1,1,-1965521238649603300177464⟩, ⟨1,2,2234674213973436651505024⟩, ⟨2,0,16632503368055881742292994⟩, ⟨2,1,3463993448650372059347554⟩, ⟨2,2,-2845978008848969346188408⟩, ⟨3,0,-22377662689236966257722020⟩, ⟨3,1,9159740375038171963052545⟩, ⟨3,2,-226030329931387937441330⟩, ⟨4,0,4557881999709362648049525⟩, ⟨4,1,-2079033894604270681566450⟩], [⟨0,0,-7418024717800883313056528⟩, ⟨0,1,-7057735868096578773614240⟩, ⟨0,2,3636304194335473841206400⟩, ⟨1,0,36660477400391483817940882⟩, ⟨1,1,17050212642463969740095500⟩, ⟨1,2,-8412785666448931671788456⟩, ⟨2,0,-62705483218570674103481634⟩, ⟨2,1,2255485403630973415986744⟩, ⟨2,2,4448469643785050592979402⟩, ⟨3,0,49200576176711597545507352⟩, ⟨3,1,-16155860673464958212146732⟩, ⟨3,2,382512866037733432593020⟩, ⟨4,0,-17460124975052812829904610⟩, ⟨4,1,3744395382338615244707630⟩, ⟨5,0,2079033894604270681566450⟩], [⟨0,0,-534681840424472697857868⟩, ⟨0,1,7418024717800883313056528⟩, ⟨0,2,-416522116805699730901824⟩, ⟨1,0,-12252634024651665556760064⟩, ⟨1,1,-4607275629969556973982222⟩, ⟨1,2,-1360414824375496489705820⟩, ⟨2,0,11952870579980722910801041⟩, ⟨2,1,1035371378005869943853833⟩, ⟨2,2,2450265151823913233931031⟩, ⟨3,0,-2766104050559233545281367⟩, ⟨3,1,-10360431343631955964624268⟩, ⟨3,2,191256433018866716296510⟩, ⟨4,0,10115122450694830131733535⟩, ⟨4,1,1489684825131574189760795⟩, ⟨5,0,-2478848105105091966483075⟩]⟩,
  LabelExclusion.constant ⟨54, [Guard.triangle 5], [⟨0,0,27⟩, ⟨1,0,-306⟩, ⟨1,1,198⟩, ⟨1,2,76⟩, ⟨2,0,432⟩, ⟨2,1,-228⟩], [⟨0,0,-312⟩, ⟨0,1,410⟩, ⟨0,2,-76⟩, ⟨1,0,600⟩, ⟨1,1,356⟩, ⟨1,2,-228⟩, ⟨2,0,-288⟩, ⟨2,1,152⟩], [⟨0,0,285⟩, ⟨0,1,-335⟩, ⟨0,2,-114⟩, ⟨1,0,174⟩, ⟨1,1,64⟩, ⟨1,2,-114⟩, ⟨2,0,-576⟩, ⟨2,1,304⟩]⟩,
  LabelExclusion.constant ⟨9176, [Guard.triangle 0], [⟨0,0,7140⟩, ⟨0,1,-5606⟩, ⟨0,2,525⟩, ⟨1,0,15483⟩, ⟨1,1,-11971⟩, ⟨1,2,2250⟩, ⟨2,0,-132⟩, ⟨2,1,60⟩], [⟨0,0,-9176⟩, ⟨0,1,-2552⟩, ⟨0,2,1200⟩, ⟨1,0,-836⟩, ⟨1,1,1982⟩, ⟨2,0,10370⟩, ⟨2,1,-3300⟩, ⟨3,0,-88⟩], [⟨0,0,2036⟩, ⟨0,1,8158⟩, ⟨0,2,-1725⟩, ⟨1,0,-7871⟩, ⟨1,1,6463⟩, ⟨1,2,-1650⟩, ⟨2,0,-8406⟩, ⟨2,1,2656⟩, ⟨3,0,72⟩]⟩,
  LabelExclusion.constant ⟨32, [Guard.triangle 5], [⟨0,0,-602⟩, ⟨0,1,301⟩, ⟨1,0,992⟩, ⟨1,1,-430⟩, ⟨2,0,-238⟩, ⟨2,1,102⟩], [⟨0,0,380⟩, ⟨0,1,132⟩, ⟨1,0,-1986⟩, ⟨1,1,-34⟩, ⟨2,0,1366⟩, ⟨3,0,-238⟩], [⟨0,0,222⟩, ⟨0,1,-433⟩, ⟨1,0,186⟩, ⟨1,1,530⟩, ⟨2,0,-528⟩, ⟨2,1,-119⟩, ⟨3,0,136⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-2⟩], [⟨0,0,1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,4⟩, ⟨1,0,-1⟩], [⟨0,0,-8⟩, ⟨1,0,2⟩], []⟩,
  LabelExclusion.constant ⟨35193858, [], [⟨0,0,-8189095⟩, ⟨0,1,18018320⟩, ⟨0,2,-27426154⟩, ⟨1,0,-20404446⟩, ⟨1,1,101324270⟩, ⟨1,2,-40882688⟩, ⟨2,0,151998150⟩, ⟨2,1,66826254⟩, ⟨3,0,-204785332⟩, ⟨3,1,-22116864⟩, ⟨4,0,76028716⟩, ⟨5,0,-8233984⟩], [⟨0,0,20701414⟩, ⟨0,1,-151867664⟩, ⟨0,2,59138404⟩, ⟨1,0,22163084⟩, ⟨1,1,-108587292⟩, ⟨1,2,-23170048⟩, ⟨2,0,-84308172⟩, ⟨2,1,77782164⟩, ⟨3,0,204263608⟩, ⟨3,1,11297792⟩, ⟨4,0,-119121496⟩, ⟨5,0,16467968⟩], [⟨0,0,-17596929⟩, ⟨0,1,-55895272⟩, ⟨0,2,86564558⟩, ⟨1,0,-22863026⟩, ⟨1,1,85237382⟩, ⟨1,2,17712640⟩, ⟨2,0,12184458⟩, ⟨2,1,-197858042⟩, ⟨3,0,-24180228⟩, ⟨3,1,27287040⟩, ⟨4,0,43092780⟩, ⟨5,0,-8233984⟩]⟩,
  LabelExclusion.constant ⟨9707891270, [], [⟨0,0,99108651438⟩, ⟨0,1,-35339494312⟩, ⟨0,2,-68623102761⟩, ⟨1,0,-73242209517⟩, ⟨1,1,-65336896373⟩, ⟨1,2,-3287241420⟩, ⟨2,0,-45792722158⟩, ⟨2,1,-42917931775⟩, ⟨3,0,71803458945⟩, ⟨3,1,30606553200⟩, ⟨4,0,-10202184400⟩], [⟨0,0,-109370452996⟩, ⟨0,1,43414603872⟩, ⟨0,2,-116337741980⟩, ⟨1,0,-72582303554⟩, ⟨1,1,368772343050⟩, ⟨1,2,20102254000⟩, ⟨2,0,-7090467972⟩, ⟨2,1,-179227432226⟩, ⟨3,0,255596731006⟩, ⟨3,1,63102485880⟩, ⟨4,0,-164011286690⟩, ⟨5,0,20404368800⟩], [⟨0,0,-4853945635⟩, ⟨0,1,99662561726⟩, ⟨0,2,-47714639219⟩, ⟨1,0,-153793877936⟩, ⟨1,1,-4564991657⟩, ⟨1,2,23389495420⟩, ⟨2,0,289853587114⟩, ⟨2,1,49983025758⟩, ⟨3,0,-167054430523⟩, ⟨3,1,-944689740⟩, ⟨4,0,41196905745⟩, ⟨5,0,-10202184400⟩]⟩,
  LabelExclusion.constant ⟨460053554744, [], [⟨0,0,3487690826230⟩, ⟨0,1,-6082656318258⟩, ⟨0,2,2364938714656⟩, ⟨1,0,1658575968680⟩, ⟨1,1,-2897639753802⟩, ⟨1,2,-1746799295311⟩, ⟨2,0,-1496937288093⟩, ⟨2,1,7784760269720⟩, ⟨2,2,81543007014⟩, ⟨3,0,-5040110961320⟩, ⟨3,1,-2028119703797⟩, ⟨4,0,2992920243160⟩, ⟨4,1,58245005010⟩, ⟨5,0,-424301361000⟩], [⟨0,0,-4613730900058⟩, ⟨0,1,5503685558832⟩, ⟨0,2,-2702787102464⟩, ⟨1,0,3014180713706⟩, ⟨1,1,5635922686802⟩, ⟨1,2,1996342051784⟩, ⟨2,0,-3277462380774⟩, ⟨2,1,-11321587927194⟩, ⟨2,2,-93192008016⟩, ⟨3,0,8337395046320⟩, ⟨3,1,3430587764374⟩, ⟨4,0,-5137237764320⟩, ⟨4,1,-116490010020⟩, ⟨5,0,848602722000⟩], [⟨0,0,-230026777372⟩, ⟨0,1,4153677345314⟩, ⟨0,2,-5067725817120⟩, ⟨1,0,-5794556276259⟩, ⟨1,1,8617928878082⟩, ⟨1,2,3743141347095⟩, ⟨2,0,-96700309454⟩, ⟨2,1,-10302216298270⟩, ⟨2,2,-174735015030⟩, ⟨3,0,6515803729424⟩, ⟨3,1,1529182105044⟩, ⟨4,0,-1866925988400⟩]⟩,
  LabelExclusion.constant ⟨1176, [Guard.triangle 0], [⟨0,0,32818⟩, ⟨0,1,-46507⟩, ⟨0,2,-32131⟩, ⟨1,0,838⟩, ⟨1,1,104727⟩, ⟨2,0,-47514⟩, ⟨2,1,-11176⟩, ⟨3,0,7272⟩], [⟨0,0,-588⟩, ⟨0,1,-17144⟩, ⟨0,2,8382⟩, ⟨1,0,22600⟩, ⟨1,1,-61334⟩, ⟨2,0,22308⟩, ⟨2,1,22352⟩, ⟨3,0,-14544⟩], [⟨0,0,-33406⟩, ⟨0,1,29363⟩, ⟨0,2,40513⟩, ⟨1,0,-4472⟩, ⟨1,1,-59889⟩, ⟨2,0,28842⟩, ⟨2,1,-11176⟩, ⟨3,0,7272⟩]⟩,
  LabelExclusion.constant ⟨555696, [Guard.triangle 0], [⟨0,0,-2768752⟩, ⟨0,1,-3326752⟩, ⟨0,2,1889085⟩, ⟨1,0,16530473⟩, ⟨1,1,-4938321⟩, ⟨1,2,-558210⟩, ⟨2,0,-7227298⟩, ⟨2,1,2630631⟩, ⟨3,0,765348⟩, ⟨3,1,-260498⟩], [⟨0,0,-555696⟩, ⟨0,1,1935208⟩, ⟨0,2,-755634⟩, ⟨1,0,-10448570⟩, ⟨1,1,4214730⟩, ⟨1,2,223284⟩, ⟨2,0,8331812⟩, ⟨2,1,-3177278⟩, ⟨3,0,-1530696⟩, ⟨3,1,520996⟩], [⟨0,0,2213056⟩, ⟨0,1,5261960⟩, ⟨0,2,-2644719⟩, ⟨1,0,-13008647⟩, ⟨1,1,3107979⟩, ⟨1,2,781494⟩, ⟨2,0,3657322⟩, ⟨2,1,-1376918⟩]⟩,
  LabelExclusion.constant ⟨70, [Guard.triangle 0], [⟨1,0,-410⟩, ⟨1,1,88⟩, ⟨1,2,-30⟩, ⟨2,0,403⟩, ⟨2,1,-51⟩, ⟨2,2,10⟩, ⟨3,0,-126⟩, ⟨3,1,6⟩, ⟨4,0,12⟩], [⟨0,0,-60⟩, ⟨0,1,34⟩, ⟨0,2,40⟩, ⟨0,3,20⟩, ⟨1,0,48⟩, ⟨1,1,-176⟩, ⟨1,2,20⟩, ⟨2,0,-398⟩, ⟨2,1,102⟩, ⟨2,2,-20⟩, ⟨3,0,204⟩, ⟨3,1,-12⟩, ⟨4,0,-24⟩], [⟨0,0,40⟩, ⟨0,1,-92⟩, ⟨0,2,7⟩, ⟨0,3,-20⟩, ⟨1,0,181⟩, ⟨1,1,112⟩, ⟨1,2,-6⟩, ⟨2,0,97⟩, ⟨2,1,-51⟩, ⟨2,2,10⟩, ⟨3,0,-90⟩, ⟨3,1,6⟩, ⟨4,0,12⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨1,0,5⟩, ⟨1,1,-1⟩], [⟨0,0,-22⟩, ⟨0,2,-2⟩, ⟨1,0,30⟩, ⟨1,1,-2⟩, ⟨2,0,-10⟩, ⟨2,1,2⟩], [⟨0,0,14⟩, ⟨0,1,1⟩, ⟨0,2,1⟩, ⟨1,0,-22⟩, ⟨1,1,2⟩, ⟨2,0,5⟩, ⟨2,1,-1⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 0], [⟨1,0,39⟩, ⟨1,1,28⟩, ⟨2,0,-45⟩, ⟨2,1,-8⟩, ⟨3,0,10⟩], [⟨0,0,-8⟩, ⟨0,1,-34⟩, ⟨0,2,-8⟩, ⟨1,0,-28⟩, ⟨1,1,-30⟩, ⟨2,0,70⟩, ⟨2,1,16⟩, ⟨3,0,-20⟩], [⟨0,0,-4⟩, ⟨0,1,14⟩, ⟨0,2,8⟩, ⟨1,0,-20⟩, ⟨1,1,-22⟩, ⟨2,0,15⟩]⟩,
  LabelExclusion.constant ⟨5, [Guard.circle 1], [], [⟨0,0,2⟩, ⟨0,1,-1⟩], [⟨0,0,-3⟩, ⟨0,1,-1⟩]⟩,
  LabelExclusion.constant ⟨13950, [Guard.triangle 0], [⟨0,0,-27900⟩, ⟨0,1,13956⟩, ⟨1,0,15039⟩, ⟨1,1,-4344⟩, ⟨2,0,-2016⟩], [⟨0,0,31932⟩, ⟨0,1,-2166⟩, ⟨1,0,-35964⟩, ⟨1,1,304⟩, ⟨2,0,8064⟩], [⟨0,0,25422⟩, ⟨0,1,-16122⟩, ⟨1,0,4797⟩, ⟨1,1,4648⟩, ⟨2,0,-3560⟩]⟩]

private def exclusionRow21 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨161649726, [], [⟨0,0,177027519⟩, ⟨0,1,-236036692⟩, ⟨1,0,3655751348⟩, ⟨1,1,-1779394480⟩, ⟨2,0,-5226143396⟩, ⟨2,1,3078920752⟩, ⟨3,0,1312539666⟩, ⟨3,1,-813016696⟩], [⟨0,0,922331078⟩, ⟨0,1,-236036692⟩, ⟨1,0,-3206297608⟩, ⟨1,1,541811008⟩, ⟨2,0,3578023080⟩, ⟨2,1,161967920⟩, ⟨3,0,-3347629660⟩, ⟨3,1,-110239552⟩, ⟨4,0,813016696⟩], [⟨0,0,-80824863⟩, ⟨1,0,-2644504940⟩, ⟨1,1,2321205488⟩, ⟨2,0,1811690388⟩, ⟨2,1,-2916952832⟩, ⟨3,0,1490675050⟩, ⟨3,1,702777144⟩, ⟨4,0,-592537592⟩]⟩,
  LabelExclusion.constant ⟨30843246, [], [⟨0,0,101589303⟩, ⟨0,1,-106729844⟩, ⟨1,0,429920340⟩, ⟨1,1,-774371924⟩, ⟨2,0,-412084715⟩, ⟨2,1,1310448303⟩, ⟨3,0,-249264005⟩, ⟨3,1,-366777446⟩, ⟨4,0,114417454⟩], [⟨0,0,459722134⟩, ⟨0,1,-106729844⟩, ⟨1,0,-1751734210⟩, ⟨1,1,232219780⟩, ⟨2,0,1962635654⟩, ⟨2,1,197526912⟩, ⟨3,0,-1858929552⟩, ⟨3,1,-94100336⟩, ⟨4,0,457669816⟩], [⟨0,0,-15421623⟩, ⟨1,0,-362293616⟩, ⟨1,1,1006591704⟩, ⟨2,0,-60040238⟩, ⟨2,1,-1112921391⟩, ⟨3,0,559503169⟩, ⟨3,1,272677110⟩, ⟨4,0,-202101858⟩]⟩,
  LabelExclusion.constant ⟨4259374, [], [⟨0,0,37172795⟩, ⟨0,1,-40552140⟩, ⟨1,0,46180412⟩, ⟨1,1,15770616⟩, ⟨2,0,-260666732⟩, ⟨2,1,132631950⟩, ⟨3,0,83076455⟩, ⟨3,1,-47761725⟩], [⟨0,0,95871318⟩, ⟨0,1,-40552140⟩, ⟨1,0,-248689970⟩, ⟨1,1,96619696⟩, ⟨2,0,285045300⟩, ⟨2,1,-52817976⟩, ⟨3,0,-257313870⟩, ⟨3,1,4631440⟩, ⟨4,0,63682300⟩], [⟨0,0,-2129687⟩, ⟨1,0,-89367828⟩, ⟨1,1,80849080⟩, ⟨2,0,167646830⟩, ⟨2,1,-185449926⟩, ⟨3,0,63440864⟩, ⟨3,1,52393165⟩, ⟨4,0,-38788310⟩]⟩,
  LabelExclusion.constant ⟨1242, [Guard.circle 0], [⟨0,0,-574⟩, ⟨0,1,-146⟩, ⟨1,0,-175⟩, ⟨1,1,-49⟩, ⟨2,0,-13⟩, ⟨2,1,-9⟩, ⟨3,0,-6⟩], [⟨0,0,196⟩, ⟨0,1,-196⟩, ⟨1,0,-206⟩, ⟨1,1,-62⟩, ⟨2,0,124⟩, ⟨2,1,-18⟩, ⟨3,0,24⟩], [⟨1,0,84⟩, ⟨1,1,48⟩, ⟨2,0,-66⟩, ⟨2,1,18⟩, ⟨3,0,-9⟩]⟩,
  LabelExclusion.constant ⟨39648, [Guard.triangle 0], [⟨0,0,137258⟩, ⟨0,1,111138⟩, ⟨0,2,-7616⟩, ⟨1,0,28821⟩, ⟨1,1,18675⟩, ⟨1,2,-3584⟩, ⟨2,0,-22376⟩, ⟨2,1,-19579⟩], [⟨0,0,100272⟩, ⟨0,1,-61776⟩, ⟨0,2,1152⟩, ⟨1,0,5988⟩, ⟨1,1,135046⟩, ⟨1,2,-7168⟩, ⟨2,0,-294292⟩, ⟨2,1,-22774⟩, ⟨3,0,89504⟩], [⟨1,0,-266690⟩, ⟨1,1,-138570⟩, ⟨1,2,8192⟩, ⟨2,0,212389⟩, ⟨2,1,35536⟩, ⟨3,0,-50346⟩]⟩,
  LabelExclusion.constant ⟨16524, [Guard.circle 0], [⟨0,0,-9952⟩, ⟨0,1,-932⟩, ⟨1,0,-3801⟩, ⟨1,1,342⟩, ⟨2,0,2591⟩, ⟨2,1,-805⟩, ⟨3,0,-736⟩], [⟨0,0,7388⟩, ⟨0,1,-7388⟩, ⟨1,0,-5856⟩, ⟨1,1,3490⟩, ⟨2,0,-4476⟩, ⟨2,1,-1610⟩, ⟨3,0,2944⟩], [⟨1,0,6258⟩, ⟨1,1,-2762⟩, ⟨2,0,-2093⟩, ⟨2,1,1403⟩, ⟨3,0,-529⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 7], [⟨0,0,36⟩, ⟨0,1,39⟩, ⟨1,0,-39⟩], [⟨0,0,6⟩, ⟨0,1,-6⟩, ⟨1,0,-18⟩], [⟨0,0,-54⟩, ⟨0,1,-45⟩, ⟨1,0,69⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 7], [⟨0,0,-6⟩, ⟨0,1,9⟩, ⟨1,0,-6⟩], [⟨1,0,-6⟩], [⟨0,0,6⟩, ⟨0,1,-9⟩, ⟨1,0,9⟩]⟩,
  LabelExclusion.constant ⟨9519090, [Guard.triangle 0], [⟨0,0,13758558⟩, ⟨0,1,14825355⟩, ⟨0,2,-3843567⟩, ⟨1,0,-20618300⟩, ⟨1,1,7541549⟩, ⟨1,2,-2732561⟩, ⟨2,0,-3677604⟩, ⟨2,1,3020889⟩], [⟨0,0,-10932246⟩, ⟨0,1,-4879618⟩, ⟨0,2,1104584⟩, ⟨1,0,10757890⟩, ⟨1,1,19299456⟩, ⟨1,2,-5465122⟩, ⟨2,0,-22719788⟩, ⟨2,1,9368374⟩, ⟨3,0,-3677604⟩], [⟨1,0,-1243201⟩, ⟨1,1,-22190838⟩, ⟨1,2,4395859⟩, ⟨2,0,24599032⟩, ⟨2,1,-4384463⟩, ⟨3,0,-525372⟩]⟩,
  LabelExclusion.constant ⟨457296700146, [Guard.triangle 0], [⟨0,0,6408331244172⟩, ⟨0,1,457360686520⟩, ⟨0,2,516992708516⟩, ⟨0,3,-1517484124736⟩, ⟨1,0,13918515489927⟩, ⟨1,1,-20148696475115⟩, ⟨1,2,3804239819556⟩, ⟨1,3,341007668480⟩, ⟨2,0,-8021243570869⟩, ⟨2,1,16665907341340⟩, ⟨2,2,-2384859667216⟩, ⟨3,0,-1733843916439⟩, ⟨3,1,-2533468994716⟩, ⟨3,2,341007668480⟩, ⟨4,0,686512571120⟩, ⟨4,1,-85251917120⟩], [⟨0,0,-7322924644464⟩, ⟨0,1,-5948009809336⟩, ⟨0,2,12378300841616⟩, ⟨0,3,-3887487420672⟩, ⟨1,0,39708647937558⟩, ⟨1,1,-43608171777860⟩, ⟨1,2,9597889469360⟩, ⟨1,3,682015336960⟩, ⟨2,0,-25219848572276⟩, ⟨2,1,35464057155768⟩, ⟨2,2,-5792742339872⟩, ⟨3,0,-6935375665756⟩, ⟨3,1,-4641775409904⟩, ⟨3,2,682015336960⟩, ⟨4,0,2746050284480⟩, ⟨4,1,-341007668480⟩], [⟨1,0,-36920390266836⟩, ⟨1,1,33953343475292⟩, ⟨1,2,-7081529088860⟩, ⟨1,3,-426259585600⟩, ⟨2,0,24745674343644⟩, ⟨2,1,-24681285349971⟩, ⟨2,2,4046723548020⟩, ⟨3,0,-2746050284480⟩, ⟨3,1,3773570524080⟩, ⟨3,2,-426259585600⟩]⟩,
  LabelExclusion.constant ⟨545454, [Guard.triangle 0], [⟨0,0,2559324⟩, ⟨0,1,-1946328⟩, ⟨0,2,67980⟩, ⟨1,0,3183741⟩, ⟨1,1,-2425524⟩, ⟨1,2,723060⟩, ⟨2,0,623727⟩, ⟨2,1,-431811⟩], [⟨0,0,-3650232⟩, ⟨0,1,5239860⟩, ⟨0,2,-1256600⟩, ⟨1,0,1200832⟩, ⟨1,1,-4287212⟩, ⟨1,2,1446120⟩, ⟨2,0,3989100⟩, ⟨2,1,-2256182⟩, ⟨3,0,831636⟩], [⟨1,0,-4468546⟩, ⟨1,1,4073918⟩, ⟨1,2,-696280⟩, ⟨2,0,-1562745⟩, ⟨2,1,362258⟩, ⟨3,0,31986⟩]⟩,
  LabelExclusion.constant ⟨378, [Guard.triangle 0], [⟨0,0,56⟩, ⟨1,0,14⟩, ⟨2,0,7⟩], [⟨0,0,-384⟩, ⟨0,1,136⟩, ⟨1,0,-112⟩, ⟨1,1,22⟩, ⟨2,0,-28⟩], [⟨0,0,340⟩, ⟨0,1,-88⟩, ⟨1,0,47⟩, ⟨1,1,-18⟩, ⟨2,0,17⟩]⟩,
  LabelExclusion.constant ⟨14, [Guard.triangle 0], [⟨0,0,-20⟩, ⟨1,0,6⟩], [⟨0,0,-62⟩, ⟨0,1,-20⟩, ⟨1,0,58⟩, ⟨1,1,6⟩, ⟨2,0,-12⟩], [⟨0,0,54⟩, ⟨0,1,10⟩, ⟨1,0,-35⟩, ⟨1,1,-3⟩, ⟨2,0,6⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 0], [⟨0,0,-30⟩, ⟨1,0,54⟩, ⟨2,0,-12⟩], [⟨0,0,-64⟩, ⟨0,1,154⟩, ⟨1,0,-168⟩, ⟨1,1,-40⟩, ⟨2,0,48⟩], [⟨0,0,58⟩, ⟨0,1,-46⟩, ⟨1,0,-1⟩, ⟨1,1,12⟩, ⟨2,0,-4⟩]⟩,
  LabelExclusion.constant ⟨36580500, [], [⟨0,0,34784700⟩, ⟨0,1,35768516⟩, ⟨0,2,6702106⟩, ⟨0,3,3607400⟩, ⟨1,0,-32570155⟩, ⟨1,1,-39928517⟩, ⟨1,2,-3287152⟩, ⟨1,3,-10664530⟩, ⟨2,0,22520576⟩, ⟨2,1,-4229849⟩, ⟨2,2,-1969565⟩, ⟨2,3,7880145⟩, ⟨3,0,-5060874⟩, ⟨3,1,5060874⟩, ⟨3,2,-2530437⟩], [⟨0,0,70155632⟩, ⟨0,1,74315592⟩, ⟨0,2,1025388⟩, ⟨0,3,-7214800⟩, ⟨1,0,-115558270⟩, ⟨1,1,-178802764⟩, ⟨1,2,-36083816⟩, ⟨1,3,21329060⟩, ⟨2,0,77864664⟩, ⟨2,1,116472238⟩, ⟨2,2,35459710⟩, ⟨2,3,-15760290⟩, ⟨3,0,-27581450⟩, ⟨3,1,-36003786⟩, ⟨3,2,5060874⟩, ⟨4,0,5060874⟩], [⟨0,0,17080682⟩, ⟨0,1,-32525008⟩, ⟨0,2,-7727494⟩, ⟨0,3,3607400⟩, ⟨1,0,-83574347⟩, ⟨1,1,39045636⟩, ⟨1,2,39370968⟩, ⟨1,3,-10664530⟩, ⟨2,0,70977348⟩, ⟨2,1,-4231734⟩, ⟨2,2,-33490145⟩, ⟨2,3,7880145⟩, ⟨3,0,-22773933⟩, ⟨3,1,15182622⟩, ⟨3,2,-2530437⟩]⟩,
  LabelExclusion.constant ⟨9450, [], [⟨0,0,6122⟩, ⟨0,1,-11366⟩, ⟨0,2,3462⟩, ⟨1,0,-6352⟩, ⟨1,1,21904⟩, ⟨1,2,-14156⟩, ⟨1,3,2588⟩, ⟨2,0,-448⟩, ⟨2,1,1324⟩, ⟨2,2,-868⟩, ⟨2,3,160⟩, ⟨3,0,168⟩, ⟨3,1,-576⟩, ⟨3,2,384⟩, ⟨3,3,-72⟩], [⟨0,0,16040⟩, ⟨0,1,2308⟩, ⟨0,2,-3462⟩, ⟨1,0,-12144⟩, ⟨1,1,-14700⟩, ⟨1,2,14156⟩, ⟨1,3,-2588⟩, ⟨2,0,5652⟩, ⟨2,1,-3180⟩, ⟨2,2,868⟩, ⟨2,3,-160⟩, ⟨3,0,616⟩, ⟨3,1,200⟩, ⟨3,2,-384⟩, ⟨3,3,72⟩, ⟨4,0,-168⟩, ⟨4,1,72⟩], [⟨0,0,5193⟩, ⟨1,0,-9588⟩, ⟨1,1,3882⟩, ⟨2,0,-582⟩, ⟨2,1,240⟩, ⟨3,0,252⟩, ⟨3,1,-108⟩]⟩]

private def exclusionRow22 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨73387112928976, [], [⟨0,0,-36693556464488⟩, ⟨0,1,101783752572303⟩, ⟨0,2,-106374753265460⟩, ⟨0,3,115199409865207⟩, ⟨0,4,-110608409172050⟩, ⟨1,0,2981285848787568⟩, ⟨1,1,-3373528064856302⟩, ⟨1,2,-7061374468609807⟩, ⟨1,3,-3029491405653877⟩, ⟨1,4,214302783396701⟩, ⟨2,0,-16410165783572117⟩, ⟨2,1,6102123377235932⟩, ⟨2,2,18466405219001418⟩, ⟨2,3,708593846891236⟩, ⟨2,4,-614284669600647⟩, ⟨3,0,28504185948608357⟩, ⟨3,1,3851226118288322⟩, ⟨3,2,-4646696896020754⟩, ⟨3,3,-173370607266272⟩, ⟨3,4,125948130936606⟩, ⟨4,0,-20728576618478301⟩, ⟨4,1,-2047464123834245⟩, ⟨4,2,866180931473859⟩, ⟨5,0,2904506035219881⟩, ⟨5,1,299318738202878⟩, ⟨5,2,-125948130936606⟩], [⟨0,0,3054672961716544⟩, ⟨0,1,-2899678540683416⟩, ⟨0,2,-362795582084324⟩, ⟨1,0,-24038551271042316⟩, ⟨1,1,7146700173667894⟩, ⟨1,2,565248400060612⟩, ⟨1,3,221216818344100⟩, ⟨2,0,64368372255402260⟩, ⟨2,1,19946078856536530⟩, ⟨2,2,3836191441237102⟩, ⟨2,3,-428605566793402⟩, ⟨3,0,-59678258192154156⟩, ⟨3,1,-35634435685791034⟩, ⟨3,2,-440514616454390⟩, ⟨3,3,1228569339201294⟩, ⟨4,0,11618024140879524⟩, ⟨4,1,7006287023251274⟩, ⟨4,2,94844952659332⟩, ⟨4,3,-251896261873212⟩], [⟨0,0,-4683793195147119⟩, ⟨0,1,1197652097429434⟩, ⟨0,2,181397791042162⟩, ⟨1,0,24101120161904417⟩, ⟨1,1,-3151257743513357⟩, ⟨1,2,-287215200723463⟩, ⟨2,0,-29899516148289284⟩, ⟨2,1,-1130396104314789⟩, ⟨2,2,786484492466575⟩, ⟨3,0,-1569562887751160⟩, ⟨3,1,-4157397596854103⟩, ⟨3,2,340250914333307⟩, ⟨4,0,14919564548038539⟩, ⟨4,1,1448826647428489⟩, ⟨4,2,-614284669600647⟩, ⟨5,0,-2904506035219881⟩, ⟨5,1,-299318738202878⟩, ⟨5,2,125948130936606⟩]⟩,
  LabelExclusion.constant ⟨1803424839178536, [], [⟨0,0,-901712419589268⟩, ⟨0,1,-8941250992242079⟩, ⟨0,2,2719517137008884⟩, ⟨0,3,-181951457934454⟩, ⟨1,0,-2983121880554298⟩, ⟨1,1,11639362539418626⟩, ⟨1,2,-4904324886141943⟩, ⟨1,3,491022245173609⟩, ⟨2,0,1311637296565584⟩, ⟨2,1,-3590418756040496⟩, ⟨2,2,1123000106367528⟩, ⟨2,3,-233776592644867⟩, ⟨3,0,-1256791601367749⟩, ⟨3,1,2060584357632513⟩, ⟨3,2,256634373590520⟩, ⟨3,3,-123891704013390⟩, ⟨4,0,118810340097674⟩, ⟨4,1,-688047874695813⟩, ⟨4,2,86705062364520⟩, ⟨5,0,20876711101120⟩, ⟨5,1,37186641648870⟩], [⟨0,0,-1179697041375762⟩, ⟨0,1,13253314834610052⟩, ⟨0,2,-8589758437997536⟩, ⟨0,3,785264186875012⟩, ⟨1,0,15907268151014872⟩, ⟨1,1,-19270217854682010⟩, ⟨1,2,8655854234097174⟩, ⟨1,3,-1421584044873126⟩, ⟨2,0,-4607362039143426⟩, ⟨2,1,9011268716881328⟩, ⟨2,2,-673775448171684⟩, ⟨2,3,-28013630763826⟩, ⟨3,0,-12899853018092⟩, ⟨3,1,-1459454502375998⟩, ⟨3,2,-937812352567126⟩, ⟨3,3,247783408026780⟩, ⟨4,0,41753422202240⟩, ⟨4,1,116126705499980⟩, ⟨4,2,74373283297740⟩], [⟨0,0,10710796554305722⟩, ⟨0,1,-1177896280312518⟩, ⟨1,0,-13651442115105083⟩, ⟨1,1,8213298003801393⟩, ⟨1,2,-603312728940558⟩, ⟨2,0,650431346726578⟩, ⟨2,1,-3536646585634940⟩, ⟨2,2,930561799699517⟩, ⟨3,0,1528188845682309⟩, ⟨3,1,-1779475200699357⟩, ⟨3,2,261790223408693⟩, ⟨4,0,-118810340097674⟩, ⟨4,1,667171163594693⟩, ⟨4,2,-123891704013390⟩, ⟨5,0,-20876711101120⟩, ⟨5,1,-37186641648870⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,1,-4⟩, ⟨0,2,1⟩], [⟨0,0,-24⟩, ⟨0,1,14⟩, ⟨0,2,-2⟩, ⟨1,0,8⟩, ⟨1,1,-2⟩], [⟨0,0,12⟩, ⟨0,1,-7⟩, ⟨0,2,1⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨0,1,-77⟩, ⟨0,2,43⟩, ⟨0,3,-6⟩, ⟨1,1,33⟩, ⟨1,2,-20⟩, ⟨1,3,3⟩], [⟨0,0,88⟩, ⟨0,1,130⟩, ⟨0,2,-86⟩, ⟨0,3,12⟩, ⟨1,0,-88⟩, ⟨1,1,-42⟩, ⟨1,2,40⟩, ⟨1,3,-6⟩, ⟨2,0,22⟩, ⟨2,1,-6⟩], [⟨0,0,25⟩, ⟨0,1,-6⟩, ⟨1,0,-11⟩, ⟨1,1,3⟩]⟩,
  LabelExclusion.constant ⟨1896101893923750, [], [⟨0,0,1859387860133122⟩, ⟨0,1,2101277038842320⟩, ⟨0,2,-437436886719225⟩, ⟨0,3,-2137030613700328⟩, ⟨1,0,126870966672464⟩, ⟨1,1,-445992213958975⟩, ⟨1,2,1209727882547849⟩, ⟨1,3,938046584143868⟩, ⟨2,0,-7543463611008⟩, ⟨2,1,-122695192665016⟩, ⟨2,2,-253206860754572⟩, ⟨2,3,-81479154618004⟩, ⟨3,1,3771731805504⟩, ⟨3,2,3771731805504⟩], [⟨0,0,-613115621938600⟩, ⟨0,1,9175574799556964⟩, ⟨0,2,6418478412768174⟩, ⟨0,3,-4274061227400656⟩, ⟨1,0,-2267685761938664⟩, ⟨1,1,-3873827356421160⟩, ⟨1,2,1303457115266226⟩, ⟨1,3,1876093168287736⟩, ⟨2,0,237038837315136⟩, ⟨2,1,-1118043218563570⟩, ⟨2,2,-1404757034380832⟩, ⟨2,3,-162958309236008⟩, ⟨3,1,305738094218096⟩, ⟨3,2,170501772847016⟩, ⟨4,1,-7543463611008⟩], [⟨0,0,-3420554429033597⟩, ⟨0,1,5484753677760194⟩, ⟨0,2,-11757361661185399⟩, ⟨0,3,2137030613700328⟩, ⟨1,0,-2394556728611128⟩, ⟨1,1,3590729129875813⟩, ⟨1,2,5237488392642687⟩, ⟨1,3,-938046584143868⟩, ⟨2,0,244582300926144⟩, ⟨2,1,-1458799523702520⟩, ⟨2,2,-561584685425468⟩, ⟨2,3,81479154618004⟩, ⟨3,1,33945586249536⟩, ⟨3,2,-3771731805504⟩]⟩,
  LabelExclusion.constant ⟨522, [Guard.circle 3], [⟨0,0,-261⟩, ⟨0,1,344⟩, ⟨0,2,61⟩, ⟨1,0,-748⟩, ⟨1,1,10⟩, ⟨1,2,20⟩, ⟨2,0,-20⟩], [⟨0,0,-748⟩, ⟨0,1,1148⟩, ⟨0,2,-400⟩, ⟨1,0,1210⟩, ⟨1,1,-20⟩, ⟨1,2,40⟩, ⟨2,0,-120⟩], [⟨0,0,1752⟩, ⟨0,1,-2096⟩, ⟨0,2,200⟩, ⟨1,0,-120⟩, ⟨1,1,510⟩, ⟨1,2,-20⟩, ⟨2,0,-261⟩, ⟨2,1,-40⟩]⟩,
  LabelExclusion.constant ⟨101180683071756642996, [], [⟨0,0,-50590341535878321498⟩, ⟨0,1,-807869196909978651288⟩, ⟨0,2,261493933826947869096⟩, ⟨0,3,-96129728011335611714⟩, ⟨0,4,-11317657200253379563⟩, ⟨1,0,180239475066790695080⟩, ⟨1,1,592541799857034145508⟩, ⟨1,2,-85309395951251580172⟩, ⟨1,3,59785402143366595075⟩, ⟨1,4,7176966746280462291⟩, ⟨2,0,-124291185726299264944⟩, ⟨2,1,-116905764890335048652⟩, ⟨2,2,-25634572777579553139⟩, ⟨2,3,-2911350734438552279⟩, ⟨2,4,-305998739469880718⟩, ⟨3,0,15472362257055635882⟩, ⟨3,1,702769532363008098⟩, ⟨3,2,2485838389701584626⟩, ⟨3,3,-1887714858219658236⟩, ⟨3,4,-234477944098476960⟩, ⟨4,0,4238158123978487700⟩, ⟨4,1,4599212942491414608⟩, ⟨4,2,526020163367858772⟩, ⟨4,3,17226950994990144⟩, ⟨5,0,-183036354321770280⟩, ⟨5,1,-34453901989980288⟩], [⟨0,0,180239475066790695080⟩, ⟨0,1,-456784943004736816714⟩, ⟨0,2,541335214433024003610⟩, ⟨0,3,-208427537737318908518⟩, ⟨0,4,-22635314400506759126⟩, ⟨1,0,312038115511736700728⟩, ⟨1,1,1050719256662871595720⟩, ⟨1,2,-218243982891572328014⟩, ⟨1,3,118736929319946866504⟩, ⟨1,4,14353933492560924582⟩, ⟨2,0,-344694674765847444910⟩, ⟨2,1,-466672745850693173010⟩, ⟨2,2,-47107407395192884402⟩, ⟨2,3,-2396968660755619602⟩, ⟨2,4,-611997478939761436⟩, ⟨3,0,55141788944903140974⟩, ⟨3,1,6642920473349225862⟩, ⟨3,2,9621336451039319352⟩, ⟨3,3,-3306473828242362552⟩, ⟨3,4,-468955888196953920⟩, ⟨4,0,12531438017613692820⟩, ⟨4,1,13763184925484263536⟩, ⟨4,2,1486542312942691176⟩, ⟨4,3,34453901989980288⟩, ⟨5,0,-549109062965310840⟩, ⟨5,1,-103361705969940864⟩], [⟨0,0,436329301238035965672⟩, ⟨0,1,362032193605917739021⟩, ⟨0,2,-786147981150500697890⟩, ⟨0,3,58943140067645936007⟩, ⟨0,4,11317657200253379563⟩, ⟨1,0,-360167037022903080792⟩, ⟨1,1,-86851681153586373811⟩, ⟨1,2,575714358642710165157⟩, ⟨1,3,-19342940474598204525⟩, ⟨1,4,-7176966746280462291⟩, ⟨2,0,50903630820924653274⟩, ⟨2,1,-81507243844097884249⟩, ⟨2,2,-84405622273269307267⟩, ⟨2,3,-7202477373782175362⟩, ⟨2,4,305998739469880718⟩, ⟨3,0,12714474371935463100⟩, ⟨3,1,12358033076486749069⟩, ⟨3,2,-10030484723496629391⟩, ⟨3,3,1021323877197154154⟩, ⟨3,4,234477944098476960⟩, ⟨4,0,-549109062965310840⟩, ⟨4,1,2473308241823728686⟩, ⟨4,2,2385741226220658024⟩, ⟨4,3,217250993103486816⟩, ⟨5,1,-91518177160885140⟩, ⟨5,2,-17226950994990144⟩]⟩,
  LabelExclusion.constant ⟨2794986, [Guard.triangle 1], [⟨0,1,1986075⟩, ⟨0,2,2203632⟩, ⟨0,3,-2199942⟩, ⟨1,0,-11224692⟩, ⟨1,1,-32191527⟩, ⟨1,2,-11168334⟩, ⟨1,3,10628292⟩, ⟨2,0,10700364⟩, ⟨2,1,-5516676⟩, ⟨2,2,-1324672⟩, ⟨2,3,-889856⟩, ⟨3,0,1769600⟩, ⟨3,1,889856⟩], [⟨0,0,-5634720⟩, ⟨0,1,5627340⟩, ⟨0,2,4407264⟩, ⟨0,3,-4399884⟩, ⟨1,0,15768876⟩, ⟨1,1,3982194⟩, ⟨1,2,-22336668⟩, ⟨1,3,21256584⟩, ⟨2,0,12883784⟩, ⟨2,1,-62445080⟩, ⟨2,2,-2649344⟩, ⟨2,3,-1779712⟩, ⟨3,0,10617600⟩, ⟨3,1,5339136⟩], [⟨0,0,6466005⟩, ⟨0,1,-2192562⟩, ⟨0,2,-4399884⟩, ⟨1,0,11114184⟩, ⟨1,1,7340886⟩, ⟨1,2,25656468⟩, ⟨2,0,10617600⟩, ⟨2,1,6389464⟩, ⟨2,2,-23036296⟩, ⟨3,1,3539200⟩, ⟨3,2,1779712⟩]⟩,
  LabelExclusion.constant ⟨24, [], [⟨0,0,-12⟩, ⟨0,1,-64⟩, ⟨0,2,20⟩], [⟨0,0,-42⟩, ⟨0,1,-194⟩, ⟨0,2,224⟩, ⟨0,3,-82⟩, ⟨0,4,10⟩, ⟨1,0,12⟩, ⟨1,1,64⟩, ⟨1,2,-20⟩], [⟨0,0,61⟩, ⟨0,1,100⟩, ⟨0,2,-133⟩, ⟨0,3,46⟩, ⟨0,4,-5⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.circle 1], [], [⟨0,0,-2⟩, ⟨0,1,-1⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 0], [⟨0,0,-12⟩, ⟨0,1,7⟩], [⟨0,0,24⟩, ⟨0,1,-14⟩], [⟨0,0,7⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,4⟩, ⟨0,1,11⟩, ⟨0,2,-11⟩, ⟨0,3,2⟩, ⟨1,0,8⟩, ⟨1,1,-2⟩], [⟨0,1,-24⟩, ⟨0,2,22⟩, ⟨0,3,-4⟩, ⟨1,0,-16⟩, ⟨1,1,4⟩], [⟨0,1,-8⟩, ⟨0,2,2⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.circle 1], [], [⟨0,1,-2⟩], [⟨0,0,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,6⟩, ⟨0,1,3⟩, ⟨0,2,-2⟩], [⟨0,0,-12⟩, ⟨0,1,-6⟩, ⟨0,2,4⟩], [⟨0,0,-1⟩, ⟨0,1,-2⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.circle 1], [], [], [⟨0,0,-2⟩, ⟨0,1,-1⟩]⟩,
  LabelExclusion.constant ⟨294, [Guard.circle 1], [⟨0,0,36⟩, ⟨0,1,-72⟩, ⟨0,2,36⟩, ⟨1,0,-36⟩], [⟨0,0,-22⟩, ⟨0,1,106⟩, ⟨1,0,82⟩, ⟨1,1,168⟩, ⟨2,0,-96⟩], [⟨0,0,-147⟩, ⟨0,1,-47⟩, ⟨1,0,22⟩, ⟨1,1,24⟩, ⟨2,0,-96⟩]⟩]

private def exclusionRow23 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨30, [Guard.circle 1], [⟨0,0,4⟩, ⟨0,1,-12⟩, ⟨0,2,4⟩], [⟨0,1,18⟩, ⟨0,2,-4⟩, ⟨1,0,-4⟩], [⟨0,0,-15⟩, ⟨0,1,-4⟩, ⟨0,2,-2⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 0], [⟨0,0,12⟩, ⟨0,1,37⟩, ⟨0,2,-15⟩, ⟨1,1,-12⟩, ⟨1,2,4⟩], [⟨0,0,-34⟩, ⟨0,1,-120⟩, ⟨1,0,-22⟩, ⟨1,1,62⟩, ⟨2,0,8⟩, ⟨2,1,-8⟩], [⟨0,0,-14⟩, ⟨0,1,30⟩, ⟨1,0,8⟩, ⟨1,1,-8⟩]⟩,
  LabelExclusion.constant ⟨14, [Guard.triangle 0], [⟨0,0,-40⟩, ⟨0,1,10⟩, ⟨1,0,72⟩, ⟨1,1,-3⟩, ⟨2,0,-28⟩, ⟨3,0,3⟩], [⟨0,0,4⟩, ⟨0,1,2⟩, ⟨1,0,-74⟩, ⟨1,1,-26⟩, ⟨2,0,44⟩, ⟨2,1,6⟩, ⟨3,0,-6⟩], [⟨0,1,-1⟩, ⟨1,1,13⟩, ⟨2,1,-3⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨0,0,16⟩, ⟨0,1,-20⟩, ⟨0,2,8⟩, ⟨0,3,-1⟩, ⟨1,0,-4⟩, ⟨1,1,1⟩], [⟨0,0,-24⟩, ⟨0,1,30⟩, ⟨0,2,-14⟩, ⟨0,3,2⟩, ⟨1,0,8⟩, ⟨1,1,-2⟩], [⟨0,1,4⟩, ⟨0,2,-1⟩]⟩,
  LabelExclusion.constant ⟨98, [Guard.circle 2], [⟨0,0,-183⟩, ⟨0,1,82⟩, ⟨0,2,-456⟩, ⟨0,3,49⟩, ⟨1,0,232⟩, ⟨1,1,114⟩, ⟨2,0,-49⟩], [⟨0,0,-134⟩, ⟨0,1,-114⟩, ⟨0,2,652⟩, ⟨0,3,-98⟩], [⟨0,0,-49⟩, ⟨0,1,652⟩, ⟨0,2,-98⟩, ⟨1,0,-232⟩, ⟨1,1,-261⟩, ⟨1,2,49⟩]⟩,
  LabelExclusion.constant ⟨89681303418, [], [⟨0,0,292997053554⟩, ⟨0,1,-163270748268⟩, ⟨0,2,56190925593⟩, ⟨0,3,-230757882588⟩, ⟨1,0,90310978974⟩, ⟨1,1,683073302711⟩, ⟨1,2,447165186098⟩, ⟨1,3,-1293073374924⟩, ⟨2,0,-502177043895⟩, ⟨2,1,79875997531⟩, ⟨2,2,1684633399962⟩, ⟨2,3,146523682184⟩, ⟨3,0,-65446945882⟩, ⟨3,1,-797998967330⟩, ⟨3,2,-111177458132⟩, ⟨4,0,139475305540⟩, ⟨4,1,18957808520⟩], [⟨0,0,-122130519458⟩, ⟨0,1,-346542422318⟩, ⟨0,2,-543818052502⟩, ⟨0,3,487155529908⟩, ⟨1,0,929514094046⟩, ⟨1,1,-2024819825158⟩, ⟨1,2,-3040056203228⟩, ⟨1,3,2732670432032⟩, ⟨2,0,671632286372⟩, ⟨2,1,2611467359932⟩, ⟨2,2,-1674537995488⟩, ⟨2,3,-293047364368⟩, ⟨3,0,-836851833240⟩, ⟨3,1,444154371040⟩, ⟨3,2,75831234080⟩], [⟨0,0,-44840651709⟩, ⟨0,1,-109801274367⟩, ⟨0,2,365366647431⟩, ⟨1,0,-211811822876⟩, ⟨1,1,-707872342783⟩, ⟨1,2,1921304000364⟩, ⟨2,0,379864565907⟩, ⟨2,1,-2006217722247⟩, ⟨2,2,-939584051830⟩, ⟨3,0,623348168042⟩, ⟨3,1,594879590330⟩, ⟨3,2,73261841092⟩, ⟨4,0,-139475305540⟩, ⟨4,1,-18957808520⟩]⟩,
  LabelExclusion.constant ⟨263533452672, [], [⟨0,0,-1926431141956⟩, ⟨0,1,603252198519⟩, ⟨0,2,2975830605516⟩, ⟨0,3,-2208502764880⟩, ⟨0,4,269913755720⟩, ⟨1,0,17038315308100⟩, ⟨1,1,-20996711580338⟩, ⟨1,2,-21754403048182⟩, ⟨1,3,25326624745036⟩, ⟨1,4,-3422483801776⟩, ⟨2,0,-21531390125285⟩, ⟨2,1,77750583215081⟩, ⟨2,2,-23267010971522⟩, ⟨2,3,-22458957651500⟩, ⟨2,4,3695454204536⟩, ⟨3,0,-8885506274441⟩, ⟨3,1,-48994456699050⟩, ⟨3,2,62199304398392⟩, ⟨3,3,-11254204106764⟩, ⟨3,4,878149503024⟩, ⟨4,0,12519669452989⟩, ⟨4,1,-28420780047530⟩, ⟨4,2,9135243746140⟩, ⟨4,3,-1756299006048⟩, ⟨5,0,2653576054257⟩, ⟨5,1,-1273035721578⟩, ⟨5,2,439074751512⟩], [⟨0,0,815330803622⟩, ⟨0,1,-874498643224⟩, ⟨0,2,161948253432⟩, ⟨1,0,-7954598015392⟩, ⟨1,1,17305804199404⟩, ⟨1,2,-6988730221808⟩, ⟨1,3,539827511440⟩, ⟨2,0,21098030815118⟩, ⟨2,1,-108910776555140⟩, ⟨2,2,60517027314992⟩, ⟨2,3,-6844967603552⟩, ⟨3,0,2174956074446⟩, ⟨3,1,113966200396092⟩, ⟨3,2,-65120609416152⟩, ⟨3,3,7390908409072⟩, ⟨4,0,-26535760542570⟩, ⟨4,1,23344661432808⟩, ⟨4,2,-9482890401432⟩, ⟨4,3,1756299006048⟩], [⟨0,0,-131766726336⟩, ⟨0,1,703434936523⟩, ⟨0,2,-94469814502⟩, ⟨1,0,551797350950⟩, ⟨1,1,-11760210354104⟩, ⟨1,2,1608138239316⟩, ⟨2,0,-5608136248822⟩, ⟨2,1,44972986798121⟩, ⟨2,2,-6631620883170⟩, ⟨3,0,246243673816⟩, ⟨3,1,-46230770249855⟩, ⟨3,2,7034885831936⟩, ⟨4,0,8708938981067⟩, ⟨4,1,7622190057878⟩, ⟨4,2,-530502847732⟩, ⟨5,0,-2653576054257⟩, ⟨5,1,1273035721578⟩, ⟨5,2,-439074751512⟩]⟩,
  LabelExclusion.constant ⟨1890, [Guard.triangle 0], [⟨0,1,-4165⟩, ⟨0,2,9080⟩, ⟨0,3,-2080⟩, ⟨1,1,385⟩, ⟨1,2,-1640⟩, ⟨1,3,400⟩], [⟨0,0,-3254⟩, ⟨0,1,6754⟩, ⟨0,2,-9680⟩, ⟨0,3,2112⟩, ⟨1,0,1358⟩, ⟨1,1,-2474⟩, ⟨1,2,1168⟩, ⟨1,3,-160⟩, ⟨2,0,-154⟩, ⟨2,1,656⟩, ⟨2,2,-160⟩], [⟨0,0,5982⟩, ⟨0,1,-9696⟩, ⟨0,2,2112⟩, ⟨1,0,-245⟩, ⟨1,1,2776⟩, ⟨1,2,-704⟩, ⟨2,0,-77⟩, ⟨2,1,328⟩, ⟨2,2,-80⟩]⟩,
  LabelExclusion.constant ⟨23682, [Guard.triangle 0], [⟨0,1,-844992⟩, ⟨0,2,1093689⟩, ⟨0,3,-226382⟩, ⟨0,4,5607⟩, ⟨1,1,-1073764⟩, ⟨1,2,344828⟩, ⟨1,3,-22428⟩], [⟨0,0,419356⟩, ⟨0,1,-317338⟩, ⟨0,2,218406⟩, ⟨1,0,-1891934⟩, ⟨1,1,487696⟩, ⟨1,2,-93916⟩, ⟨1,3,11214⟩, ⟨2,0,536882⟩, ⟨2,1,-172414⟩, ⟨2,2,11214⟩], [⟨0,0,-466720⟩, ⟨0,1,31053⟩, ⟨0,2,51798⟩, ⟨1,0,2006884⟩, ⟨1,1,-972870⟩, ⟨1,2,100926⟩, ⟨2,0,268441⟩, ⟨2,1,-86207⟩, ⟨2,2,5607⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨0,0,8⟩, ⟨0,2,-8⟩, ⟨1,1,6⟩, ⟨1,2,2⟩, ⟨2,0,-2⟩, ⟨2,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,-8⟩, ⟨0,2,8⟩, ⟨1,0,6⟩, ⟨1,2,-2⟩], [⟨0,0,-4⟩, ⟨0,1,12⟩, ⟨1,0,-6⟩, ⟨1,1,-7⟩, ⟨2,0,2⟩, ⟨2,1,1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 5], [⟨0,0,3⟩, ⟨0,1,1⟩, ⟨0,2,-3⟩, ⟨1,0,-6⟩, ⟨1,1,1⟩, ⟨1,2,2⟩, ⟨2,0,4⟩, ⟨2,1,-2⟩], [⟨0,0,2⟩, ⟨0,1,-14⟩, ⟨0,2,6⟩, ⟨1,0,-4⟩, ⟨1,1,12⟩, ⟨1,2,-4⟩], [⟨0,0,-5⟩, ⟨0,1,6⟩, ⟨1,0,10⟩, ⟨1,1,-7⟩, ⟨2,0,-4⟩, ⟨2,1,2⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 8], [⟨0,0,13⟩, ⟨0,1,-41⟩, ⟨0,2,16⟩, ⟨1,0,14⟩, ⟨1,1,-10⟩, ⟨2,0,1⟩], [⟨0,0,-14⟩, ⟨0,1,40⟩, ⟨0,2,-16⟩, ⟨1,0,-2⟩, ⟨1,1,2⟩], [⟨0,0,1⟩, ⟨0,1,20⟩, ⟨0,2,-8⟩, ⟨1,0,-12⟩, ⟨1,1,9⟩, ⟨2,0,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-2⟩], [⟨0,0,1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [], [⟨0,0,-8⟩, ⟨0,1,2⟩], [⟨0,0,4⟩, ⟨0,1,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,-8⟩, ⟨0,1,2⟩], []⟩,
  LabelExclusion.constant ⟨2516710993200, [], [⟨0,0,3953132595468⟩, ⟨0,1,-1283423464817⟩, ⟨0,2,-389734610321⟩, ⟨0,3,1252386309⟩, ⟨1,0,-198509744860⟩, ⟨1,1,225026106586⟩, ⟨1,2,-5925292567⟩, ⟨1,3,4994988012⟩, ⟨2,0,-44030403544⟩, ⟨2,1,38039576848⟩, ⟨2,2,-17193955759⟩, ⟨2,3,-354583521⟩, ⟨3,0,-13187913684⟩, ⟨3,1,-6593956842⟩, ⟨3,2,6593956842⟩], [⟨0,0,-2603641675356⟩, ⟨0,1,-1330848676732⟩, ⟨0,2,791993083732⟩, ⟨0,3,-2504772618⟩, ⟨1,0,3349888303106⟩, ⟨1,1,-512703990810⟩, ⟨1,2,61800465254⟩, ⟨1,3,-9989976024⟩, ⟨2,0,25684787768⟩, ⟨2,1,-255881186184⟩, ⟨2,2,30842076308⟩, ⟨2,3,709167042⟩, ⟨3,0,-44030403544⟩, ⟨3,1,79836649146⟩, ⟨3,2,-13187913684⟩, ⟨4,0,-13187913684⟩], [⟨0,0,-1258355496600⟩, ⟨0,1,2642902275078⟩, ⟨0,2,-402258473411⟩, ⟨0,3,1252386309⟩, ⟨1,0,-2603641675356⟩, ⟨1,1,399610796207⟩, ⟨1,2,-55875172687⟩, ⟨1,3,4994988012⟩, ⟨2,0,-603244292362⟩, ⟨2,1,200759962892⟩, ⟨2,2,-13648120549⟩, ⟨2,3,-354583521⟩, ⟨3,0,224194532628⟩, ⟨3,1,-72533525262⟩, ⟨3,2,6593956842⟩]⟩]

private def exclusionRow24 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨542419200, [], [⟨0,0,3199373796⟩, ⟨0,1,-3516091635⟩, ⟨0,2,-207303021⟩, ⟨1,0,475464828⟩, ⟨1,1,-1128408018⟩, ⟨1,2,530786619⟩, ⟨2,0,-220870908⟩, ⟨2,1,331306362⟩], [⟨0,0,-5070586432⟩, ⟨0,1,-2736517636⟩, ⟨0,2,1178812910⟩, ⟨0,3,92134676⟩, ⟨1,0,4422344194⟩, ⟨1,1,-1863856064⟩, ⟨1,2,1484452858⟩, ⟨1,3,-235905164⟩, ⟨2,0,475464828⟩, ⟨2,1,357837402⟩, ⟨2,2,-147247272⟩, ⟨3,0,-220870908⟩], [⟨0,0,-271209600⟩, ⟨0,1,3864086652⟩, ⟨0,2,-405137103⟩, ⟨0,3,-46067338⟩, ⟨1,0,-5070586432⟩, ⟨1,1,3616077009⟩, ⟨1,2,-1214036757⟩, ⟨1,3,117952582⟩, ⟨2,0,1222970398⟩, ⟨2,1,-650342118⟩, ⟨2,2,73623636⟩]⟩,
  LabelExclusion.constant ⟨993000, [], [⟨0,0,3431416⟩, ⟨0,1,-860235⟩, ⟨0,2,-330997⟩, ⟨0,3,115494⟩, ⟨1,0,797874⟩, ⟨1,1,469717⟩, ⟨1,2,-458188⟩, ⟨1,3,43679⟩, ⟨2,0,-48508⟩, ⟨2,1,61858⟩, ⟨2,2,-8682⟩, ⟨2,3,-10488⟩, ⟨3,0,-43424⟩, ⟨3,1,-21712⟩, ⟨3,2,21712⟩], [⟨0,0,-3852916⟩, ⟨0,1,-696518⟩, ⟨0,2,1585946⟩, ⟨0,3,-230988⟩, ⟨1,0,3234632⟩, ⟨1,1,-4710070⟩, ⟨1,2,1265808⟩, ⟨1,3,-87358⟩, ⟨2,0,971570⟩, ⟨2,1,-280530⟩, ⟨2,2,-66540⟩, ⟨2,3,20976⟩, ⟨3,0,-48508⟩, ⟨3,1,238096⟩, ⟨3,2,-43424⟩, ⟨4,0,-43424⟩], [⟨0,0,-496500⟩, ⟨0,1,1354958⟩, ⟨0,2,-230988⟩, ⟨1,0,-3852916⟩, ⟨1,1,1178450⟩, ⟨1,2,-87358⟩, ⟨2,0,-196784⟩, ⟨2,1,-45564⟩, ⟨2,2,20976⟩, ⟨3,0,173696⟩, ⟨3,1,-43424⟩]⟩,
  LabelExclusion.constant ⟨6216, [Guard.triangle 0], [⟨0,0,-33226⟩, ⟨0,1,43566⟩, ⟨0,2,-19664⟩, ⟨1,0,59501⟩, ⟨1,1,-17913⟩, ⟨1,2,5904⟩, ⟨2,0,-14801⟩, ⟨2,1,1476⟩], [⟨0,0,-3108⟩, ⟨0,1,3560⟩, ⟨1,0,-18944⟩, ⟨1,1,8930⟩, ⟨2,0,5986⟩, ⟨2,1,-2952⟩], [⟨0,0,30118⟩, ⟨0,1,-1780⟩, ⟨1,0,-78445⟩, ⟨1,1,15199⟩, ⟨2,0,20787⟩, ⟨2,1,-4428⟩]⟩,
  LabelExclusion.constant ⟨468, [Guard.triangle 0], [⟨0,0,-6136⟩, ⟨0,1,10031⟩, ⟨0,2,-4894⟩, ⟨1,0,9834⟩, ⟨1,1,-2754⟩, ⟨1,2,1428⟩, ⟨2,0,-2380⟩], [⟨0,0,-468⟩, ⟨0,1,270⟩, ⟨1,0,-6370⟩, ⟨1,1,3376⟩, ⟨2,0,1836⟩, ⟨2,1,-952⟩], [⟨0,0,5668⟩, ⟨0,1,-135⟩, ⟨1,0,-16204⟩, ⟨1,1,3206⟩, ⟨2,0,4216⟩, ⟨2,1,-952⟩]⟩,
  LabelExclusion.constant ⟨72, [Guard.triangle 0], [⟨0,0,958⟩, ⟨0,1,-1200⟩, ⟨0,2,134⟩, ⟨1,0,-825⟩, ⟨1,1,649⟩, ⟨1,2,-48⟩, ⟨2,0,168⟩, ⟨2,1,-72⟩], [⟨0,0,-72⟩, ⟨0,1,-1834⟩, ⟨0,2,938⟩, ⟨1,0,850⟩, ⟨1,1,382⟩, ⟨1,2,-336⟩, ⟨2,0,-336⟩, ⟨2,1,144⟩], [⟨0,0,-1030⟩, ⟨0,1,938⟩, ⟨1,0,1675⟩, ⟨1,1,-939⟩, ⟨2,0,-504⟩, ⟨2,1,216⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 0], [⟨0,1,390⟩, ⟨0,2,-313⟩, ⟨0,3,56⟩, ⟨1,1,-234⟩, ⟨1,2,141⟩, ⟨1,3,-21⟩], [⟨0,0,468⟩, ⟨0,1,-2154⟩, ⟨0,2,962⟩, ⟨0,3,-112⟩, ⟨1,0,-52⟩, ⟨1,1,950⟩, ⟨1,2,-408⟩, ⟨1,3,42⟩, ⟨2,0,-156⟩, ⟨2,1,42⟩], [⟨0,0,-1416⟩, ⟨0,1,1815⟩, ⟨0,2,-593⟩, ⟨0,3,56⟩, ⟨1,0,858⟩, ⟨1,1,-855⟩, ⟨1,2,246⟩, ⟨1,3,-21⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 0], [⟨0,1,-7⟩, ⟨0,2,2⟩], [⟨0,0,-28⟩, ⟨0,1,8⟩, ⟨1,0,14⟩, ⟨1,1,-4⟩], [⟨0,0,16⟩, ⟨0,1,-4⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨0,1,88⟩, ⟨0,2,-57⟩, ⟨0,3,9⟩, ⟨1,1,-33⟩, ⟨1,2,20⟩, ⟨1,3,-3⟩], [⟨0,0,44⟩, ⟨0,1,-320⟩, ⟨0,2,150⟩, ⟨0,3,-18⟩, ⟨1,0,44⟩, ⟨1,1,98⟩, ⟨1,2,-52⟩, ⟨1,3,6⟩, ⟨2,0,-22⟩, ⟨2,1,6⟩], [⟨0,0,-52⟩, ⟨0,1,48⟩, ⟨0,2,-9⟩, ⟨1,0,22⟩, ⟨1,1,-17⟩, ⟨1,2,3⟩]⟩,
  LabelExclusion.constant ⟨16, [Guard.triangle 6], [⟨0,1,8⟩], [⟨0,0,8⟩, ⟨0,1,4⟩, ⟨1,0,-8⟩], [⟨0,0,6⟩, ⟨0,1,-3⟩]⟩,
  LabelExclusion.constant ⟨36, [Guard.circle 0], [⟨0,0,-20⟩, ⟨0,1,-21⟩, ⟨0,2,2⟩, ⟨1,0,2⟩, ⟨1,1,-1⟩], [⟨0,0,2⟩, ⟨0,1,-6⟩, ⟨0,2,4⟩, ⟨1,0,-2⟩, ⟨1,1,-2⟩], [⟨0,1,15⟩, ⟨1,1,-3⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 6], [⟨0,0,12⟩, ⟨0,1,62⟩, ⟨0,2,10⟩, ⟨1,0,-17⟩, ⟨1,1,-39⟩, ⟨2,0,14⟩], [⟨0,0,34⟩, ⟨0,1,-20⟩, ⟨0,2,4⟩, ⟨1,0,-62⟩, ⟨1,1,-22⟩, ⟨2,0,28⟩], [⟨0,1,-29⟩, ⟨0,2,-4⟩, ⟨1,1,14⟩]⟩,
  LabelExclusion.constant ⟨144, [Guard.triangle 1], [⟨0,0,193⟩, ⟨0,1,588⟩, ⟨0,2,-172⟩, ⟨1,0,-358⟩, ⟨1,1,-43⟩, ⟨1,2,34⟩, ⟨2,0,69⟩, ⟨2,1,-17⟩], [⟨0,0,324⟩, ⟨0,1,20⟩, ⟨0,2,-344⟩, ⟨1,0,-216⟩, ⟨1,1,158⟩, ⟨1,2,68⟩, ⟨2,0,36⟩, ⟨2,1,-34⟩], [⟨0,0,72⟩, ⟨0,1,-499⟩, ⟨0,2,-86⟩, ⟨1,1,358⟩, ⟨1,2,17⟩, ⟨2,1,-51⟩]⟩,
  LabelExclusion.constant ⟨1851600, [], [⟨0,0,11710840⟩, ⟨0,1,-15755028⟩, ⟨0,2,-8521828⟩, ⟨1,0,2616700⟩, ⟨1,1,4612547⟩, ⟨1,2,4778572⟩, ⟨2,1,-370320⟩, ⟨2,2,-1301445⟩, ⟨3,1,186225⟩, ⟨3,2,186225⟩], [⟨0,0,9539688⟩, ⟨0,1,22436176⟩, ⟨0,2,-17043656⟩, ⟨1,0,3066790⟩, ⟨1,1,9498678⟩, ⟨1,2,9557144⟩, ⟨2,0,-6350750⟩, ⟨2,1,-3978914⟩, ⟨2,2,-2602890⟩, ⟨3,1,1857990⟩, ⟨3,2,372450⟩, ⟨4,1,-372450⟩], [⟨0,0,-925800⟩, ⟨0,1,-18332284⟩, ⟨0,2,8521828⟩, ⟨1,1,14501741⟩, ⟨1,2,-4778572⟩, ⟨2,1,-4835460⟩, ⟨2,2,1301445⟩, ⟨3,1,558675⟩, ⟨3,2,-186225⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,-54⟩, ⟨0,1,69⟩, ⟨1,0,-45⟩], [⟨0,0,6⟩, ⟨0,1,-18⟩, ⟨1,0,-6⟩], [⟨0,0,36⟩, ⟨0,1,-39⟩, ⟨1,0,39⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,6⟩, ⟨0,1,9⟩, ⟨1,0,-9⟩], [⟨0,1,-6⟩], [⟨0,0,-6⟩, ⟨0,1,-6⟩, ⟨1,0,9⟩]⟩,
  LabelExclusion.constant ⟨16, [Guard.triangle 0], [⟨0,0,-1028⟩, ⟨0,1,1220⟩, ⟨0,2,-162⟩, ⟨1,0,212⟩, ⟨1,1,-389⟩, ⟨1,2,42⟩, ⟨2,1,21⟩], [⟨0,0,48⟩, ⟨0,1,-400⟩, ⟨0,2,-162⟩, ⟨1,0,-32⟩, ⟨1,1,274⟩, ⟨1,2,42⟩, ⟨2,1,-42⟩], [⟨0,0,948⟩, ⟨0,1,-972⟩, ⟨1,0,-244⟩, ⟨1,1,495⟩, ⟨2,1,-63⟩]⟩]

private def exclusionRow25 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨324, [Guard.triangle 7], [⟨0,0,-4914⟩, ⟨0,1,-4140⟩, ⟨0,2,828⟩, ⟨1,0,5676⟩, ⟨1,1,3016⟩, ⟨1,2,-667⟩, ⟨2,0,-957⟩], [⟨0,0,1584⟩, ⟨0,1,-3240⟩, ⟨0,2,1656⟩, ⟨1,0,-4430⟩, ⟨1,1,3538⟩, ⟨1,2,-1334⟩, ⟨2,0,754⟩], [⟨0,0,162⟩, ⟨0,1,9108⟩, ⟨0,2,-828⟩, ⟨1,1,-8674⟩, ⟨1,2,667⟩, ⟨2,1,1334⟩]⟩,
  LabelExclusion.constant ⟨306, [Guard.triangle 0], [⟨0,0,6522⟩, ⟨0,1,-43755⟩, ⟨0,2,-6039⟩, ⟨1,0,9487⟩, ⟨1,1,28181⟩, ⟨1,2,1824⟩, ⟨2,0,-7798⟩, ⟨2,1,-4427⟩, ⟨3,0,1273⟩], [⟨0,0,-7134⟩, ⟨0,1,15492⟩, ⟨0,2,-8052⟩, ⟨1,0,7124⟩, ⟨1,1,17966⟩, ⟨1,2,2432⟩, ⟨2,0,-10504⟩, ⟨2,1,-6308⟩, ⟨3,0,2546⟩], [⟨0,1,23625⟩, ⟨0,2,6039⟩, ⟨1,1,-20088⟩, ⟨1,2,-1824⟩, ⟨2,1,3819⟩]⟩,
  LabelExclusion.constant ⟨378, [Guard.triangle 5], [⟨0,0,93⟩, ⟨0,1,942⟩, ⟨0,2,129⟩, ⟨0,3,-93⟩, ⟨1,0,16⟩, ⟨1,1,352⟩, ⟨1,2,52⟩, ⟨1,3,-36⟩], [⟨0,0,-282⟩, ⟨0,1,210⟩, ⟨0,2,258⟩, ⟨0,3,-186⟩, ⟨1,0,-442⟩, ⟨1,1,428⟩, ⟨1,2,104⟩, ⟨1,3,-72⟩, ⟨2,0,-136⟩, ⟨2,1,144⟩], [⟨0,0,189⟩, ⟨0,1,-729⟩, ⟨0,2,-279⟩, ⟨1,1,-441⟩, ⟨1,2,78⟩, ⟨2,1,-68⟩, ⟨2,2,72⟩]⟩,
  LabelExclusion.constant ⟨22, [Guard.triangle 0], [⟨0,0,-40⟩, ⟨0,1,12⟩], [⟨0,0,-120⟩, ⟨0,1,116⟩, ⟨0,2,-44⟩, ⟨0,3,6⟩, ⟨1,0,40⟩, ⟨1,1,-12⟩], [⟨0,0,116⟩, ⟨0,1,-93⟩, ⟨0,2,28⟩, ⟨0,3,-3⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 0], [⟨0,0,4⟩, ⟨1,0,-1⟩], [⟨0,0,-4⟩, ⟨1,0,1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,8⟩, ⟨0,2,-1⟩, ⟨1,0,-9⟩, ⟨1,2,1⟩, ⟨2,0,3⟩, ⟨2,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,2⟩, ⟨1,0,6⟩, ⟨1,1,4⟩, ⟨1,2,-2⟩, ⟨2,0,-6⟩, ⟨2,1,2⟩], [⟨1,1,-3⟩, ⟨1,2,1⟩, ⟨2,0,3⟩, ⟨2,1,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,2⟩, ⟨0,1,-3⟩, ⟨1,0,9⟩, ⟨1,1,2⟩, ⟨1,2,-1⟩, ⟨2,0,-4⟩, ⟨2,1,1⟩], [⟨0,0,-6⟩, ⟨0,1,4⟩, ⟨1,0,-10⟩, ⟨1,1,-6⟩, ⟨1,2,2⟩, ⟨2,0,8⟩, ⟨2,1,-2⟩], [⟨1,0,-3⟩, ⟨1,1,1⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 0], [⟨0,0,4⟩, ⟨1,0,-1⟩], [⟨0,0,-4⟩, ⟨1,0,1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder, Guard.triangle 0], [⟨0,0,2⟩, ⟨0,1,2⟩, ⟨1,0,-6⟩, ⟨2,0,1⟩], [⟨0,0,-2⟩, ⟨0,1,-2⟩, ⟨1,0,10⟩, ⟨2,0,-2⟩], []⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 0], [⟨0,0,32⟩, ⟨1,0,-6⟩], [⟨0,0,-16⟩, ⟨0,1,-32⟩, ⟨1,0,24⟩, ⟨1,1,6⟩, ⟨2,0,-4⟩], [⟨0,0,-20⟩, ⟨0,1,32⟩, ⟨1,0,-17⟩, ⟨1,1,-6⟩, ⟨2,0,4⟩]⟩,
  LabelExclusion.constant ⟨102, [Guard.triangle 0], [⟨0,0,-128⟩, ⟨1,0,317⟩, ⟨1,1,-78⟩, ⟨2,0,-50⟩, ⟨2,1,13⟩], [⟨0,0,-556⟩, ⟨0,1,112⟩, ⟨1,0,634⟩, ⟨1,1,-256⟩, ⟨1,2,26⟩, ⟨2,0,-100⟩, ⟨2,1,26⟩], [⟨0,0,480⟩, ⟨0,1,-116⟩, ⟨1,0,-600⟩, ⟨1,1,306⟩, ⟨1,2,-39⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 0], [⟨0,0,14⟩, ⟨0,1,-4⟩], [⟨0,0,-24⟩, ⟨0,1,-8⟩, ⟨0,2,4⟩, ⟨1,0,14⟩, ⟨1,1,-4⟩], [⟨0,0,-2⟩, ⟨0,1,8⟩, ⟨0,2,-2⟩, ⟨1,0,-7⟩, ⟨1,1,2⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 4], [⟨0,2,-2⟩, ⟨1,0,6⟩, ⟨1,1,-2⟩, ⟨2,0,-4⟩, ⟨2,1,-2⟩], [⟨0,2,-2⟩, ⟨1,0,-2⟩, ⟨1,1,10⟩, ⟨1,2,1⟩, ⟨2,0,-1⟩, ⟨3,0,1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 4], [⟨0,2,-2⟩, ⟨1,0,2⟩, ⟨1,1,-2⟩, ⟨2,1,-2⟩], [⟨0,2,-2⟩, ⟨1,0,-2⟩, ⟨1,1,10⟩, ⟨1,2,1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.circle 4], [⟨0,2,-2⟩, ⟨1,0,2⟩, ⟨1,1,2⟩, ⟨1,2,-1⟩, ⟨2,0,-4⟩, ⟨2,1,-3⟩, ⟨3,0,-1⟩], [⟨0,2,-2⟩, ⟨1,0,-2⟩, ⟨1,1,10⟩, ⟨1,2,2⟩, ⟨3,0,2⟩], []⟩]

private def exclusionRow26 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨4, [Guard.triangle 0], [⟨1,0,4⟩, ⟨1,1,-1⟩], [⟨0,0,-4⟩, ⟨0,2,2⟩, ⟨1,1,-2⟩], [⟨0,0,4⟩, ⟨0,1,2⟩, ⟨0,2,-2⟩, ⟨1,0,-6⟩, ⟨1,1,3⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨1,0,-53⟩, ⟨1,1,16⟩, ⟨2,0,28⟩, ⟨2,1,-4⟩, ⟨3,0,-4⟩], [⟨0,0,-8⟩, ⟨0,1,2⟩], [⟨0,0,4⟩, ⟨0,1,-14⟩, ⟨0,2,4⟩, ⟨1,0,66⟩, ⟨1,1,-16⟩, ⟨2,0,-32⟩, ⟨2,1,4⟩, ⟨3,0,4⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨1,0,8⟩, ⟨1,1,-3⟩], [⟨0,0,-8⟩, ⟨0,1,2⟩, ⟨0,2,6⟩, ⟨1,1,-6⟩], [⟨0,0,4⟩, ⟨0,1,2⟩, ⟨0,2,-3⟩, ⟨1,0,-11⟩, ⟨1,1,6⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.circle 4], [⟨0,0,-4⟩, ⟨0,1,16⟩, ⟨0,3,-4⟩, ⟨1,0,-9⟩, ⟨1,2,2⟩], [⟨0,0,4⟩, ⟨0,1,-16⟩, ⟨0,3,4⟩, ⟨1,0,1⟩], []⟩,
  LabelExclusion.constant ⟨1242, [Guard.circle 0], [⟨0,0,-621⟩, ⟨0,1,-884⟩, ⟨0,2,-64⟩, ⟨0,3,-202⟩, ⟨0,4,-16⟩, ⟨0,5,8⟩, ⟨1,0,424⟩, ⟨1,1,362⟩, ⟨1,2,20⟩, ⟨1,3,56⟩, ⟨1,4,-16⟩], [⟨0,0,424⟩, ⟨0,1,1086⟩, ⟨0,2,148⟩, ⟨0,3,244⟩, ⟨0,4,16⟩, ⟨0,5,-16⟩, ⟨1,0,-176⟩, ⟨1,1,-284⟩, ⟨1,2,-4⟩, ⟨1,3,-48⟩, ⟨1,4,16⟩], [⟨0,0,248⟩, ⟨0,1,-418⟩, ⟨0,2,108⟩, ⟨0,3,54⟩, ⟨0,5,8⟩, ⟨1,0,-248⟩, ⟨1,1,-78⟩, ⟨1,2,-16⟩, ⟨1,3,-8⟩]⟩,
  LabelExclusion.constant ⟨54162, [], [⟨0,0,-27081⟩, ⟨0,1,-153244⟩, ⟨0,2,93994⟩, ⟨0,3,26523⟩, ⟨1,0,-343340⟩, ⟨1,1,321617⟩, ⟨1,2,-117980⟩, ⟨1,3,-21351⟩, ⟨2,0,729298⟩, ⟨2,1,-266228⟩, ⟨2,2,143206⟩, ⟨2,3,4170⟩, ⟨3,0,-358136⟩, ⟨3,1,28356⟩, ⟨3,2,-18348⟩, ⟨4,0,36696⟩], [⟨0,0,-289178⟩, ⟨0,1,459112⟩, ⟨0,2,-134942⟩, ⟨0,3,-53046⟩, ⟨1,0,1686730⟩, ⟨1,1,-915560⟩, ⟨1,2,193258⟩, ⟨1,3,42702⟩, ⟨2,0,-1845164⟩, ⟨2,1,861570⟩, ⟨2,2,-278072⟩, ⟨2,3,-8340⟩, ⟨3,0,486572⟩, ⟨3,1,-101748⟩, ⟨3,2,36696⟩, ⟨4,0,-36696⟩], [⟨0,0,587011⟩, ⟨0,1,20939⟩, ⟨0,2,-26523⟩, ⟨1,0,-1371822⟩, ⟨1,1,37247⟩, ⟨1,2,21351⟩, ⟨2,0,849470⟩, ⟨2,1,-130696⟩, ⟨2,2,-4170⟩, ⟨3,0,-91740⟩, ⟨3,1,18348⟩]⟩,
  LabelExclusion.constant ⟨50, [Guard.circle 0], [⟨0,0,-25⟩, ⟨0,1,-13⟩, ⟨0,2,-4⟩, ⟨1,0,6⟩], [⟨0,0,6⟩, ⟨1,0,4⟩], [⟨0,0,4⟩, ⟨0,1,-12⟩, ⟨0,2,4⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 0], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,1⟩], []⟩,
  LabelExclusion.constant ⟨42, [Guard.triangle 0], [⟨0,0,48⟩, ⟨0,1,-15⟩, ⟨0,2,15⟩, ⟨1,0,6⟩, ⟨1,1,-12⟩, ⟨1,2,-2⟩, ⟨2,0,-2⟩, ⟨2,1,2⟩], [⟨0,0,-44⟩, ⟨0,2,-30⟩, ⟨1,0,8⟩, ⟨1,1,28⟩, ⟨1,2,4⟩, ⟨2,1,-4⟩], [⟨0,2,15⟩, ⟨1,1,-14⟩, ⟨1,2,-2⟩, ⟨2,1,2⟩]⟩,
  LabelExclusion.constant ⟨174, [Guard.triangle 0], [⟨0,0,-2034⟩, ⟨0,1,2064⟩, ⟨0,2,-291⟩, ⟨1,0,49⟩, ⟨1,1,3190⟩, ⟨1,2,-350⟩, ⟨2,0,-1325⟩, ⟨2,1,-720⟩, ⟨2,2,80⟩, ⟨3,0,280⟩], [⟨0,0,1686⟩, ⟨0,1,-4014⟩, ⟨0,2,582⟩, ⟨1,0,-4960⟩, ⟨1,1,-2790⟩, ⟨1,2,700⟩, ⟨2,0,2910⟩, ⟨2,1,720⟩, ⟨2,2,-160⟩, ⟨3,0,-400⟩], [⟨0,1,2184⟩, ⟨0,2,-291⟩, ⟨1,1,-1554⟩, ⟨1,2,-350⟩, ⟨2,1,630⟩, ⟨2,2,80⟩, ⟨3,1,-80⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,4⟩, ⟨0,1,-1⟩, ⟨0,2,4⟩, ⟨0,3,-1⟩, ⟨1,0,4⟩, ⟨1,1,-5⟩, ⟨1,2,1⟩], [⟨0,0,-8⟩, ⟨0,1,10⟩, ⟨0,2,-10⟩, ⟨0,3,2⟩, ⟨1,0,-8⟩, ⟨1,1,10⟩, ⟨1,2,-2⟩], [⟨0,1,-4⟩, ⟨0,2,1⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 5], [⟨0,1,4⟩, ⟨1,0,-1⟩], [⟨0,1,-4⟩, ⟨1,0,1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 0], [⟨0,0,4⟩, ⟨0,1,-1⟩], [⟨0,0,-4⟩, ⟨0,1,1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0], [⟨0,0,16⟩, ⟨0,1,-4⟩], [⟨0,0,16⟩, ⟨0,1,-92⟩, ⟨0,2,38⟩, ⟨0,3,-4⟩, ⟨1,0,16⟩, ⟨1,1,-4⟩], [⟨0,0,-68⟩, ⟨0,1,97⟩, ⟨0,2,-36⟩, ⟨0,3,4⟩]⟩]

private def exclusionRow27 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨22, [Guard.triangle 0], [⟨0,0,-36⟩, ⟨0,1,39⟩, ⟨0,2,-10⟩, ⟨1,0,6⟩, ⟨1,1,-7⟩, ⟨1,2,2⟩], [⟨0,0,-114⟩, ⟨0,1,76⟩, ⟨1,0,54⟩, ⟨1,1,-36⟩, ⟨2,0,-6⟩, ⟨2,1,4⟩], [⟨0,0,106⟩, ⟨0,1,-94⟩, ⟨0,2,20⟩, ⟨1,0,-18⟩, ⟨1,1,18⟩, ⟨1,2,-4⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.triangle 0], [⟨0,0,16⟩, ⟨0,1,-4⟩], [⟨0,0,-16⟩, ⟨0,1,-44⟩, ⟨0,2,20⟩, ⟨0,3,-2⟩, ⟨1,0,16⟩, ⟨1,1,-4⟩], [⟨0,0,-12⟩, ⟨0,1,19⟩, ⟨0,2,-8⟩, ⟨0,3,1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.circle 4], [⟨0,2,8⟩, ⟨0,3,-11⟩, ⟨0,4,3⟩, ⟨1,2,-2⟩, ⟨1,3,-2⟩, ⟨2,1,-4⟩, ⟨2,2,1⟩], [⟨0,2,-4⟩, ⟨0,3,6⟩, ⟨0,4,-2⟩, ⟨1,2,10⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.circle 4], [⟨0,2,2⟩, ⟨0,3,-10⟩, ⟨0,4,3⟩, ⟨1,2,4⟩, ⟨1,3,-3⟩, ⟨2,1,-4⟩, ⟨2,2,1⟩], [⟨0,2,-2⟩, ⟨0,3,6⟩, ⟨0,4,-2⟩, ⟨1,2,8⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 0, Guard.circle 4], [⟨0,2,2⟩, ⟨0,3,-4⟩, ⟨0,4,2⟩, ⟨1,2,-2⟩, ⟨1,3,-2⟩, ⟨2,1,-4⟩, ⟨2,2,1⟩], [⟨0,2,-2⟩, ⟨0,3,4⟩, ⟨0,4,-2⟩, ⟨1,2,10⟩], []⟩,
  LabelExclusion.constant ⟨12, [Guard.triangle 0], [⟨0,1,-110⟩, ⟨0,2,57⟩, ⟨0,3,-7⟩, ⟨1,1,15⟩, ⟨1,2,-8⟩, ⟨1,3,1⟩], [⟨0,0,-50⟩, ⟨0,1,-60⟩, ⟨0,2,14⟩, ⟨1,0,80⟩, ⟨1,1,-6⟩, ⟨1,2,-2⟩, ⟨2,0,-10⟩, ⟨2,1,2⟩], [⟨0,0,26⟩, ⟨0,1,105⟩, ⟨0,2,-57⟩, ⟨0,3,7⟩, ⟨1,0,-5⟩, ⟨1,1,-14⟩, ⟨1,2,8⟩, ⟨1,3,-1⟩]⟩,
  LabelExclusion.constant ⟨4, [], [⟨0,0,-1⟩, ⟨1,0,-6⟩], [], [⟨0,0,8⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,-1⟩, ⟨0,1,-2⟩], [⟨0,0,2⟩, ⟨0,1,-4⟩], [⟨0,0,4⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 5], [⟨0,1,-7⟩, ⟨0,2,8⟩, ⟨1,0,12⟩, ⟨1,1,-12⟩], [⟨0,1,-1⟩, ⟨1,0,-12⟩, ⟨1,1,12⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,21⟩, ⟨0,1,24⟩, ⟨1,0,-96⟩], [⟨0,0,-42⟩, ⟨0,1,-36⟩, ⟨1,0,144⟩], [⟨1,0,36⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 9], [⟨0,0,3⟩], [⟨0,0,-6⟩], []⟩,
  LabelExclusion.constant ⟨4, [Guard.circle 0], [⟨0,0,-1⟩, ⟨1,0,-2⟩], [], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 8], [⟨0,1,5⟩, ⟨0,2,5⟩, ⟨0,3,1⟩, ⟨1,1,-3⟩, ⟨1,2,-1⟩], [⟨0,1,36⟩, ⟨0,2,-4⟩, ⟨0,3,-6⟩], [⟨0,1,-9⟩, ⟨0,2,-3⟩]⟩,
  LabelExclusion.constant ⟨78, [], [⟨0,0,934⟩, ⟨0,1,-1234⟩, ⟨0,2,180⟩, ⟨1,0,-1342⟩, ⟨1,1,2205⟩, ⟨1,2,-576⟩, ⟨2,0,-192⟩, ⟨2,1,81⟩, ⟨2,2,459⟩, ⟨3,0,189⟩, ⟨3,1,-459⟩], [⟨0,0,-1002⟩, ⟨0,1,540⟩, ⟨1,0,1576⟩, ⟨1,1,-636⟩, ⟨1,2,-540⟩, ⟨2,1,-378⟩, ⟨2,2,918⟩], [⟨0,0,231⟩, ⟨0,1,-270⟩, ⟨1,0,-765⟩, ⟨1,1,1269⟩, ⟨2,0,567⟩, ⟨2,1,-1377⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.triangle 3], [⟨0,1,-9⟩, ⟨1,0,3⟩], [⟨0,0,-18⟩, ⟨0,1,18⟩], [⟨0,0,9⟩]⟩,
  LabelExclusion.constant ⟨52, [Guard.bOrder], [⟨0,0,676⟩, ⟨0,1,-1569⟩, ⟨0,2,-1134⟩, ⟨1,0,-2609⟩, ⟨1,1,8271⟩, ⟨1,2,567⟩, ⟨2,0,513⟩, ⟨2,1,-1701⟩], [⟨0,0,52⟩, ⟨1,0,1824⟩, ⟨1,1,-7074⟩, ⟨1,2,3402⟩], [⟨0,0,-702⟩, ⟨0,1,1701⟩, ⟨1,0,1539⟩, ⟨1,1,-5103⟩]⟩]

private def exclusionRow28 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨6, [Guard.bOrder], [⟨0,0,104⟩, ⟨0,1,-1⟩, ⟨1,0,-321⟩, ⟨1,1,30⟩, ⟨2,0,30⟩], [⟨0,0,-202⟩, ⟨0,1,6⟩, ⟨1,0,660⟩, ⟨1,1,-180⟩], [⟨0,0,-3⟩, ⟨1,0,90⟩]⟩,
  LabelExclusion.constant ⟨11664, [Guard.aOrder], [⟨0,0,-18465⟩, ⟨0,1,12122⟩, ⟨0,2,-680⟩, ⟨0,3,-325⟩, ⟨1,0,477⟩, ⟨1,1,13326⟩, ⟨1,2,-3955⟩, ⟨1,3,-1300⟩, ⟨2,0,-10380⟩, ⟨2,1,3760⟩, ⟨2,2,1300⟩], [⟨0,0,31056⟩, ⟨0,1,178⟩, ⟨0,2,-6040⟩, ⟨0,3,-650⟩, ⟨1,0,-18336⟩, ⟨1,1,15784⟩, ⟨1,2,576⟩, ⟨1,3,-520⟩, ⟨2,0,-16608⟩, ⟨2,1,6016⟩, ⟨2,2,2080⟩], [⟨0,0,-4848⟩, ⟨0,1,-16528⟩, ⟨0,2,4048⟩, ⟨0,3,1040⟩, ⟨1,0,33216⟩, ⟨1,1,-12032⟩, ⟨1,2,-4160⟩]⟩,
  LabelExclusion.constant ⟨576, [Guard.triangle 3], [⟨0,0,759⟩, ⟨0,1,-840⟩, ⟨0,2,225⟩, ⟨1,0,-875⟩, ⟨1,1,-875⟩, ⟨2,0,500⟩], [⟨0,0,-1518⟩, ⟨0,1,-780⟩, ⟨0,2,450⟩], [⟨0,1,2000⟩]⟩,
  LabelExclusion.constant ⟨1296, [Guard.bOrder], [⟨0,0,-648⟩, ⟨0,1,672⟩, ⟨0,2,133⟩, ⟨0,3,-49⟩, ⟨1,0,-1581⟩, ⟨1,1,-550⟩, ⟨1,2,595⟩, ⟨1,3,-84⟩, ⟨2,0,-660⟩, ⟨2,1,-560⟩, ⟨2,2,140⟩], [⟨0,0,48⟩, ⟨0,1,1610⟩, ⟨0,2,168⟩, ⟨0,3,-98⟩, ⟨1,0,-1536⟩, ⟨1,1,-2200⟩, ⟨1,2,224⟩, ⟨1,3,56⟩, ⟨2,0,1056⟩, ⟨2,1,896⟩, ⟨2,2,-224⟩], [⟨0,0,624⟩, ⟨0,1,-1264⟩, ⟨0,2,-336⟩, ⟨0,3,112⟩, ⟨1,0,2112⟩, ⟨1,1,1792⟩, ⟨1,2,-448⟩]⟩,
  LabelExclusion.constant ⟨9000, [], [⟨0,0,7445⟩, ⟨0,1,13208⟩, ⟨0,2,2238⟩, ⟨0,3,107⟩, ⟨1,0,-25671⟩, ⟨1,1,-33208⟩, ⟨1,2,-3701⟩, ⟨1,3,852⟩, ⟨2,0,-44988⟩, ⟨2,1,41532⟩, ⟨2,2,-5112⟩, ⟨3,0,44772⟩, ⟨3,1,-5964⟩], [⟨0,0,-38780⟩, ⟨0,1,-8096⟩, ⟨0,2,-428⟩, ⟨1,0,31014⟩, ⟨1,1,28200⟩, ⟨1,2,-2766⟩, ⟨2,0,118968⟩, ⟨2,1,-51792⟩, ⟨2,2,5112⟩, ⟨3,0,-38376⟩, ⟨3,1,5112⟩], [⟨0,0,4467⟩, ⟨0,1,-6396⟩, ⟨0,2,-1810⟩, ⟨0,3,-107⟩, ⟨1,0,71409⟩, ⟨1,1,-5216⟩, ⟨1,2,6467⟩, ⟨1,3,-852⟩, ⟨2,0,-73980⟩, ⟨2,1,10260⟩, ⟨3,0,-6396⟩, ⟨3,1,852⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 3], [⟨1,0,3⟩], [⟨1,0,-3⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.circle 2], [⟨0,1,-1⟩], [⟨0,1,1⟩], []⟩,
  LabelExclusion.constant ⟨14, [Guard.bOrder], [⟨0,0,7⟩, ⟨0,1,28⟩, ⟨0,2,-4⟩, ⟨0,3,-12⟩, ⟨1,0,28⟩, ⟨1,1,-72⟩, ⟨1,2,60⟩, ⟨2,0,20⟩, ⟨2,1,-24⟩], [⟨0,0,-28⟩, ⟨0,1,8⟩, ⟨0,2,24⟩, ⟨1,0,100⟩, ⟨1,1,-76⟩, ⟨1,2,-24⟩, ⟨2,0,-20⟩, ⟨2,1,24⟩], [⟨0,0,7⟩, ⟨0,1,-18⟩, ⟨0,2,-8⟩, ⟨0,3,12⟩, ⟨1,0,-78⟩, ⟨1,1,88⟩, ⟨1,2,-36⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.circle 2], [⟨0,1,-1⟩], [⟨0,1,1⟩], []⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,1,-2⟩, ⟨0,2,1⟩, ⟨1,1,-4⟩, ⟨2,0,3⟩], [⟨0,0,-2⟩, ⟨0,1,2⟩, ⟨1,0,-6⟩], [⟨0,0,4⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,-1⟩, ⟨0,1,-2⟩], [⟨0,0,2⟩, ⟨0,1,-4⟩], [⟨0,0,4⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,3⟩], [⟨0,0,-6⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,9⟩, ⟨0,1,-12⟩, ⟨0,2,12⟩, ⟨1,0,-24⟩, ⟨1,1,-18⟩, ⟨2,0,12⟩], [⟨0,0,-18⟩, ⟨0,1,12⟩, ⟨0,2,-12⟩, ⟨1,0,24⟩, ⟨1,1,36⟩, ⟨2,0,-24⟩], [⟨1,0,24⟩, ⟨1,1,-6⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 6], [⟨0,0,3⟩], [⟨0,0,-6⟩], []⟩]

private def exclusionRow29 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨4, [Guard.triangle 2], [⟨0,0,1⟩, ⟨0,1,-8⟩, ⟨1,0,2⟩], [], [⟨0,0,8⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,-3⟩], [⟨0,0,6⟩, ⟨0,1,12⟩, ⟨1,0,-48⟩], [⟨1,0,12⟩]⟩,
  LabelExclusion.constant ⟨14, [Guard.bOrder], [⟨0,0,-70⟩, ⟨0,1,28⟩, ⟨0,2,96⟩, ⟨1,0,208⟩, ⟨1,1,-384⟩], [⟨0,0,14⟩, ⟨0,1,126⟩, ⟨0,2,-144⟩, ⟨1,0,-312⟩, ⟨1,1,576⟩], [⟨0,0,63⟩, ⟨0,1,-72⟩, ⟨1,0,-78⟩, ⟨1,1,144⟩]⟩,
  LabelExclusion.constant ⟨5625, [], [⟨0,0,76249⟩, ⟨0,1,-58232⟩, ⟨1,0,-64632⟩, ⟨1,1,50730⟩, ⟨2,0,-64998⟩, ⟨2,1,-14268⟩, ⟨3,0,14268⟩], [⟨0,0,-33297⟩, ⟨0,1,-58232⟩, ⟨1,0,148116⟩, ⟨1,1,50730⟩, ⟨2,0,-131580⟩, ⟨2,1,-14268⟩, ⟨3,0,57072⟩], [⟨0,0,6918⟩, ⟨1,0,-63408⟩, ⟨2,0,114144⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder], [⟨0,0,-1⟩], [], [⟨0,0,1⟩]⟩,
  LabelExclusion.constant ⟨12, [Guard.triangle 3], [⟨0,0,13⟩, ⟨1,0,2⟩], [⟨0,0,-26⟩, ⟨0,1,-30⟩], [⟨0,1,8⟩]⟩,
  LabelExclusion.constant ⟨1484250, [], [⟨0,0,-1322269⟩, ⟨0,1,-1538508⟩, ⟨0,2,3882897⟩, ⟨1,0,905261⟩, ⟨1,1,-269341⟩, ⟨1,2,-1223220⟩, ⟨2,0,241240⟩, ⟨2,1,1223220⟩], [⟨0,0,3804826⟩, ⟨0,1,-12860862⟩, ⟨0,2,5177196⟩, ⟨1,0,-140180⟩, ⟨1,1,-952030⟩, ⟨1,2,-1223220⟩, ⟨2,0,241240⟩, ⟨2,1,1223220⟩], [⟨0,0,6282765⟩, ⟨0,1,-5462469⟩, ⟨0,2,1294299⟩, ⟨1,0,-1166061⟩, ⟨1,1,-1294299⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 2], [⟨0,0,1⟩, ⟨0,2,-1⟩, ⟨1,1,-2⟩, ⟨2,0,-1⟩], [⟨0,0,-1⟩, ⟨0,2,1⟩, ⟨1,1,2⟩, ⟨2,0,1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 2], [⟨0,2,-1⟩, ⟨1,0,1⟩, ⟨1,1,-2⟩, ⟨2,0,-1⟩], [⟨0,2,1⟩, ⟨1,0,-1⟩, ⟨1,1,2⟩, ⟨2,0,1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 2], [⟨0,1,1⟩, ⟨0,2,-1⟩, ⟨1,1,-2⟩, ⟨2,0,-1⟩], [⟨0,1,-1⟩, ⟨0,2,1⟩, ⟨1,1,2⟩, ⟨2,0,1⟩], []⟩,
  LabelExclusion.constant ⟨6, [Guard.bOrder], [⟨0,0,3⟩, ⟨0,1,-54⟩, ⟨1,0,22⟩, ⟨1,1,192⟩, ⟨2,0,-64⟩], [⟨0,0,-16⟩, ⟨0,1,-36⟩, ⟨1,0,84⟩, ⟨1,1,64⟩, ⟨2,0,-64⟩], [⟨0,0,5⟩, ⟨0,1,18⟩, ⟨1,0,-2⟩, ⟨1,1,-128⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 2], [⟨0,0,1⟩, ⟨0,2,-1⟩, ⟨1,1,-2⟩, ⟨2,0,-1⟩], [⟨0,0,-1⟩, ⟨0,2,1⟩, ⟨1,1,2⟩, ⟨2,0,1⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.circle 2], [⟨0,1,1⟩, ⟨0,2,-1⟩, ⟨1,1,-2⟩, ⟨2,0,-1⟩], [⟨0,1,-1⟩, ⟨0,2,1⟩, ⟨1,1,2⟩, ⟨2,0,1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.circle 0], [⟨1,0,-1⟩], [⟨0,0,-2⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,1,24⟩, ⟨1,0,-96⟩], [⟨0,0,48⟩, ⟨0,1,42⟩, ⟨0,2,-12⟩, ⟨1,0,-240⟩, ⟨1,1,24⟩, ⟨2,0,96⟩], [⟨0,0,-24⟩, ⟨0,1,-21⟩, ⟨0,2,6⟩, ⟨1,0,165⟩, ⟨1,1,-42⟩]⟩,
  LabelExclusion.constant ⟨62, [], [⟨0,0,322⟩, ⟨0,1,1960⟩, ⟨1,0,-153⟩, ⟨1,1,-1008⟩], [⟨0,0,62⟩, ⟨0,1,-3358⟩, ⟨0,2,1904⟩, ⟨1,0,954⟩, ⟨1,1,2038⟩, ⟨1,2,6048⟩, ⟨2,0,-306⟩, ⟨2,1,-2016⟩], [⟨0,0,-1710⟩, ⟨0,1,2631⟩, ⟨0,2,-952⟩, ⟨1,0,614⟩, ⟨1,1,1012⟩, ⟨1,2,-4032⟩]⟩]

private def exclusionRow30 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨2, [Guard.bOrder], [⟨0,0,35⟩, ⟨1,0,-50⟩], [⟨0,0,-68⟩, ⟨0,1,-10⟩, ⟨1,0,174⟩, ⟨1,1,220⟩, ⟨2,0,-100⟩], [⟨0,0,-1⟩, ⟨1,0,2⟩, ⟨1,1,-40⟩]⟩,
  LabelExclusion.constant ⟨810, [], [⟨0,0,15570⟩, ⟨0,1,-11640⟩, ⟨0,2,1860⟩, ⟨1,0,-16260⟩, ⟨1,1,-1860⟩], [⟨0,0,-4022⟩, ⟨0,1,-2660⟩, ⟨0,2,1916⟩, ⟨0,3,744⟩, ⟨1,0,292⟩, ⟨1,1,-10776⟩, ⟨1,2,-1488⟩, ⟨2,0,6504⟩, ⟨2,1,744⟩], [⟨0,0,803⟩, ⟨0,1,-4306⟩, ⟨0,2,958⟩, ⟨0,3,372⟩, ⟨1,0,-3292⟩, ⟨1,1,20556⟩, ⟨1,2,-372⟩]⟩,
  LabelExclusion.constant ⟨6642, [], [⟨0,0,24732⟩, ⟨0,1,-10072⟩, ⟨0,2,-11872⟩, ⟨1,0,-12824⟩, ⟨1,1,11872⟩], [⟨0,0,37694⟩, ⟨0,1,-134282⟩, ⟨0,2,88188⟩, ⟨0,3,-23744⟩, ⟨1,0,-13786⟩, ⟨1,1,-30732⟩, ⟨1,2,47488⟩, ⟨2,0,25648⟩, ⟨2,1,-23744⟩], [⟨0,0,-11084⟩, ⟨0,1,697⟩, ⟨0,2,32222⟩, ⟨0,3,-11872⟩, ⟨1,0,20633⟩, ⟨1,1,-35826⟩, ⟨1,2,11872⟩]⟩,
  LabelExclusion.constant ⟨4783212, [], [⟨0,0,-30221970⟩, ⟨0,1,82925880⟩, ⟨0,2,11694840⟩, ⟨1,0,48378786⟩, ⟨1,1,-358869180⟩, ⟨1,2,-42792192⟩, ⟨2,0,-17315472⟩, ⟨2,1,171168768⟩], [⟨0,0,4783212⟩, ⟨0,1,-55660728⟩, ⟨0,2,23071790⟩, ⟨0,3,-40931940⟩, ⟨1,0,-58419970⟩, ⟨1,1,113306128⟩, ⟨1,2,121306314⟩, ⟨1,3,149772672⟩, ⟨2,0,5090106⟩, ⟨2,1,129656892⟩, ⟨2,2,-641882880⟩, ⟨3,0,-17315472⟩, ⟨3,1,171168768⟩], [⟨0,0,-41168015⟩, ⟨0,1,-71527069⟩, ⟨0,2,32001865⟩, ⟨0,3,-20465970⟩, ⟨1,0,153378190⟩, ⟨1,1,351248040⟩, ⟨1,2,-169189809⟩, ⟨1,3,74886336⟩, ⟨2,0,-49581001⟩, ⟨2,1,-345397551⟩, ⟨2,2,246055104⟩]⟩,
  LabelExclusion.constant ⟨21708, [Guard.bOrder], [⟨0,0,-10854⟩, ⟨0,1,-12194⟩, ⟨0,2,-18476⟩, ⟨1,0,-27856⟩, ⟨1,1,73904⟩], [⟨0,0,-1340⟩, ⟨0,1,23584⟩, ⟨0,2,-13794⟩, ⟨0,3,27714⟩, ⟨1,0,-24782⟩, ⟨1,1,66542⟩, ⟨1,2,-129332⟩, ⟨2,0,-27856⟩, ⟨2,1,73904⟩], [⟨0,0,11524⟩, ⟨0,1,30268⟩, ⟨0,2,-6897⟩, ⟨0,3,13857⟩, ⟨1,0,11051⟩, ⟨1,1,-58368⟩, ⟨1,2,-4619⟩]⟩,
  LabelExclusion.constant ⟨320, [], [⟨0,0,337⟩, ⟨0,1,2223⟩, ⟨1,0,-68⟩, ⟨1,1,-429⟩], [⟨0,0,320⟩, ⟨0,1,-3990⟩, ⟨0,2,-2730⟩, ⟨1,0,1280⟩, ⟨1,1,920⟩, ⟨1,2,-6006⟩, ⟨2,0,136⟩, ⟨2,1,858⟩], [⟨0,0,-2652⟩, ⟨0,1,402⟩, ⟨0,2,2730⟩, ⟨1,0,-1249⟩, ⟨1,1,-4059⟩, ⟨1,2,5148⟩]⟩,
  LabelExclusion.constant ⟨60, [Guard.bOrder], [⟨0,0,-95⟩, ⟨1,0,-65⟩], [⟨0,0,-60⟩, ⟨0,1,226⟩, ⟨1,0,-50⟩, ⟨1,1,-14⟩, ⟨2,0,26⟩], [⟨0,0,125⟩, ⟨0,1,-226⟩, ⟨1,0,233⟩, ⟨1,1,-4⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [], [⟨0,0,-8⟩, ⟨0,1,8⟩, ⟨1,0,-2⟩], [⟨0,0,4⟩, ⟨0,1,-3⟩, ⟨1,0,1⟩]⟩,
  LabelExclusion.constant ⟨2, [], [⟨0,0,1⟩, ⟨0,1,-2⟩, ⟨1,0,-4⟩], [⟨0,0,-6⟩, ⟨0,1,4⟩, ⟨1,0,8⟩], [⟨0,0,4⟩]⟩,
  LabelExclusion.constant ⟨24, [Guard.circle 0], [⟨0,0,-4⟩, ⟨0,1,-8⟩, ⟨1,0,-8⟩], [⟨1,0,-4⟩], [⟨1,0,3⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,3⟩, ⟨0,2,-48⟩, ⟨0,3,144⟩, ⟨1,0,42⟩, ⟨1,1,-156⟩, ⟨1,2,-288⟩, ⟨2,0,-48⟩, ⟨2,1,144⟩], [⟨0,0,-6⟩, ⟨0,2,-48⟩, ⟨0,3,288⟩, ⟨1,0,48⟩, ⟨1,2,-576⟩, ⟨2,0,-96⟩, ⟨2,1,288⟩], [⟨1,0,-66⟩, ⟨1,1,300⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,5⟩, ⟨0,1,-12⟩, ⟨0,2,8⟩, ⟨1,0,-17⟩, ⟨1,1,-16⟩, ⟨2,0,8⟩], [⟨0,0,-10⟩, ⟨0,1,-6⟩, ⟨0,2,16⟩, ⟨1,0,18⟩, ⟨1,1,-32⟩, ⟨2,0,16⟩], [⟨1,0,25⟩]⟩,
  LabelExclusion.constant ⟨24, [Guard.circle 0], [⟨0,0,-4⟩, ⟨0,1,-8⟩, ⟨1,0,-8⟩], [⟨0,1,-4⟩], [⟨0,1,3⟩]⟩,
  LabelExclusion.constant ⟨104, [Guard.triangle 0], [⟨0,0,460⟩, ⟨0,1,-624⟩, ⟨0,2,-52⟩, ⟨0,3,216⟩, ⟨1,0,120⟩, ⟨1,1,104⟩, ⟨1,2,-432⟩, ⟨2,0,-52⟩, ⟨2,1,216⟩], [⟨0,0,156⟩, ⟨0,1,-900⟩, ⟨0,2,488⟩, ⟨0,3,216⟩, ⟨1,1,-4⟩, ⟨1,2,-432⟩, ⟨2,0,-52⟩, ⟨2,1,216⟩], [⟨0,0,-13⟩, ⟨0,1,-70⟩, ⟨0,2,324⟩, ⟨1,0,13⟩, ⟨1,1,-54⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.triangle 3], [⟨0,1,82⟩, ⟨1,0,-497⟩, ⟨1,1,78⟩, ⟨2,0,1209⟩], [⟨0,0,-146⟩, ⟨0,1,502⟩, ⟨1,0,346⟩, ⟨1,1,-1534⟩, ⟨2,0,-182⟩], [⟨0,0,73⟩, ⟨0,1,210⟩, ⟨1,0,-173⟩, ⟨1,1,-806⟩, ⟨2,0,91⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,-4⟩, ⟨0,1,-240⟩, ⟨0,2,395⟩, ⟨0,3,-150⟩, ⟨1,0,-2⟩, ⟨1,1,-298⟩, ⟨1,2,300⟩, ⟨2,0,143⟩, ⟨2,1,-150⟩], [⟨0,0,8⟩, ⟨0,1,-98⟩, ⟨0,2,490⟩, ⟨0,3,-300⟩, ⟨1,0,-4⟩, ⟨1,1,-596⟩, ⟨1,2,600⟩, ⟨2,0,286⟩, ⟨2,1,-300⟩], [⟨0,1,286⟩, ⟨0,2,-300⟩]⟩]

private def exclusionRow31 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨2, [], [⟨0,0,-1⟩, ⟨0,1,-16⟩, ⟨0,2,16⟩], [⟨0,0,2⟩, ⟨0,1,38⟩, ⟨0,2,-8⟩, ⟨1,0,-2⟩, ⟨1,1,-8⟩], [⟨0,0,12⟩, ⟨0,1,-16⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.circle 1], [], [⟨0,0,-2⟩], [⟨0,0,-1⟩, ⟨0,1,-3⟩]⟩,
  LabelExclusion.half ⟨2, [Guard.bOrder], [⟨0,0,3⟩, ⟨0,2,1⟩, ⟨1,0,-3⟩, ⟨1,1,-2⟩, ⟨2,0,1⟩], [⟨0,0,-2⟩, ⟨0,2,-2⟩, ⟨1,0,6⟩, ⟨1,1,4⟩, ⟨2,0,-2⟩], [⟨0,0,-2⟩, ⟨0,1,2⟩, ⟨0,2,-1⟩, ⟨1,0,-1⟩, ⟨1,1,2⟩, ⟨2,0,-1⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.circle 0], [⟨0,0,-1⟩], [⟨0,0,2⟩, ⟨0,1,-2⟩, ⟨1,0,-2⟩], []⟩,
  LabelExclusion.constant ⟨18, [], [⟨0,0,20624⟩, ⟨0,1,-39004⟩, ⟨0,2,10521⟩, ⟨0,3,10990⟩, ⟨0,4,-3140⟩, ⟨1,0,-16193⟩, ⟨1,1,23886⟩, ⟨1,2,-31673⟩, ⟨1,3,1794⟩, ⟨1,4,3076⟩, ⟨2,0,-7588⟩, ⟨2,1,15473⟩, ⟨2,2,8064⟩, ⟨2,3,-9700⟩, ⟨2,4,-744⟩, ⟨3,0,9144⟩, ⟨3,1,-7741⟩, ⟨3,2,10172⟩, ⟨3,3,2976⟩, ⟨4,0,-1953⟩, ⟨4,1,-3548⟩, ⟨4,2,-3720⟩, ⟨5,1,1488⟩], [⟨0,0,-1570⟩, ⟨0,1,3190⟩, ⟨1,0,1538⟩, ⟨1,1,-6594⟩, ⟨2,0,-372⟩, ⟨2,1,3516⟩, ⟨3,1,-558⟩], [⟨0,0,388⟩, ⟨0,1,-10135⟩, ⟨0,2,13029⟩, ⟨0,3,-14130⟩, ⟨0,4,3140⟩, ⟨1,0,-1368⟩, ⟨1,1,24865⟩, ⟨1,2,8603⟩, ⟨1,3,1282⟩, ⟨1,4,-3076⟩, ⟨2,0,1740⟩, ⟨2,1,-14817⟩, ⟨2,2,-2484⟩, ⟨2,3,8956⟩, ⟨2,4,744⟩, ⟨3,0,-955⟩, ⟨3,1,-4563⟩, ⟨3,2,-10172⟩, ⟨3,3,-2976⟩, ⟨4,0,186⟩, ⟨4,1,6524⟩, ⟨4,2,3720⟩, ⟨5,1,-1488⟩]⟩,
  LabelExclusion.constant ⟨14, [], [⟨0,0,391⟩, ⟨0,1,-195⟩, ⟨0,2,-179⟩, ⟨0,3,-24⟩, ⟨1,0,-999⟩, ⟨1,1,953⟩, ⟨1,2,6⟩, ⟨1,3,-54⟩, ⟨2,0,324⟩, ⟨2,1,-306⟩, ⟨2,2,54⟩], [⟨0,0,130⟩, ⟨0,1,-578⟩, ⟨0,2,-26⟩, ⟨0,3,48⟩, ⟨1,0,-72⟩, ⟨1,1,1760⟩, ⟨1,2,-732⟩, ⟨1,3,108⟩, ⟨2,1,-576⟩, ⟨2,2,216⟩], [⟨0,0,-36⟩, ⟨0,1,-105⟩, ⟨0,2,142⟩, ⟨0,3,48⟩, ⟨1,0,65⟩, ⟨1,1,239⟩, ⟨1,2,-426⟩, ⟨1,3,108⟩, ⟨2,0,-36⟩, ⟨2,1,-90⟩, ⟨2,2,54⟩]⟩,
  LabelExclusion.constant ⟨18, [Guard.bOrder], [⟨0,0,-8⟩, ⟨0,1,-17⟩, ⟨1,0,-2⟩, ⟨1,1,4⟩], [⟨0,0,-2⟩, ⟨0,1,12⟩, ⟨1,0,-6⟩, ⟨1,1,-4⟩, ⟨2,0,4⟩], [⟨0,0,9⟩, ⟨0,1,17⟩, ⟨1,1,-4⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder], [⟨0,0,-1⟩, ⟨0,1,-3⟩, ⟨0,2,-4⟩, ⟨0,3,3⟩, ⟨1,0,7⟩, ⟨1,1,3⟩, ⟨1,2,3⟩, ⟨1,3,-6⟩, ⟨2,0,-17⟩, ⟨2,1,7⟩, ⟨2,2,12⟩, ⟨3,0,5⟩, ⟨3,1,-6⟩], [⟨0,0,-4⟩, ⟨0,1,6⟩, ⟨1,0,10⟩, ⟨1,1,-12⟩], [⟨0,0,3⟩, ⟨0,1,-1⟩, ⟨0,2,7⟩, ⟨0,3,-3⟩, ⟨1,0,-9⟩, ⟨1,1,3⟩, ⟨1,2,-9⟩, ⟨1,3,6⟩, ⟨2,0,12⟩, ⟨2,1,-1⟩, ⟨2,2,-12⟩, ⟨3,0,-5⟩, ⟨3,1,6⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,7⟩, ⟨0,1,-6⟩], [⟨0,0,-6⟩, ⟨0,1,-6⟩, ⟨1,0,6⟩], [⟨0,0,-4⟩, ⟨0,1,6⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0], [⟨0,0,1⟩], [⟨0,0,-1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder, Guard.triangle 0], [⟨0,0,1⟩, ⟨0,1,2⟩, ⟨1,0,-4⟩], [⟨0,0,-2⟩, ⟨0,1,-2⟩, ⟨1,0,8⟩], []⟩,
  LabelExclusion.constant ⟨4, [], [⟨0,0,297⟩, ⟨1,0,-3222⟩, ⟨2,0,9084⟩, ⟨3,0,-2664⟩], [⟨0,0,4⟩, ⟨0,1,-594⟩, ⟨1,0,614⟩, ⟨1,1,2880⟩, ⟨2,0,-3972⟩, ⟨2,1,-888⟩, ⟨3,0,3552⟩], [⟨0,0,-299⟩, ⟨1,0,2622⟩, ⟨2,0,-6216⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder], [⟨0,0,1⟩, ⟨1,0,10⟩], [⟨0,0,-6⟩, ⟨0,1,14⟩, ⟨1,0,4⟩], [⟨0,0,2⟩, ⟨0,1,-8⟩, ⟨1,0,-8⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder], [⟨1,0,20⟩, ⟨2,0,-12⟩], [⟨0,0,2⟩, ⟨0,1,20⟩, ⟨1,0,-38⟩, ⟨1,1,-12⟩, ⟨2,0,48⟩], [⟨0,0,-1⟩, ⟨1,0,-12⟩]⟩,
  LabelExclusion.constant ⟨1, [], [⟨0,0,-9⟩, ⟨0,1,16⟩, ⟨1,0,-4⟩], [⟨0,0,1⟩, ⟨0,1,-16⟩, ⟨1,0,4⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder], [⟨0,0,1⟩, ⟨0,1,-48⟩, ⟨0,2,128⟩, ⟨1,0,30⟩, ⟨1,1,-96⟩], [⟨0,0,-2⟩, ⟨0,1,48⟩, ⟨0,2,-128⟩, ⟨1,0,-10⟩, ⟨1,1,32⟩], []⟩]

private def exclusionRow32 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨2, [Guard.triangle 3], [⟨0,0,-1⟩, ⟨0,1,16⟩, ⟨1,0,-8⟩], [⟨0,0,2⟩, ⟨0,1,-32⟩, ⟨1,0,8⟩], []⟩,
  LabelExclusion.constant ⟨4, [Guard.circle 0], [⟨0,0,-1⟩, ⟨0,1,-1⟩, ⟨1,0,-1⟩], [], []⟩,
  LabelExclusion.constant ⟨3719565926948, [Guard.bOrder], [⟨0,0,-4415635034693084⟩, ⟨0,1,-148179863273592⟩, ⟨0,2,-121758352973118⟩, ⟨0,3,-140719235218560⟩, ⟨1,0,34106167970535792⟩, ⟨1,1,5751512863130986⟩, ⟨1,2,460746996997464⟩, ⟨1,3,562990712468480⟩, ⟨2,0,-43433992751356540⟩, ⟨2,1,7114174969467728⟩, ⟨2,2,105560758587840⟩, ⟨3,0,-469228251481960⟩, ⟨3,1,562990712468480⟩, ⟨4,0,175934597646400⟩], [⟨0,0,3719565926948⟩, ⟨0,1,8834989635313116⟩, ⟨0,2,303798858401080⟩, ⟨0,3,224814498765534⟩, ⟨1,0,-26512512415339206⟩, ⟨1,1,-42799460668107114⟩, ⟨1,2,-1538517621226496⟩, ⟨1,3,-908234709933432⟩, ⟨2,0,106641798860417292⟩, ⟨2,1,13130278141975502⟩, ⟨2,2,2930652547202504⟩, ⟨2,3,35186919529280⟩, ⟨3,0,-43639111133094220⟩, ⟨3,1,-6057115285534952⟩, ⟨3,2,105560758587840⟩, ⟨4,0,-821097446774760⟩, ⟨4,1,-316682275763520⟩, ⟨5,0,175934597646400⟩], [⟨0,0,4413775251729610⟩, ⟨0,1,-8699880441556823⟩, ⟨0,2,-313408637056171⟩, ⟨0,3,56623971671586⟩, ⟨1,0,-16421206058655806⟩, ⟨1,1,31970107942657127⟩, ⟨1,2,1774850929885324⟩, ⟨1,3,-217746715003528⟩, ⟨2,0,-17092347548635290⟩, ⟨2,1,-28234688498264102⟩, ⟨2,2,-3722358236611304⟩, ⟨2,3,-35186919529280⟩, ⟨3,0,29775984771744600⟩, ⟨3,1,4649638504363752⟩, ⟨3,2,-105560758587840⟩, ⟨4,0,-498412035573240⟩, ⟨4,1,316682275763520⟩, ⟨5,0,-175934597646400⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.circle 0], [⟨0,1,-1⟩, ⟨1,0,-1⟩], [⟨0,1,2⟩], []⟩,
  LabelExclusion.constant ⟨10, [Guard.circle 1], [], [⟨0,0,2⟩], [⟨0,0,-3⟩, ⟨0,1,-5⟩]⟩,
  LabelExclusion.constant ⟨606532470, [Guard.triangle 0], [⟨0,0,2137026556⟩, ⟨0,1,-1047046285⟩, ⟨0,2,-42374579⟩, ⟨0,3,31668470⟩, ⟨1,0,-831977121⟩, ⟨1,1,249799798⟩, ⟨1,2,1207785⟩, ⟨1,3,-1669808⟩, ⟨2,0,-145224871⟩, ⟨2,1,-101804226⟩, ⟨2,2,417452⟩, ⟨3,0,68927971⟩, ⟨3,1,4174520⟩, ⟨4,0,-2922164⟩], [⟨0,0,-2552804782⟩, ⟨0,1,1514425710⟩, ⟨0,2,-166631228⟩, ⟨0,3,-121038278⟩, ⟨1,0,3285403986⟩, ⟨1,1,-1075329574⟩, ⟨1,2,-7335852⟩, ⟨1,3,6679232⟩, ⟨2,0,208241954⟩, ⟨2,1,412852506⟩, ⟨2,2,-1669808⟩, ⟨3,0,-258178900⟩, ⟨3,1,-16698080⟩, ⟨4,0,11688656⟩], [⟨0,0,789834313⟩, ⟨0,1,-565634471⟩, ⟨0,2,90785330⟩, ⟨0,3,89369808⟩, ⟨1,0,-2006102466⟩, ⟨1,1,1037802617⟩, ⟨1,2,9989498⟩, ⟨1,3,-5009424⟩, ⟨2,0,531334276⟩, ⟨2,1,-314805348⟩, ⟨2,2,1252356⟩, ⟨3,0,162220912⟩, ⟨3,1,12523560⟩, ⟨4,0,-8766492⟩]⟩,
  LabelExclusion.constant ⟨2844100, [Guard.circle 0], [⟨0,0,62409⟩, ⟨0,1,-1463285⟩, ⟨0,2,-97328⟩, ⟨1,0,217263⟩, ⟨1,1,194656⟩, ⟨1,2,-455700⟩, ⟨2,0,1009372⟩, ⟨2,1,911400⟩, ⟨3,0,-455700⟩], [⟨0,0,-124818⟩, ⟨0,1,-167166⟩, ⟨0,2,-389312⟩, ⟨1,0,1302520⟩, ⟨1,1,-132776⟩, ⟨1,2,-1822800⟩, ⟨2,0,6771688⟩, ⟨2,1,3645600⟩, ⟨3,0,-1822800⟩], [⟨0,1,-681296⟩, ⟨0,2,681296⟩, ⟨1,1,-4552492⟩, ⟨1,2,3189900⟩, ⟨2,0,681296⟩, ⟨2,1,-6379800⟩, ⟨3,0,3189900⟩]⟩,
  LabelExclusion.constant ⟨26886861494824050, [Guard.bOrder], [⟨0,0,-13443430747412025⟩, ⟨0,1,-32718729377876892296⟩, ⟨0,2,-220153830286556693⟩, ⟨0,3,957914569040233728⟩, ⟨1,0,80671558349419103237⟩, ⟨1,1,77433834757402303392⟩, ⟨1,2,489176320764502000⟩, ⟨1,3,-1346963002222903296⟩, ⟨2,0,-177492172984133189635⟩, ⟨2,1,6263971685662613888⟩, ⟨2,2,-252555562916794368⟩, ⟨3,0,34027436486607152400⟩, ⟨3,1,-1346963002222903296⟩, ⟨4,0,-1767888940417560576⟩], [⟨0,0,-32691842516382068246⟩, ⟨0,1,48871383667276193776⟩, ⟨0,2,10559484177343889282⟩, ⟨0,3,882818317314203500⟩, ⟨1,0,40775985436381192722⟩, ⟨1,1,-149068180769659305164⟩, ⟨1,2,-33725658990240242172⟩, ⟨1,3,-522931152852336704⟩, ⟨2,0,212355012069896198154⟩, ⟨2,1,145158932519710882356⟩, ⟨2,2,24808246127188469568⟩, ⟨2,3,-1010222251667177472⟩, ⟨3,0,-266083390283465246116⟩, ⟨3,1,-47374217294708477376⟩, ⟨3,2,-336740750555725824⟩, ⟨4,0,47334236360384603840⟩, ⟨4,1,3704148256112984064⟩, ⟨5,0,-2357185253890080768⟩], [⟨0,0,16359364688938446148⟩, ⟨0,1,-6991392341668759312⟩, ⟨0,2,-7540682891662661633⟩, ⟨0,3,-1840732886354437228⟩, ⟨1,0,-69439199923511110755⟩, ⟨1,1,39425179102096505260⟩, ⟨1,2,28103796374097129420⟩, ⟨1,3,1869894155075240000⟩, ⟨2,0,35684917330537617293⟩, ⟨2,1,-128137756965639680948⟩, ⟨2,2,-22871986811493046080⟩, ⟨2,3,1010222251667177472⟩, ⟨3,0,112738923563605524180⟩, ⟨3,1,51415106301377187264⟩, ⟨3,2,336740750555725824⟩, ⟨4,0,-33780421150516639424⟩, ⟨4,1,-3704148256112984064⟩, ⟨5,0,2357185253890080768⟩]⟩,
  LabelExclusion.constant ⟨4, [Guard.circle 0], [⟨0,0,-1⟩, ⟨0,1,-1⟩, ⟨1,0,-1⟩], [⟨0,0,2⟩, ⟨0,1,-2⟩], []⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 5], [⟨0,1,4⟩, ⟨1,0,-1⟩], [⟨0,1,-4⟩, ⟨1,0,1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder, Guard.triangle 0], [⟨0,0,1⟩, ⟨0,1,2⟩, ⟨0,2,1⟩, ⟨1,0,-4⟩, ⟨1,1,-2⟩, ⟨2,0,1⟩], [⟨0,0,-2⟩, ⟨0,2,-2⟩, ⟨1,0,6⟩, ⟨1,1,4⟩, ⟨2,0,-2⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.circle 2], [⟨0,0,-3⟩, ⟨0,1,6⟩, ⟨1,0,2⟩], [⟨0,0,2⟩, ⟨0,1,-16⟩], [⟨0,0,-11⟩, ⟨0,1,10⟩, ⟨1,0,-2⟩]⟩,
  LabelExclusion.constant ⟨6, [Guard.bOrder], [⟨0,0,3⟩, ⟨0,1,70⟩, ⟨0,2,-128⟩, ⟨0,3,52⟩, ⟨1,0,16⟩, ⟨1,1,-4⟩, ⟨1,2,-108⟩, ⟨2,0,-12⟩, ⟨2,1,60⟩, ⟨3,0,-4⟩], [⟨0,0,-32⟩, ⟨0,1,104⟩, ⟨1,0,-8⟩], [⟨0,0,13⟩, ⟨0,1,-74⟩, ⟨0,2,24⟩, ⟨0,3,-52⟩, ⟨1,0,-44⟩, ⟨1,1,116⟩, ⟨1,2,108⟩, ⟨2,0,4⟩, ⟨2,1,-60⟩, ⟨3,0,4⟩]⟩,
  LabelExclusion.constant ⟨2, [Guard.bOrder], [⟨0,0,9⟩, ⟨0,1,-2⟩, ⟨0,3,-8⟩, ⟨1,0,-8⟩, ⟨1,1,8⟩, ⟨1,2,4⟩], [⟨0,0,-16⟩, ⟨0,1,48⟩, ⟨0,2,8⟩, ⟨0,3,16⟩, ⟨1,1,-8⟩, ⟨1,2,-16⟩], [⟨0,0,-1⟩, ⟨0,1,-10⟩, ⟨0,2,4⟩, ⟨1,0,4⟩, ⟨1,1,-12⟩, ⟨1,2,4⟩]⟩,
  LabelExclusion.constant ⟨1, [Guard.triangle 0, Guard.triangle 3], [⟨0,1,4⟩, ⟨1,0,-1⟩], [⟨0,1,-4⟩, ⟨1,0,1⟩], []⟩,
  LabelExclusion.constant ⟨2, [Guard.triangle 9], [⟨0,0,3⟩], [⟨0,0,-6⟩], []⟩]

private def exclusionRow33 : Array LabelExclusion := #[
  LabelExclusion.constant ⟨1, [Guard.circle 2], [⟨0,1,-1⟩], [⟨0,1,1⟩], []⟩]

private def exclusionRows : Array (Array LabelExclusion) := #[exclusionRow0, exclusionRow1, exclusionRow2, exclusionRow3, exclusionRow4, exclusionRow5, exclusionRow6, exclusionRow7, exclusionRow8, exclusionRow9, exclusionRow10, exclusionRow11, exclusionRow12, exclusionRow13, exclusionRow14, exclusionRow15, exclusionRow16, exclusionRow17, exclusionRow18, exclusionRow19, exclusionRow20, exclusionRow21, exclusionRow22, exclusionRow23, exclusionRow24, exclusionRow25, exclusionRow26, exclusionRow27, exclusionRow28, exclusionRow29, exclusionRow30, exclusionRow31, exclusionRow32, exclusionRow33]

private def exclusionByIdx (i : Nat) : LabelExclusion :=
  ((exclusionRows.getD (i / 16) #[]).getD (i % 16)
    (.constant ⟨0,[],[],[],[]⟩))

private theorem checked_exclusions_0 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 0 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 0 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_1 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 1 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 1 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_2 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 2 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 2 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_3 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 3 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 3 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_4 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 4 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 4 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_5 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 5 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 5 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_6 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 6 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 6 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_7 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 7 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 7 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_8 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 8 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 8 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_9 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 9 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 9 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_10 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 10 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 10 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_11 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 11 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 11 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_12 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 12 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 12 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_13 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 13 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 13 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_14 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 14 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 14 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_15 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 15 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 15 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_16 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 16 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 16 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_17 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 17 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 17 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_18 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 18 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 18 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_19 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 19 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 19 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_20 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 20 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 20 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_21 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 21 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 21 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_22 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 22 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 22 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_23 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 23 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 23 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_24 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 24 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 24 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_25 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 25 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 25 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_26 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 26 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 26 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_27 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 27 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 27 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_28 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 28 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 28 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_29 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 29 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 29 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_30 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 30 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 30 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_31 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 31 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 31 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_32 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 32 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 32 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_exclusions_33 : ∀ j : Fin 16,
    validExclusion (lookupThreeCode ((16 * 33 + (j : Nat)) % 529))
      (exclusionByIdx ((16 * 33 + (j : Nat)) % 529)) = true := by
  decide +kernel

private theorem checked_blocks (i : Fin 34) (j : Fin 16) :
    validExclusion (lookupThreeCode ((16 * (i : Nat) + (j : Nat)) % 529))
      (exclusionByIdx ((16 * (i : Nat) + (j : Nat)) % 529)) = true := by
  fin_cases i
  · exact checked_exclusions_0 j
  · exact checked_exclusions_1 j
  · exact checked_exclusions_2 j
  · exact checked_exclusions_3 j
  · exact checked_exclusions_4 j
  · exact checked_exclusions_5 j
  · exact checked_exclusions_6 j
  · exact checked_exclusions_7 j
  · exact checked_exclusions_8 j
  · exact checked_exclusions_9 j
  · exact checked_exclusions_10 j
  · exact checked_exclusions_11 j
  · exact checked_exclusions_12 j
  · exact checked_exclusions_13 j
  · exact checked_exclusions_14 j
  · exact checked_exclusions_15 j
  · exact checked_exclusions_16 j
  · exact checked_exclusions_17 j
  · exact checked_exclusions_18 j
  · exact checked_exclusions_19 j
  · exact checked_exclusions_20 j
  · exact checked_exclusions_21 j
  · exact checked_exclusions_22 j
  · exact checked_exclusions_23 j
  · exact checked_exclusions_24 j
  · exact checked_exclusions_25 j
  · exact checked_exclusions_26 j
  · exact checked_exclusions_27 j
  · exact checked_exclusions_28 j
  · exact checked_exclusions_29 j
  · exact checked_exclusions_30 j
  · exact checked_exclusions_31 j
  · exact checked_exclusions_32 j
  · exact checked_exclusions_33 j

private theorem check_exclusions (i : Fin 529) :
    validExclusion (lookupThreeCode i) (exclusionByIdx i) = true := by
  let block : Fin 34 := ⟨(i : Nat)/16, by omega⟩
  let slot : Fin 16 := ⟨(i : Nat)%16, Nat.mod_lt _ (by decide)⟩
  have h : 16*(block : Nat) + (slot : Nat) = (i : Nat) := by
    have hN := Nat.mod_add_div (i : Nat) 16
    dsimp [block,slot]
    omega
  have hmod : (16*(block : Nat) + (slot : Nat)) % 529 = (i : Nat) := by
    rw [h, Nat.mod_eq_of_lt i.isLt]
  simpa only [hmod] using checked_blocks block slot

private theorem rejectCases (i : Fin 529) (a b : ℝ) (ha : 1<a) (hb : a<b)
    (h : StandardDistanceData (fromThree (readThree (lookupThreeCode i)) a b)) : False :=
  label_excluded (lookupThreeCode i) (exclusionByIdx i) a b ha hb h (check_exclusions i)

private theorem edge_roundtrip : ∀ k : Fin 10,
    edgeIndex (edgePair k).1 (edgePair k).2 = k := by decide

private theorem edge_distinct : ∀ k : Fin 10, (edgePair k).1 ≠ (edgePair k).2 := by decide

private theorem edge_symmetric : ∀ i j : Fin 5, edgeIndex i j = edgeIndex j i := by decide

private def edgeMap (g : Fin 5 → Fin 5) (k : Fin 10) : Fin 10 :=
  edgeIndex (g (edgePair k).1) (g (edgePair k).2)

private theorem edgeMap_injective (g : Fin 5 → Fin 5) (hg : Function.Injective g) :
    Function.Injective (edgeMap g) := by
  intro i j h
  have hi := edgePair_eq (g (edgePair i).1) (g (edgePair i).2)
    (fun he => edge_distinct i (hg he))
  have hj := edgePair_eq (g (edgePair j).1) (g (edgePair j).2)
    (fun he => edge_distinct j (hg he))
  change edgeIndex (g (edgePair i).1) (g (edgePair i).2) =
      edgeIndex (g (edgePair j).1) (g (edgePair j).2) at h
  rw [h] at hi
  have firstPair :
      ((edgePair i).1 = (edgePair j).1 ∧ (edgePair i).2 = (edgePair j).2) ∨
      ((edgePair i).1 = (edgePair j).2 ∧ (edgePair i).2 = (edgePair j).1) := by
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · have he := hi.symm.trans hj
      exact Or.inl ⟨hg (congrArg Prod.fst he), hg (congrArg Prod.snd he)⟩
    · have he := hi.symm.trans hj
      exact Or.inr ⟨hg (congrArg Prod.fst he), hg (congrArg Prod.snd he)⟩
    · have he := hi.symm.trans hj
      exact Or.inr ⟨hg (congrArg Prod.snd he), hg (congrArg Prod.fst he)⟩
    · have he := hi.symm.trans hj
      exact Or.inl ⟨hg (congrArg Prod.snd he), hg (congrArg Prod.fst he)⟩
  rw [← edge_roundtrip i, ← edge_roundtrip j]
  rcases firstPair with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [h₁,h₂]
  · rw [h₁,h₂,edge_symmetric]

private theorem edgeMap_apply (g : Fin 5 → Fin 5) (i j : Fin 5) (hij : i ≠ j) :
    edgeMap g (edgeIndex i j) = edgeIndex (g i) (g j) := by
  rcases edgePair_eq i j hij with h | h
  · simp [edgeMap,h]
  · simp [edgeMap,h,edge_symmetric]

private theorem ones_comp (c : Fin 10 → Bool) (g : Fin 10 → Fin 10)
    (hg : Function.Injective g) : ones (c ∘ g) = ones c := by
  classical
  let S : Finset (Fin 10) := Finset.univ.filter (fun k => (c ∘ g) k = true)
  let T : Finset (Fin 10) := Finset.univ.filter (fun k => c k = true)
  change S.card = T.card
  have hsurj : Function.Surjective g := Finite.surjective_of_injective hg
  have him : S.image g = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      simpa [S,T] using hy
    · intro hx
      obtain ⟨y,rfl⟩ := hsurj x
      exact Finset.mem_image.mpr ⟨y, by simpa [S,T] using hx, rfl⟩
  rw [← Finset.card_image_of_injective S hg, him]

private theorem data_reindex {d d' : Fin 5 → Fin 5 → ℝ}
    (h : StandardDistanceData d) (e : Fin 5 → Fin 5) (he : Function.Injective e)
    (hd : ∀ i j, d (e i) (e j) = d' i j) : StandardDistanceData d' := by
  constructor
  · intro o i j k l
    have hh := h.gram (e o) (e i) (e j) (e k) (e l)
    simpa only [squaredGram, hd] using hh
  · intro i j k hij hik hjk
    have hh := h.triangle (e i) (e j) (e k) (fun h => hij (he h))
      (fun h => hik (he h)) (fun h => hjk (he h))
    simpa only [hd] using hh
  · intro i j k l hij hik hil hjk hjl hkl
    have hh := h.circle (e i) (e j) (e k) (e l) (fun h => hij (he h))
      (fun h => hik (he h)) (fun h => hil (he h))
      (fun h => hjk (he h)) (fun h => hjl (he h)) (fun h => hkl (he h))
    simpa only [hd] using hh

private theorem three_distance_mod_four (a b : ℝ) (ha : 1 < a) (hb : a < b)
    (c : Fin 10 → Fin 3) (hAll : hasAllThree c)
    (h : StandardDistanceData (fromThree c a b)) :
    ones (fun k => decide (c k = 1)) % 4 = 1 := by
  let paint : Fin 10 → Bool := fun k => decide (c k = 1)
  let m := encode paint
  let label := caseId m
  let e := renumber m
  have hcases := coloring_coverage m
  have he : Function.Injective e := fun i j hij => hcases.1 i j hij
  let c' := c ∘ edgeMap e
  have hcolors (k : Fin 10) : (paint ∘ edgeMap e) k = twoPatterns label k := by
    have hh := hcases.2 (edgePair k).1 (edgePair k).2 (edge_distinct k)
    rw [edge_roundtrip k, encode_correct paint] at hh
    exact hh
  have hcount : ones (twoPatterns label) = ones paint := by
    rw [← funext hcolors]
    exact ones_comp paint _ (edgeMap_injective e he)
  change ones paint % 4 = 1
  rw [← hcount]
  by_contra! hno
  have hpos : 0 < ones (twoPatterns label) := by
    rw [hcount]
    obtain ⟨k,hk⟩ := hAll.2.1
    exact Finset.card_pos.mpr ⟨k, by simp [paint,hk]⟩
  have hmid (k : Fin 10) : c' k = 1 ↔ twoPatterns label k = true := by
    rw [← hcolors k]
    simp [c',paint]
  obtain ⟨m',hm'⟩ := packThree label c' hmid
  have hsurj : Function.Surjective (edgeMap e) :=
    Finite.surjective_of_injective (edgeMap_injective e he)
  have hAll' : hasAllThree (unpackThree label m') := by
    rw [funext hm']
    rcases hAll with ⟨⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩⟩
    obtain ⟨u,hu⟩ := hsurj i
    obtain ⟨v,hv⟩ := hsurj j
    obtain ⟨w,hw⟩ := hsurj k
    exact ⟨⟨u,by simpa [c',hu] using hi⟩,⟨v,by simpa [c',hv] using hj⟩,⟨w,by simpa [c',hw] using hk⟩⟩
  have cfirst : StandardDistanceData (fromThree (unpackThree label m') a b) := by
    refine data_reindex h e he (fun i j => ?_)
    by_cases hij : i = j
    · subst j
      simp [fromThree]
    · have he' : e i ≠ e j := fun h => hij (he h)
      simp [fromThree, he', hij, hm', c', edgeMap_apply e i j hij]
  obtain ⟨he2,hcases2⟩ := three_coverage label hpos hno m' hAll'
  let e' := permThree label m'
  let idx := caseNumThree label m'
  have he' : Function.Injective e' := fun i j hij => he2 i j hij
  apply rejectCases idx a b ha hb
  refine data_reindex cfirst e' he' (fun i j => ?_)
  by_cases hij : i = j
  · subst j
    simp [fromThree]
  · have heij : e' i ≠ e' j := fun h => hij (he' h)
    have hh := hcases2 i j hij
    change unpackThree label (↑m') (edgeIndex (e' i) (e' j)) =
      readThree (lookupThreeCode idx) (edgeIndex i j) at hh
    simp [fromThree,heij,hij,hh]

private noncomputable def distanceValues {n : ℕ} (p : Config n) : Finset ℝ := by
  classical
  exact p.toFinset.offDiag.image (fun v : Point × Point => dist v.1 v.2)

private theorem point_distance_mem {n : ℕ} (p : Config n) (hp : Function.Injective p)
    (i j : Fin n) (hij : i ≠ j) : dist (p i) (p j) ∈ distanceValues p := by
  classical
  exact Finset.mem_image.mpr ⟨(p i,p j), Finset.mem_offDiag.mpr
    ⟨image_contains p i,image_contains p j, fun h => hij (hp h)⟩, rfl⟩

private theorem distance_indices {n : ℕ} (p : Config n) {d : ℝ}
    (hd : d ∈ distanceValues p) :
    ∃ i j : Fin n, i ≠ j ∧ dist (p i) (p j) = d := by
  classical
  obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨ha,hb,hne⟩ := Finset.mem_offDiag.mp hab
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
  exact ⟨i,j,fun h => hne (congrArg p h),rfl⟩

private theorem positive_distance {n : ℕ} (p : Config n) (hp : Function.Injective p)
    {d : ℝ} (hd : d ∈ distanceValues p) : 0 < d := by
  obtain ⟨i,j,hne,rfl⟩ := distance_indices p hd
  exact dist_pos.mpr (fun h => hne (hp h))

private theorem sq_ratio_lt {u v r : ℝ} (u_pos : 0 < u) (huv : u < v) (hr : 0 < r) :
    u^2/r^2 < v^2/r^2 := by
  have hsum : 0 < v+u := by linarith
  have hprod := mul_pos (sub_pos.mpr huv) hsum
  apply div_lt_div_of_pos_right _ (by positivity)
  nlinarith only [hprod]

private noncomputable def middleEdges (p : Config 5) (s : ℝ) : Fin 10 → Bool := by
  classical
  exact fun k => decide (dist (p (edgePair k).1) (p (edgePair k).2) = s)

private theorem middle_geometry (p : Config 5) (hp : Function.Injective p)
    (hgp : InGeneralPosition p.toFinset) (r s t : ℝ) (hr : 0 < r)
    (hrs : r < s) (hst : s < t) (hD : distanceValues p = {r,s,t}) :
    ones (middleEdges p s) % 4 = 1 := by
  classical
  let lab : ℝ → Fin 3 := fun d => if d = r then 0 else if d = s then 1 else 2
  let c : Fin 10 → Fin 3 := fun k => lab (dist (p (edgePair k).1) (p (edgePair k).2))
  let a := s^2/r^2
  let b := t^2/r^2
  have ha : 1 < a := by
    have h := sq_ratio_lt hr hrs hr
    simpa [a,ne_of_gt hr] using h
  have hb : a < b := sq_ratio_lt (lt_trans hr hrs) hst hr
  have label_pair (i j : Fin 5) (hne : i ≠ j) :
      c (edgeIndex i j) = lab (dist (p i) (p j)) := by
    rcases edgePair_eq i j hne with h | h
    · simp [c,h]
    · simp [c,h,dist_comm]
  have has (d : ℝ) (h : d ∈ distanceValues p) : ∃ k : Fin 10, c k = lab d := by
    obtain ⟨i,j,hij,he⟩ := distance_indices p h
    exact ⟨edgeIndex i j, by rw [label_pair i j hij,he]⟩
  have hAll : hasAllThree c := by
    refine ⟨?_,?_,?_⟩
    · simpa [lab] using has r (by simp [hD])
    · simpa [lab,hrs.ne'] using has s (by simp [hD])
    · simpa [lab,hst.ne',(hrs.trans hst).ne'] using has t (by simp [hD])
  have hsq : 0 < r^2 := by positivity
  have hdata := data_of_points p hp hgp (r^2) hsq.ne'
  have heq : (fun i j => dist (p i) (p j)^2/r^2) = fromThree c a b := by
    funext i j
    by_cases hne : i = j
    · subst j
      simp [fromThree]
    · have hd := point_distance_mem p hp i j hne
      rw [hD] at hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd
      rw [fromThree, if_neg hne, label_pair i j hne]
      rcases hd with h | h | h
      · simp [h,lab,hsq.ne']
      · simp [h,lab,hrs.ne',a]
      · simp [h,lab,hst.ne',(hrs.trans hst).ne',b]
  rw [heq] at hdata
  have h := three_distance_mod_four a b ha hb c hAll hdata
  have hc : (fun k => decide (c k = 1)) = middleEdges p s := by
    funext k
    let d := dist (p (edgePair k).1) (p (edgePair k).2)
    change decide (lab d = 1) = decide (d = s)
    by_cases hrs' : d = s
    · simp [lab,hrs',hrs.ne']
    · by_cases hr' : d = r <;> simp [lab,hrs',hr',hrs.ne]
  simpa only [hc] using h

private def dropPoint (p : Config 6) (k : Fin 6) : Config 5 := p ∘ k.succAbove

private theorem gp_subset {S T : Finset Point} (h : S ⊆ T)
    (hT : InGeneralPosition T) : InGeneralPosition S := by
  constructor
  · intro x hx y hy z hz hxy hyz hxz
    exact hT.1 (h hx) (h hy) (h hz) hxy hyz hxz
  · intro U hU hcard
    exact hT.2 U (hU.trans h) hcard

private def edgePairSix : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),
    (2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

private def edgeIndexSix (i j : Fin 6) : Fin 15 :=
  ![![0,0,1,2,3,4], ![0,0,5,6,7,8], ![1,5,0,9,10,11],
    ![2,6,9,0,12,13], ![3,7,10,12,0,14], ![4,8,11,13,14,0]] i j

private def dropEdge (v : Fin 6 × Fin 10) : Fin 15 :=
  edgeIndexSix (v.1.succAbove (edgePair v.2).1) (v.1.succAbove (edgePair v.2).2)

private theorem dropEdge_pair : ∀ k : Fin 6, ∀ j : Fin 10,
    edgePairSix (dropEdge (k,j)) = (k.succAbove (edgePair j).1,
      k.succAbove (edgePair j).2) := by decide +kernel

private theorem dropEdge_fiber : ∀ j : Fin 15,
    ((Finset.univ : Finset (Fin 6 × Fin 10)).filter (fun p => dropEdge p = j)).card = 4 := by
  decide +kernel

private theorem count_four (g : Fin 6 → Fin 6 → Bool) :
    (∑ k : Fin 6, ones (fun j => g (k.succAbove (edgePair j).1) (k.succAbove (edgePair j).2)))
      = 4 * (∑ j : Fin 15, if g (edgePairSix j).1 (edgePairSix j).2 then (1:ℕ) else 0) := by
  let value (j : Fin 15) : ℕ := if g (edgePairSix j).1 (edgePairSix j).2 then 1 else 0
  calc
    _ = ∑ k : Fin 6, ∑ j : Fin 10, value (dropEdge (k,j)) := by
      simp only [ones, Finset.card_eq_sum_ones, Finset.sum_filter]
      simp only [value,dropEdge_pair]
    _ = ∑ u : Fin 6 × Fin 10, value (dropEdge u) := by
      rw [← Finset.sum_product', Finset.univ_product_univ]
    _ = ∑ j : Fin 15, ∑ u ∈ Finset.univ.filter (fun p => dropEdge p = j), value j :=
      (Finset.sum_fiberwise' Finset.univ dropEdge value).symm
    _ = ∑ j : Fin 15, 4 * value j := by
      simp only [Finset.sum_const,nsmul_eq_mul,dropEdge_fiber]
      rfl
    _ = _ := by rw [Finset.mul_sum]

private theorem six_distance_lower (p : Config 6) (hp : Function.Injective p)
    (hgp : InGeneralPosition p.toFinset) : 4 ≤ distinctDistances p.toFinset := by
  classical
  let D := distanceValues p
  change 4 ≤ D.card
  by_contra! hsmall
  have hpinj (i : Fin 6) : Function.Injective (dropPoint p i) :=
    hp.comp (Fin.succAbove_right_injective (p := i))
  have hsub (i : Fin 6) : (dropPoint p i).toFinset ⊆ p.toFinset := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    exact image_contains p (i.succAbove j)
  have hdsub (i : Fin 6) : distanceValues (dropPoint p i) ⊆ D := by
    intro u hu
    obtain ⟨j,k,hne,rfl⟩ := distance_indices (dropPoint p i) hu
    exact point_distance_mem p hp _ _ (fun h => hne (Fin.succAbove_right_injective h))
  have hcard (i : Fin 6) : 3 ≤ (distanceValues (dropPoint p i)).card :=
    Esgk.general_position_five_exact.1 (dropPoint p i) (hpinj i) (gp_subset (hsub i) hgp)
  have hd : D.card = 3 := by
    have hh := (hcard 0).trans (Finset.card_le_card (hdsub 0))
    omega
  have hD (i : Fin 6) : distanceValues (dropPoint p i) = D := by
    refine Finset.eq_of_subset_of_card_le (hdsub i) ?_
    simpa [hd] using hcard i
  let e := D.orderEmbOfFin hd
  let r := e 0
  let s := e 1
  let t := e 2
  have hrs : r < s := e.strictMono (by decide)
  have hst : s < t := e.strictMono (by decide)
  have hr : 0 < r := positive_distance p hp (D.orderEmbOfFin_mem hd 0)
  have hvalues : D = {r,s,t} := by
    ext u
    constructor
    · intro hu
      obtain ⟨j,hj⟩ := (D.orderIsoOfFin hd).surjective ⟨u,hu⟩
      have eq : e j = u := by exact congrArg Subtype.val hj
      simp only [Finset.mem_insert,Finset.mem_singleton]
      fin_cases j
      · exact Or.inl eq.symm
      · exact Or.inr (Or.inl eq.symm)
      · exact Or.inr (Or.inr eq.symm)
    · intro hu
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact D.orderEmbOfFin_mem hd 0
      · exact D.orderEmbOfFin_mem hd 1
      · exact D.orderEmbOfFin_mem hd 2
  have congr (i : Fin 6) : (ones (middleEdges (dropPoint p i) s)) % 4 = 1 :=
    middle_geometry _ (hpinj i) (gp_subset (hsub i) hgp) r s t hr hrs hst (hD i |>.trans hvalues)
  have hmul := count_four (fun i j => decide (dist (p i) (p j) = s))
  let m (i : Fin 6) := ones (middleEdges (dropPoint p i) s)
  have hsum : (∑ i : Fin 6, m i) % 4 = 0 := by
    change (∑ i : Fin 6, m i) = _ at hmul
    rw [hmul, Nat.mul_mod_right]
  have term (i : Fin 6) : m i = 4 * (m i / 4) + 1 := by
    have hm : m i % 4 = 1 := congr i
    have h := Nat.mod_add_div (m i) 4
    omega
  have htotal : (∑ i : Fin 6, m i) = 4 * (∑ i : Fin 6, m i / 4) + 6 := by
    calc
      _ = ∑ i : Fin 6, (4 * (m i / 4) + 1) := Finset.sum_congr rfl fun i _ => term i
      _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum]
  omega

private abbrev LatticePoint := ℤ × ℤ

private def latticeDiff (x y : LatticePoint) : LatticePoint := (x.1-y.1,x.2-y.2)

private def triangleInt (o a b : LatticePoint) : ℤ :=
  (a.1-o.1)*(b.2-o.2)-(a.2-o.2)*(b.1-o.1)

private def normInt (p : LatticePoint) : ℤ := p.1^2+p.1*p.2+p.2^2

private def circleInt (o a b c : LatticePoint) :=
  triangleInt o a b * normInt (latticeDiff c o) -
  triangleInt o a c * normInt (latticeDiff b o) +
  triangleInt o b c * normInt (latticeDiff a o)

private noncomputable def toPlane (s : ℝ) (p : LatticePoint) : Point :=
  xy ((p.1 : ℝ) + (p.2 : ℝ)/2) (s*(p.2 : ℝ)/2)

private theorem toPlane_inj (s : ℝ) (hs : s ≠ 0) : Function.Injective (toPlane s) := by
  intro a b h
  have hx := congrArg (fun p : Point => p 0) h
  have hy := congrArg (fun p : Point => p 1) h
  simp only [toPlane,xy_zero] at hx
  simp only [toPlane,xy_one] at hy
  have he : s*(((a.2 : ℝ)-(b.2 : ℝ))) = 0 := by linarith only [hy]
  have hy' : (a.2 : ℝ) = (b.2 : ℝ) := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hs)
  have hx' : (a.1 : ℝ) = (b.1 : ℝ) := by linarith only [hx,hy']
  exact Prod.ext (by exact_mod_cast hx') (by exact_mod_cast hy')

private theorem distance_lattice (s : ℝ) (hs : s^2=3) (x y : LatticePoint) :
    dist (toPlane s x) (toPlane s y)^2 = (normInt (latticeDiff x y) : ℝ) := by
  rw [dist_sq_xy]
  simp only [toPlane,xy_zero,xy_one,normInt,latticeDiff]
  push_cast
  linear_combination (((x.2 : ℝ)-(y.2 : ℝ))^2 / 4)*hs

private theorem triangle_lattice (s : ℝ) (o a b : LatticePoint) :
    area (toPlane s o) (toPlane s a) (toPlane s b) =
      s/2 * (triangleInt o a b : ℝ) := by
  simp only [area,toPlane,xy_zero,xy_one,triangleInt]
  push_cast
  ring

private theorem circle_lattice (s : ℝ) (hs : s^2=3) (o a b c : LatticePoint) :
    liftedArea (toPlane s o) (toPlane s a) (toPlane s b) (toPlane s c) =
      s/2 * (circleInt o a b c : ℝ) := by
  simp only [liftedArea,triangle_lattice,distance_lattice s hs,circleInt]
  push_cast
  ring

private theorem lattice_upper {n : ℕ} (v : Fin n → LatticePoint)
    (hv : Function.Injective v) (allowed : Finset ℤ)
    (ht : ∀ i j k : Fin n, i < j → j < k → triangleInt (v i) (v j) (v k) ≠ 0)
    (hq : ∀ i j k l : Fin n, i < j → j < k → k < l →
      circleInt (v i) (v j) (v k) (v l) ≠ 0)
    (hd : ∀ i j : Fin n, i ≠ j → normInt (latticeDiff (v i) (v j)) ∈ allowed) :
    ∃ p : Config n, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
      distinctDistances p.toFinset ≤ allowed.card := by
  classical
  let s := Real.sqrt 3
  have hs : s^2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 : s ≠ 0 := (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ)<3)).ne'
  let p := toPlane s ∘ v
  have hi := (toPlane_inj s h0).comp hv
  have hT (i j k : Fin n) (hij : i<j) (hjk : j<k) : area (p i) (p j) (p k) ≠ 0 := by
    change area (toPlane s (v i)) (toPlane s (v j)) (toPlane s (v k)) ≠ 0
    rw [triangle_lattice]
    exact mul_ne_zero (div_ne_zero h0 (by norm_num)) (by exact_mod_cast ht i j k hij hjk)
  have hQ (i j k l : Fin n) (hij : i<j) (hjk : j<k) (hkl : k<l) :
      liftedArea (p i) (p j) (p k) (p l) ≠ 0 := by
    change liftedArea (toPlane s (v i)) (toPlane s (v j)) (toPlane s (v k)) (toPlane s (v l)) ≠ 0
    rw [circle_lattice s hs]
    exact mul_ne_zero (div_ne_zero h0 (by norm_num)) (by exact_mod_cast hq i j k l hij hjk hkl)
  refine ⟨p,hi,gp_of_area p hi hT hQ,?_⟩
  let imageR := allowed.image (fun u : ℤ => Real.sqrt (u : ℝ))
  have hsub : distanceValues p ⊆ imageR := by
    intro q hq
    obtain ⟨i,j,hij,rfl⟩ := distance_indices p hq
    refine Finset.mem_image.mpr ⟨normInt (latticeDiff (v i) (v j)), hd i j hij, ?_⟩
    rw [← distance_lattice s hs, Real.sqrt_sq dist_nonneg]
    rfl
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

private def latticeSixPoints : Fin 6 → LatticePoint :=
  ![(1,0),(2,0),(3,1),(0,2),(2,2),(0,3)]

private theorem lattice_six_bound :
    ∃ p : Config 6, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
      distinctDistances p.toFinset ≤ 4 := by
  let points := latticeSixPoints
  let distances : Finset ℤ := {1,3,4,7}
  have hi : ∀ i j, points i = points j → i=j := by
    dsimp [points]
    decide +kernel
  have ht : ∀ i j k, i < j → j < k → triangleInt (points i) (points j) (points k) ≠ 0 := by
    dsimp [points]
    decide +kernel
  have hq : ∀ i j k l, i<j → j<k → k<l →
      circleInt (points i) (points j) (points k) (points l) ≠ 0 := by
    dsimp [points]
    decide +kernel
  have hd : ∀ i j, i ≠ j → normInt (latticeDiff (points i) (points j)) ∈ distances := by
    dsimp [points,distances]
    decide +kernel
  have bound : distances.card = 4 := by decide
  simpa only [bound] using lattice_upper points (fun i j h => hi i j h) distances ht hq hd


private theorem six_exact :
    (∀ p : Config 6, Function.Injective p → InGeneralPosition p.toFinset →
      4 ≤ distinctDistances p.toFinset) ∧
      ∃ p : Config 6, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
        distinctDistances p.toFinset = 4 := by
  refine ⟨six_distance_lower,?_⟩
  obtain ⟨p,hp,hgp,hu⟩ := lattice_six_bound
  exact ⟨p,hp,hgp,Nat.le_antisymm hu (six_distance_lower p hp hgp)⟩

end Esgk

open Esgk in
theorem solution :
    (∀ p : Config 6, Function.Injective p → InGeneralPosition p.toFinset →
      4 ≤ distinctDistances p.toFinset) ∧
      ∃ p : Config 6, Function.Injective p ∧ InGeneralPosition p.toFinset ∧
        distinctDistances p.toFinset = 4 :=
  Esgk.six_exact

#print axioms solution
