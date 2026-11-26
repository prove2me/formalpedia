-- Prove2me | solution 1 for GRH.explicit_weighted_prefix_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:17:03.466342+00:00
-- url     : https://prove2.me/submissions/9ca0e746-2c44-42bb-8bd2-0084ffb026f0

import Theorems.Thm_GRH_dirichlet_weighted_prefix_cover_of_rational_table
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open GRH.DirichletPrefix

set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

private def oneData : Array ℕ := #[
  0, 1048576, 573341, 402757, 313492, 258119, 220220, 192552, 171411, 154699, 141135, 129892,
  120412, 112303, 105284, 99144, 93724, 88904, 84586, 80696, 77170, 73959, 71023, 68325,
  65839, 63539, 61406, 59420, 57567, 55834, 54210, 52684, 51247, 49892, 48611, 47399,
  46250, 45160, 44123, 43136, 42195, 41297, 40440, 39619, 38834, 38081, 37359, 36666,
  36000, 35359, 34742, 34148, 33576, 33023, 32490, 31975, 31477, 30995, 30529, 30078,
  29641, 29217, 28807, 28408, 28021, 27645, 27280, 26925, 26580, 26244, 25917, 25599,
  25289, 24987, 24693, 24406, 24126, 23853, 23586, 23326, 23072, 22823, 22581, 22344,
  22112, 21885, 21663, 21446, 21234, 21026, 20822, 20623, 20427, 20236, 20048, 19864,
  19684, 19507, 19334, 19164, 18997, 18833, 18672, 18514, 18359, 18206, 18057, 17910,
  17765, 17623, 17483, 17346, 17211, 17078, 16948, 16819, 16693, 16569, 16446, 16326,
  16207, 16091, 15976, 15863, 15751, 15641, 15533, 15427, 15322, 15218, 15116, 15015,
  14916, 14819, 14722, 14627, 14534, 14441, 14350, 14260, 14171, 14084, 13997, 13912,
  13828, 13745, 13663, 13582, 13502, 13423, 13345, 13268, 13192, 13117, 13042, 12969,
  12897, 12825, 12754, 12684, 12615, 12547, 12480, 12413, 12347, 12282, 12217, 12154,
  12091, 12028, 11967, 11906, 11845, 11786, 11727, 11668, 11610, 11553, 11497, 11441,
  11385, 11331, 11276, 11223, 11170, 11117, 11065, 11013, 10962, 10912, 10862, 10812,
  10763, 10715, 10666, 10619, 10572, 10525, 10479, 10433, 10387, 10342, 10298, 10253,
  10210, 10166, 10123, 10081, 10038, 9997, 9955, 9914, 9873, 9833, 9793, 9753,
  9714, 9675, 9636, 9598, 9560, 9522, 9485, 9448, 9411, 9374, 9338, 9303,
  9267, 9232, 9197, 9162, 9128, 9094, 9060, 9026, 8993, 8960, 8927, 8894,
  8862, 8830, 8798, 8767, 8735, 8704, 8674, 8643, 8613, 8582, 8553, 8523,
  8493, 8464, 8435, 8406, 8378]
private def oneUpper (n : ℕ) : ℕ := (oneData[n]?).getD 0

private def threeData : Array ℕ := #[
  0, 1048576, 684465, 533319, 446788, 389462, 348127, 316621, 291644, 271253, 254224, 239742,
  227242, 216320, 206677, 198085, 190372, 183401, 177062, 171268, 165946, 161038, 156493, 152270,
  148334, 144654, 141205, 137963, 134910, 132027, 129302, 126719, 124267, 121936, 119716, 117600,
  115579, 113646, 111796, 110023, 108323, 106689, 105119, 103607, 102152, 100749, 99395, 98089,
  96826, 95605, 94424, 93280, 92172, 91098, 90056, 89045, 88063, 87109, 86182, 85280,
  84403, 83548, 82717, 81906, 81116, 80346, 79595, 78861, 78146, 77447, 76764, 76097,
  75445, 74807, 74183, 73573, 72976, 72391, 71819, 71258, 70708, 70170, 69642, 69124,
  68617, 68119, 67630, 67151, 66680, 66218, 65765, 65319, 64881, 64451, 64028, 63613,
  63204, 62802, 62407, 62018, 61636, 61260, 60889, 60525, 60166, 59813, 59465, 59122,
  58785]
private def threeUpper (n : ℕ) : ℕ := (threeData[n]?).getD 0

/-- Explicit period tables give closed rectangles for all divisor levels,
including characters of prime conductor seven and the height-three case. -/
theorem solution (d : ℕ) (a b H : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 7/8)
    (hH : 0 ≤ H) (h : ((d ∣ 24 ∨ d ∣ 36 ∨ d ∣ 42 ∨ d ∣ 60) ∧ (27/31:ℝ) ≤ a ∧ H ≤ 1) ∨
      (d ∣ 6 ∧ (8/13:ℝ) ≤ a ∧ H ≤ 3)) : Covers d a b H := by
  have bs := mul_self_le_mul_self (ha.trans hab) hb
  rcases h with ⟨hd,hx,hh⟩ | ⟨hd,hx,hh⟩
  · have hgeom : b^2+H^2 ≤ (((153:ℝ)/100)*(27/31))^2 := by
      nlinarith [mul_self_le_mul_self hH hh]
    rcases hd with hd|hd|hd|hd
    · apply GRH.dirichlet_weighted_prefix_cover_of_rational_table d 24 31 4 1048576 27 31 153 100
        oneUpper a b H (by decide) hd (by decide) (by decide) (by decide) (by decide) hx hgeom
      · decide
      · unfold Table
        decide
      · decide
    · apply GRH.dirichlet_weighted_prefix_cover_of_rational_table d 36 255 6 1048576 27 31 153 100
        oneUpper a b H (by decide) hd (by decide) (by decide) (by decide) (by decide) hx hgeom
      · decide
      · unfold Table
        decide
      · decide
    · apply GRH.dirichlet_weighted_prefix_cover_of_rational_table d 42 51 6 1048576 27 31 153 100
        oneUpper a b H (by decide) hd (by decide) (by decide) (by decide) (by decide) hx hgeom
      · decide
      · unfold Table
        decide
      · decide
    · apply GRH.dirichlet_weighted_prefix_cover_of_rational_table d 60 99 8 1048576 27 31 153 100
        oneUpper a b H (by decide) hd (by decide) (by decide) (by decide) (by decide) hx hgeom
      · decide
      · unfold Table
        decide
      · decide
  · have hgeom : b^2+H^2 ≤ (((51:ℝ)/10)*(8/13))^2 := by
      nlinarith [mul_self_le_mul_self hH hh]
    apply GRH.dirichlet_weighted_prefix_cover_of_rational_table d 6 107 1 1048576 8 13 51 10
      threeUpper a b H (by decide) hd (by decide) (by decide) (by decide) (by decide) hx hgeom
    · decide
    · unfold Table
      decide
    · decide
