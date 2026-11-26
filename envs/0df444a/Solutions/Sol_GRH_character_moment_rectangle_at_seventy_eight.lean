-- Prove2me | solution 1 for GRH.character_moment_rectangle_at_seventy_eight
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:21:20.164874+00:00
-- url     : https://prove2.me/submissions/26a087bf-ef59-4a0c-8d7d-4e79f17a4f59

import Definitions.Def_GRH_CharacterMoment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open GRH.CharacterMoment

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private def U : Finset ℕ := {1, 5, 7, 11, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55, 59, 61, 67, 71, 73, 77}
private def inverseData : Array ℕ := #[0, 1, 0, 0, 0, 47, 0, 67, 0, 0, 0, 71,
  0, 0, 0, 0, 0, 23, 0, 37, 0, 0, 0, 17,
  0, 25, 0, 0, 0, 35, 0, 73, 0, 0, 0, 29,
  0, 19, 0, 0, 0, 59, 0, 49, 0, 0, 0, 5,
  0, 43, 0, 0, 0, 53, 0, 61, 0, 0, 0, 41,
  0, 55, 0, 0, 0, 0, 0, 7, 0, 0, 0, 11,
  0, 31, 0, 0, 0, 77]
private def inverse (k : ℕ) : ℕ := read inverseData k

private def rankData : Array ℕ := #[0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4,
  4, 4, 4, 4, 4, 5, 5, 6, 6, 6, 6, 7,
  7, 8, 8, 8, 8, 9, 9, 10, 10, 10, 10, 11,
  11, 12, 12, 12, 12, 13, 13, 14, 14, 14, 14, 15,
  15, 16, 16, 16, 16, 17, 17, 18, 18, 18, 18, 19,
  19, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 22,
  22, 23, 23, 23, 23, 24]
private def rank (k : ℕ) : ℕ := read rankData k

private def weightData : Array ℕ := #[64, 0, 0, 0, 0, 64, 64, 128, 128, 128, 128, 192,
  192, 192, 192, 192, 192, 225, 225, 276, 276, 276, 276, 250,
  250, 299, 299, 299, 299, 302, 302, 280, 280, 280, 280, 306,
  306, 339, 339, 339, 339, 306, 306, 280, 280, 280, 280, 298,
  298, 296, 296, 296, 296, 285, 285, 276, 276, 276, 276, 245,
  245, 263, 263, 263, 263, 263, 263, 209, 209, 209, 209, 192,
  192, 128, 128, 128, 128, 64]
private def weight (k : ℕ) : ℕ := read weightData k

private def centerData : Array ℕ := #[0, 0, 0, 0, 0, 10, 24, 52, 97, 176, 272, 420,
  613, 868, 1192, 1596, 2112, 2732, 3480, 4376, 5432, 6668, 1, 1,
  1]
private def center (k : ℕ) : ℕ := read centerData k

private def upperData : Array ℕ := #[0, 1048576, 573341, 402757, 313492, 258119, 220220, 192552, 171411, 154699, 141135, 129892,
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
  8493, 8464, 8435, 8406, 8378, 8349, 8321, 8293, 8265, 8238, 8210, 8183,
  8156, 8129, 8103, 8076, 8050, 8024, 7998, 7972, 7947, 7922, 7896, 7871,
  7846, 7822, 7797, 7773, 7749, 7725, 7701, 7677, 7654, 7630, 7607, 7584,
  7561, 7538, 7516, 7493, 7471, 7448, 7426, 7404, 7383, 7361, 7340, 7318,
  7297, 7276, 7255, 7234, 7213, 7193, 7172, 7152, 7132, 7111, 7091, 7072,
  7052, 7032, 7013, 6993, 6974, 6955, 6936, 6917, 6898, 6879, 6861, 6842,
  6824, 6806, 6787, 6769, 6751, 6733, 6716, 6698, 6680, 6663, 6646, 6628,
  6611, 6594, 6577, 6560, 6543, 6527, 6510, 6493, 6477, 6461, 6444, 6428,
  6412, 6396, 6380, 6364, 6349]
private def upper (k : ℕ) : ℕ := read upperData k

private def r5p2 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2,
  0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 2]
private def r5p4 : Array ℕ := #[0, 7, 0, 0, 0, 0, 0, 4, 0, 0, 0, 12,
  0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 24,
  0, 10, 0, 0, 0, 4, 0, 12, 0, 0, 0, 4,
  0, 12, 0, 0, 0, 0, 0, 18, 0, 0, 0, 12,
  0, 10, 0, 0, 0, 24, 0, 7, 0, 0, 0, 4,
  0, 20, 0, 0, 0, 0, 0, 16, 0, 0, 0, 28,
  0, 16, 0, 0, 0, 4]
private def r6p2 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2,
  0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2,
  0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0,
  0, 2, 0, 0, 0, 2, 0, 5, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 2]
private def r6p4 : Array ℕ := #[0, 13, 0, 0, 0, 12, 0, 4, 0, 0, 0, 12,
  0, 0, 0, 0, 0, 8, 0, 4, 0, 0, 0, 40,
  0, 22, 0, 0, 0, 40, 0, 24, 0, 0, 0, 8,
  0, 24, 0, 0, 0, 12, 0, 44, 0, 0, 0, 12,
  0, 22, 0, 0, 0, 40, 0, 13, 0, 0, 0, 44,
  0, 63, 0, 0, 0, 0, 0, 40, 0, 0, 0, 44,
  0, 40, 0, 0, 0, 40]
private def r7p2 : Array ℕ := #[0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2,
  0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2,
  0, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2,
  0, 2, 0, 0, 0, 2, 0, 5, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 2]
private def r7p4 : Array ℕ := #[0, 43, 0, 0, 0, 36, 0, 52, 0, 0, 0, 64,
  0, 0, 0, 0, 0, 44, 0, 40, 0, 0, 0, 52,
  0, 46, 0, 0, 0, 52, 0, 72, 0, 0, 0, 44,
  0, 40, 0, 0, 0, 64, 0, 62, 0, 0, 0, 36,
  0, 52, 0, 0, 0, 64, 0, 66, 0, 0, 0, 60,
  0, 67, 0, 0, 0, 0, 0, 48, 0, 0, 0, 60,
  0, 68, 0, 0, 0, 64]
private def r8p2 : Array ℕ := #[0, 3, 0, 0, 0, 2, 0, 4, 0, 0, 0, 2,
  0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 4,
  0, 2, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4,
  0, 2, 0, 0, 0, 2, 0, 5, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 2]
private def r8p4 : Array ℕ := #[0, 80, 0, 0, 0, 64, 0, 104, 0, 0, 0, 124,
  0, 0, 0, 0, 0, 92, 0, 92, 0, 0, 0, 76,
  0, 76, 0, 0, 0, 68, 0, 136, 0, 0, 0, 120,
  0, 76, 0, 0, 0, 128, 0, 92, 0, 0, 0, 80,
  0, 112, 0, 0, 0, 132, 0, 144, 0, 0, 0, 96,
  0, 97, 0, 0, 0, 0, 0, 72, 0, 0, 0, 108,
  0, 120, 0, 0, 0, 112]
private def r9p2 : Array ℕ := #[0, 3, 0, 0, 0, 4, 0, 6, 0, 0, 0, 2,
  0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 2,
  0, 3, 0, 0, 0, 2, 0, 2, 0, 0, 0, 4,
  0, 2, 0, 0, 0, 4, 0, 3, 0, 0, 0, 6,
  0, 2, 0, 0, 0, 2, 0, 5, 0, 0, 0, 0,
  0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 2]
private def r9p4 : Array ℕ := #[0, 170, 0, 0, 0, 160, 0, 188, 0, 0, 0, 200,
  0, 0, 0, 0, 0, 212, 0, 176, 0, 0, 0, 140,
  0, 184, 0, 0, 0, 128, 0, 176, 0, 0, 0, 204,
  0, 144, 0, 0, 0, 180, 0, 126, 0, 0, 0, 164,
  0, 202, 0, 0, 0, 180, 0, 211, 0, 0, 0, 148,
  0, 139, 0, 0, 0, 0, 0, 160, 0, 0, 0, 172,
  0, 180, 0, 0, 0, 152]
private def r10p2 : Array ℕ := #[0, 3, 0, 0, 0, 4, 0, 6, 0, 0, 0, 4,
  0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 2,
  0, 4, 0, 0, 0, 4, 0, 2, 0, 0, 0, 4,
  0, 2, 0, 0, 0, 6, 0, 5, 0, 0, 0, 6,
  0, 2, 0, 0, 0, 2, 0, 5, 0, 0, 0, 2,
  0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0,
  0, 2, 0, 0, 0, 4]
private def r10p4 : Array ℕ := #[0, 265, 0, 0, 0, 272, 0, 260, 0, 0, 0, 276,
  0, 0, 0, 0, 0, 284, 0, 272, 0, 0, 0, 252,
  0, 254, 0, 0, 0, 224, 0, 264, 0, 0, 0, 288,
  0, 288, 0, 0, 0, 256, 0, 262, 0, 0, 0, 292,
  0, 316, 0, 0, 0, 296, 0, 307, 0, 0, 0, 268,
  0, 257, 0, 0, 0, 0, 0, 268, 0, 0, 0, 296,
  0, 268, 0, 0, 0, 276]
private def r11p2 : Array ℕ := #[0, 5, 0, 0, 0, 4, 0, 6, 0, 0, 0, 6,
  0, 0, 0, 0, 0, 4, 0, 6, 0, 0, 0, 2,
  0, 6, 0, 0, 0, 4, 0, 2, 0, 0, 0, 4,
  0, 2, 0, 0, 0, 8, 0, 5, 0, 0, 0, 6,
  0, 4, 0, 0, 0, 2, 0, 6, 0, 0, 0, 2,
  0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2,
  0, 4, 0, 0, 0, 4]
private def r11p4 : Array ℕ := #[0, 385, 0, 0, 0, 420, 0, 408, 0, 0, 0, 456,
  0, 0, 0, 0, 0, 396, 0, 420, 0, 0, 0, 372,
  0, 392, 0, 0, 0, 368, 0, 424, 0, 0, 0, 408,
  0, 400, 0, 0, 0, 436, 0, 430, 0, 0, 0, 412,
  0, 464, 0, 0, 0, 440, 0, 461, 0, 0, 0, 412,
  0, 436, 0, 0, 0, 0, 0, 376, 0, 0, 0, 424,
  0, 412, 0, 0, 0, 448]
private def r12p2 : Array ℕ := #[0, 7, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6,
  0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 2,
  0, 8, 0, 0, 0, 6, 0, 2, 0, 0, 0, 4,
  0, 2, 0, 0, 0, 8, 0, 6, 0, 0, 0, 8,
  0, 4, 0, 0, 0, 2, 0, 8, 0, 0, 0, 4,
  0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4,
  0, 4, 0, 0, 0, 4]
private def r12p4 : Array ℕ := #[0, 613, 0, 0, 0, 636, 0, 588, 0, 0, 0, 684,
  0, 0, 0, 0, 0, 588, 0, 636, 0, 0, 0, 556,
  0, 648, 0, 0, 0, 556, 0, 580, 0, 0, 0, 624,
  0, 580, 0, 0, 0, 640, 0, 596, 0, 0, 0, 640,
  0, 664, 0, 0, 0, 572, 0, 664, 0, 0, 0, 584,
  0, 632, 0, 0, 0, 0, 0, 536, 0, 0, 0, 632,
  0, 584, 0, 0, 0, 608]
private def r13p2 : Array ℕ := #[0, 7, 0, 0, 0, 6, 0, 8, 0, 0, 0, 8,
  0, 0, 0, 0, 0, 6, 0, 8, 0, 0, 0, 4,
  0, 8, 0, 0, 0, 6, 0, 4, 0, 0, 0, 6,
  0, 2, 0, 0, 0, 8, 0, 7, 0, 0, 0, 8,
  0, 6, 0, 0, 0, 4, 0, 8, 0, 0, 0, 4,
  0, 6, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4,
  0, 6, 0, 0, 0, 6]
private def r13p4 : Array ℕ := #[0, 833, 0, 0, 0, 868, 0, 856, 0, 0, 0, 904,
  0, 0, 0, 0, 0, 844, 0, 868, 0, 0, 0, 820,
  0, 840, 0, 0, 0, 816, 0, 868, 0, 0, 0, 856,
  0, 844, 0, 0, 0, 880, 0, 878, 0, 0, 0, 856,
  0, 912, 0, 0, 0, 888, 0, 909, 0, 0, 0, 860,
  0, 884, 0, 0, 0, 0, 0, 824, 0, 0, 0, 872,
  0, 860, 0, 0, 0, 896]
private def r14p2 : Array ℕ := #[0, 7, 0, 0, 0, 8, 0, 10, 0, 0, 0, 8,
  0, 0, 0, 0, 0, 6, 0, 8, 0, 0, 0, 6,
  0, 8, 0, 0, 0, 8, 0, 6, 0, 0, 0, 6,
  0, 4, 0, 0, 0, 8, 0, 7, 0, 0, 0, 10,
  0, 6, 0, 0, 0, 6, 0, 9, 0, 0, 0, 6,
  0, 8, 0, 0, 0, 0, 0, 6, 0, 0, 0, 4,
  0, 6, 0, 0, 0, 8]
private def r14p4 : Array ℕ := #[0, 1185, 0, 0, 0, 1192, 0, 1168, 0, 0, 0, 1196,
  0, 0, 0, 0, 0, 1204, 0, 1192, 0, 0, 0, 1160,
  0, 1170, 0, 0, 0, 1144, 0, 1180, 0, 0, 0, 1204,
  0, 1204, 0, 0, 0, 1172, 0, 1178, 0, 0, 0, 1208,
  0, 1236, 0, 0, 0, 1212, 0, 1215, 0, 0, 0, 1188,
  0, 1177, 0, 0, 0, 0, 0, 1188, 0, 0, 0, 1204,
  0, 1188, 0, 0, 0, 1196]
private def r15p2 : Array ℕ := #[0, 9, 0, 0, 0, 10, 0, 12, 0, 0, 0, 8,
  0, 0, 0, 0, 0, 8, 0, 10, 0, 0, 0, 8,
  0, 9, 0, 0, 0, 8, 0, 6, 0, 0, 0, 8,
  0, 6, 0, 0, 0, 8, 0, 7, 0, 0, 0, 10,
  0, 8, 0, 0, 0, 8, 0, 11, 0, 0, 0, 6,
  0, 8, 0, 0, 0, 0, 0, 8, 0, 0, 0, 6,
  0, 6, 0, 0, 0, 8]
private def r15p4 : Array ℕ := #[0, 1610, 0, 0, 0, 1596, 0, 1604, 0, 0, 0, 1616,
  0, 0, 0, 0, 0, 1640, 0, 1616, 0, 0, 0, 1568,
  0, 1596, 0, 0, 0, 1568, 0, 1608, 0, 0, 0, 1640,
  0, 1580, 0, 0, 0, 1616, 0, 1562, 0, 0, 0, 1596,
  0, 1642, 0, 0, 0, 1592, 0, 1639, 0, 0, 0, 1588,
  0, 1567, 0, 0, 0, 0, 0, 1576, 0, 0, 0, 1588,
  0, 1616, 0, 0, 0, 1592]
private def r16p2 : Array ℕ := #[0, 11, 0, 0, 0, 10, 0, 12, 0, 0, 0, 10,
  0, 0, 0, 0, 0, 10, 0, 12, 0, 0, 0, 8,
  0, 9, 0, 0, 0, 8, 0, 8, 0, 0, 0, 10,
  0, 8, 0, 0, 0, 10, 0, 7, 0, 0, 0, 10,
  0, 8, 0, 0, 0, 10, 0, 13, 0, 0, 0, 8,
  0, 9, 0, 0, 0, 0, 0, 8, 0, 0, 0, 8,
  0, 8, 0, 0, 0, 10]
private def r16p4 : Array ℕ := #[0, 2100, 0, 0, 0, 2080, 0, 2112, 0, 0, 0, 2132,
  0, 0, 0, 0, 0, 2112, 0, 2112, 0, 0, 0, 2084,
  0, 2076, 0, 0, 0, 2084, 0, 2136, 0, 0, 0, 2112,
  0, 2080, 0, 0, 0, 2132, 0, 2084, 0, 0, 0, 2080,
  0, 2128, 0, 0, 0, 2132, 0, 2152, 0, 0, 0, 2116,
  0, 2117, 0, 0, 0, 0, 0, 2080, 0, 0, 0, 2116,
  0, 2136, 0, 0, 0, 2132]
private def r17p2 : Array ℕ := #[0, 12, 0, 0, 0, 12, 0, 12, 0, 0, 0, 12,
  0, 0, 0, 0, 0, 12, 0, 12, 0, 0, 0, 10,
  0, 9, 0, 0, 0, 8, 0, 10, 0, 0, 0, 10,
  0, 10, 0, 0, 0, 10, 0, 9, 0, 0, 0, 10,
  0, 10, 0, 0, 0, 10, 0, 15, 0, 0, 0, 10,
  0, 11, 0, 0, 0, 0, 0, 10, 0, 0, 0, 10,
  0, 10, 0, 0, 0, 12]
private def r17p4 : Array ℕ := #[0, 2739, 0, 0, 0, 2716, 0, 2724, 0, 0, 0, 2736,
  0, 0, 0, 0, 0, 2740, 0, 2724, 0, 0, 0, 2748,
  0, 2702, 0, 0, 0, 2708, 0, 2748, 0, 0, 0, 2700,
  0, 2720, 0, 0, 0, 2744, 0, 2718, 0, 0, 0, 2712,
  0, 2708, 0, 0, 0, 2720, 0, 2762, 0, 0, 0, 2744,
  0, 2763, 0, 0, 0, 0, 0, 2720, 0, 0, 0, 2732,
  0, 2748, 0, 0, 0, 2760]
private def r18p2 : Array ℕ := #[0, 12, 0, 0, 0, 12, 0, 14, 0, 0, 0, 14,
  0, 0, 0, 0, 0, 14, 0, 12, 0, 0, 0, 10,
  0, 11, 0, 0, 0, 10, 0, 12, 0, 0, 0, 12,
  0, 10, 0, 0, 0, 12, 0, 11, 0, 0, 0, 10,
  0, 12, 0, 0, 0, 12, 0, 15, 0, 0, 0, 12,
  0, 12, 0, 0, 0, 0, 0, 12, 0, 0, 0, 12,
  0, 12, 0, 0, 0, 14]
private def r18p4 : Array ℕ := #[0, 3477, 0, 0, 0, 3464, 0, 3460, 0, 0, 0, 3468,
  0, 0, 0, 0, 0, 3452, 0, 3460, 0, 0, 0, 3504,
  0, 3462, 0, 0, 0, 3480, 0, 3484, 0, 0, 0, 3460,
  0, 3488, 0, 0, 0, 3476, 0, 3496, 0, 0, 0, 3472,
  0, 3462, 0, 0, 0, 3480, 0, 3477, 0, 0, 0, 3500,
  0, 3507, 0, 0, 0, 0, 0, 3496, 0, 0, 0, 3500,
  0, 3492, 0, 0, 0, 3504]
private def r19p2 : Array ℕ := #[0, 14, 0, 0, 0, 14, 0, 16, 0, 0, 0, 14,
  0, 0, 0, 0, 0, 14, 0, 12, 0, 0, 0, 12,
  0, 13, 0, 0, 0, 12, 0, 14, 0, 0, 0, 14,
  0, 12, 0, 0, 0, 14, 0, 13, 0, 0, 0, 12,
  0, 13, 0, 0, 0, 12, 0, 15, 0, 0, 0, 12,
  0, 14, 0, 0, 0, 0, 0, 14, 0, 0, 0, 14,
  0, 14, 0, 0, 0, 16]
private def r19p4 : Array ℕ := #[0, 4387, 0, 0, 0, 4376, 0, 4376, 0, 0, 0, 4372,
  0, 0, 0, 0, 0, 4364, 0, 4360, 0, 0, 0, 4380,
  0, 4354, 0, 0, 0, 4372, 0, 4364, 0, 0, 0, 4372,
  0, 4380, 0, 0, 0, 4368, 0, 4386, 0, 0, 0, 4364,
  0, 4378, 0, 0, 0, 4368, 0, 4363, 0, 0, 0, 4360,
  0, 4380, 0, 0, 0, 0, 0, 4376, 0, 0, 0, 4400,
  0, 4392, 0, 0, 0, 4384]
private def r20p2 : Array ℕ := #[0, 16, 0, 0, 0, 16, 0, 16, 0, 0, 0, 16,
  0, 0, 0, 0, 0, 14, 0, 14, 0, 0, 0, 14,
  0, 15, 0, 0, 0, 14, 0, 14, 0, 0, 0, 16,
  0, 14, 0, 0, 0, 14, 0, 15, 0, 0, 0, 14,
  0, 15, 0, 0, 0, 14, 0, 16, 0, 0, 0, 14,
  0, 14, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16,
  0, 16, 0, 0, 0, 18]
private def r20p4 : Array ℕ := #[0, 5443, 0, 0, 0, 5448, 0, 5432, 0, 0, 0, 5444,
  0, 0, 0, 0, 0, 5408, 0, 5428, 0, 0, 0, 5440,
  0, 5420, 0, 0, 0, 5420, 0, 5412, 0, 0, 0, 5444,
  0, 5416, 0, 0, 0, 5416, 0, 5452, 0, 0, 0, 5412,
  0, 5420, 0, 0, 0, 5428, 0, 5435, 0, 0, 0, 5428,
  0, 5411, 0, 0, 0, 0, 0, 5444, 0, 0, 0, 5432,
  0, 5448, 0, 0, 0, 5440]
private def r21p2 : Array ℕ := #[0, 18, 0, 0, 0, 18, 0, 18, 0, 0, 0, 16,
  0, 0, 0, 0, 0, 16, 0, 16, 0, 0, 0, 16,
  0, 17, 0, 0, 0, 16, 0, 16, 0, 0, 0, 18,
  0, 16, 0, 0, 0, 16, 0, 16, 0, 0, 0, 16,
  0, 17, 0, 0, 0, 16, 0, 16, 0, 0, 0, 16,
  0, 16, 0, 0, 0, 0, 0, 16, 0, 0, 0, 18,
  0, 18, 0, 0, 0, 18]
private def r21p4 : Array ℕ := #[0, 6665, 0, 0, 0, 6672, 0, 6672, 0, 0, 0, 6668,
  0, 0, 0, 0, 0, 6660, 0, 6668, 0, 0, 0, 6656,
  0, 6668, 0, 0, 0, 6668, 0, 6664, 0, 0, 0, 6680,
  0, 6656, 0, 0, 0, 6656, 0, 6680, 0, 0, 0, 6664,
  0, 6668, 0, 0, 0, 6668, 0, 6662, 0, 0, 0, 6668,
  0, 6657, 0, 0, 0, 0, 0, 6668, 0, 0, 0, 6672,
  0, 6672, 0, 0, 0, 6668]

private def rowData : Array (List (Array ℕ)) := #[
  [],
  [],
  [],
  [],
  [],
  [r5p2, r5p4],
  [r6p2, r6p4],
  [r7p2, r7p4],
  [r8p2, r8p4],
  [r9p2, r9p4],
  [r10p2, r10p4],
  [r11p2, r11p4],
  [r12p2, r12p4],
  [r13p2, r13p4],
  [r14p2, r14p4],
  [r15p2, r15p4],
  [r16p2, r16p4],
  [r17p2, r17p4],
  [r18p2, r18p4],
  [r19p2, r19p4],
  [r20p2, r20p4],
  [r21p2, r21p4],
  [],
  [],
  []]
private def rows (r : ℕ) : List (Array ℕ) := (rowData[rank r]?).getD []

private def validAt (r : ℕ) : Prop :=
  r ≠ 0 → Rows 78 U inverse (entry r) (rows r) ∧
   64^(2^(rows r).length) * deviation U (lastRow (entry r) (rows r)) (center (rank r))
     ≤ (weight r)^(2^(rows r).length)

private theorem block0 : ∀ k : Fin 3, validAt (k.val+0) := by
  unfold validAt
  decide +kernel

private theorem block3 : ∀ k : Fin 3, validAt (k.val+3) := by
  unfold validAt
  decide +kernel

private theorem block6 : ∀ k : Fin 3, validAt (k.val+6) := by
  unfold validAt
  decide +kernel

private theorem block9 : ∀ k : Fin 3, validAt (k.val+9) := by
  unfold validAt
  decide +kernel

private theorem block12 : ∀ k : Fin 3, validAt (k.val+12) := by
  unfold validAt
  decide +kernel

private theorem block15 : ∀ k : Fin 3, validAt (k.val+15) := by
  unfold validAt
  decide +kernel

private theorem block18 : ∀ k : Fin 3, validAt (k.val+18) := by
  unfold validAt
  decide +kernel

private theorem block21 : ∀ k : Fin 3, validAt (k.val+21) := by
  unfold validAt
  decide +kernel

private theorem block24 : ∀ k : Fin 3, validAt (k.val+24) := by
  unfold validAt
  decide +kernel

private theorem block27 : ∀ k : Fin 3, validAt (k.val+27) := by
  unfold validAt
  decide +kernel

private theorem block30 : ∀ k : Fin 3, validAt (k.val+30) := by
  unfold validAt
  decide +kernel

private theorem block33 : ∀ k : Fin 3, validAt (k.val+33) := by
  unfold validAt
  decide +kernel

private theorem block36 : ∀ k : Fin 3, validAt (k.val+36) := by
  unfold validAt
  decide +kernel

private theorem block39 : ∀ k : Fin 3, validAt (k.val+39) := by
  unfold validAt
  decide +kernel

private theorem block42 : ∀ k : Fin 3, validAt (k.val+42) := by
  unfold validAt
  decide +kernel

private theorem block45 : ∀ k : Fin 3, validAt (k.val+45) := by
  unfold validAt
  decide +kernel

private theorem block48 : ∀ k : Fin 3, validAt (k.val+48) := by
  unfold validAt
  decide +kernel

private theorem block51 : ∀ k : Fin 3, validAt (k.val+51) := by
  unfold validAt
  decide +kernel

private theorem block54 : ∀ k : Fin 3, validAt (k.val+54) := by
  unfold validAt
  decide +kernel

private theorem block57 : ∀ k : Fin 3, validAt (k.val+57) := by
  unfold validAt
  decide +kernel

private theorem block60 : ∀ k : Fin 3, validAt (k.val+60) := by
  unfold validAt
  decide +kernel

private theorem block63 : ∀ k : Fin 3, validAt (k.val+63) := by
  unfold validAt
  decide +kernel

private theorem block66 : ∀ k : Fin 3, validAt (k.val+66) := by
  unfold validAt
  decide +kernel

private theorem block69 : ∀ k : Fin 3, validAt (k.val+69) := by
  unfold validAt
  decide +kernel

private theorem block72 : ∀ k : Fin 3, validAt (k.val+72) := by
  unfold validAt
  decide +kernel

private theorem block75 : ∀ k : Fin 3, validAt (k.val+75) := by
  unfold validAt
  decide +kernel

private theorem profile : Profile 78 64 weight := by
  refine ⟨U,inverse,rows,(fun r => center (rank r)),?_,?_,by decide,?_⟩
  · decide +kernel
  · unfold Permutes
    decide +kernel
  · rintro ⟨r,hr⟩
    change validAt r
    by_cases h0 : r < 3
    · exact block0 ⟨r,h0⟩
    by_cases h3 : r < 6
    · have h := block3 ⟨r-3,by omega⟩
      simpa only [show r-3+3=r by omega] using h
    by_cases h6 : r < 9
    · have h := block6 ⟨r-6,by omega⟩
      simpa only [show r-6+6=r by omega] using h
    by_cases h9 : r < 12
    · have h := block9 ⟨r-9,by omega⟩
      simpa only [show r-9+9=r by omega] using h
    by_cases h12 : r < 15
    · have h := block12 ⟨r-12,by omega⟩
      simpa only [show r-12+12=r by omega] using h
    by_cases h15 : r < 18
    · have h := block15 ⟨r-15,by omega⟩
      simpa only [show r-15+15=r by omega] using h
    by_cases h18 : r < 21
    · have h := block18 ⟨r-18,by omega⟩
      simpa only [show r-18+18=r by omega] using h
    by_cases h21 : r < 24
    · have h := block21 ⟨r-21,by omega⟩
      simpa only [show r-21+21=r by omega] using h
    by_cases h24 : r < 27
    · have h := block24 ⟨r-24,by omega⟩
      simpa only [show r-24+24=r by omega] using h
    by_cases h27 : r < 30
    · have h := block27 ⟨r-27,by omega⟩
      simpa only [show r-27+27=r by omega] using h
    by_cases h30 : r < 33
    · have h := block30 ⟨r-30,by omega⟩
      simpa only [show r-30+30=r by omega] using h
    by_cases h33 : r < 36
    · have h := block33 ⟨r-33,by omega⟩
      simpa only [show r-33+33=r by omega] using h
    by_cases h36 : r < 39
    · have h := block36 ⟨r-36,by omega⟩
      simpa only [show r-36+36=r by omega] using h
    by_cases h39 : r < 42
    · have h := block39 ⟨r-39,by omega⟩
      simpa only [show r-39+39=r by omega] using h
    by_cases h42 : r < 45
    · have h := block42 ⟨r-42,by omega⟩
      simpa only [show r-42+42=r by omega] using h
    by_cases h45 : r < 48
    · have h := block45 ⟨r-45,by omega⟩
      simpa only [show r-45+45=r by omega] using h
    by_cases h48 : r < 51
    · have h := block48 ⟨r-48,by omega⟩
      simpa only [show r-48+48=r by omega] using h
    by_cases h51 : r < 54
    · have h := block51 ⟨r-51,by omega⟩
      simpa only [show r-51+51=r by omega] using h
    by_cases h54 : r < 57
    · have h := block54 ⟨r-54,by omega⟩
      simpa only [show r-54+54=r by omega] using h
    by_cases h57 : r < 60
    · have h := block57 ⟨r-57,by omega⟩
      simpa only [show r-57+57=r by omega] using h
    by_cases h60 : r < 63
    · have h := block60 ⟨r-60,by omega⟩
      simpa only [show r-60+60=r by omega] using h
    by_cases h63 : r < 66
    · have h := block63 ⟨r-63,by omega⟩
      simpa only [show r-63+63=r by omega] using h
    by_cases h66 : r < 69
    · have h := block66 ⟨r-66,by omega⟩
      simpa only [show r-66+66=r by omega] using h
    by_cases h69 : r < 72
    · have h := block69 ⟨r-69,by omega⟩
      simpa only [show r-69+69=r by omega] using h
    by_cases h72 : r < 75
    · have h := block72 ⟨r-72,by omega⟩
      simpa only [show r-72+72=r by omega] using h
    by_cases h75 : r < 78
    · have h := block75 ⟨r-75,by omega⟩
      simpa only [show r-75+75=r by omega] using h
    omega

/-- A multiplicative convolution certificate gives the closed height-one
rectangle for every conductor dividing 78. -/
theorem solution (d : ℕ) (hd : d ∣ 78) (a b H : ℝ) (ha : (27/31:ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ 7/8) (hH : 0 ≤ H) (hhi : H ≤ 1) : Covers d a b H := by
  refine ⟨78,351,339,1048576,64,27,31,153,100,weight,upper,by decide,hd,by decide,
    by decide,by decide,by decide,by decide,ha,?_,profile,?_,?_,?_⟩
  · have re := mul_self_le_mul_self (show 0 ≤ b by linarith) hb
    have im := mul_self_le_mul_self hH hhi
    nlinarith
  · decide +kernel
  · unfold GRH.DirichletPrefix.Table
    decide +kernel
  · decide +kernel
