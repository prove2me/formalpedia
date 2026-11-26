-- Prove2me | solution 1 for GRH.weighted_energy_rectangle_at_one_hundred_fourteen
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:07:38.456158+00:00
-- url     : https://prove2.me/submissions/da0912c7-b8b7-4949-bf0f-747c0e8a95e5

import Definitions.Def_GRH_WeightedEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open GRH.WeightedEnergy
open GRH.CharacterMoment (units entry read Rows Permutes)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def U : Finset ℕ := ⟨([1, 5, 7, 11, 13, 17, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55, 59, 61, 65, 67, 71, 73, 77, 79, 83, 85, 89, 91, 97, 101, 103, 107, 109, 113] : List ℕ), by decide⟩
private def I : Finset ℕ := ⟨([5, 7, 11, 13, 17, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55, 59, 61, 65, 67, 71, 73, 77, 79, 83, 85, 89, 91, 97, 101, 103, 107, 109, 113] : List ℕ), by decide⟩

private def inverseData : Array ℕ := #[0, 1, 0, 0, 0, 23, 0, 49, 0, 0, 0, 83,
  0, 79, 0, 0, 0, 47, 0, 0, 0, 0, 0, 5,
  0, 73, 0, 0, 0, 59, 0, 103, 0, 0, 0, 101,
  0, 37, 0, 0, 0, 89, 0, 61, 0, 0, 0, 17,
  0, 7, 0, 0, 0, 71, 0, 85, 0, 0, 0, 29,
  0, 43, 0, 0, 0, 107, 0, 97, 0, 0, 0, 53,
  0, 25, 0, 0, 0, 77, 0, 13, 0, 0, 0, 11,
  0, 55, 0, 0, 0, 41, 0, 109, 0, 0, 0, 0,
  0, 67, 0, 0, 0, 35, 0, 31, 0, 0, 0, 65,
  0, 91, 0, 0, 0, 113]
private def inverse (i : ℕ) : ℕ := read inverseData i

private def keyData : Array ℕ := #[0, 1, 1, 1, 1, 5, 5, 7, 7, 7, 7, 11,
  11, 13, 13, 13, 13, 17, 17, 17, 17, 17, 17, 23,
  23, 25, 25, 25, 25, 29, 29, 31, 31, 31, 31, 35,
  35, 37, 37, 37, 37, 41, 41, 43, 43, 43, 43, 47,
  47, 49, 49, 49, 49, 53, 53, 55, 55, 55, 55, 59,
  59, 61, 61, 61, 61, 65, 65, 67, 67, 67, 67, 71,
  71, 73, 73, 73, 73, 77, 77, 79, 79, 79, 79, 83,
  83, 85, 85, 85, 85, 89, 89, 91, 91, 91, 91, 91,
  91, 97, 97, 97, 97, 101, 101, 103, 103, 103, 103, 107,
  107, 109, 109, 109, 109, 113]
private def key (i : ℕ) : ℕ := read keyData i

private def weightData : Array ℕ := #[207, 791263, 0, 0, 0, 65957, 0, 63412, 0, 0, 0, 17951,
  0, 24105, 0, 0, 0, 21580, 0, 0, 0, 0, 0, 5108,
  0, 8329, 0, 0, 0, 3452, 0, 5875, 0, 0, 0, 2525,
  0, 4421, 0, 0, 0, 1950, 0, 3484, 0, 0, 0, 1565,
  0, 2840, 0, 0, 0, 1295, 0, 2379, 0, 0, 0, 1096,
  0, 2032, 0, 0, 0, 945, 0, 1767, 0, 0, 0, 826,
  0, 1558, 0, 0, 0, 733, 0, 1387, 0, 0, 0, 654,
  0, 1232, 0, 0, 0, 584, 0, 1647, 0, 0, 0, 0,
  0, 1020, 0, 0, 0, 487, 0, 936, 0, 0, 0, 449,
  0, 864, 0, 0, 0, 210]
private def weight (i : ℕ) : ℕ := read weightData i

private def scaleData : Array ℕ := #[0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3,
  0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4,
  0, 5, 0, 0, 0, 5, 0, 5, 0, 0, 0, 5,
  0, 5, 0, 0, 0, 6, 0, 5, 0, 0, 0, 6,
  0, 5, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6,
  0, 5, 0, 0, 0, 6, 0, 5, 0, 0, 0, 6,
  0, 5, 0, 0, 0, 5, 0, 5, 0, 0, 0, 5,
  0, 5, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0,
  0, 4, 0, 0, 0, 4, 0, 4, 0, 0, 0, 3,
  0, 2, 0, 0, 0, 1]
private def scale (i : ℕ) : ℕ := read scaleData i

private def dualData : Array ℕ := #[0, 0, 0, 0, 0, 60, 0, 30, 0, 0, 0, 20,
  0, 15, 0, 0, 0, 15, 0, 0, 0, 0, 0, 15,
  0, 12, 0, 0, 0, 12, 0, 12, 0, 0, 0, 12,
  0, 12, 0, 0, 0, 10, 0, 12, 0, 0, 0, 10,
  0, 12, 0, 0, 0, 10, 0, 10, 0, 0, 0, 10,
  0, 12, 0, 0, 0, 10, 0, 12, 0, 0, 0, 10,
  0, 12, 0, 0, 0, 12, 0, 12, 0, 0, 0, 12,
  0, 12, 0, 0, 0, 15, 0, 15, 0, 0, 0, 0,
  0, 15, 0, 0, 0, 15, 0, 15, 0, 0, 0, 20,
  0, 30, 0, 0, 0, 60]
private def dual (i : ℕ) : ℕ := read dualData i

private def baseData : Array ℕ := #[0, 23887342, 0, 0, 0, 7238886, 0, 6926035, 0, 0, 0, 8138203,
  0, 6007325, 0, 0, 0, 9506060, 0, 0, 0, 0, 0, 7238886,
  0, 7971077, 0, 0, 0, 6291440, 0, 6175950, 0, 0, 0, 7826686,
  0, 7389292, 0, 0, 0, 6961773, 0, 6324125, 0, 0, 0, 9506060,
  0, 6926035, 0, 0, 0, 9026448, 0, 7520810, 0, 0, 0, 6291440,
  0, 6324125, 0, 0, 0, 6889302, 0, 7432075, 0, 0, 0, 9026448,
  0, 7971077, 0, 0, 0, 5227648, 0, 6007325, 0, 0, 0, 8138203,
  0, 7520810, 0, 0, 0, 6961773, 0, 5996930, 0, 0, 0, 0,
  0, 7432075, 0, 0, 0, 7826686, 0, 6175950, 0, 0, 0, 6889302,
  0, 5996930, 0, 0, 0, 4885352]
private def base (i : ℕ) : ℕ := read baseData i

private def u0 : Array ℕ := #[0, 1048576, 573341, 402757, 313492, 258119, 220220, 192552, 171411, 154699, 141135, 129892,
  120412, 112303, 105284, 99144]
private def u1 : Array ℕ := #[93724, 88904, 84586, 80696, 77170, 73959, 71023, 68325, 65839, 63539, 61406, 59420,
  57567, 55834, 54210, 52684]
private def u2 : Array ℕ := #[51247, 49892, 48611, 47399, 46250, 45160, 44123, 43136, 42195, 41297, 40440, 39619,
  38834, 38081, 37359, 36666]
private def u3 : Array ℕ := #[36000, 35359, 34742, 34148, 33576, 33023, 32490, 31975, 31477, 30995, 30529, 30078,
  29641, 29217, 28807, 28408]
private def u4 : Array ℕ := #[28021, 27645, 27280, 26925, 26580, 26244, 25917, 25599, 25289, 24987, 24693, 24406,
  24126, 23853, 23586, 23326]
private def u5 : Array ℕ := #[23072, 22823, 22581, 22344, 22112, 21885, 21663, 21446, 21234, 21026, 20822, 20623,
  20427, 20236, 20048, 19864]
private def u6 : Array ℕ := #[19684, 19507, 19334, 19164, 18997, 18833, 18672, 18514, 18359, 18206, 18057, 17910,
  17765, 17623, 17483, 17346]
private def u7 : Array ℕ := #[17211, 17078, 16948, 16819, 16693, 16569, 16446, 16326, 16207, 16091, 15976, 15863,
  15751, 15641, 15533, 15427]
private def u8 : Array ℕ := #[15322, 15218, 15116, 15015, 14916, 14819, 14722, 14627, 14534, 14441, 14350, 14260,
  14171, 14084, 13997, 13912]
private def u9 : Array ℕ := #[13828, 13745, 13663, 13582, 13502, 13423, 13345, 13268, 13192, 13117, 13042, 12969,
  12897, 12825, 12754, 12684]
private def u10 : Array ℕ := #[12615, 12547, 12480, 12413, 12347, 12282, 12217, 12154, 12091, 12028, 11967, 11906,
  11845, 11786, 11727, 11668]
private def u11 : Array ℕ := #[11610, 11553, 11497, 11441, 11385, 11331, 11276, 11223, 11170, 11117, 11065, 11013,
  10962, 10912, 10862, 10812]
private def u12 : Array ℕ := #[10763, 10715, 10666, 10619, 10572, 10525, 10479, 10433, 10387, 10342, 10298, 10253,
  10210, 10166, 10123, 10081]
private def u13 : Array ℕ := #[10038, 9997, 9955, 9914, 9873, 9833, 9793, 9753, 9714, 9675, 9636, 9598,
  9560, 9522, 9485, 9448]
private def u14 : Array ℕ := #[9411, 9374, 9338, 9303, 9267, 9232, 9197, 9162, 9128, 9094, 9060, 9026,
  8993, 8960, 8927, 8894]
private def u15 : Array ℕ := #[8862, 8830, 8798, 8767, 8735, 8704, 8674, 8643, 8613, 8582, 8553, 8523,
  8493, 8464, 8435, 8406]
private def u16 : Array ℕ := #[8378, 8349, 8321, 8293, 8265, 8238, 8210, 8183, 8156, 8129, 8103, 8076,
  8050, 8024, 7998, 7972]
private def u17 : Array ℕ := #[7947, 7922, 7896, 7871, 7846, 7822, 7797, 7773, 7749, 7725, 7701, 7677,
  7654, 7630, 7607, 7584]
private def u18 : Array ℕ := #[7561, 7538, 7516, 7493, 7471, 7448, 7426, 7404, 7383, 7361, 7340, 7318,
  7297, 7276, 7255, 7234]
private def u19 : Array ℕ := #[7213, 7193, 7172, 7152, 7132, 7111, 7091, 7072, 7052, 7032, 7013, 6993,
  6974, 6955, 6936, 6917]
private def u20 : Array ℕ := #[6898, 6879, 6861, 6842, 6824, 6806, 6787, 6769, 6751, 6733, 6716, 6698,
  6680, 6663, 6646, 6628]
private def u21 : Array ℕ := #[6611, 6594, 6577, 6560, 6543, 6527, 6510, 6493, 6477, 6461, 6444, 6428,
  6412, 6396, 6380, 6364]
private def u22 : Array ℕ := #[6349, 6333, 6317, 6302, 6286, 6271, 6256, 6241, 6226, 6211, 6196, 6181,
  6166, 6151, 6137, 6122]
private def u23 : Array ℕ := #[6108, 6093, 6079, 6064, 6050, 6036, 6022, 6008, 5994, 5980, 5967, 5953,
  5939, 5926, 5912, 5899]
private def u24 : Array ℕ := #[5885, 5872, 5859, 5846, 5832, 5819, 5806, 5793, 5781, 5768, 5755, 5742,
  5730, 5717, 5705, 5692]
private def u25 : Array ℕ := #[5680, 5667, 5655, 5643, 5631, 5619, 5607, 5595, 5583, 5571, 5559, 5547,
  5535, 5524, 5512, 5501]
private def u26 : Array ℕ := #[5489, 5478, 5466, 5455, 5443, 5432, 5421, 5410, 5399, 5388, 5377, 5366,
  5355, 5344, 5333, 5322]
private def u27 : Array ℕ := #[5312, 5301, 5290, 5280, 5269, 5259, 5248, 5238, 5227, 5217, 5207, 5196,
  5186, 5176, 5166, 5156]
private def u28 : Array ℕ := #[5146, 5136, 5126, 5116, 5106, 5096, 5087, 5077, 5067, 5058, 5048, 5038,
  5029, 5019, 5010, 5000]
private def u29 : Array ℕ := #[4991, 4982, 4972, 4963, 4954, 4945, 4936, 4926, 4917, 4908, 4899, 4890,
  4881, 4872, 4864, 4855]
private def u30 : Array ℕ := #[4846, 4837, 4828, 4820, 4811, 4802, 4794, 4785, 4777, 4768, 4760, 4751,
  4743, 4734, 4726, 4718]
private def u31 : Array ℕ := #[4709, 4701, 4693, 4685, 4677, 4668, 4660, 4652, 4644, 4636, 4628, 4620,
  4612, 4605, 4597, 4589]
private def u32 : Array ℕ := #[4581, 4573, 4565, 4558, 4550, 4542, 4535, 4527, 4520, 4512, 4504, 4497,
  4490, 4482, 4475, 4467]
private def u33 : Array ℕ := #[4460, 4453, 4445, 4438, 4431, 4423, 4416, 4409, 4402, 4395, 4388, 4381,
  4373, 4366, 4359, 4352]
private def u34 : Array ℕ := #[4345, 4338, 4332, 4325, 4318, 4311, 4304, 4297, 4291, 4284, 4277, 4270,
  4264, 4257, 4250, 4244]
private def u35 : Array ℕ := #[4237, 4231, 4224, 4217, 4211, 4204, 4198, 4192, 4185, 4179, 4172, 4166,
  4160, 4153, 4147, 4141]
private def u36 : Array ℕ := #[4134, 4128, 4122, 4116, 4110, 4103, 4097, 4091, 4085, 4079, 4073, 4067,
  4061, 4055, 4049, 4043]
private def u37 : Array ℕ := #[4037, 4031, 4025, 4019, 4013, 4007, 4002, 3996, 3990, 3984, 3978, 3973,
  3967, 3961, 3956, 3950]
private def u38 : Array ℕ := #[3944, 3939, 3933, 3927, 3922, 3916, 3911, 3905, 3900, 3894, 3889, 3883,
  3878, 3872, 3867, 3861]
private def u39 : Array ℕ := #[3856, 3851, 3845, 3840, 3835, 3829, 3824, 3819, 3813, 3808, 3803, 3798,
  3793, 3787, 3782, 3777]
private def u40 : Array ℕ := #[3772, 3767, 3762, 3757, 3752, 3746, 3741, 3736, 3731, 3726, 3721, 3716,
  3711, 3706, 3702, 3697]
private def u41 : Array ℕ := #[3692, 3687, 3682, 3677, 3672, 3667, 3663, 3658, 3653, 3648, 3643, 3639,
  3634, 3629, 3624, 3620]
private def u42 : Array ℕ := #[3615, 3610, 3606, 3601, 3596, 3592, 3587, 3583, 3578, 3573, 3569, 3564,
  3560, 3555, 3551, 3546]
private def u43 : Array ℕ := #[3542, 3537, 3533, 3528, 3524, 3519, 3515, 3511, 3506, 3502, 3497, 3493,
  3489, 3484, 3480, 3476]
private def u44 : Array ℕ := #[3472, 3467, 3463, 3459, 3454, 3450, 3446, 3442, 3438, 3433, 3429, 3425,
  3421, 3417, 3412, 3408]
private def u45 : Array ℕ := #[3404, 3400, 3396, 3392, 3388, 3384, 3380, 3376, 3372, 3368, 3364, 3360,
  3356, 3352, 3348, 3344]
private def u46 : Array ℕ := #[3340, 3336, 3332, 3328, 3324, 3320, 3316, 3312, 3308, 3305, 3301, 3297,
  3293, 3289, 3285, 3282]
private def u47 : Array ℕ := #[3278, 3274, 3270, 3266, 3263, 3259, 3255, 3251, 3248, 3244, 3240, 3237,
  3233, 3229, 3225, 3222]
private def u48 : Array ℕ := #[3218]
private def upper (n : ℕ) : ℕ :=
  let j := n%16
  match n/16 with
  | 0 => read u0 j
  | 1 => read u1 j
  | 2 => read u2 j
  | 3 => read u3 j
  | 4 => read u4 j
  | 5 => read u5 j
  | 6 => read u6 j
  | 7 => read u7 j
  | 8 => read u8 j
  | 9 => read u9 j
  | 10 => read u10 j
  | 11 => read u11 j
  | 12 => read u12 j
  | 13 => read u13 j
  | 14 => read u14 j
  | 15 => read u15 j
  | 16 => read u16 j
  | 17 => read u17 j
  | 18 => read u18 j
  | 19 => read u19 j
  | 20 => read u20 j
  | 21 => read u21 j
  | 22 => read u22 j
  | 23 => read u23 j
  | 24 => read u24 j
  | 25 => read u25 j
  | 26 => read u26 j
  | 27 => read u27 j
  | 28 => read u28 j
  | 29 => read u29 j
  | 30 => read u30 j
  | 31 => read u31 j
  | 32 => read u32 j
  | 33 => read u33 j
  | 34 => read u34 j
  | 35 => read u35 j
  | 36 => read u36 j
  | 37 => read u37 j
  | 38 => read u38 j
  | 39 => read u39 j
  | 40 => read u40 j
  | 41 => read u41 j
  | 42 => read u42 j
  | 43 => read u43 j
  | 44 => read u44 j
  | 45 => read u45 j
  | 46 => read u46 j
  | 47 => read u47 j
  | 48 => read u48 j
  | _ => 0

private def row0 : Array ℕ := #[0, 2397874001659970, 0, 0, 0, 2087922534431142, 0, 2067293431887134, 0, 0, 0, 2114635838428744,
  0, 2037348852651628, 0, 0, 0, 2149793362138546, 0, 0, 0, 0, 0, 2087922534431142,
  0, 2116137271369369, 0, 0, 0, 2034141164416450, 0, 2046898652415818, 0, 0, 0, 2098538861722588,
  0, 2084829445812668, 0, 0, 0, 2053866830266974, 0, 2053571112196761, 0, 0, 0, 2149793362138546,
  0, 2067293431887134, 0, 0, 0, 2141318582581496, 0, 2086621516035955, 0, 0, 0, 2034141164416450,
  0, 2053571112196761, 0, 0, 0, 2062929271054082, 0, 2087190889925080, 0, 0, 0, 2141318582581496,
  0, 2116137271369369, 0, 0, 0, 2007085956268968, 0, 2037348852651628, 0, 0, 0, 2114635838428744,
  0, 2086621516035955, 0, 0, 0, 2053866830266974, 0, 2022195214701016, 0, 0, 0, 0,
  0, 2087190889925080, 0, 0, 0, 2098538861722588, 0, 2046898652415818, 0, 0, 0, 2062929271054082,
  0, 2022195214701016, 0, 0, 0, 1986449025234284]
private def row1 : Array ℕ := #[0, 156396107836823718883924777210610, 0, 0, 0, 156261948456166198771735527927056, 0, 156229061401590546764402528247522, 0, 0, 0, 156276267549819106256946314155440,
  0, 156210532875448985987683512827080, 0, 0, 0, 156286193936496687402817399309656, 0, 0, 0, 0, 0, 156261948456166198771735527927056,
  0, 156283478623889639364180638645823, 0, 0, 0, 156188414801463166689060885675400, 0, 156213038664322716070471971509144, 0, 0, 0, 156250227443108077172754445339328,
  0, 156240676937187389309391325600832, 0, 0, 0, 156198459128714177027200402817648, 0, 156224336500036823250976513156359, 0, 0, 0, 156286193936496687402817399309656,
  0, 156229061401590546764402528247522, 0, 0, 0, 156285198133758848064227851537176, 0, 156245477235003184406000705528479, 0, 0, 0, 156188414801463166689060885675400,
  0, 156224336500036823250976513156359, 0, 0, 0, 156221063076813660400063991350376, 0, 156241652189534968506143044905400, 0, 0, 0, 156285198133758848064227851537176,
  0, 156283478623889639364180638645823, 0, 0, 0, 156183201464652145621926567472720, 0, 156210532875448985987683512827080, 0, 0, 0, 156276267549819106256946314155440,
  0, 156245477235003184406000705528479, 0, 0, 0, 156198459128714177027200402817648, 0, 156173576852077989549321862979080, 0, 0, 0, 0,
  0, 156241652189534968506143044905400, 0, 0, 0, 156250227443108077172754445339328, 0, 156213038664322716070471971509144, 0, 0, 0, 156221063076813660400063991350376,
  0, 156173576852077989549321862979080, 0, 0, 0, 156158948968900234582425075053840]
private def row2 : Array ℕ := #[0, 878767824212863266961425045546208269692099040769795442150354573490, 0, 0, 0, 878767784440068870266239575742902326033542019911514545186187818352, 0, 878767751657409990664821287986724451285908802110591454141080209842, 0, 0, 0, 878767786218062549366361367279811129756779432375218708246214477088,
  0, 878767743643940032191492356644457722100196865106185097443368718768, 0, 0, 0, 878767779153126958136775508864194081270995554356763204499271313392, 0, 0, 0, 0, 0, 878767784440068870266239575742902326033542019911514545186187818352,
  0, 878767792607772522872492379624203728179366351102205340813424559527, 0, 0, 0, 878767716698555956458241155486848860494732492261883462165673013472, 0, 878767729172978018006276070584434916607041808402483423688267698464, 0, 0, 0, 878767755691526621873620388199984331155796175648974677840476484336,
  0, 878767751470350895166264577711408164138838769989723882030227690912, 0, 0, 0, 878767715344646268512625898298305805000661090499114612578420467040, 0, 878767749131338647863602151166607443864358833039728619984267477287, 0, 0, 0, 878767779153126958136775508864194081270995554356763204499271313392,
  0, 878767751657409990664821287986724451285908802110591454141080209842, 0, 0, 0, 878767773325335927043144139455219459756415645369279051238506625632, 0, 878767764956170447648082999701960080818474058031828996561099899687, 0, 0, 0, 878767716698555956458241155486848860494732492261883462165673013472,
  0, 878767749131338647863602151166607443864358833039728619984267477287, 0, 0, 0, 878767740237528429132042225471072805353921895689025667010264694976, 0, 878767748068733272005403122144236801569933774224256444476528890800, 0, 0, 0, 878767773325335927043144139455219459756415645369279051238506625632,
  0, 878767792607772522872492379624203728179366351102205340813424559527, 0, 0, 0, 878767728383745061034231129287141162841444735771121594266018600224, 0, 878767743643940032191492356644457722100196865106185097443368718768, 0, 0, 0, 878767786218062549366361367279811129756779432375218708246214477088,
  0, 878767764956170447648082999701960080818474058031828996561099899687, 0, 0, 0, 878767715344646268512625898298305805000661090499114612578420467040, 0, 878767700934697771570362073888838264763938139134393663163478539952, 0, 0, 0, 0,
  0, 878767748068733272005403122144236801569933774224256444476528890800, 0, 0, 0, 878767755691526621873620388199984331155796175648974677840476484336, 0, 878767729172978018006276070584434916607041808402483423688267698464, 0, 0, 0, 878767740237528429132042225471072805353921895689025667010264694976,
  0, 878767700934697771570362073888838264763938139134393663163478539952, 0, 0, 0, 878767705425893020597911811040739533010283905856366850049980882240]

private def cert : Data where
  Q := 114
  M := 767
  R := 18
  D := 1048576
  p := 27
  t := 31
  v := 153
  w := 100
  L := 60
  c := 878767751470350895166264577711408164138838769989723882030227690912
  U := U
  I := I
  inv := inverse
  key := key
  W := weight
  scale := scale
  dual := dual
  u := upper
  T := base
  rows := [row0, row1, row2]

private theorem mass0 : weight 0=weightSum 114 767 upper key 0 := by decide +kernel
private theorem mass1 : weight 1=weightSum 114 767 upper key 1 := by decide +kernel
private theorem mass5 : weight 5=weightSum 114 767 upper key 5 := by decide +kernel
private theorem mass7 : weight 7=weightSum 114 767 upper key 7 := by decide +kernel
private theorem mass11 : weight 11=weightSum 114 767 upper key 11 := by decide +kernel
private theorem mass13 : weight 13=weightSum 114 767 upper key 13 := by decide +kernel
private theorem mass17 : weight 17=weightSum 114 767 upper key 17 := by decide +kernel
private theorem mass23 : weight 23=weightSum 114 767 upper key 23 := by decide +kernel
private theorem mass25 : weight 25=weightSum 114 767 upper key 25 := by decide +kernel
private theorem mass29 : weight 29=weightSum 114 767 upper key 29 := by decide +kernel
private theorem mass31 : weight 31=weightSum 114 767 upper key 31 := by decide +kernel
private theorem mass35 : weight 35=weightSum 114 767 upper key 35 := by decide +kernel
private theorem mass37 : weight 37=weightSum 114 767 upper key 37 := by decide +kernel
private theorem mass41 : weight 41=weightSum 114 767 upper key 41 := by decide +kernel
private theorem mass43 : weight 43=weightSum 114 767 upper key 43 := by decide +kernel
private theorem mass47 : weight 47=weightSum 114 767 upper key 47 := by decide +kernel
private theorem mass49 : weight 49=weightSum 114 767 upper key 49 := by decide +kernel
private theorem mass53 : weight 53=weightSum 114 767 upper key 53 := by decide +kernel
private theorem mass55 : weight 55=weightSum 114 767 upper key 55 := by decide +kernel
private theorem mass59 : weight 59=weightSum 114 767 upper key 59 := by decide +kernel
private theorem mass61 : weight 61=weightSum 114 767 upper key 61 := by decide +kernel
private theorem mass65 : weight 65=weightSum 114 767 upper key 65 := by decide +kernel
private theorem mass67 : weight 67=weightSum 114 767 upper key 67 := by decide +kernel
private theorem mass71 : weight 71=weightSum 114 767 upper key 71 := by decide +kernel
private theorem mass73 : weight 73=weightSum 114 767 upper key 73 := by decide +kernel
private theorem mass77 : weight 77=weightSum 114 767 upper key 77 := by decide +kernel
private theorem mass79 : weight 79=weightSum 114 767 upper key 79 := by decide +kernel
private theorem mass83 : weight 83=weightSum 114 767 upper key 83 := by decide +kernel
private theorem mass85 : weight 85=weightSum 114 767 upper key 85 := by decide +kernel
private theorem mass89 : weight 89=weightSum 114 767 upper key 89 := by decide +kernel
private theorem mass91 : weight 91=weightSum 114 767 upper key 91 := by decide +kernel
private theorem mass97 : weight 97=weightSum 114 767 upper key 97 := by decide +kernel
private theorem mass101 : weight 101=weightSum 114 767 upper key 101 := by decide +kernel
private theorem mass103 : weight 103=weightSum 114 767 upper key 103 := by decide +kernel
private theorem mass107 : weight 107=weightSum 114 767 upper key 107 := by decide +kernel
private theorem mass109 : weight 109=weightSum 114 767 upper key 109 := by decide +kernel
private theorem mass113 : weight 113=weightSum 114 767 upper key 113 := by decide +kernel

private theorem massAll : ∀ i ∈ keys cert, weight i=weightSum 114 767 upper key i := by
  intro i hi
  have h : i=0 ∨ i=1 ∨ i=5 ∨ i=7 ∨ i=11 ∨ i=13 ∨ i=17 ∨ i=23 ∨ i=25 ∨ i=29 ∨ i=31 ∨ i=35 ∨ i=37 ∨ i=41 ∨ i=43 ∨ i=47 ∨ i=49 ∨ i=53 ∨ i=55 ∨ i=59 ∨ i=61 ∨ i=65 ∨ i=67 ∨ i=71 ∨ i=73 ∨ i=77 ∨ i=79 ∨ i=83 ∨ i=85 ∨ i=89 ∨ i=91 ∨ i=97 ∨ i=101 ∨ i=103 ∨ i=107 ∨ i=109 ∨ i=113 := by
    simpa only [keys,cert,I,Finset.mem_insert,Finset.mem_mk,Multiset.mem_coe,List.mem_cons,List.not_mem_nil,or_false] using hi
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact mass0
  · exact mass1
  · exact mass5
  · exact mass7
  · exact mass11
  · exact mass13
  · exact mass17
  · exact mass23
  · exact mass25
  · exact mass29
  · exact mass31
  · exact mass35
  · exact mass37
  · exact mass41
  · exact mass43
  · exact mass47
  · exact mass49
  · exact mass53
  · exact mass55
  · exact mass59
  · exact mass61
  · exact mass65
  · exact mass67
  · exact mass71
  · exact mass73
  · exact mass77
  · exact mass79
  · exact mass83
  · exact mass85
  · exact mass89
  · exact mass91
  · exact mass97
  · exact mass101
  · exact mass103
  · exact mass107
  · exact mass109
  · exact mass113

private theorem corr1 : base 1=correlation cert 1 := by decide +kernel
private theorem corr5 : base 5=correlation cert 5 := by decide +kernel
private theorem corr7 : base 7=correlation cert 7 := by decide +kernel
private theorem corr11 : base 11=correlation cert 11 := by decide +kernel
private theorem corr13 : base 13=correlation cert 13 := by decide +kernel
private theorem corr17 : base 17=correlation cert 17 := by decide +kernel
private theorem corr23 : base 23=correlation cert 23 := by decide +kernel
private theorem corr25 : base 25=correlation cert 25 := by decide +kernel
private theorem corr29 : base 29=correlation cert 29 := by decide +kernel
private theorem corr31 : base 31=correlation cert 31 := by decide +kernel
private theorem corr35 : base 35=correlation cert 35 := by decide +kernel
private theorem corr37 : base 37=correlation cert 37 := by decide +kernel
private theorem corr41 : base 41=correlation cert 41 := by decide +kernel
private theorem corr43 : base 43=correlation cert 43 := by decide +kernel
private theorem corr47 : base 47=correlation cert 47 := by decide +kernel
private theorem corr49 : base 49=correlation cert 49 := by decide +kernel
private theorem corr53 : base 53=correlation cert 53 := by decide +kernel
private theorem corr55 : base 55=correlation cert 55 := by decide +kernel
private theorem corr59 : base 59=correlation cert 59 := by decide +kernel
private theorem corr61 : base 61=correlation cert 61 := by decide +kernel
private theorem corr65 : base 65=correlation cert 65 := by decide +kernel
private theorem corr67 : base 67=correlation cert 67 := by decide +kernel
private theorem corr71 : base 71=correlation cert 71 := by decide +kernel
private theorem corr73 : base 73=correlation cert 73 := by decide +kernel
private theorem corr77 : base 77=correlation cert 77 := by decide +kernel
private theorem corr79 : base 79=correlation cert 79 := by decide +kernel
private theorem corr83 : base 83=correlation cert 83 := by decide +kernel
private theorem corr85 : base 85=correlation cert 85 := by decide +kernel
private theorem corr89 : base 89=correlation cert 89 := by decide +kernel
private theorem corr91 : base 91=correlation cert 91 := by decide +kernel
private theorem corr97 : base 97=correlation cert 97 := by decide +kernel
private theorem corr101 : base 101=correlation cert 101 := by decide +kernel
private theorem corr103 : base 103=correlation cert 103 := by decide +kernel
private theorem corr107 : base 107=correlation cert 107 := by decide +kernel
private theorem corr109 : base 109=correlation cert 109 := by decide +kernel
private theorem corr113 : base 113=correlation cert 113 := by decide +kernel

private theorem corrAll : ∀ i ∈ U, base i=correlation cert i := by
  intro i hi
  have h : i=1 ∨ i=5 ∨ i=7 ∨ i=11 ∨ i=13 ∨ i=17 ∨ i=23 ∨ i=25 ∨ i=29 ∨ i=31 ∨ i=35 ∨ i=37 ∨ i=41 ∨ i=43 ∨ i=47 ∨ i=49 ∨ i=53 ∨ i=55 ∨ i=59 ∨ i=61 ∨ i=65 ∨ i=67 ∨ i=71 ∨ i=73 ∨ i=77 ∨ i=79 ∨ i=83 ∨ i=85 ∨ i=89 ∨ i=91 ∨ i=97 ∨ i=101 ∨ i=103 ∨ i=107 ∨ i=109 ∨ i=113 := by
    simpa only [U,Finset.mem_insert,Finset.mem_mk,Multiset.mem_coe,List.mem_cons,List.not_mem_nil,or_false] using hi
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact corr1
  · exact corr5
  · exact corr7
  · exact corr11
  · exact corr13
  · exact corr17
  · exact corr23
  · exact corr25
  · exact corr29
  · exact corr31
  · exact corr35
  · exact corr37
  · exact corr41
  · exact corr43
  · exact corr47
  · exact corr49
  · exact corr53
  · exact corr55
  · exact corr59
  · exact corr61
  · exact corr65
  · exact corr67
  · exact corr71
  · exact corr73
  · exact corr77
  · exact corr79
  · exact corr83
  · exact corr85
  · exact corr89
  · exact corr91
  · exact corr97
  · exact corr101
  · exact corr103
  · exact corr107
  · exact corr109
  · exact corr113

private def powers (k : ℕ) : Prop := let n := k+1
  0<upper n ∧ (upper n-1)^31*n^27≤1048576^31 ∧ 1048576^31≤(upper n)^31*n^27 ∧ upper (n+1)≤upper n

private theorem powers0 : ∀ k : Fin 32, powers (k.val+0) := by
  unfold powers
  decide +kernel

private theorem powers32 : ∀ k : Fin 32, powers (k.val+32) := by
  unfold powers
  decide +kernel

private theorem powers64 : ∀ k : Fin 32, powers (k.val+64) := by
  unfold powers
  decide +kernel

private theorem powers96 : ∀ k : Fin 32, powers (k.val+96) := by
  unfold powers
  decide +kernel

private theorem powers128 : ∀ k : Fin 32, powers (k.val+128) := by
  unfold powers
  decide +kernel

private theorem powers160 : ∀ k : Fin 32, powers (k.val+160) := by
  unfold powers
  decide +kernel

private theorem powers192 : ∀ k : Fin 32, powers (k.val+192) := by
  unfold powers
  decide +kernel

private theorem powers224 : ∀ k : Fin 32, powers (k.val+224) := by
  unfold powers
  decide +kernel

private theorem powers256 : ∀ k : Fin 32, powers (k.val+256) := by
  unfold powers
  decide +kernel

private theorem powers288 : ∀ k : Fin 32, powers (k.val+288) := by
  unfold powers
  decide +kernel

private theorem powers320 : ∀ k : Fin 32, powers (k.val+320) := by
  unfold powers
  decide +kernel

private theorem powers352 : ∀ k : Fin 32, powers (k.val+352) := by
  unfold powers
  decide +kernel

private theorem powers384 : ∀ k : Fin 32, powers (k.val+384) := by
  unfold powers
  decide +kernel

private theorem powers416 : ∀ k : Fin 32, powers (k.val+416) := by
  unfold powers
  decide +kernel

private theorem powers448 : ∀ k : Fin 32, powers (k.val+448) := by
  unfold powers
  decide +kernel

private theorem powers480 : ∀ k : Fin 32, powers (k.val+480) := by
  unfold powers
  decide +kernel

private theorem powers512 : ∀ k : Fin 32, powers (k.val+512) := by
  unfold powers
  decide +kernel

private theorem powers544 : ∀ k : Fin 32, powers (k.val+544) := by
  unfold powers
  decide +kernel

private theorem powers576 : ∀ k : Fin 32, powers (k.val+576) := by
  unfold powers
  decide +kernel

private theorem powers608 : ∀ k : Fin 32, powers (k.val+608) := by
  unfold powers
  decide +kernel

private theorem powers640 : ∀ k : Fin 32, powers (k.val+640) := by
  unfold powers
  decide +kernel

private theorem powers672 : ∀ k : Fin 32, powers (k.val+672) := by
  unfold powers
  decide +kernel

private theorem powers704 : ∀ k : Fin 32, powers (k.val+704) := by
  unfold powers
  decide +kernel

private theorem powers736 : ∀ k : Fin 32, powers (k.val+736) := by
  unfold powers
  decide +kernel

private theorem table : GRH.DirichletPrefix.Table 767 1048576 27 31 upper := by
  rintro ⟨k,hk⟩
  change powers k
  by_cases h0 : k < 32
  · exact powers0 ⟨k,h0⟩
  by_cases h32 : k < 64
  · have e := powers32 ⟨k-32,by omega⟩
    simpa only [show k-32+32=k by omega] using e
  by_cases h64 : k < 96
  · have e := powers64 ⟨k-64,by omega⟩
    simpa only [show k-64+64=k by omega] using e
  by_cases h96 : k < 128
  · have e := powers96 ⟨k-96,by omega⟩
    simpa only [show k-96+96=k by omega] using e
  by_cases h128 : k < 160
  · have e := powers128 ⟨k-128,by omega⟩
    simpa only [show k-128+128=k by omega] using e
  by_cases h160 : k < 192
  · have e := powers160 ⟨k-160,by omega⟩
    simpa only [show k-160+160=k by omega] using e
  by_cases h192 : k < 224
  · have e := powers192 ⟨k-192,by omega⟩
    simpa only [show k-192+192=k by omega] using e
  by_cases h224 : k < 256
  · have e := powers224 ⟨k-224,by omega⟩
    simpa only [show k-224+224=k by omega] using e
  by_cases h256 : k < 288
  · have e := powers256 ⟨k-256,by omega⟩
    simpa only [show k-256+256=k by omega] using e
  by_cases h288 : k < 320
  · have e := powers288 ⟨k-288,by omega⟩
    simpa only [show k-288+288=k by omega] using e
  by_cases h320 : k < 352
  · have e := powers320 ⟨k-320,by omega⟩
    simpa only [show k-320+320=k by omega] using e
  by_cases h352 : k < 384
  · have e := powers352 ⟨k-352,by omega⟩
    simpa only [show k-352+352=k by omega] using e
  by_cases h384 : k < 416
  · have e := powers384 ⟨k-384,by omega⟩
    simpa only [show k-384+384=k by omega] using e
  by_cases h416 : k < 448
  · have e := powers416 ⟨k-416,by omega⟩
    simpa only [show k-416+416=k by omega] using e
  by_cases h448 : k < 480
  · have e := powers448 ⟨k-448,by omega⟩
    simpa only [show k-448+448=k by omega] using e
  by_cases h480 : k < 512
  · have e := powers480 ⟨k-480,by omega⟩
    simpa only [show k-480+480=k by omega] using e
  by_cases h512 : k < 544
  · have e := powers512 ⟨k-512,by omega⟩
    simpa only [show k-512+512=k by omega] using e
  by_cases h544 : k < 576
  · have e := powers544 ⟨k-544,by omega⟩
    simpa only [show k-544+544=k by omega] using e
  by_cases h576 : k < 608
  · have e := powers576 ⟨k-576,by omega⟩
    simpa only [show k-576+576=k by omega] using e
  by_cases h608 : k < 640
  · have e := powers608 ⟨k-608,by omega⟩
    simpa only [show k-608+608=k by omega] using e
  by_cases h640 : k < 672
  · have e := powers640 ⟨k-640,by omega⟩
    simpa only [show k-640+640=k by omega] using e
  by_cases h672 : k < 704
  · have e := powers672 ⟨k-672,by omega⟩
    simpa only [show k-672+672=k by omega] using e
  by_cases h704 : k < 736
  · have e := powers704 ⟨k-704,by omega⟩
    simpa only [show k-704+704=k by omega] using e
  by_cases h736 : k < 768
  · have e := powers736 ⟨k-736,by omega⟩
    simpa only [show k-736+736=k by omega] using e
  omega

private theorem valid : Valid cert := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,?_,?_,?_,
    by decide,by decide,by decide,?_,massAll,?_,corrAll,?_,table,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · unfold Permutes
    decide +kernel
  · change ∀ r : Fin 114, r.val≠0 → (key r.val=1 ∨ key r.val∈I) ∧
        ∀ b ∈ U, entry r.val b=entry (key r.val) b
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Checked integer weights and group convolution rows cover the closed
height-one rectangle at every divisor of the witness period. -/
theorem solution (d : ℕ) (hd : d ∣ 114) (a b H : ℝ) (ha : (27/31:ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ 7/8) (hH : 0 ≤ H) (hhi : H ≤ 1) : Covers d a b H := by
  refine ⟨cert,valid,hd,ha,?_⟩
  change b^2+H^2 ≤ (((153:ℝ)/100)*(27/31))^2
  have re := mul_self_le_mul_self (show 0 ≤ b by linarith) hb
  have im := mul_self_le_mul_self hH hhi
  nlinarith
