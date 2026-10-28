-- Prove2me | solution 1 for D1Bound5.pellFiniteCertificate_exists
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:31:39.10311+00:00
-- url     : https://prove2.me/submissions/72e1da1a-442f-4025-b4b3-3d45c58fd3c8

import Mathlib.Tactic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Group.Int.Units
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership00_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership01_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership02_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership03_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership04_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership05_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership06_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership07_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership08_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership09_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership10_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership11_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership12_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership13_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership14_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership15_20261024
import Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCoverageLightBlock00_20261024
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock01_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock02_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock03_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock04_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock05_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock06_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock07_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock08_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock09_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock10_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock11_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock12_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock13_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock14_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock15_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock16_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock17_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock18_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock19_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock20_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock21_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock22_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock23_checked
import Theorems.Thm_D1Bound5_pellFieldCoverageBlock24_checked

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

private theorem transfer_certificate_of_mem (d : ℤ) (hd : d ∈ pellFieldCoverageParameters) :
    Nonempty (PellFiniteCertificate d (10^275)) := by
  have he : pellFieldCoverageParameters = (([7,15,23,31,39,47,55,71,79,87,95,103,111,119,127,143,151,159,167,183,191,199,215,223,231,239,247,255,263,271,287,295,303,311,319,327,335,359,367,383,391,399,407,415,431,439,447,455,463,471,479,487,503,511,519,527,535,543,551,559,583,591,599,607] : List ℤ) ++ (([615,623,631,647,655,663,671,679,687,695,703,719,727,743,751,759,767,791,799,807,815,823,831,839,863,871,879,887,895,903,911,919,935,943,951,959,967,983,991,1007,1015,1023,1031,1039,1047,1055,1063,1079,1087,1095,1103,1111,1119,1135,1151,1159,1167,1191,1199,1207,1223,1231,1239,1247] : List ℤ) ++ (([1255,1263,1271,1279,1295,1303,1311,1319,1327,1335,1343,1351,1367,1383,1391,1399,1407,1415,1423,1439,1447,1455,1463,1471,1479,1487,1495,1511,1527,1535,1543,1551,1559,1567,1583,1591,1599,1607,1615,1623,1631,1639,1655,1663,1671,1679,1687,1695,1703,1711,1727,1735,1743,1751,1759,1767,1783,1799,1807,1823,1831,1839,1847,1855] : List ℤ) ++ (([1871,1879,1887,1895,1903,1919,1927,1943,1951,1959,1967,1983,1991,1999,2015,2031,2039,2047,2055,2063,2071,2087,2095,2103,2111,2119,2127,2135,2143,2159,2167,2183,2191,2199,2207,2215,2231,2239,2247,2255,2263,2271,2279,2287,2311,2319,2327,2335,2343,2351,2359,2383,2391,2399,2407,2415,2423,2431,2447,2455,2463,2471,2479,2487] : List ℤ) ++ (([2495,2503,2519,2543,2551,2559,2567,2591,2599,2607,2615,2623,2631,2639,2647,2663,2671,2679,2687,2703,2711,2719,2735,2743,2751,2759,2767,2791,2807,2815,2823,2831,2839,2847,2855,2863,2879,2887,2895,2903,2911,2919,2927,2935,2951,2959,2967,2983,2991,2999,3007,3023,3031,3039,3047,3055,3063,3071,3079,3095,3103,3111,3119,3127] : List ℤ) ++ (([3135,3143,3151,3167,3183,3191,3199,3207,3215,3223,3239,3247,3255,3263,3271,3279,3287,3295,3311,3319,3327,3335,3343,3351,3359,3367,3383,3391,3399,3407,3415,3423,3431,3439,3455,3463,3471,3487,3495,3503,3511,3527,3535,3543,3551,3559,3567,3583,3599,3607,3615,3623,3631,3639,3647,3655,3671,3679,3687,3695,3711,3719,3727,3743] : List ℤ) ++ (([3759,3767,3783,3791,3799,3815,3823,3831,3839,3847,3855,3863,3895,3903,3911,3919,3927,3935,3943,3959,3967,3983,3991,3999,4007,4015,4031,4039,4047,4055,4063,4071,4079,4087,4103,4111,4119,4127,4135,4143,4151,4159,4183,4191,4199,4207,4215,4223,4231,4247,4255,4271,4279,4287,4295,4303,4319,4327,4343,4351,4359,4367,4391,4399] : List ℤ) ++ (([4407,4415,4423,4431,4439,4447,4463,4471,4479,4487,4495,4503,4511,4519,4535,4543,4551,4559,4567,4583,4591,4607,4615,4623,4631,4639,4647,4663,4679,4687,4695,4703,4711,4727,4735,4751,4759,4767,4783,4791,4799,4807,4823,4831,4839,4847,4855,4863,4871,4879,4895,4903,4911,4919,4927,4935,4943,4951,4967,4983,4991,4999,5007,5015] : List ℤ) ++ (([5023,5039,5055,5063,5071,5079,5087,5095,5111,5119,5127,5135,5143,5151,5159,5167,5183,5191,5199,5207,5215,5223,5231,5255,5263,5271,5279,5287,5295,5303,5311,5327,5335,5343,5351,5359,5367,5383,5399,5407,5423,5431,5447,5455,5471,5479,5487,5495,5503,5511,5519,5527,5543,5551,5559,5567,5583,5591,5599,5615,5623,5631,5639,5647] : List ℤ) ++ (([5655,5663,5671,5695,5703,5711,5719,5727,5735,5743,5759,5767,5783,5791,5799,5807,5815,5839,5847,5855,5863,5871,5879,5903,5911,5919,5927,5935,5943,5951,5959,5983,5991,5999,6007,6015,6023,6031,6047,6055,6063,6071,6079,6087,6095,6103,6119,6127,6135,6143,6151,6159,6167,6191,6199,6207,6215,6231,6239,6247,6263,6271,6279,6287] : List ℤ) ++ (([6295,6303,6311,6319,6335,6343,6351,6359,6367,6383,6391,6407,6415,6423,6431,6439,6447,6455,6463,6479,6487,6495,6503,6511,6519,6527,6535,6551,6559,6567,6583,6599,6607,6623,6631,6639,6663,6671,6679,6695,6703,6711,6719,6735,6743,6751,6767,6783,6791,6799,6807,6815,6823,6839,6847,6855,6863,6871,6879,6887,6895,6911,6919,6927] : List ℤ) ++ (([6935,6943,6951,6959,6967,6983,6991,6999,7015,7023,7031,7039,7055,7063,7071,7079,7087,7095,7103,7111,7127,7135,7143,7151,7159,7167,7183,7199,7207,7215,7223,7231,7239,7247,7255,7271,7279,7287,7295,7303,7311,7319,7327,7343,7351,7359,7367,7383,7391,7415,7423,7431,7439,7447,7455,7463,7471,7487,7495,7503,7511,7519,7527,7535] : List ℤ) ++ (([7543,7559,7567,7583,7591,7599,7607,7615,7631,7639,7647,7655,7663,7671,7679,7687,7703,7711,7719,7727,7735,7743,7751,7759,7783,7799,7807,7815,7823,7831,7847,7855,7863,7871,7879,7887,7895,7903,7919,7927,7951,7959,7967,7991,7999,8007,8015,8023,8031,8039,8047,8063,8071,8079,8087,8095,8103,8111,8119,8135,8143,8151,8159,8167] : List ℤ) ++ (([8191,8207,8215,8223,8231,8239,8247,8255,8263,8279,8287,8295,8311,8319,8327,8335,8351,8359,8367,8383,8391,8399,8407,8423,8431,8439,8447,8455,8463,8471,8479,8495,8503,8511,8519,8527,8535,8543,8551,8567,8583,8599,8607,8615,8623,8639,8647,8655,8663,8671,8679,8687,8695,8711,8719,8727,8735,8743,8751,8759,8767,8783,8791,8799] : List ℤ) ++ (([8807,8815,8823,8831,8839,8855,8863,8871,8879,8887,8895,8903,8911,8927,8935,8943,8951,8983,8999,9007,9015,9023,9031,9039,9047,9055,9071,9079,9087,9095,9103,9111,9119,9127,9143,9151,9159,9167,9183,9191,9199,9215,9223,9231,9239,9247,9255,9263,9271,9287,9303,9311,9319,9327,9335,9343,9367,9383,9391,9399,9407,9415,9431,9439] : List ℤ) ++ ([9447,9455,9463,9471,9479,9487,9503,9511,9519,9527,9535,9543,9551,9591,9599,9607,9615,9623,9631,9647,9655,9663,9671,9679,9687,9695,9703,9719,9727,9735,9743,9759,9767,9791,9799,9807,9815,9823,9831,9839,9847,9863,9871,9879,9887,9895,9903,9911,9919,9935,9943,9951,9959,9967,9983,9991] : List ℤ)))))))))))))))) := by rfl
  rw [he] at hd
  simp only [List.mem_append] at hd
  rcases hd with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership00_20261024 d h0
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership01_20261024 d h1
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership02_20261024 d h2
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership03_20261024 d h3
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership04_20261024 d h4
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership05_20261024 d h5
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership06_20261024 d h6
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership07_20261024 d h7
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership08_20261024 d h8
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership09_20261024 d h9
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership10_20261024 d h10
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership11_20261024 d h11
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership12_20261024 d h12
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership13_20261024 d h13
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership14_20261024 d h14
  · exact D1Bound5.Prove2MeTransfer.pellCertificateMembership15_20261024 d h15

private theorem transfer_coverage_blocks (b : Fin 25) (r : Fin 50) :
    PellFieldCoverageLightAt (50*b.val+r.val) := by
  fin_cases b
  · exact D1Bound5.Prove2MeTransfer.pellCoverageLightBlock00_20261024 r
  · exact D1Bound5.pellFieldCoverageBlock01_checked r
  · exact D1Bound5.pellFieldCoverageBlock02_checked r
  · exact D1Bound5.pellFieldCoverageBlock03_checked r
  · exact D1Bound5.pellFieldCoverageBlock04_checked r
  · exact D1Bound5.pellFieldCoverageBlock05_checked r
  · exact D1Bound5.pellFieldCoverageBlock06_checked r
  · exact D1Bound5.pellFieldCoverageBlock07_checked r
  · exact D1Bound5.pellFieldCoverageBlock08_checked r
  · exact D1Bound5.pellFieldCoverageBlock09_checked r
  · exact D1Bound5.pellFieldCoverageBlock10_checked r
  · exact D1Bound5.pellFieldCoverageBlock11_checked r
  · exact D1Bound5.pellFieldCoverageBlock12_checked r
  · exact D1Bound5.pellFieldCoverageBlock13_checked r
  · exact D1Bound5.pellFieldCoverageBlock14_checked r
  · exact D1Bound5.pellFieldCoverageBlock15_checked r
  · exact D1Bound5.pellFieldCoverageBlock16_checked r
  · exact D1Bound5.pellFieldCoverageBlock17_checked r
  · exact D1Bound5.pellFieldCoverageBlock18_checked r
  · exact D1Bound5.pellFieldCoverageBlock19_checked r
  · exact D1Bound5.pellFieldCoverageBlock20_checked r
  · exact D1Bound5.pellFieldCoverageBlock21_checked r
  · exact D1Bound5.pellFieldCoverageBlock22_checked r
  · exact D1Bound5.pellFieldCoverageBlock23_checked r
  · exact D1Bound5.pellFieldCoverageBlock24_checked r

private theorem transfer_coverage_all (k : Fin 1250) : PellFieldCoverageLightAt k.val := by
  let b : Fin 25 := ⟨k.val/50, by omega⟩
  let r : Fin 50 := ⟨k.val%50, Nat.mod_lt _ (by decide)⟩
  have h := transfer_coverage_blocks b r
  have he : 50*b.val+r.val = k.val := by
    dsimp [b,r]
    omega
  simpa only [he] using h

theorem _root_.solution (d : ℤ) (hd : 7 ≤ d) (hupper : d < 10000)
    (hmod : d % 8 = 7) (hsq : Squarefree d) :
    Nonempty (PellFiniteCertificate d (10^275)) := by
  have hk0 : 0 ≤ d/8 := by omega
  have hklt : (d/8).toNat < 1250 := by omega
  let k : Fin 1250 := ⟨(d/8).toNat,hklt⟩
  have heq : 7+8*(k.val : ℤ) = d := by dsimp [k]; omega
  have hc := transfer_coverage_all k
  dsimp only [PellFieldCoverageLightAt] at hc
  change 7+8*(k.val : ℤ) ∈ pellFieldCoverageParameters ∨ (2 ≤ pellFieldCoverageFactors.getD k.val 0 ∧ (pellFieldCoverageFactors.getD k.val 0)*(pellFieldCoverageFactors.getD k.val 0) ∣ 7+8*(k.val : ℤ)) at hc
  rw [heq] at hc
  rcases hc with hmem | hbad
  · exact transfer_certificate_of_mem d hmem
  · have hu : IsUnit (pellFieldCoverageFactors.getD k.val 0) := hsq _ hbad.2
    have hh := Int.isUnit_iff.mp hu
    omega

end D1Bound5
end
