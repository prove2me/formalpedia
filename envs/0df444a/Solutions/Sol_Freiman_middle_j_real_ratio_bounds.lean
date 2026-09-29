-- Prove2me | solution 1 for Freiman.middle_j_real_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:57:50.96432+00:00
-- url     : https://prove2.me/submissions/aba05330-7441-42f3-8368-9d0813b4360d

import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

open Freiman

namespace Freiman.JProof_Freiman_middle_j_real_ratio_bounds

theorem sqrt_bounds :
    (173205080 / 100000000 : ℝ) < Real.sqrt 3 ∧
    Real.sqrt 3 < (173205081 / 100000000 : ℝ) ∧
    (458257569 / 100000000 : ℝ) < Real.sqrt 21 ∧
    Real.sqrt 21 < (458257570 / 100000000 : ℝ) := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h21 := Real.sq_sqrt (show (0:ℝ) ≤ 21 by norm_num)
  have hn3 := Real.sqrt_nonneg (3:ℝ)
  have hn21 := Real.sqrt_nonneg (21:ℝ)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem inverse_bounds (x a l u : ℝ) (hl : 0 < l) (hu : 0 < u)
    (hd : 0 < a+x) (hlo : l*(a+x) < 1) (hhi : 1 < u*(a+x)) :
    l < 1/(a+x) ∧ 1/(a+x) < u := by
  exact ⟨(lt_div_iff₀ hd).2 hlo,(div_lt_iff₀ hd).2 hhi⟩


theorem alpha_box : (26376261/100000000:ℝ) < middleAlpha ∧ middleAlpha < (13188131/50000000:ℝ) := by
  have h := sqrt_bounds
  unfold middleAlpha
  constructor <;> linarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem beta_box : (4945549/6250000:ℝ) < middleBeta ∧ middleBeta < (15825757/20000000:ℝ) := by
  have h := sqrt_bounds
  unfold middleBeta
  constructor <;> linarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem rho_box : (1830127/2500000:ℝ) < middleRho ∧ middleRho < (73205081/100000000:ℝ) := by
  have h := sqrt_bounds
  unfold middleRho
  constructor <;> linarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem alpha3_box : (30639483/100000000:ℝ) < prefixEval [3] middleAlpha ∧ prefixEval [3] middleAlpha < (7659871/25000000:ℝ) := by
  have h := alpha_box
  change (30639483/100000000:ℝ) < 1/(3+middleAlpha) ∧ 1/(3+middleAlpha) < (7659871/25000000:ℝ)
  have hd : 0 < 3+middleAlpha := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem rho3_box : (26794919/100000000:ℝ) < prefixEval [3] middleRho ∧ prefixEval [3] middleRho < (669873/2500000:ℝ) := by
  have h := rho_box
  change (26794919/100000000:ℝ) < 1/(3+middleRho) ∧ 1/(3+middleRho) < (669873/2500000:ℝ)
  have hd : 0 < 3+middleRho := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem rho23_box : (22046349/50000000:ℝ) < prefixEval [2,3] middleRho ∧ prefixEval [2,3] middleRho < (44092699/100000000:ℝ) := by
  have h := rho3_box
  change (22046349/50000000:ℝ) < 1/(2+prefixEval [3] middleRho) ∧ 1/(2+prefixEval [3] middleRho) < (44092699/100000000:ℝ)
  have hd : 0 < 2+prefixEval [3] middleRho := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem rho13_box : (9858439/12500000:ℝ) < prefixEval [1,3] middleRho ∧ prefixEval [1,3] middleRho < (39433757/50000000:ℝ) := by
  have h := rho3_box
  rw [prefixEval]
  norm_num only [PNat.one_coe, Nat.cast_one]
  change (9858439/12500000:ℝ) < 1/(1+prefixEval [3] middleRho) ∧ 1/(1+prefixEval [3] middleRho) < (39433757/50000000:ℝ)
  have hd : 0 < 1+prefixEval [3] middleRho := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem rho113_box : (55907301/100000000:ℝ) < prefixEval [1,1,3] middleRho ∧ prefixEval [1,1,3] middleRho < (27953651/50000000:ℝ) := by
  have h := rho13_box
  rw [prefixEval]
  norm_num only [PNat.one_coe, Nat.cast_one]
  change (55907301/100000000:ℝ) < 1/(1+prefixEval [1,3] middleRho) ∧ 1/(1+prefixEval [1,3] middleRho) < (27953651/50000000:ℝ)
  have hd : 0 < 1+prefixEval [1,3] middleRho := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem beta2_box : (8956439/25000000:ℝ) < prefixEval [2] middleBeta ∧ prefixEval [2] middleBeta < (17912879/50000000:ℝ) := by
  have h := beta_box
  change (8956439/25000000:ℝ) < 1/(2+middleBeta) ∧ 1/(2+middleBeta) < (17912879/50000000:ℝ)
  have hd : 0 < 2+middleBeta := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem beta12_box : (73623737/100000000:ℝ) < prefixEval [1,2] middleBeta ∧ prefixEval [1,2] middleBeta < (73623739/100000000:ℝ) := by
  have h := beta2_box
  rw [prefixEval]
  norm_num only [PNat.one_coe, Nat.cast_one]
  change (73623737/100000000:ℝ) < 1/(1+prefixEval [2] middleBeta) ∧ 1/(1+prefixEval [2] middleBeta) < (73623739/100000000:ℝ)
  have hd : 0 < 1+prefixEval [2] middleBeta := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem beta112_box : (5759581/10000000:ℝ) < prefixEval [1,1,2] middleBeta ∧ prefixEval [1,1,2] middleBeta < (14398953/25000000:ℝ) := by
  have h := beta12_box
  rw [prefixEval]
  norm_num only [PNat.one_coe, Nat.cast_one]
  change (5759581/10000000:ℝ) < 1/(1+prefixEval [1,2] middleBeta) ∧ 1/(1+prefixEval [1,2] middleBeta) < (14398953/25000000:ℝ)
  have hd : 0 < 1+prefixEval [1,2] middleBeta := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem beta312_box : (13382447/50000000:ℝ) < prefixEval [3,1,2] middleBeta ∧ prefixEval [3,1,2] middleBeta < (5352979/20000000:ℝ) := by
  have h := beta12_box
  change (13382447/50000000:ℝ) < 1/(3+prefixEval [1,2] middleBeta) ∧ 1/(3+prefixEval [1,2] middleBeta) < (5352979/20000000:ℝ)
  have hd : 0 < 3+prefixEval [1,2] middleBeta := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem rho313_box : (527889/2000000:ℝ) < prefixEval [3,1,3] middleRho ∧ prefixEval [3,1,3] middleRho < (6598613/25000000:ℝ) := by
  have h := rho13_box
  change (527889/2000000:ℝ) < 1/(3+prefixEval [1,3] middleRho) ∧ 1/(3+prefixEval [1,3] middleRho) < (6598613/25000000:ℝ)
  have hd : 0 < 3+prefixEval [1,3] middleRho := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem rho3313_box : (1225511/4000000:ℝ) < prefixEval [3,3,1,3] middleRho ∧ prefixEval [3,3,1,3] middleRho < (1914861/6250000:ℝ) := by
  have h := rho313_box
  change (1225511/4000000:ℝ) < 1/(3+prefixEval [3,1,3] middleRho) ∧ 1/(3+prefixEval [3,1,3] middleRho) < (1914861/6250000:ℝ)
  have hd : 0 < 3+prefixEval [3,1,3] middleRho := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem beta3312_box : (15301521/50000000:ℝ) < prefixEval [3,3,1,2] middleBeta ∧ prefixEval [3,3,1,2] middleBeta < (30603043/100000000:ℝ) := by
  have h := beta312_box
  change (15301521/50000000:ℝ) < 1/(3+prefixEval [3,1,2] middleBeta) ∧ 1/(3+prefixEval [3,1,2] middleBeta) < (30603043/100000000:ℝ)
  have hd : 0 < 3+prefixEval [3,1,2] middleBeta := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem rho33_box : (3060023/10000000:ℝ) < prefixEval [3,3] middleRho ∧ prefixEval [3,3] middleRho < (30600231/100000000:ℝ) := by
  have h := rho3_box
  change (3060023/10000000:ℝ) < 1/(3+prefixEval [3] middleRho) ∧ 1/(3+prefixEval [3] middleRho) < (30600231/100000000:ℝ)
  have hd : 0 < 3+prefixEval [3] middleRho := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem rho33313_box : (30244577/100000000:ℝ) < prefixEval [3,3,3,1,3] middleRho ∧ prefixEval [3,3,3,1,3] middleRho < (30244579/100000000:ℝ) := by
  have h := rho3313_box
  change (30244577/100000000:ℝ) < 1/(3+prefixEval [3,3,1,3] middleRho) ∧ 1/(3+prefixEval [3,3,1,3] middleRho) < (30244579/100000000:ℝ)
  have hd : 0 < 3+prefixEval [3,3,1,3] middleRho := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem beta32_box : (14888673/50000000:ℝ) < prefixEval [3,2] middleBeta ∧ prefixEval [3,2] middleBeta < (29777347/100000000:ℝ) := by
  have h := beta2_box
  change (14888673/50000000:ℝ) < 1/(3+prefixEval [2] middleBeta) ∧ 1/(3+prefixEval [2] middleBeta) < (29777347/100000000:ℝ)
  have hd : 0 < 3+prefixEval [2] middleBeta := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

theorem beta33312_box : (6049551/20000000:ℝ) < prefixEval [3,3,3,1,2] middleBeta ∧ prefixEval [3,3,3,1,2] middleBeta < (7561939/25000000:ℝ) := by
  have h := beta3312_box
  change (6049551/20000000:ℝ) < 1/(3+prefixEval [3,3,1,2] middleBeta) ∧ 1/(3+prefixEval [3,3,1,2] middleBeta) < (7561939/25000000:ℝ)
  have hd : 0 < 3+prefixEval [3,3,1,2] middleBeta := by linarith [h.1]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [h.1,h.2]
  · apply (div_lt_iff₀ hd).2
    nlinarith [h.1,h.2]

end Freiman.JProof_Freiman_middle_j_real_ratio_bounds


open Freiman

namespace Freiman.JProof_Freiman_middle_j_real_ratio_bounds

theorem jR_lower : (735/1000:ℝ) < middleJR := by
  have ha := rho3_box
  have hb := rho3313_box
  have hc := beta2_box
  have hd := beta3312_box
  unfold middleJR middleJA middleJB middleJC middleJD
  apply (lt_div_iff₀ (by linarith [hc.1,hd.2])).2
  nlinarith [ha.2,hb.1,hc.2,hd.1]

theorem j_factor_lower (r : ℝ) (hr : r ∈ Set.Icc (3/10:ℝ) (1/3)) :
    (3/4:ℝ) < middleJR * ((1+r*middleJC)*(1+r*middleJD)) /
      ((1+r*middleJA)*(1+r*middleJB)) := by
  have ha : (0:ℝ) < middleJA ∧ middleJA < 268/1000 := by
    unfold middleJA
    constructor <;> linarith [rho3_box.1,rho3_box.2]
  have hb : (0:ℝ) < middleJB ∧ middleJB < 307/1000 := by
    unfold middleJB
    constructor <;> linarith [rho3313_box.1,rho3313_box.2]
  have hc : (358/1000:ℝ) < middleJC := by
    unfold middleJC
    linarith [beta2_box.1]
  have hd : (306/1000:ℝ) < middleJD := by
    unfold middleJD
    linarith [beta3312_box.1]
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have ha0 := ha.1
  have hb0 := hb.1
  have hJR0 : 0 < middleJR := by linarith [jR_lower]
  have hc0 : 0 < middleJC := by linarith
  have hd0 : 0 < middleJD := by linarith
  have hD : 0 < (1+r*middleJA)*(1+r*middleJB) := by positivity
  apply (lt_div_iff₀ hD).2
  calc
    (3/4:ℝ)*((1+r*middleJA)*(1+r*middleJB)) ≤
        (3/4:ℝ)*((1+r*(268/1000))*(1+r*(307/1000))) := by
      gcongr
      · exact le_of_lt ha.2
      · exact le_of_lt hb.2
    _ < (735/1000:ℝ)*((1+r*(358/1000))*(1+r*(306/1000))) := by
      nlinarith [hr.1, sq_nonneg (r-3/10)]
    _ ≤ middleJR*((1+r*middleJC)*(1+r*middleJD)) := by
      gcongr
      · exact le_of_lt jR_lower


theorem hstar_box (p s : ℝ) (hp : p ∈ Set.Icc (1/4:ℝ) (4/5))
    (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) :
    middleHStar p s ≤ (3/4:ℝ)*((1+s*(297/1000))^2)/((1+p*(307/1000))^2) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have ha : (263/1000:ℝ) < middleAlpha ∧ middleAlpha < 264/1000 := by
    constructor <;> linarith [alpha_box.1,alpha_box.2]
  have hb : (306/1000:ℝ) < prefixEval [3] middleAlpha ∧
      prefixEval [3] middleAlpha < 307/1000 := by
    constructor <;> linarith [alpha3_box.1,alpha3_box.2]
  have ha0 : 0 < middleAlpha := by linarith [ha.1]
  have hb0 : 0 < prefixEval [3] middleAlpha := by linarith [hb.1]
  have hNp : 0 < (1+s*(297/1000:ℝ))^2 := by positivity
  have hD : 0 < (1+p*middleAlpha)*(1+p*prefixEval [3] middleAlpha) := by
    have ha0 : 0 < middleAlpha := by linarith [ha.1]
    have hb0 : 0 < prefixEval [3] middleAlpha := by linarith [hb.1]
    positivity
  have hN : (1+s*middleAlpha)*(1+s*prefixEval [3] middleAlpha) ≤
      (1+s*(297/1000:ℝ))^2 := by
    calc
      _ ≤ (1+s*(264/1000:ℝ))*(1+s*(307/1000:ℝ)) := by
        gcongr
        · exact le_of_lt ha.2
        · exact le_of_lt hb.2
      _ ≤ _ := by nlinarith [sq_nonneg s]
  have hp2 : p^2 ≤ (4/5:ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4/5-p by linarith [hp.2])
      (show 0 ≤ 4/5+p by linarith)]
  have hDb : (1+p*(307/1000:ℝ))^2 ≤
      (21/20:ℝ)*((1+p*middleAlpha)*(1+p*prefixEval [3] middleAlpha)) := by
    calc
      _ ≤ (21/20:ℝ)*((1+p*(263/1000:ℝ))*(1+p*(306/1000:ℝ))) := by
        nlinarith [hp.2,hp2]
      _ ≤ _ := by
        gcongr
        · exact le_of_lt ha.1
        · exact le_of_lt hb.1
  unfold middleHStar middleScalarThreshold
  apply (div_le_div_iff₀ hD (by positivity)).2
  calc
    _ ≤ (5/7:ℝ)*(1+s*(297/1000))^2 *
        ((21/20:ℝ)*((1+p*middleAlpha)*(1+p*prefixEval [3] middleAlpha))) := by
      gcongr
    _ = _ := by ring

theorem threshold_compare (p s F x y z w : ℝ)
    (hp : p ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5))
    (hF : (3/4:ℝ) < F) (hx : x ∈ Set.Icc (0:ℝ) (307/1000))
    (hy : y ∈ Set.Icc (0:ℝ) (307/1000))
    (hz : (297/1000:ℝ) ≤ z) (hw : (297/1000:ℝ) ≤ w) :
    middleHStar p s < F*((1+s*z)*(1+s*w))/((1+p*x)*(1+p*y)) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hF0 : 0 < F := by linarith
  have hx0 := hx.1
  have hy0 := hy.1
  have hz0 : 0 ≤ z := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hN : (1+s*(297/1000:ℝ))^2 ≤ (1+s*z)*(1+s*w) := by
    rw [pow_two]
    gcongr
  have hD : (1+p*x)*(1+p*y) ≤ (1+p*(307/1000:ℝ))^2 := by
    rw [pow_two]
    gcongr
    · exact hx.2
    · exact hy.2
  calc
    middleHStar p s ≤ (3/4:ℝ)*(1+s*(297/1000))^2/(1+p*(307/1000))^2 := hstar_box p s hp hs
    _ < F*(1+s*(297/1000))^2/(1+p*(307/1000))^2 := by
      apply div_lt_div_of_pos_right _ (by positivity)
      exact mul_lt_mul_of_pos_right hF (by positivity)
    _ ≤ F*((1+s*z)*(1+s*w))/((1+p*x)*(1+p*y)) := by
      apply div_le_div₀ (by positivity) _ (by positivity) hD
      exact mul_le_mul_of_nonneg_left hN (le_of_lt hF0)

end Freiman.JProof_Freiman_middle_j_real_ratio_bounds


open Freiman Freiman.JProof_Freiman_middle_j_real_ratio_bounds

theorem solution :
    ∀ p s x y : ℝ, p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) →
      x ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) → y ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) →
      middleHStar p s < middleH p s x y ∧
      (5/19:ℝ)*middleH p s x y < middleScalarA p s (549/1000) ∧
      (5/19:ℝ)*middleH p s x y < middleScalarB p s (313/1000) := by
  intro p s x y hp hs hx hy
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hxlo : (263/1000:ℝ) ≤ x := by linarith [hx.1,alpha_box.1]
  have hylo : (263/1000:ℝ) ≤ y := by linarith [hy.1,alpha_box.1]
  have hxhi : x ≤ (307/1000:ℝ) := by linarith [hx.2,alpha3_box.2]
  have hyhi : y ≤ (307/1000:ℝ) := by linarith [hy.2,alpha3_box.2]
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hN0 : 0 < (1+s*x)*(1+s*y) := by positivity
  have hD0 : 0 < (1+p*x)*(1+p*y) := by positivity
  have hD1 : 1 ≤ (1+p*x)*(1+p*y) := by
    have hpx := mul_nonneg hp0 hx0
    have hpy := mul_nonneg hp0 hy0
    nlinarith [mul_nonneg hpx hpy]
  constructor
  · calc
      middleHStar p s ≤ (3/4:ℝ)*(1+s*(297/1000))^2/(1+p*(307/1000))^2 := hstar_box p s hp hs
      _ < (1+s*(263/1000))^2/(1+p*(307/1000))^2 := by
        apply div_lt_div_of_pos_right _ (by positivity)
        nlinarith [sq_nonneg s]
      _ ≤ middleH p s x y := by
        unfold middleH
        apply div_le_div₀ (by positivity) _ hD0
        · rw [pow_two]
          gcongr
        · rw [pow_two]
          gcongr
  have h630 : 0 < prefixEval [2,3] middleRho := by linarith [rho23_box.1]
  have h660 : 0 < prefixEval [1,1,3] middleRho := by linarith [rho113_box.1]
  have h690 : 0 < prefixEval [1,1,2] middleBeta := by linarith [beta112_box.1]
  have h950 : 0 < middleBeta := by linarith [beta_box.1]
  have hDA0 : 0 < (1+p*prefixEval [2,3] middleRho)*(1+p*prefixEval [1,1,3] middleRho) := by positivity
  have hDA2 : (1+p*prefixEval [2,3] middleRho)*(1+p*prefixEval [1,1,3] middleRho) < 2 := by
    have h63 : p*prefixEval [2,3] middleRho ≤ (4/5:ℝ)*(45/100) := by
      gcongr
      · exact hp.2
      · linarith [rho23_box.2]
    have h66 : p*prefixEval [1,1,3] middleRho ≤ (4/5:ℝ)*(56/100) := by
      gcongr
      · exact hp.2
      · linarith [rho113_box.2]
    calc
      _ ≤ (1+(4/5:ℝ)*(45/100))*(1+(4/5:ℝ)*(56/100)) := by gcongr
      _ < 2 := by norm_num
  have hNA : (1+s*x)*(1+s*y) ≤
      (1+s*prefixEval [1,1,2] middleBeta)*(1+s*middleBeta) := by
    gcongr
    · linarith [beta112_box.1]
    · linarith [beta_box.1]
  constructor
  · unfold middleH middleScalarA middleScalarThreshold
    rw [← mul_div_assoc]
    apply (div_lt_div_iff₀ hD0 hDA0).2
    calc
      (5/19:ℝ)*((1+s*x)*(1+s*y))*
          ((1+p*prefixEval [2,3] middleRho)*(1+p*prefixEval [1,1,3] middleRho)) <
          (5/19:ℝ)*((1+s*x)*(1+s*y))*2 := by gcongr
      _ < (549/1000:ℝ)*((1+s*x)*(1+s*y)) := by nlinarith [hN0]
      _ ≤ (549/1000:ℝ)*((1+s*prefixEval [1,1,2] middleBeta)*(1+s*middleBeta))*
          ((1+p*x)*(1+p*y)) := by
        calc
          _ ≤ (549/1000:ℝ)*((1+s*prefixEval [1,1,2] middleBeta)*(1+s*middleBeta)) := by gcongr
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hD1
  · have h20 : 0 < prefixEval [3,1,2] middleBeta := by linarith [beta312_box.1]
    have h280 : 0 < prefixEval [3] middleAlpha := by linarith [alpha3_box.1]
    have hDB0 : 0 < (1+p*prefixEval [3,1,2] middleBeta)*(1+p*prefixEval [3] middleAlpha) := by positivity
    have hNB : (1+s*x)*(1+s*y) ≤
        (1+s*prefixEval [2,3] middleRho)*(1+s*prefixEval [1,1,3] middleRho) := by
      gcongr
      · linarith [rho23_box.1]
      · linarith [rho113_box.1]
    have hb : 1+p*(307/1000:ℝ) ≤ (21/20:ℝ)*(1+p*(263/1000)) := by nlinarith [hp.2]
    have hDB : (1+p*prefixEval [3,1,2] middleBeta)*(1+p*prefixEval [3] middleAlpha) ≤
        (21/20:ℝ)^2*((1+p*x)*(1+p*y)) := by
      calc
        _ ≤ (1+p*(307/1000:ℝ))*(1+p*(307/1000:ℝ)) := by
          gcongr
          · linarith [beta312_box.2]
          · linarith [alpha3_box.2]
        _ ≤ ((21/20:ℝ)*(1+p*(263/1000)))*((21/20:ℝ)*(1+p*(263/1000))) := by gcongr
        _ ≤ ((21/20:ℝ)*(1+p*x))*((21/20:ℝ)*(1+p*y)) := by gcongr
        _ = _ := by ring
    unfold middleH middleScalarB middleScalarThreshold
    rw [← mul_div_assoc]
    apply (div_lt_div_iff₀ hD0 hDB0).2
    calc
      (5/19:ℝ)*((1+s*x)*(1+s*y))*
          ((1+p*prefixEval [3,1,2] middleBeta)*(1+p*prefixEval [3] middleAlpha)) ≤
          (5/19:ℝ)*((1+s*x)*(1+s*y))*((21/20:ℝ)^2*((1+p*x)*(1+p*y))) := by gcongr
      _ < (313/1000:ℝ)*((1+s*x)*(1+s*y))*((1+p*x)*(1+p*y)) := by
        have hpos := mul_pos hN0 hD0
        nlinarith [hpos]
      _ ≤ (313/1000:ℝ)*((1+s*prefixEval [2,3] middleRho)*(1+s*prefixEval [1,1,3] middleRho))*
          ((1+p*x)*(1+p*y)) := by gcongr

#print axioms solution
