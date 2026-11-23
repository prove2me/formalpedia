-- Prove2me | solution 1 for CatalyticTreeEval.Main.corollary_4_7_resource_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T06:32:45.529848+00:00
-- url     : https://prove2.me/submissions/804aac84-4f21-4d67-8aa8-3f1798373327

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false
set_option maxHeartbeats 400000

open CatalyticTreeEval.Main

namespace Resource47

lemma log2_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log₂ x :=
  Real.logb_nonneg (by norm_num) hx

lemma log2_self (K : ℝ) (hK : 0 < K) : exp₂ (log₂ K) = K :=
  Real.rpow_logb (by norm_num) (by norm_num) hK

lemma log2_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    log₂ (x * y) = log₂ x + log₂ y := by
  unfold log₂
  rw [Real.log_mul hx.ne' hy.ne']
  ring

lemma log2_le_log2 {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log₂ x ≤ log₂ y := by
  unfold log₂
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (Real.log_pos (by norm_num)).le

lemma log2_two_rpow (A : ℝ) : log₂ (exp₂ A) = A := by
  exact Real.logb_rpow (by norm_num) (by norm_num)

lemma exp2_nat (n : ℕ) : exp₂ (n : ℝ) = (2 : ℝ) ^ n := by
  unfold exp₂
  rw [Real.rpow_natCast]

lemma exp2_two : exp₂ (2 : ℝ) = 4 := by
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, exp2_nat]
  norm_num

lemma le_exp2_abs_log (K : ℝ) : K ≤ exp₂ |log₂ (max 1 K)| := by
  calc
    K ≤ max 1 K := le_max_right _ _
    _ = exp₂ (log₂ (max 1 K)) :=
      (log2_self _ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).symm
    _ ≤ exp₂ |log₂ (max 1 K)| := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact le_abs_self _

lemma log2_add_two_le (δ : ℝ) (hδ : 0 < δ) (l : ℕ) (hl : 1 ≤ l) :
    log₂ (l + 2) ≤ (3 + 1 / (δ * Real.log 2)) * (l : ℝ) ^ δ := by
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := lt_of_lt_of_le zero_lt_one hlR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (1 : ℝ) ≤ (l : ℝ) ^ δ := Real.one_le_rpow hlR hδ.le
  have hpow0 : (0 : ℝ) < (l : ℝ) ^ δ := Real.rpow_pos_of_pos hl0 δ
  have hlogpow := Real.log_le_sub_one_of_pos hpow0
  rw [Real.log_rpow hl0] at hlogpow
  have hlog : Real.log (l : ℝ) ≤ (l : ℝ) ^ δ / δ := by
    have hδlog : δ * Real.log (l : ℝ) ≤ (l : ℝ) ^ δ := by linarith
    exact (le_div_iff₀ hδ).2 (by nlinarith)
  have hmono : Real.log ((l : ℝ) + 2) ≤ Real.log (4 * (l : ℝ)) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  have h4 : Real.log (4 * (l : ℝ)) = 2 * Real.log 2 + Real.log (l : ℝ) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hl0.ne']
    have : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [this]
  rw [h4] at hmono
  unfold log₂
  have hmain : Real.log ((l : ℝ) + 2) / Real.log 2 ≤
      2 + ((l : ℝ) ^ δ / δ) / Real.log 2 := by
    calc
      _ ≤ (2 * Real.log 2 + (l : ℝ) ^ δ / δ) / Real.log 2 := by
        apply (div_le_div_iff_of_pos_right hlog2).2
        linarith
      _ = _ := by field_simp
  have hconst : 2 + ((l : ℝ) ^ δ / δ) / Real.log 2 ≤
      (3 + 1 / (δ * Real.log 2)) * (l : ℝ) ^ δ := by
    have hid : ((l : ℝ) ^ δ / δ) / Real.log 2 =
        (1 / (δ * Real.log 2)) * (l : ℝ) ^ δ := by
      field_simp
    rw [hid]
    nlinarith [sq_nonneg ((l : ℝ) ^ δ)]
  exact hmain.trans hconst

lemma catalyst_estimate (ε : ℝ) (hε : 0 < ε) {t : ℕ} (ht2 : 2 ≤ t)
    (htceil : (3 / ε : ℝ) ≤ t) (Cd Cc0 : ℝ) (hCd : 0 < Cd) (hCc0 : 0 < Cc0)
    {d m : ℕ} (hdNat : 0 < d) (hm1 : (1 : ℝ) ≤ m)
    (l : ℕ) (hl : 1 ≤ l)
    (hd : (d : ℝ) ≤ exp₂ (Cd * (l : ℝ) ^ (1 / (t : ℝ)) *
      (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ)))) :
    Cc0 * d * (1 + log₂ (d * m)) ≤
      exp₂ ((2 * (Cd * (3 + 1 / ((ε / 3) * Real.log 2))) +
        |log₂ (max 1 (2 * Cc0 * (1 + log₂ (m : ℝ))))|) * (l : ℝ) ^ ε) := by
  have ht0 : 0 < t := by omega
  have htR0 : (0 : ℝ) < t := by exact_mod_cast ht0
  have htmul : (3 : ℝ) ≤ ε * t := by
    have := (div_le_iff₀ hε).1 htceil
    nlinarith
  have haε : 1 / (t : ℝ) ≤ ε / 3 := by
    apply (div_le_iff₀ htR0).2
    nlinarith
  have ha2 : 1 / (t : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ htR0).2
    have ht2R : (2 : ℝ) ≤ t := by exact_mod_cast ht2
    nlinarith
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  let c : ℝ := ε / 3
  let Cpow : ℝ := 3 + 1 / (c * Real.log 2)
  let Ccat : ℝ := Cd * Cpow
  let Kcat : ℝ := 2 * Cc0 * (1 + log₂ (m : ℝ))
  let Cc : ℝ := 2 * Ccat + |log₂ (max 1 Kcat)|
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hCpow : 1 ≤ Cpow := by
    dsimp [Cpow]
    have : 0 < 1 / (c * Real.log 2) := by positivity
    linarith
  have hCcat : 0 < Ccat := mul_pos hCd (lt_of_lt_of_le zero_lt_one hCpow)
  have hl0 : (0 : ℝ) < l := lt_of_lt_of_le zero_lt_one hlR
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdNat
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  have hlogm : 0 ≤ log₂ (m : ℝ) := log2_nonneg hm1
  have hKcat : 0 < Kcat := by dsimp [Kcat]; positivity
  let a : ℝ := 1 / (t : ℝ)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hacε : a + c ≤ ε := by dsimp [a, c]; linarith
  have hL : log₂ ((l : ℝ) + 2) ≤ Cpow * (l : ℝ) ^ c := by
    exact log2_add_two_le c hc_pos l hl
  have hL0 : 0 ≤ log₂ ((l : ℝ) + 2) := log2_nonneg (by linarith)
  have hlogpow : (log₂ ((l : ℝ) + 2)) ^ (1 - a) ≤ Cpow * (l : ℝ) ^ c := by
    have h1ma : 0 ≤ 1 - a := by linarith
    calc
      _ ≤ (Cpow * (l : ℝ) ^ c) ^ (1 - a) := Real.rpow_le_rpow hL0 hL h1ma
      _ ≤ (Cpow * (l : ℝ) ^ c) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · have : (1 : ℝ) ≤ (l : ℝ) ^ c := Real.one_le_rpow hlR hc_pos.le
          nlinarith
        · linarith
      _ = Cpow * (l : ℝ) ^ c := Real.rpow_one _
  have hdexp : (d : ℝ) ≤ exp₂ (Ccat * (l : ℝ) ^ (a + c)) := by
    refine hd.trans ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc
      Cd * (l : ℝ) ^ (1 / (t : ℝ)) * (log₂ ((l : ℝ) + 2)) ^ (1 - 1 / (t : ℝ))
          ≤ Cd * (l : ℝ) ^ a * (Cpow * (l : ℝ) ^ c) := by
            change Cd * (l : ℝ) ^ a * (log₂ ((l : ℝ) + 2)) ^ (1 - a) ≤ _
            exact mul_le_mul_of_nonneg_left hlogpow
              (mul_nonneg hCd.le (Real.rpow_nonneg hl0.le _))
      _ = Ccat * (l : ℝ) ^ (a + c) := by
        dsimp [Ccat]
        rw [Real.rpow_add hl0]
        ring
  have hlogd : log₂ (d : ℝ) ≤ Ccat * (l : ℝ) ^ (a + c) := by
    have := log2_le_log2 hdpos hdexp
    rwa [log2_two_rpow] at this
  have hlogdm : log₂ ((d : ℝ) * m) = log₂ (d : ℝ) + log₂ (m : ℝ) :=
    log2_mul hdpos hmpos
  let E : ℝ := Ccat * (l : ℝ) ^ (a + c)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hmain : Cc0 * d * (1 + log₂ ((d : ℝ) * m)) ≤ Kcat * exp₂ (2 * E) := by
    have hR : (1 : ℝ) ≤ 1 + log₂ (m : ℝ) := by linarith
    have hsum : 1 + log₂ ((d : ℝ) * m) ≤ (1 + log₂ (m : ℝ)) * (E + 1) := by
      rw [hlogdm]
      dsimp [E] at hlogd ⊢
      nlinarith [mul_nonneg hlogm hE0]
    have hfactor : E + 1 ≤ 2 * exp₂ E := by
      have hadd := Real.add_one_le_exp (Real.log 2 * E)
      have hexp : Real.exp (Real.log 2 * E) = exp₂ E := by
        unfold exp₂
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [hexp] at hadd
      have hL : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have := Real.log_two_gt_d9
        norm_num at this ⊢
        linarith
      nlinarith
    calc
      Cc0 * d * (1 + log₂ ((d : ℝ) * m))
          ≤ Cc0 * exp₂ E * ((1 + log₂ (m : ℝ)) * (E + 1)) := by
            have hdE : (d : ℝ) ≤ exp₂ E := hdexp
            have hsum0 : 0 ≤ 1 + log₂ ((d : ℝ) * m) := by
              rw [hlogdm]
              have : 0 ≤ log₂ (d : ℝ) := log2_nonneg (by exact_mod_cast hdNat)
              linarith
            have h1 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ Cc0 * d)
            have h2 := mul_le_mul_of_nonneg_right hdE
              (show (0 : ℝ) ≤ Cc0 * ((1 + log₂ (m : ℝ)) * (E + 1)) by positivity)
            dsimp [E] at hdE ⊢
            nlinarith
      _ ≤ Kcat * exp₂ (2 * E) := by
        have hprod : Cc0 * exp₂ E * ((1 + log₂ (m : ℝ)) * (E + 1)) ≤
            (2 * Cc0 * (1 + log₂ (m : ℝ))) * (exp₂ E * exp₂ E) := by
          have hn : 0 ≤ Cc0 * exp₂ E * (1 + log₂ (m : ℝ)) :=
            mul_nonneg (mul_nonneg hCc0.le (Real.rpow_pos_of_pos (by norm_num) _).le)
              (by linarith)
          have h := mul_le_mul_of_nonneg_left hfactor hn
          nlinarith
        calc
          _ ≤ (2 * Cc0 * (1 + log₂ (m : ℝ))) * (exp₂ E * exp₂ E) := hprod
          _ = Kcat * exp₂ (2 * E) := by
            dsimp [Kcat]
            unfold exp₂
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            ring_nf
  have hK : Kcat ≤ exp₂ |log₂ (max 1 Kcat)| := le_exp2_abs_log Kcat
  have hlpow1 : (1 : ℝ) ≤ (l : ℝ) ^ ε := Real.one_le_rpow hlR hε.le
  have hexpcompare : 2 * E + |log₂ (max 1 Kcat)| ≤ Cc * (l : ℝ) ^ ε := by
    have hsub : (l : ℝ) ^ (a + c) ≤ (l : ℝ) ^ ε :=
      Real.rpow_le_rpow_of_exponent_le hlR hacε
    have habs : 0 ≤ |log₂ (max 1 Kcat)| := abs_nonneg _
    have habsP : |log₂ (max 1 Kcat)| ≤ |log₂ (max 1 Kcat)| * (l : ℝ) ^ ε := by
      nlinarith [mul_nonneg habs (sub_nonneg.mpr hlpow1)]
    calc
      2 * E + |log₂ (max 1 Kcat)| =
          (2 * Ccat) * (l : ℝ) ^ (a + c) + |log₂ (max 1 Kcat)| := by
        dsimp [E]
        ring
      _ ≤ (2 * Ccat) * (l : ℝ) ^ ε + |log₂ (max 1 Kcat)| :=
        add_le_add_left (mul_le_mul_of_nonneg_left hsub (by positivity)) _
      _ ≤ (2 * Ccat) * (l : ℝ) ^ ε + |log₂ (max 1 Kcat)| * (l : ℝ) ^ ε :=
        add_le_add_right habsP _
      _ = Cc * (l : ℝ) ^ ε := by dsimp [Cc]; ring
  calc
    _ ≤ Kcat * exp₂ (2 * E) := hmain
    _ ≤ exp₂ |log₂ (max 1 Kcat)| * exp₂ (2 * E) :=
      mul_le_mul_of_nonneg_right hK (Real.rpow_pos_of_pos (by norm_num) _).le
    _ = exp₂ (2 * E + |log₂ (max 1 Kcat)|) := by
      unfold exp₂
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring_nf
    _ ≤ exp₂ (Cc * (l : ℝ) ^ ε) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpcompare

lemma dimension_linear {t : ℕ} (ht2 : 2 ≤ t) (Cd : ℝ) (hCd : 0 < Cd)
    {d : ℕ} (l : ℕ) (hl : 1 ≤ l)
    (hd : (d : ℝ) ≤ exp₂ (Cd * (l : ℝ) ^ (1 / (t : ℝ)) *
      (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ)))) :
    (d : ℝ) ≤ exp₂ ((Cd * (3 + 1 / Real.log 2)) * l) := by
  have ht0 : 0 < t := by omega
  have htR0 : (0 : ℝ) < t := by exact_mod_cast ht0
  have ht2R : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  have ha1 : 1 / (t : ℝ) ≤ 1 := by
    apply (div_le_iff₀ htR0).2
    nlinarith
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  let a : ℝ := 1 / (t : ℝ)
  let C : ℝ := 3 + 1 / Real.log 2
  have hC : 1 ≤ C := by
    dsimp [C]
    have : 0 < 1 / Real.log 2 := by positivity
    linarith
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hl0 : (0 : ℝ) < l := lt_of_lt_of_le zero_lt_one hlR
  have hlog : log₂ ((l : ℝ) + 2) ≤ C * l := by
    simpa [C] using log2_add_two_le 1 (by norm_num) l hl
  have hlog0 : 0 ≤ log₂ ((l : ℝ) + 2) := log2_nonneg (by linarith)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1' : a ≤ 1 := ha1
  have h1a : 0 ≤ 1 - a := by linarith
  have hraise : (log₂ ((l : ℝ) + 2)) ^ (1 - a) ≤ C * (l : ℝ) ^ (1 - a) := by
    calc
      _ ≤ (C * (l : ℝ)) ^ (1 - a) := Real.rpow_le_rpow hlog0 hlog h1a
      _ = C ^ (1 - a) * (l : ℝ) ^ (1 - a) := by
        rw [Real.mul_rpow hC0.le hl0.le]
      _ ≤ C * (l : ℝ) ^ (1 - a) := by
        have hc : C ^ (1 - a) ≤ C := by
          calc
            C ^ (1 - a) ≤ C ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hC (by linarith)
            _ = C := Real.rpow_one _
        exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hl0.le _)
  refine hd.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  calc
    Cd * (l : ℝ) ^ (1 / (t : ℝ)) * (log₂ ((l : ℝ) + 2)) ^ (1 - 1 / (t : ℝ))
        ≤ Cd * (l : ℝ) ^ a * (C * (l : ℝ) ^ (1 - a)) := by
          change Cd * (l : ℝ) ^ a * (log₂ ((l : ℝ) + 2)) ^ (1 - a) ≤ _
          exact mul_le_mul_of_nonneg_left hraise
            (mul_nonneg hCd.le (Real.rpow_nonneg hl0.le _))
    _ = Cd * C * ((l : ℝ) ^ a * (l : ℝ) ^ (1 - a)) := by ring
    _ = Cd * C * (l : ℝ) ^ (a + (1 - a)) := by rw [Real.rpow_add hl0]
    _ = (Cd * C) * l := by rw [show a + (1 - a) = 1 by ring, Real.rpow_one]
    _ = (Cd * (3 + 1 / Real.log 2)) * l := by rfl

end Resource47

open Resource47

theorem solution
    (ε : ℝ) (hε : 0 < ε) {t : ℕ} (p : Fin t → ℕ) (hp : OddPrimeData p)
    (ht : t = max 2 ⌈3 / ε⌉₊)
    (F : List Bool → Frame) (k : ℕ) (Cd Csl : ℝ)
    (hCd : 0 < Cd) (hCsl : 0 < Csl)
    (hk : k ≤ 3 ^ t)
    (hF : ∀ l : ℕ, 1 ≤ l →
      (F (natCode l)).m = modulus p ∧
      (F (natCode l)).l = l ∧
      (F (natCode l)).k = k ∧
      ((F (natCode l)).d : ℝ) ≤ exp₂ (Cd * (l : ℝ) ^ (1 / (t : ℝ)) *
        (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ))) ∧
      ((F (natCode l)).s : ℝ) ≤ Csl * l)
    (Cs0 Cc0 Ct0 B Cw Ctw : ℝ) (q0 qw : ℕ)
    (hCs0 : 0 < Cs0) (hCc0 : 0 < Cc0) (hCt0 : 0 < Ct0) (hB : 0 < B)
    (hCw : 0 < Cw) (hCtw : 0 < Ctw) (hq0 : 0 < q0) (hqw : 0 < qw) :
    ∃ (Cs Cc Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 0 < q ∧
      ∀ h l : ℕ, 0 < h → 0 < l →
      let a := natCode l
      Cw * (Cs0 * ((F a).l + h * (lg (F a).k + log₂ (F a).m) + (F a).s) +
          (F a).s + 1) ≤ Cs * (l + h : ℝ) ∧
      Cc0 * (F a).d * (1 + log₂ ((F a).d * (F a).m)) ≤
        exp₂ (Cc * (l : ℝ) ^ ε) ∧
      Ctw * (Ct0 * (B * (F a).k) ^ h *
          ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q0 + 1) *
          ((2 : ℝ) ^ (F a).s + 1) ^ qw ≤
        Ct * (2 : ℝ) ^ (q * (l + h)) := by
  have hm0 : 0 < modulus p := by
    apply Finset.prod_pos
    intro i hi
    exact (hp.1.2.1 i).pos
  have hm1 : (1 : ℝ) ≤ modulus p := by exact_mod_cast hm0
  have ht2 : 2 ≤ t := by rw [ht]; exact le_max_left _ _
  have htceil : (3 / ε : ℝ) ≤ t := by
    calc
      (3 / ε : ℝ) ≤ (⌈3 / ε⌉₊ : ℕ) := Nat.le_ceil _
      _ ≤ t := by
        exact_mod_cast (show ⌈3 / ε⌉₊ ≤ t by rw [ht]; exact le_max_right _ _)
  let G : ℝ := |lg k + log₂ (modulus p)|
  let Cs : ℝ := Cw * (Cs0 * (1 + G + Csl) + Csl + 1)
  let Cc : ℝ := 2 * (Cd * (3 + 1 / ((ε / 3) * Real.log 2))) +
    |log₂ (max 1 (2 * Cc0 * (1 + log₂ (modulus p))))|
  let R : ℝ := max 1 (B * k)
  let Kd : ℝ := |log₂ (max 1 (k : ℝ))|
  let Dtime : ℝ := Cd * (3 + 1 / Real.log 2)
  let Etime : ℝ := 1 + Kd + Dtime + Csl
  let Ktime : ℝ := Ctw * (Ct0 + 1)
  let J : ℝ := |log₂ (max 1 Ktime)|
  let Q : ℝ := J + log₂ R + Etime * q0 + 2 * q0 + Csl * qw + qw + 1
  let q : ℕ := ⌈Q⌉₊
  have hG : 0 ≤ G := abs_nonneg _
  have hCs : 0 < Cs := by dsimp [Cs]; positivity
  have hCc : 0 < Cc := by dsimp [Cc]; positivity
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlogR : 0 ≤ log₂ R := log2_nonneg hR
  have hKd : 0 ≤ Kd := abs_nonneg _
  have hDtime : 0 < Dtime := by dsimp [Dtime]; positivity
  have hEtime : 1 ≤ Etime := by
    dsimp [Etime]
    linarith [hKd, hDtime.le, hCsl.le]
  have hKtime : 0 < Ktime := by dsimp [Ktime]; positivity
  have hJ : 0 ≤ J := abs_nonneg _
  have hQ : 0 < Q := by
    dsimp [Q]
    have hq0R : (0 : ℝ) ≤ q0 := by positivity
    have hqwR : (0 : ℝ) ≤ qw := by positivity
    positivity
  have hq : 0 < q := Nat.ceil_pos.mpr hQ
  refine ⟨Cs, Cc, 1, q, hCs, hCc, by norm_num, hq, ?_⟩
  intro h l hh hl
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl0 : (0 : ℝ) < l := lt_of_lt_of_le zero_lt_one hlR
  have hh0 : (0 : ℝ) < h := lt_of_lt_of_le zero_lt_one hhR
  have hlhs : (1 : ℝ) ≤ l + h := by linarith
  obtain ⟨hm, hlf, hkf, hd, hs⟩ := hF l hl
  dsimp only
  rw [hm, hlf, hkf]
  let d : ℝ := (F (natCode l)).d
  let s : ℝ := (F (natCode l)).s
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hfree : Cw * (Cs0 * (l + h * (lg k + log₂ (modulus p)) + s) + s + 1) ≤
      Cs * (l + h) := by
    have hG' : lg k + log₂ (modulus p) ≤ G := le_abs_self _
    have hmul : h * (lg k + log₂ (modulus p)) ≤ G * (l + h) := by
      have hmul0 : (h : ℝ) * (lg k + log₂ (modulus p)) ≤ G * h := by
        have hn := mul_nonneg (sub_nonneg.mpr hG') hh0.le
        nlinarith only [hn]
      calc
        _ ≤ G * h := hmul0
        _ ≤ G * (l + h) := by
          have hn := mul_nonneg hG hl0.le
          nlinarith only [hn]
    have hmul' := mul_le_mul_of_nonneg_left hmul hCs0.le
    have hs' : Cs0 * s ≤ Cs0 * Csl * (l + h) := by
      have h1 := mul_le_mul_of_nonneg_left hs hCs0.le
      have h2 : Cs0 * (Csl * l) ≤ Cs0 * Csl * (l + h) := by
        have hn := mul_nonneg (mul_nonneg hCs0.le hCsl.le) hh0.le
        nlinarith only [hn]
      exact h1.trans h2
    have hs'' : s ≤ Csl * (l + h) := by
      have hn := mul_nonneg hCsl.le hh0.le
      nlinarith only [hs, hn]
    have hl' : l ≤ (l + h : ℝ) := by linarith only [hh0]
    have hl'0 := mul_le_mul_of_nonneg_left hl' hCs0.le
    have hinside : Cs0 * (l + h * (lg k + log₂ (modulus p)) + s) + s + 1 ≤
        (Cs0 * (1 + G + Csl) + Csl + 1) * (l + h) := by
      nlinarith only [hmul', hs', hs'', hl'0, hlhs]
    calc
      _ ≤ Cw * ((Cs0 * (1 + G + Csl) + Csl + 1) * (l + h)) :=
        mul_le_mul_of_nonneg_left hinside hCw.le
      _ = Cs * (l + h) := by dsimp [Cs]; ring
  refine ⟨hfree, ?_, ?_⟩
  · by_cases hdz : (F (natCode l)).d = 0
    · simp only [hdz, Nat.cast_zero, mul_zero, zero_mul]
      exact (Real.rpow_pos_of_pos (by norm_num) _).le
    · exact catalyst_estimate ε hε ht2 htceil Cd Cc0 hCd hCc0
        (Nat.pos_of_ne_zero hdz) hm1 l hl hd
  · have hdlin : d ≤ exp₂ (Dtime * l) := by
      exact dimension_linear ht2 Cd hCd l hl hd
    have hEl : Etime ≤ Etime * (l : ℝ) := by
      have hn := mul_nonneg (zero_le_one.trans hEtime)
        (by linarith : (0 : ℝ) ≤ (l : ℝ) - 1)
      nlinarith only [hn]
    have hlE : (l : ℝ) ≤ Etime * l := by
      calc
        (l : ℝ) = 1 * l := by ring
        _ ≤ Etime * l := mul_le_mul_of_nonneg_right hEtime hl0.le
    have h2l : (2 : ℝ) ^ l ≤ exp₂ (Etime * l) := by
      rw [← exp2_nat]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlE
    have hkexp : (k : ℝ) ≤ exp₂ (Etime * l) := by
      calc
        (k : ℝ) ≤ exp₂ Kd := le_exp2_abs_log _
        _ ≤ exp₂ (Etime * l) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hle : Kd ≤ Etime := by
            dsimp [Etime]
            linarith [hKd, hDtime.le, hCsl.le]
          exact hle.trans hEl
    have hde : d ≤ exp₂ (Etime * l) := by
      refine hdlin.trans ?_
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hle : Dtime ≤ Etime := by
        dsimp [Etime]
        linarith [hKd, hDtime.le, hCsl.le]
      exact mul_le_mul_of_nonneg_right hle hl0.le
    have h2s : (2 : ℝ) ^ (F (natCode l)).s ≤ exp₂ (Etime * l) := by
      calc
        (2 : ℝ) ^ (F (natCode l)).s = exp₂ s := (exp2_nat _).symm
        _ ≤ exp₂ (Csl * l) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
        _ ≤ exp₂ (Etime * l) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hle : Csl ≤ Etime := by
            dsimp [Etime]
            linarith [hKd, hDtime.le, hCsl.le]
          exact mul_le_mul_of_nonneg_right hle hl0.le
    have hX : (2 : ℝ) ^ l + k + d + (2 : ℝ) ^ (F (natCode l)).s ≤
        exp₂ (Etime * l + 2) := by
      have hsum : (2 : ℝ) ^ l + k + d + (2 : ℝ) ^ (F (natCode l)).s ≤
          4 * exp₂ (Etime * l) := by linarith
      calc
        _ ≤ 4 * exp₂ (Etime * l) := hsum
        _ = exp₂ (Etime * l + 2) := by
          rw [← exp2_two]
          unfold exp₂
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          ring_nf
    have hY : (2 : ℝ) ^ (F (natCode l)).s + 1 ≤ exp₂ (Csl * l + 1) := by
      have he : (1 : ℝ) ≤ exp₂ (Csl * l) := by
        apply Real.one_le_rpow (by norm_num)
        positivity
      have hs' : (2 : ℝ) ^ (F (natCode l)).s ≤ exp₂ (Csl * l) := by
        calc
          _ = exp₂ s := (exp2_nat _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      calc
        _ ≤ 2 * exp₂ (Csl * l) := by linarith
        _ = exp₂ (Csl * l + 1) := by
          have he1 : exp₂ (1 : ℝ) = 2 := by
            rw [show (1 : ℝ) = (1 : ℕ) by norm_num, exp2_nat]
            norm_num
          rw [← he1]
          unfold exp₂
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          ring_nf
    have hRpow : (B * k : ℝ) ^ h ≤ exp₂ (log₂ R * h) := by
      calc
        (B * k : ℝ) ^ h ≤ R ^ h := by
          apply pow_le_pow_left₀ (by positivity)
          exact le_max_right _ _
        _ = R ^ (h : ℝ) := (Real.rpow_natCast _ _).symm
        _ = exp₂ (log₂ R) ^ (h : ℝ) := by rw [log2_self R hR0]
        _ = exp₂ (log₂ R * h) := by
          unfold exp₂
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hX0 : 0 ≤ (2 : ℝ) ^ l + k + d + (2 : ℝ) ^ (F (natCode l)).s := by
      dsimp [d]
      positivity
    have hXpow : ((2 : ℝ) ^ l + k + d + (2 : ℝ) ^ (F (natCode l)).s) ^ q0 ≤
        exp₂ ((Etime * l + 2) * q0) := by
      calc
        _ ≤ exp₂ (Etime * l + 2) ^ q0 := pow_le_pow_left₀ hX0 hX _
        _ = exp₂ (Etime * l + 2) ^ (q0 : ℝ) := (Real.rpow_natCast _ _).symm
        _ = exp₂ ((Etime * l + 2) * q0) := by
          unfold exp₂
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hYpow : ((2 : ℝ) ^ (F (natCode l)).s + 1) ^ qw ≤
        exp₂ ((Csl * l + 1) * qw) := by
      have hbase : 0 ≤ (2 : ℝ) ^ (F (natCode l)).s + 1 := by
        have hp := pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (F (natCode l)).s
        linarith only [hp]
      calc
        _ ≤ exp₂ (Csl * l + 1) ^ qw := pow_le_pow_left₀ hbase hY _
        _ = exp₂ (Csl * l + 1) ^ (qw : ℝ) := (Real.rpow_natCast _ _).symm
        _ = exp₂ ((Csl * l + 1) * qw) := by
          unfold exp₂
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hZ : (B * k : ℝ) ^ h *
        ((2 : ℝ) ^ l + k + d + (2 : ℝ) ^ (F (natCode l)).s) ^ q0 ≤
        exp₂ (log₂ R * h + (Etime * l + 2) * q0) := by
      calc
        _ ≤ exp₂ (log₂ R * h) * exp₂ ((Etime * l + 2) * q0) :=
          mul_le_mul hRpow hXpow (pow_nonneg hX0 _)
            (Real.rpow_pos_of_pos (by norm_num) _).le
        _ = _ := by
          unfold exp₂
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hadd : Ct0 * ((B * k : ℝ) ^ h *
        ((2 : ℝ) ^ l + k + d + (2 : ℝ) ^ (F (natCode l)).s) ^ q0) + 1 ≤
        (Ct0 + 1) * exp₂ (log₂ R * h + (Etime * l + 2) * q0) := by
      have he : (1 : ℝ) ≤ exp₂ (log₂ R * h + (Etime * l + 2) * q0) := by
        apply Real.one_le_rpow (by norm_num)
        positivity
      have hz := mul_le_mul_of_nonneg_left hZ hCt0.le
      nlinarith only [hz, he]
    have hmain : Ctw * (Ct0 * (B * k) ^ h *
        ((2 : ℝ) ^ l + k + d + (2 : ℝ) ^ (F (natCode l)).s) ^ q0 + 1) *
        ((2 : ℝ) ^ (F (natCode l)).s + 1) ^ qw ≤
        Ktime * exp₂ (log₂ R * h + (Etime * l + 2) * q0 + (Csl * l + 1) * qw) := by
      calc
        _ ≤ Ctw * ((Ct0 + 1) * exp₂ (log₂ R * h + (Etime * l + 2) * q0)) *
            exp₂ ((Csl * l + 1) * qw) := by
          have hadd' : Ctw * (Ct0 * (B * k : ℝ) ^ h *
              ((2 : ℝ) ^ l + k + d + (2 : ℝ) ^ (F (natCode l)).s) ^ q0 + 1) ≤
              Ctw * ((Ct0 + 1) * exp₂ (log₂ R * h + (Etime * l + 2) * q0)) := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hadd hCtw.le
          have hn : 0 ≤ Ctw * ((Ct0 + 1) *
              exp₂ (log₂ R * h + (Etime * l + 2) * q0)) :=
            mul_nonneg hCtw.le (mul_nonneg (by linarith)
              (Real.rpow_pos_of_pos (by norm_num) _).le)
          have hYbase : 0 ≤ (2 : ℝ) ^ (F (natCode l)).s + 1 := by
            have hp := pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (F (natCode l)).s
            linarith only [hp]
          have hYn : 0 ≤ ((2 : ℝ) ^ (F (natCode l)).s + 1) ^ qw :=
            pow_nonneg hYbase _
          exact mul_le_mul hadd' hYpow hYn hn
        _ = Ktime * exp₂ (log₂ R * h + (Etime * l + 2) * q0 + (Csl * l + 1) * qw) := by
          have hexp : exp₂ (log₂ R * h + (Etime * l + 2) * q0) *
              exp₂ ((Csl * l + 1) * qw) =
              exp₂ (log₂ R * h + (Etime * l + 2) * q0 + (Csl * l + 1) * qw) := by
            unfold exp₂
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          calc
            _ = Ktime * (exp₂ (log₂ R * h + (Etime * l + 2) * q0) *
                exp₂ ((Csl * l + 1) * qw)) := by dsimp [Ktime]; ring
            _ = _ := by rw [hexp]
    have hJexp : Ktime ≤ exp₂ J := le_exp2_abs_log _
    have hexponent : J + (log₂ R * h + (Etime * l + 2) * q0 +
        (Csl * l + 1) * qw) ≤ Q * (l + h) := by
      have h1 : J ≤ J * (l + h) := by
        nlinarith only [mul_nonneg hJ (by linarith : (0 : ℝ) ≤ (l + h : ℝ) - 1)]
      have h2 : log₂ R * h ≤ log₂ R * (l + h) := by
        nlinarith only [mul_nonneg hlogR hl0.le]
      have h3 : (Etime * l + 2) * q0 ≤ (Etime * q0 + 2 * q0) * (l + h) := by
        have hq0R : (0 : ℝ) ≤ q0 := by positivity
        have hn1 := mul_nonneg (mul_nonneg (zero_le_one.trans hEtime) hq0R) hh0.le
        have hn2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq0R)
          (by linarith : (0 : ℝ) ≤ (l + h : ℝ) - 1)
        nlinarith only [hn1, hn2]
      have h4 : (Csl * l + 1) * qw ≤ (Csl * qw + qw) * (l + h) := by
        have hqwR : (0 : ℝ) ≤ qw := by positivity
        have hn1 := mul_nonneg (mul_nonneg hCsl.le hqwR) hh0.le
        have hn2 := mul_nonneg hqwR (by linarith : (0 : ℝ) ≤ (l + h : ℝ) - 1)
        nlinarith only [hn1, hn2]
      calc
        _ ≤ (J + log₂ R + (Etime * q0 + 2 * q0) + (Csl * qw + qw) + 1) * (l + h) := by
          nlinarith only [h1, h2, h3, h4, hlhs]
        _ = Q * (l + h) := by dsimp [Q]; ring
    calc
      _ ≤ Ktime * exp₂ (log₂ R * h + (Etime * l + 2) * q0 + (Csl * l + 1) * qw) := hmain
      _ ≤ exp₂ J * exp₂ (log₂ R * h + (Etime * l + 2) * q0 + (Csl * l + 1) * qw) :=
        mul_le_mul_of_nonneg_right hJexp (Real.rpow_pos_of_pos (by norm_num) _).le
      _ = exp₂ (J + (log₂ R * h + (Etime * l + 2) * q0 + (Csl * l + 1) * qw)) := by
        unfold exp₂
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ exp₂ (Q * (l + h)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
      _ ≤ exp₂ ((q : ℝ) * (l + h)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hceil : Q ≤ (q : ℝ) := Nat.le_ceil Q
        have hn := mul_nonneg (sub_nonneg.mpr hceil)
          (show (0 : ℝ) ≤ (l + h : ℝ) by positivity)
        nlinarith only [hn]
      _ = 1 * (2 : ℝ) ^ (q * (l + h)) := by
        rw [show (q : ℝ) * (l + h : ℝ) = ((q * (l + h) : ℕ) : ℝ) by norm_num,
          exp2_nat]
        ring
