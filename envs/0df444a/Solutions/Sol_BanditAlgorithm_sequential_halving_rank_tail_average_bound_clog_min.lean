-- Prove2me | solution 1 for BanditAlgorithm.sequential_halving_rank_tail_average_bound_clog_min
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T18:15:05.60837+00:00
-- url     : https://prove2.me/submissions/f9e10eb9-b38b-4448-9d0c-a348bd5e42f1

import Definitions.Def_SequentialHalving
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory

namespace BanditAlgorithm

private lemma exp_le_eleven_tenths_mul_one_add {z : ℝ}
    (hz0 : 0 ≤ z) (hzhalf : z ≤ 1 / 2) :
    Real.exp z ≤ (11 / 10 : ℝ) * (1 + z) := by
  have he := Real.exp_bound' hz0 (by linarith : z ≤ 1) (n := 4) (by omega)
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hz2 : z ^ 2 ≤ z / 2 := by nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hzhalf)]
  have hz3 : z ^ 3 ≤ z / 4 := by
    have hstep : z ^ 3 ≤ z ^ 2 / 2 := by
      nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hzhalf)]
    nlinarith
  have hz4 : z ^ 4 ≤ z / 8 := by
    have hz3nonneg : 0 ≤ z ^ 3 := by positivity
    have hstep : z ^ 4 ≤ z ^ 3 / 2 := by
      nlinarith [mul_nonneg hz3nonneg (sub_nonneg.mpr hzhalf)]
    nlinarith
  nlinarith

private lemma exp_le_three_mul_self_of_one_le_of_le_three_halves {y : ℝ}
    (hy1 : 1 ≤ y) (hy : y ≤ 3 / 2) : Real.exp y ≤ 3 * y := by
  let z := y - 1
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hzhalf : z ≤ 1 / 2 := by dsimp [z]; linarith
  have hzexp := exp_le_eleven_tenths_mul_one_add hz0 hzhalf
  have he1 : Real.exp 1 < (30 / 11 : ℝ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  rw [show y = 1 + z by dsimp [z]; ring, Real.exp_add]
  have hcoef : Real.exp 1 * (11 / 10 : ℝ) < 3 := by nlinarith
  calc
    Real.exp 1 * Real.exp z ≤ Real.exp 1 * ((11 / 10 : ℝ) * (1 + z)) :=
      mul_le_mul_of_nonneg_left hzexp (Real.exp_pos 1).le
    _ = (Real.exp 1 * (11 / 10 : ℝ)) * (1 + z) := by ring
    _ ≤ 3 * (1 + z) := by
      have hzone : 0 ≤ 1 + z := by linarith
      exact mul_le_mul_of_nonneg_right hcoef.le hzone

private lemma ceil_inverse_exp_factor_le_three {b : ℝ} (hb : 0 < b) :
    let s := Nat.ceil (1 / b)
    Real.exp (b * ((s : ℝ) - 1)) ≤
      3 * (s : ℝ) * (1 - Real.exp (-b)) := by
  let s := Nat.ceil (1 / b)
  have hinvpos : 0 < 1 / b := by positivity
  have hspos : 0 < s := Nat.ceil_pos.mpr hinvpos
  have hceil_lower : 1 / b ≤ (s : ℝ) := Nat.le_ceil _
  have hceil_upper : (s : ℝ) < 1 / b + 1 := Nat.ceil_lt_add_one hinvpos.le
  have hys_lower : 1 ≤ b * (s : ℝ) := by
    have h := (div_le_iff₀ hb).mp (show (1 : ℝ) / b ≤ (s : ℝ) by
      simpa only [one_div] using hceil_lower)
    nlinarith
  have hys_upper : b * (s : ℝ) < 1 + b := by
    have := mul_lt_mul_of_pos_left hceil_upper hb
    field_simp at this
    nlinarith
  have hs_pred_lt : ((s - 1 : ℕ) : ℝ) < 1 / b := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hspos))]
    have hnat : s - 1 < s := Nat.sub_lt (Nat.zero_lt_of_lt hspos) (by omega)
    have := (Nat.lt_ceil).mp (show s - 1 < Nat.ceil (1 / b) by simpa [s] using hnat)
    simpa [Nat.cast_sub (by omega : 1 ≤ s)] using this
  have hmain : Real.exp (b * (s : ℝ)) ≤
      3 * (s : ℝ) * (Real.exp b - 1) := by
    rcases lt_trichotomy s 2 with hslt | hseq | hsgt
    · have hs1 : s = 1 := by omega
      simp only [hs1, Nat.cast_one] at hceil_lower hys_lower hys_upper ⊢
      have hb1 : 1 ≤ b := by
        have := (div_le_iff₀ hb).mp (show (1 : ℝ) / b ≤ 1 by
          simpa only [one_div] using hceil_lower)
        nlinarith
      have he : 2 ≤ Real.exp b := by
        calc
          2 ≤ 1 + b := by linarith
          _ ≤ Real.exp b := by simpa [add_comm] using Real.add_one_le_exp b
      simpa only [mul_one] using (show Real.exp b ≤ 3 * (Real.exp b - 1) by linarith)
    · simp only [hseq, Nat.cast_ofNat] at hceil_lower hys_lower hys_upper hs_pred_lt ⊢
      have hbhalf : (1 / 2 : ℝ) ≤ b := by
        have := (div_le_iff₀ hb).mp (show (1 : ℝ) / b ≤ 2 by
          simpa only [one_div] using hceil_lower)
        nlinarith
      have hb1 : b < 1 := by
        have := (lt_div_iff₀ hb).mp (show (1 : ℝ) < 1 / b by
          norm_num at hs_pred_lt ⊢
          simpa only [one_div] using hs_pred_lt)
        nlinarith
      have hzlow : (3 / 2 : ℝ) ≤ Real.exp b := by
        calc
          (3 / 2 : ℝ) ≤ 1 + b := by linarith
          _ ≤ Real.exp b := by simpa [add_comm] using Real.add_one_le_exp b
      have hzhigh : Real.exp b < 3 := by
        exact (Real.exp_lt_exp.mpr hb1).trans Real.exp_one_lt_three
      rw [show b * (2 : ℝ) = b + b by ring, Real.exp_add]
      nlinarith [mul_nonneg (sub_nonneg.mpr hzlow)
        (sub_nonneg.mpr (le_of_lt hzhigh))]
    · have hs3 : 3 ≤ s := by omega
      have hsminuspos : (0 : ℝ) < (s : ℝ) - 1 := by
        have hsR : (1 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 1 < s)
        linarith
      have hbpred : b * ((s : ℝ) - 1) < 1 := by
        have := mul_lt_mul_of_pos_left hs_pred_lt hb
        field_simp at this
        simpa [Nat.cast_sub (by omega : 1 ≤ s)] using this
      have hratio : (s : ℝ) / ((s : ℝ) - 1) ≤ 3 / 2 := by
        apply (div_le_iff₀ hsminuspos).2
        have hs3R : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs3
        nlinarith
      have hys : b * (s : ℝ) ≤ 3 / 2 := by
        have hbdiv : b < 1 / ((s : ℝ) - 1) := by
          exact (lt_div_iff₀ hsminuspos).2 hbpred
        calc
          b * (s : ℝ) ≤ (1 / ((s : ℝ) - 1)) * (s : ℝ) := by
            exact mul_le_mul_of_nonneg_right hbdiv.le (Nat.cast_nonneg _)
          _ = (s : ℝ) / ((s : ℝ) - 1) := by ring
          _ ≤ 3 / 2 := hratio
      have hexp := exp_le_three_mul_self_of_one_le_of_le_three_halves
        hys_lower hys
      have hlinear : b * (s : ℝ) ≤ (s : ℝ) * (Real.exp b - 1) := by
        have := Real.add_one_le_exp b
        have hsnonneg : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
        nlinarith
      exact hexp.trans (by nlinarith)
  have heq : Real.exp (b * ((s : ℝ) - 1)) * Real.exp b =
      Real.exp (b * (s : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpos : 0 < Real.exp b := Real.exp_pos b
  have hmul : Real.exp (b * ((s : ℝ) - 1)) * Real.exp b ≤
      (3 * (s : ℝ) * (1 - Real.exp (-b))) * Real.exp b := by
    rw [heq]
    calc
      Real.exp (b * (s : ℝ)) ≤ 3 * (s : ℝ) * (Real.exp b - 1) := hmain
      _ = (3 * (s : ℝ) * (1 - Real.exp (-b))) * Real.exp b := by
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
  exact le_of_mul_le_mul_right hmul hpos

private lemma fin_exp_rank_tail_le_geometric (k threshold : ℕ) (b : ℝ)
    (hb : 0 < b) (hthreshold : threshold ≤ k) :
    (∑ i : Fin k,
      if threshold ≤ (i : ℕ) then Real.exp (-b * (((i : ℕ) + 1 : ℕ) : ℝ)) else 0) ≤
      Real.exp (-b * ((threshold + 1 : ℕ) : ℝ)) / (1 - Real.exp (-b)) := by
  change (∑ i : Fin k,
      (fun r : ℕ ↦ if threshold ≤ r then Real.exp (-b * (((r + 1 : ℕ) : ℝ))) else 0)
        (i : ℕ)) ≤ _
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ ↦ if threshold ≤ r then Real.exp (-b * (((r + 1 : ℕ) : ℝ))) else 0) k]
  have hfilter :
      (∑ i ∈ Finset.range k,
          if threshold ≤ i then Real.exp (-b * (((i : ℕ) + 1 : ℕ) : ℝ)) else 0) =
        ∑ i ∈ Finset.Ico threshold k,
          Real.exp (-b * (((i : ℕ) + 1 : ℕ) : ℝ)) := by
    rw [← Finset.sum_filter
      (s := Finset.range k) (p := fun i : ℕ ↦ threshold ≤ i)
      (f := fun i : ℕ ↦ Real.exp (-b * (((i : ℕ) + 1 : ℕ) : ℝ)))]
    congr 1
    ext i
    simp [Finset.mem_Ico, and_comm]
  rw [hfilter, Finset.sum_Ico_eq_sum_range]
  let z := Real.exp (-b)
  let A := Real.exp (-b * ((threshold + 1 : ℕ) : ℝ))
  have hzpos : 0 < z := Real.exp_pos _
  have hzlt : z < 1 := by
    dsimp [z]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hznorm : ‖z‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hzpos]; exact hzlt
  have hzsum : Summable (fun r : ℕ ↦ z ^ r) :=
    summable_geometric_of_norm_lt_one hznorm
  have hterm (r : ℕ) :
      Real.exp (-b * (((threshold + r : ℕ) + 1 : ℕ) : ℝ)) = A * z ^ r := by
    rw [← Real.exp_nat_mul]
    dsimp [A, z]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  calc
    (∑ r ∈ Finset.range (k - threshold),
        Real.exp (-b * (((threshold + r : ℕ) + 1 : ℕ) : ℝ))) =
        ∑ r ∈ Finset.range (k - threshold), A * z ^ r := by
          apply Finset.sum_congr rfl
          intro r _hr
          exact hterm r
    _ ≤ ∑' r : ℕ, A * z ^ r :=
      (hzsum.mul_left A).sum_le_tsum _ (fun _ _ ↦ by positivity)
    _ = A * (1 - z)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hznorm]
    _ = Real.exp (-b * ((threshold + 1 : ℕ) : ℝ)) /
        (1 - Real.exp (-b)) := by simp [A, z, div_eq_mul_inv]

private lemma fin_exp_rank_tail_has_good_cutoff
    (k q : ℕ) (hq : 0 < q) (hqk : q ≤ k) (b : ℝ) (hb : 0 < b)
    (hlarge : 1 < b * (q : ℝ)) :
    ∃ threshold : ℕ, threshold < q ∧
      (∑ i : Fin k,
        if threshold ≤ (i : ℕ) then
          Real.exp (-b * (((i : ℕ) + 1 : ℕ) : ℝ)) else 0) /
          ((q - threshold : ℕ) : ℝ) ≤
        3 * Real.exp (-b * (q : ℝ)) := by
  let s := Nat.ceil (1 / b)
  let threshold := q - s
  have hinvlt : 1 / b < (q : ℝ) := by
    apply (div_lt_iff₀ hb).2
    nlinarith
  have hspos : 0 < s := Nat.ceil_pos.mpr (by positivity : (0 : ℝ) < 1 / b)
  have hsq : s ≤ q := by
    exact Nat.ceil_le.mpr hinvlt.le
  have htlt : threshold < q := by dsimp [threshold]; omega
  have htq : threshold ≤ q := Nat.le_of_lt htlt
  have htk : threshold ≤ k := htq.trans hqk
  refine ⟨threshold, htlt, ?_⟩
  have hden : q - threshold = s := by dsimp [threshold]; omega
  rw [hden]
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
  have hD : 0 < 1 - Real.exp (-b) := sub_pos.mpr <|
    Real.exp_lt_one_iff.mpr (by linarith)
  have htail := fin_exp_rank_tail_le_geometric k threshold b hb htk
  have hfactor := ceil_inverse_exp_factor_le_three (b := b) hb
  dsimp [s] at hfactor
  have hindex : ((threshold + 1 : ℕ) : ℝ) =
      (q : ℝ) - (s : ℝ) + 1 := by
    dsimp [threshold]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hsq]
  have hAeq : Real.exp (-b * ((threshold + 1 : ℕ) : ℝ)) =
      Real.exp (-b * (q : ℝ)) * Real.exp (b * ((s : ℝ) - 1)) := by
    rw [hindex, ← Real.exp_add]
    congr 1
    ring
  have hnum : Real.exp (-b * ((threshold + 1 : ℕ) : ℝ)) ≤
      (3 * Real.exp (-b * (q : ℝ)) * (s : ℝ)) * (1 - Real.exp (-b)) := by
    rw [hAeq]
    have hE : 0 ≤ Real.exp (-b * (q : ℝ)) := Real.exp_pos _ |>.le
    nlinarith [mul_le_mul_of_nonneg_left hfactor hE]
  have hquot : Real.exp (-b * ((threshold + 1 : ℕ) : ℝ)) /
        (1 - Real.exp (-b)) ≤
      3 * Real.exp (-b * (q : ℝ)) * (s : ℝ) := by
    exact (div_le_iff₀ hD).2 (by simpa [mul_assoc] using hnum)
  calc
    (∑ i : Fin k,
        if threshold ≤ (i : ℕ) then
          Real.exp (-b * (((i : ℕ) + 1 : ℕ) : ℝ)) else 0) / (s : ℝ) ≤
        (Real.exp (-b * ((threshold + 1 : ℕ) : ℝ)) /
          (1 - Real.exp (-b))) / (s : ℝ) := div_le_div_of_nonneg_right htail hsR.le
    _ ≤ (3 * Real.exp (-b * (q : ℝ)) * (s : ℝ)) / (s : ℝ) :=
      div_le_div_of_nonneg_right hquot hsR.le
    _ = 3 * Real.exp (-b * (q : ℝ)) := by field_simp

private lemma seqHalvingCount_le' (k s : ℕ) : seqHalvingCount k s ≤ k := by
  induction s with
  | zero => simp [seqHalvingCount]
  | succ s ih =>
      rw [seqHalvingCount]
      omega

private lemma seqHalvingCount_pos' (k s : ℕ) (hk : 0 < k) :
    0 < seqHalvingCount k s := by
  induction s with
  | zero => simpa [seqHalvingCount]
  | succ s ih =>
      rw [seqHalvingCount]
      exact Nat.div_pos (by omega) (by omega)

private lemma seqHalving_budget_le_four_phase_mass
    {k n ℓ : ℕ} (hn : k * Nat.clog 2 k ≤ n)
    (hℓ : ℓ < Nat.clog 2 k) :
    n ≤ 4 * Nat.clog 2 k * seqHalvingPulls k n ℓ *
      seqHalvingCount k (ℓ + 1) := by
  let L := Nat.clog 2 k
  let m := seqHalvingCount k ℓ
  let q := seqHalvingCount k (ℓ + 1)
  let u := seqHalvingPulls k n ℓ
  have hL : 0 < L := Nat.zero_lt_of_lt hℓ
  have hk : 0 < k := by
    have hp := Nat.pow_lt_of_lt_clog hℓ
    have hp0 : 0 < 2 ^ ℓ := pow_pos (by decide) _
    omega
  have hm : 0 < m := seqHalvingCount_pos' k ℓ hk
  have hdenpos : 0 < L * m := Nat.mul_pos hL hm
  have hdenle : L * m ≤ n := by
    calc
      L * m ≤ L * k := Nat.mul_le_mul_left _ (seqHalvingCount_le' k ℓ)
      _ = k * L := Nat.mul_comm _ _
      _ ≤ n := hn
  have hu : 0 < u := by
    dsimp [u, seqHalvingPulls]
    exact Nat.div_pos hdenle hdenpos
  have hnlt : n < (L * m) * (u + 1) := by
    simpa [u, seqHalvingPulls] using Nat.lt_mul_div_succ n hdenpos
  have hmq : m ≤ 2 * q := by
    dsimp [q]
    rw [seqHalvingCount]
    omega
  have hu2 : u + 1 ≤ 2 * u := by omega
  calc
    n ≤ (L * m) * (u + 1) := Nat.le_of_lt hnlt
    _ ≤ (L * m) * (2 * u) := Nat.mul_le_mul_left _ hu2
    _ = (2 * L * u) * m := by ring
    _ ≤ (2 * L * u) * (2 * q) := Nat.mul_le_mul_left _ hmq
    _ = 4 * L * u * q := by ring

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k n : ℕ} (gap : Fin k → ℝ)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < gap i →
      ((i : ℕ) + 1 : ℝ) / gap i ^ 2 ≤ H₂)
    (ℓ : ℕ) (hℓ : ℓ < Nat.clog 2 k) :
    ∃ threshold : ℕ, threshold < BanditAlgorithm.seqHalvingCount k (ℓ + 1) ∧
      min 1 ((∑ i : Fin k,
          if threshold ≤ (i : ℕ) ∧ 0 < gap i then
            Real.exp (-(BanditAlgorithm.seqHalvingPulls k n ℓ : ℝ) * gap i ^ 2 / 4)
          else 0) /
            ((BanditAlgorithm.seqHalvingCount k (ℓ + 1) - threshold : ℕ) : ℝ)) ≤
        3 * Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  let L := Nat.clog 2 k
  let m := seqHalvingCount k ℓ
  let q := seqHalvingCount k (ℓ + 1)
  let u := seqHalvingPulls k n ℓ
  have hL : 0 < L := Nat.zero_lt_of_lt hℓ
  have hk : 0 < k := by
    have hp := Nat.pow_lt_of_lt_clog hℓ
    have hp0 : 0 < 2 ^ ℓ := pow_pos (by decide) _
    omega
  have hm : 0 < m := BanditAlgorithm.seqHalvingCount_pos' k ℓ hk
  have hq : 0 < q := BanditAlgorithm.seqHalvingCount_pos' k (ℓ + 1) hk
  have hqk : q ≤ k := BanditAlgorithm.seqHalvingCount_le' k (ℓ + 1)
  by_cases htriv : 1 ≤ 3 * Real.exp (-(n / (16 * H₂ * (L : ℝ))))
  · refine ⟨0, hq, ?_⟩
    exact (min_le_left _ _).trans htriv
  by_cases hposgap : ∃ i : Fin k, 0 < gap i
  · rcases hposgap with ⟨ipos, hipos⟩
    have hHpos : 0 < H₂ := by
      have hfracpos : 0 < (((ipos : ℕ) + 1 : ℝ) / gap ipos ^ 2) := by positivity
      exact hfracpos.trans_le (hH₂ ipos hipos)
    have hdenle : L * m ≤ n := by
      calc
        L * m ≤ L * k := Nat.mul_le_mul_left _
          (BanditAlgorithm.seqHalvingCount_le' k ℓ)
        _ = k * L := Nat.mul_comm _ _
        _ ≤ n := hn
    have hdenpos : 0 < L * m := Nat.mul_pos hL hm
    have hu : 0 < u := by
      dsimp [u, seqHalvingPulls]
      exact Nat.div_pos hdenle hdenpos
    let b : ℝ := (u : ℝ) / (4 * H₂)
    let c : ℝ := (n : ℝ) / (16 * H₂ * (L : ℝ))
    have hb : 0 < b := by dsimp [b]; positivity
    have hc : 0 < c := by
      have hnpos : 0 < n := Nat.zero_lt_of_lt (lt_of_lt_of_le
        (Nat.mul_pos hk hL) hn)
      dsimp [c]
      positivity
    have hbudget := BanditAlgorithm.seqHalving_budget_le_four_phase_mass hn hℓ
    have hcble : c ≤ b * (q : ℝ) := by
      have hbudgetR : (n : ℝ) ≤
          4 * (L : ℝ) * (u : ℝ) * (q : ℝ) := by
        exact_mod_cast hbudget
      dsimp [c, b]
      have hdenR : 0 < 16 * H₂ * (L : ℝ) := by positivity
      apply (div_le_iff₀ hdenR).2
      field_simp
      nlinarith
    have hcgt : 1 < c := by
      have hRlt : 3 * Real.exp (-c) < 1 := by
        have := lt_of_not_ge htriv
        simpa [c, L] using this
      by_contra hnot
      have hcle : c ≤ 1 := le_of_not_gt hnot
      have hmono : Real.exp (-1) ≤ Real.exp (-c) :=
        Real.exp_le_exp.mpr (by linarith)
      have hone : 1 < 3 * Real.exp (-1) := by
        rw [Real.exp_neg]
        exact (lt_div_iff₀ (Real.exp_pos 1)).2 (by
          simpa only [one_mul] using Real.exp_one_lt_three)
      nlinarith
    have hlarge : 1 < b * (q : ℝ) := hcgt.trans_le hcble
    obtain ⟨threshold, htq, hgeom⟩ :=
      BanditAlgorithm.fin_exp_rank_tail_has_good_cutoff k q hq hqk b hb hlarge
    refine ⟨threshold, htq, ?_⟩
    have hsumbound :
        (∑ i : Fin k,
          if threshold ≤ (i : ℕ) ∧ 0 < gap i then
            Real.exp (-(u : ℝ) * gap i ^ 2 / 4)
          else 0) ≤
        ∑ i : Fin k,
          if threshold ≤ (i : ℕ) then
            Real.exp (-b * (((i : ℕ) + 1 : ℕ) : ℝ)) else 0 := by
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hcond : threshold ≤ (i : ℕ) ∧ 0 < gap i
      · simp only [hcond, if_true, hcond.1]
        have hsq : 0 < gap i ^ 2 := sq_pos_of_pos hcond.2
        have hrank : (((i : ℕ) + 1 : ℝ)) ≤ H₂ * gap i ^ 2 :=
          (div_le_iff₀ hsq).mp (hH₂ i hcond.2)
        have hrankdiv : (((i : ℕ) + 1 : ℝ)) / H₂ ≤ gap i ^ 2 :=
          (div_le_iff₀ hHpos).2 (by simpa [mul_comm] using hrank)
        apply Real.exp_le_exp.mpr
        dsimp [b]
        have huR : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg _
        have hcoeff : (0 : ℝ) ≤ (u : ℝ) / 4 := by positivity
        have hmul := mul_le_mul_of_nonneg_left hrankdiv hcoeff
        have hrewrite : ((u : ℝ) / (4 * H₂)) * (((i : ℕ) + 1 : ℝ)) =
            ((u : ℝ) / 4) * ((((i : ℕ) + 1 : ℝ)) / H₂) := by
          field_simp [ne_of_gt hHpos]
        calc
          -(u : ℝ) * gap i ^ 2 / 4 = -((u : ℝ) / 4 * gap i ^ 2) := by ring
          _ ≤ -((u : ℝ) / 4 * ((((i : ℕ) + 1 : ℝ)) / H₂)) :=
            neg_le_neg hmul
          _ = -(((u : ℝ) / (4 * H₂)) * (((i : ℕ) + 1 : ℝ))) :=
            congrArg Neg.neg hrewrite.symm
          _ = -((u : ℝ) / (4 * H₂)) * (((i : ℕ) + 1 : ℝ)) := by ring
          _ = -((u : ℝ) / (4 * H₂)) * ((((i : ℕ) + 1 : ℕ) : ℝ)) := by
            norm_num
      · by_cases ht : threshold ≤ (i : ℕ)
        · have hgap : ¬ 0 < gap i := fun hg ↦ hcond ⟨ht, hg⟩
          simp only [hgap, if_false, ht, if_true]
          exact (Real.exp_pos _).le
        · simp [hcond, ht]
    have hdenposR : (0 : ℝ) < (q - threshold : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt htq
    have havg :
        (∑ i : Fin k,
          if threshold ≤ (i : ℕ) ∧ 0 < gap i then
            Real.exp (-(u : ℝ) * gap i ^ 2 / 4)
          else 0) / ((q - threshold : ℕ) : ℝ) ≤
        3 * Real.exp (-b * (q : ℝ)) :=
      (div_le_div_of_nonneg_right hsumbound hdenposR.le).trans hgeom
    have hexp : 3 * Real.exp (-b * (q : ℝ)) ≤ 3 * Real.exp (-c) := by
      gcongr
      linarith
    exact (min_le_right _ _).trans (havg.trans hexp)
  · refine ⟨0, hq, ?_⟩
    have hnone : ∀ i : Fin k, ¬ 0 < gap i := by
      simpa only [not_exists] using hposgap
    have hRnonneg : 0 ≤
        3 * Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) :=
      mul_nonneg (by norm_num) (Real.exp_pos _).le
    simpa [hnone] using hRnonneg
