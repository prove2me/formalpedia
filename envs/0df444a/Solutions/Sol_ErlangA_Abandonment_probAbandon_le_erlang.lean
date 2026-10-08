-- Prove2me | solution 1 for ErlangA.Abandonment.probAbandon_le_erlang
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T10:53:07.221488+00:00
-- url     : https://prove2.me/submissions/c0a17b2a-2394-4322-a25c-e46aac670470

import Mathlib
import Definitions.Def_ErlangA_Abandonment_Model
import Definitions.Def_KellyStochasticNetworks_Erlang

open ErlangA.Abandonment Filter Topology
set_option maxHeartbeats 40000

private theorem weight_pos (N : ℕ) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) (k : ℕ) :
    0 < weight N lam μ θ k := by
  classical
  unfold weight
  split_ifs with h
  · exact div_pos (pow_pos (div_pos hlam hμ) _) (by positivity)
  · apply mul_pos
    · apply Finset.prod_pos
      intro j hj
      have hjn : N < j := by have := (Finset.mem_Icc.mp hj).1; omega
      have hp : 0 < ((j - N : ℕ) : ℝ) := by exact_mod_cast (show 0 < j - N by omega)
      exact div_pos hlam (by positivity)
    · exact div_pos (pow_pos (div_pos hlam hμ) _) (by positivity)

private theorem weight_antitone (N : ℕ) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (k : ℕ) :
    AntitoneOn (fun θ => weight N lam μ θ k) (Set.Ioi 0) := by
  classical
  intro θ₁ h₁ θ₂ h₂ hle
  unfold weight
  split_ifs
  · exact le_rfl
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Finset.prod_le_prod
    · intro j hj
      exact le_of_lt (div_pos hlam (by
        have hjn : N < j := by have := (Finset.mem_Icc.mp hj).1; omega
        have hp : 0 < ((j - N : ℕ) : ℝ) := by exact_mod_cast (show 0 < j - N by omega)
        have ht : 0 < θ₂ := h₂
        positivity))
    · intro j hj
      have hjn : N < j := by have := (Finset.mem_Icc.mp hj).1; omega
      have hp : 0 < ((j - N : ℕ) : ℝ) := by exact_mod_cast (show 0 < j - N by omega)
      apply div_le_div_of_nonneg_left (le_of_lt hlam) (by
        have ht : 0 < θ₁ := h₁
        positivity)
      linarith [mul_le_mul_of_nonneg_left hle (le_of_lt hp)]

private theorem tail_formula (N n : ℕ) (lam μ θ : ℝ) :
    weight N lam μ θ (N + n) =
      (∏ j ∈ Finset.Icc (N + 1) (N + n),
        lam / ((N : ℝ) * μ + ((j - N : ℕ) : ℝ) * θ)) *
        ((lam / μ)^N / (Nat.factorial N : ℝ)) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [weight]
  · simp only [weight, if_neg (show ¬ N + n ≤ N by omega)]

private theorem tail_recurrence (N n : ℕ) (lam μ θ : ℝ) :
    weight N lam μ θ (N + (n + 1)) =
      weight N lam μ θ (N + n) *
        (lam / ((N : ℝ) * μ + ((n : ℝ) + 1) * θ)) := by
  classical
  rw [tail_formula, tail_formula]
  rw [show N + (n + 1) = (N + n) + 1 by omega,
    Finset.prod_Icc_succ_top (show N + 1 ≤ N + n + 1 by omega)]
  simp only [show N + n + 1 - N = n + 1 by omega, Nat.cast_add, Nat.cast_one]
  ring

private theorem weight_summable (N : ℕ) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    Summable (weight N lam μ θ) := by
  have ht : Summable (fun n => weight N lam μ θ (N + n)) := by
    apply summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num)
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * lam / θ)
    apply eventually_atTop.mpr
    refine ⟨K, fun n hn => ?_⟩
    have hkn : (K : ℝ) ≤ n := by exact_mod_cast hn
    have hnθ : 2 * lam < (n : ℝ) * θ := by
      have hh := (div_lt_iff₀ hθ).mp hK
      exact hh.trans_le (mul_le_mul_of_nonneg_right hkn hθ.le)
    have hw := weight_pos N lam μ θ hlam hμ hθ (N + n)
    have hden : 0 < (N : ℝ) * μ + ((n : ℝ) + 1) * θ := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (weight_pos N lam μ θ hlam hμ hθ _), abs_of_pos hw,
      tail_recurrence]
    have hr : lam / ((N : ℝ) * μ + ((n : ℝ) + 1) * θ) ≤ 1/2 := by
      apply (div_le_iff₀ hden).2
      have hNu : 0 ≤ (N : ℝ) * μ := by positivity
      linarith
    calc
      weight N lam μ θ (N + n) *
          (lam / ((N : ℝ) * μ + ((n : ℝ) + 1) * θ)) ≤
          weight N lam μ θ (N + n) * (1/2) :=
        mul_le_mul_of_nonneg_left hr hw.le
      _ = (1/2) * weight N lam μ θ (N + n) := by ring
  rw [← summable_nat_add_iff N]
  simpa only [Nat.add_comm] using ht

private theorem abandonment_tail (N : ℕ) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    probAbandon N lam μ θ =
      ((∑' n, weight N lam μ θ (N + n)) -
        ((N : ℝ) * μ / lam) *
          ((∑' n, weight N lam μ θ (N + n)) - weight N lam μ θ N)) /
        (∑' k, weight N lam μ θ k) := by
  let w := weight N lam μ θ
  have hw := weight_summable N lam μ θ hlam hμ hθ
  have ht : Summable (fun n => w (N + n)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 hw
  have ht' : Summable (fun n => w (N + (n + 1))) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff 1).2 ht
  have hshift : (∑' n, w (N + (n + 1))) = (∑' n, w (N + n)) - w N := by
    have hh := ht.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, Nat.add_zero, Nat.add_assoc] at hh
    linarith
  have he (n : ℕ) :
      w (N + n) * (((n : ℝ) + 1) * θ /
        ((N : ℝ) * μ + ((n : ℝ) + 1) * θ)) =
        w (N + n) - ((N : ℝ) * μ / lam) * w (N + (n + 1)) := by
    dsimp [w]
    rw [tail_recurrence]
    have hd : (N : ℝ) * μ + ((n : ℝ) + 1) * θ ≠ 0 := by positivity
    field_simp
    <;> ring
  unfold probAbandon stationaryDist
  have hf : (fun n : ℕ => weight N lam μ θ (N + n) /
      (∑' j, weight N lam μ θ j) *
      (((n : ℝ) + 1) * θ / ((N : ℝ) * μ + ((n : ℝ) + 1) * θ))) =
      fun n => (w (N + n) - ((N : ℝ) * μ / lam) * w (N + (n + 1))) /
        (∑' j, w j) := by
    funext n
    rw [← he]
    dsimp [w]
    ring
  rw [hf, tsum_div_const, ht.tsum_sub (ht'.mul_left _), tsum_mul_left, hshift]

private theorem finite_balance (N : ℕ) (lam μ θ : ℝ)
    (hμ : 0 < μ) (k : ℕ) (hk : k < N) :
    lam * weight N lam μ θ k =
      μ * ((k : ℝ) + 1) * weight N lam μ θ (k + 1) := by
  have hkN : k ≤ N := by omega
  have hkp : k + 1 ≤ N := by omega
  simp only [weight, if_pos hkN, if_pos hkp, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hm : μ ≠ 0 := ne_of_gt hμ
  have hf : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem finite_gap (N : ℕ) (hN : 1 ≤ N) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    lam * (∑ k ∈ Finset.range N, weight N lam μ θ k) <
      (N : ℝ) * μ * ((∑ k ∈ Finset.range N, weight N lam μ θ k) +
        weight N lam μ θ N) := by
  let w := weight N lam μ θ
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hshift : (∑ k ∈ Finset.range N, w (k + 1)) + w 0 =
      (∑ k ∈ Finset.range N, w k) + w N := by
    have h1 := Finset.sum_range_succ w N
    have h2 := Finset.sum_range_succ' w N
    linarith
  have hb : lam * (∑ k ∈ Finset.range N, w k) ≤
      (N : ℝ) * μ * (∑ k ∈ Finset.range N, w (k + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [finite_balance N lam μ θ hμ k (Finset.mem_range.mp hk)]
    have hkn : (k : ℝ) + 1 ≤ N := by
      exact_mod_cast (show k + 1 ≤ N by have := Finset.mem_range.mp hk; omega)
    have hwp := weight_pos N lam μ θ hlam hμ hθ (k + 1)
    dsimp [w]
    calc
      μ * ((k : ℝ) + 1) * weight N lam μ θ (k + 1) ≤
          μ * (N : ℝ) * weight N lam μ θ (k + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkn hμ.le) hwp.le
      _ = (N : ℝ) * μ * weight N lam μ θ (k + 1) := by ring
  have hw0 := weight_pos N lam μ θ hlam hμ hθ 0
  dsimp [w] at hshift hb
  have hs := congrArg (fun t : ℝ => (N : ℝ) * μ * t) hshift
  have hp := mul_pos (mul_pos hNpos hμ) hw0
  nlinarith only [hb, hs, hp]

private theorem normalization_split (N : ℕ) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    (∑' k, weight N lam μ θ k) =
      (∑ k ∈ Finset.range N, weight N lam μ θ k) +
        (∑' n, weight N lam μ θ (N + n)) := by
  have hh := (weight_summable N lam μ θ hlam hμ hθ).sum_add_tsum_nat_add N
  simpa only [Nat.add_comm] using hh.symm

private theorem tail_ge (N : ℕ) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    weight N lam μ θ N ≤ ∑' n, weight N lam μ θ (N + n) := by
  have ht : Summable (fun n => weight N lam μ θ (N + n)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff N).2 (weight_summable N lam μ θ hlam hμ hθ)
  simpa only [Nat.add_zero] using
    (ht.le_tsum 0 (fun n _ => (weight_pos N lam μ θ hlam hμ hθ _).le))

private theorem total_pos (N : ℕ) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    0 < ∑' k, weight N lam μ θ k :=
  (weight_pos N lam μ θ hlam hμ hθ 0).trans_le
    ((weight_summable N lam μ θ hlam hμ hθ).le_tsum 0
      (fun k _ => (weight_pos N lam μ θ hlam hμ hθ k).le))

private theorem tail_antitone (N : ℕ) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) :
    AntitoneOn (fun θ => ∑' n, weight N lam μ θ (N + n)) (Set.Ioi 0) := by
  intro θ₁ h₁ θ₂ h₂ hle
  apply Summable.tsum_le_tsum (fun n => weight_antitone N lam μ hlam hμ _ h₁ h₂ hle)
  · simpa only [Nat.add_comm] using
      (summable_nat_add_iff N).2 (weight_summable N lam μ θ₂ hlam hμ h₂)
  · simpa only [Nat.add_comm] using
      (summable_nat_add_iff N).2 (weight_summable N lam μ θ₁ hlam hμ h₁)

theorem solution (N : ℕ) (hN : 1 ≤ N) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    probAbandon N lam μ θ ≤ KellyStochasticNetworks.erlang (lam / μ) N := by
  classical
  let S := ∑ k ∈ Finset.range N, weight N lam μ θ k
  let T := ∑' n, weight N lam μ θ (N + n)
  let a := weight N lam μ θ N
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ =>
    (weight_pos N lam μ θ hlam hμ hθ k).le)
  have ha : 0 < a := weight_pos N lam μ θ hlam hμ hθ N
  have hTa : a ≤ T := tail_ge N lam μ θ hlam hμ hθ
  have hZ : 0 < S + T := by linarith
  have hZa : 0 < S + a := by linarith
  have hgap := finite_gap N hN lam μ θ hlam hμ hθ
  change lam * S < (N : ℝ) * μ * (S + a) at hgap
  have herlang : KellyStochasticNetworks.erlang (lam / μ) N = a / (S + a) := by
    unfold KellyStochasticNetworks.erlang
    have hs : (∑ k ∈ Finset.range (N + 1), (lam / μ)^k / (Nat.factorial k : ℝ)) =
        S + a := by
      rw [← Finset.sum_range_succ]
      apply Finset.sum_congr rfl
      intro k hk
      rw [weight, if_pos (show k ≤ N by have := Finset.mem_range.mp hk; omega)]
    rw [hs]
    dsimp only [a]
    rw [weight, if_pos (le_refl N)]
  rw [herlang, abandonment_tail N lam μ θ hlam hμ hθ,
    normalization_split N lam μ θ hlam hμ hθ]
  change (T - ((N : ℝ) * μ / lam) * (T - a)) / (S + T) ≤ a / (S + a)
  rw [div_le_div_iff₀ hZ hZa]
  have hKS : S ≤ ((N : ℝ) * μ / lam) * (S + a) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith [hgap]
  have hTa0 : 0 ≤ T - a := by linarith
  have hprod : S * (T - a) ≤ ((N : ℝ) * μ / lam) * (S + a) * (T - a) :=
    mul_le_mul_of_nonneg_right hKS hTa0
  nlinarith [hprod]

#print axioms solution
