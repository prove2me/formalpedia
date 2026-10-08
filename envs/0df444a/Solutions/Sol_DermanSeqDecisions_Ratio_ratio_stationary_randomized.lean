-- Prove2me | solution 1 for DermanSeqDecisions.Ratio.ratio_stationary_randomized
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:07:16.580489+00:00
-- url     : https://prove2.me/submissions/c3ed530e-a477-45d6-98df-4d849c804eec

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite


namespace DermanSeqDecisions.Ratio

open Filter

lemma dr_sum_cons {β : Type*} [Fintype β] {n : ℕ} {R : Type*} [AddCommMonoid R]
    (F : (Fin (n + 1) → β) → R) :
    ∑ h : Fin (n + 1) → β, F h = ∑ x : β, ∑ g : Fin n → β, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => β)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma dr_prevWeight_sum {S Act : Type*} [Fintype S] (M : MDC S Act) (i : S)
    (l : List (S × Act)) : ∑ j, prevWeight M i l j = 1 := by
  cases l with
  | nil =>
    simp [prevWeight]
    convert Finset.card_singleton i
    ext; simp
  | cons p rest =>
    obtain ⟨k, b⟩ := p
    simp only [prevWeight]
    have := M.P_sum k b; rwa [tsum_fintype] at this

lemma dr_mass {S Act : Type*} [Fintype S] [Fintype Act] (M : MDC S Act)
    (hA : ∀ s, M.A s = Finset.univ) (θ : Policy M) (i : S) (n : ℕ) :
    ∑ g : Fin n → S × Act, histProb θ i (List.ofFn g) = 1 := by
  induction n with
  | zero => simp [histProb]
  | succ n ih =>
    rw [dr_sum_cons]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    rw [Fintype.sum_prod_type]
    simp only [histProb]
    have : ∀ j : S, ∀ g : Fin n → S × Act,
        ∑ a : Act, histProb θ i (List.ofFn fun k => g k) *
          prevWeight M i (List.ofFn fun k => g k) j * θ.prob (List.ofFn fun k => g k) j a
        = histProb θ i (List.ofFn g) * prevWeight M i (List.ofFn g) j := by
      intro j g
      rw [← Finset.mul_sum]
      have := θ.prob_sum (List.ofFn g) j
      rw [hA] at this
      simp [this]
    simp_rw [Finset.sum_comm (γ := Act), this]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, dr_prevWeight_sum, mul_one]
    exact ih

lemma dr_hp_le {S Act : Type*} [Fintype S] [Fintype Act] (M : MDC S Act)
    (hA : ∀ s, M.A s = Finset.univ) (θ : Policy M) (i : S) (n : ℕ) (g : Fin n → S × Act) :
    histProb θ i (List.ofFn g) ≤ 1 := by
  rw [← dr_mass M hA θ i n]
  exact Finset.single_le_sum (f := fun g => histProb θ i (List.ofFn g)) (fun _ _ => bot_le)
    (Finset.mem_univ g)

lemma dr_mass_real {S Act : Type*} [Fintype S] [Fintype Act] (M : MDC S Act)
    (hA : ∀ s, M.A s = Finset.univ) (θ : Policy M) (i : S) (n : ℕ) :
    ∑ g : Fin n → S × Act, (histProb θ i (List.ofFn g)).toReal = 1 := by
  rw [← ENNReal.toReal_sum, dr_mass M hA]; · simp
  intro g _; exact ne_top_of_le_ne_top ENNReal.one_ne_top (dr_hp_le M hA θ i n g)

lemma dr_exp_bounds {S Act : Type*} [Fintype S] [Fintype Act] (M : MDC S Act)
    (hA : ∀ s, M.A s = Finset.univ) (θ : Policy M) (i : S) (c : S → Act → ℝ) (lo hi : ℝ)
    (h : ∀ s a, lo ≤ c s a ∧ c s a ≤ hi) (t : ℕ) :
    lo ≤ expCostR θ i c t ∧ expCostR θ i c t ≤ hi := by
  have hm := dr_mass_real M hA θ i (t + 1)
  unfold expCostR
  constructor
  · calc lo = ∑ g : Fin (t+1) → S × Act, (histProb θ i (List.ofFn g)).toReal * lo := by
          rw [← Finset.sum_mul, hm, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun g _ =>
          mul_le_mul_of_nonneg_left (h _ _).1 ENNReal.toReal_nonneg
  · calc _ ≤ ∑ g : Fin (t+1) → S × Act, (histProb θ i (List.ofFn g)).toReal * hi :=
          Finset.sum_le_sum fun g _ =>
          mul_le_mul_of_nonneg_left (h _ _).2 ENNReal.toReal_nonneg
      _ = hi := by rw [← Finset.sum_mul, hm, one_mul]

lemma dr_exp_lin {S Act : Type*} [Fintype S] [Fintype Act] {M : MDC S Act}
    (θ : Policy M) (i : S) (w' w'' : S → Act → ℝ) (m : ℝ) (t : ℕ) :
    expCostR θ i (fun s a => w' s a - m * w'' s a) t =
      expCostR θ i w' t - m * expCostR θ i w'' t := by
  simp only [expCostR, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro g _; ring

lemma dr_nonempty_act {S Act : Type*} [Fintype S] [Nonempty S] (M : MDC S Act) : Nonempty Act :=
  ⟨(M.A_nonempty (Classical.arbitrary S)).choose⟩

lemma dr_pos_lb {S Act : Type*} [Fintype S] [Fintype Act] [Nonempty S] [Nonempty Act]
    (w : S → Act → ℝ) (hw : ∀ s a, 0 < w s a) : ∃ δ > 0, ∀ s a, δ ≤ w s a := by
  obtain ⟨p, hp⟩ := Finite.exists_min (fun p : S × Act => w p.1 p.2)
  exact ⟨w p.1 p.2, hw _ _, fun s a => hp (s, a)⟩

lemma dr_abs_ub {S Act : Type*} [Fintype S] [Fintype Act]
    (w : S → Act → ℝ) : ∃ K > 0, ∀ s a, |w s a| ≤ K := by
  refine ⟨1 + ∑ p : S × Act, |w p.1 p.2|, by positivity, fun s a => ?_⟩
  have := Finset.single_le_sum (f := fun p : S × Act => |w p.1 p.2|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ (s, a))
  simp only at this; linarith

/-- The key bounded-sums facts. -/
lemma dr_sums {S Act : Type*} [Fintype S] [Fintype Act] (M : MDC S Act)
    (hA : ∀ s, M.A s = Finset.univ) (θ : Policy M) (i : S) (c : S → Act → ℝ) (lo hi : ℝ)
    (h : ∀ s a, lo ≤ c s a ∧ c s a ≤ hi) (T : ℕ) :
    lo * (T + 1) ≤ ∑ t ∈ Finset.range (T + 1), expCostR θ i c t ∧
      ∑ t ∈ Finset.range (T + 1), expCostR θ i c t ≤ hi * (T + 1) := by
  have h1 := Finset.sum_le_sum (s := Finset.range (T+1))
    (fun t _ => (dr_exp_bounds M hA θ i c lo hi h t).1)
  have h2 := Finset.sum_le_sum (s := Finset.range (T+1))
    (fun t _ => (dr_exp_bounds M hA θ i c lo hi h t).2)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1 h2
  push_cast at h1 h2
  constructor <;> linarith

theorem avg_nonpos_core {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a)
    (θ : Policy M) (i : S) (m : ℝ) (hψ : ratioCost θ i w' w'' ≤ m) :
    avgCostR θ i (fun s a => w' s a - m * w'' s a) ≤ 0 := by
  have := dr_nonempty_act M
  obtain ⟨δ, hδ, hδw⟩ := dr_pos_lb w'' hw''
  obtain ⟨K1, hK1, hK1w⟩ := dr_abs_ub w'
  obtain ⟨K2, hK2, hK2w⟩ := dr_abs_ub w''
  set K := K1 + K2 with hK
  have hb' : ∀ s a, -K ≤ w' s a ∧ w' s a ≤ K := fun s a => by
    have := abs_le.1 (hK1w s a); constructor <;> linarith
  have hb'' : ∀ s a, δ ≤ w'' s a ∧ w'' s a ≤ K := fun s a => by
    have := abs_le.1 (hK2w s a); constructor <;> linarith [hδw s a]
  set A : ℕ → ℝ := fun T => ∑ t ∈ Finset.range (T + 1), expCostR θ i w' t with hAdef
  set B : ℕ → ℝ := fun T => ∑ t ∈ Finset.range (T + 1), expCostR θ i w'' t with hBdef
  have hA' : ∀ T : ℕ, -K * ((T : ℝ) + 1) ≤ A T ∧ A T ≤ K * (T + 1) := fun T =>
    dr_sums M hA θ i w' (-K) K hb' T
  have hB' : ∀ T : ℕ, δ * ((T : ℝ) + 1) ≤ B T ∧ B T ≤ K * (T + 1) := fun T =>
    dr_sums M hA θ i w'' δ K hb'' T
  have hBpos : ∀ T, 0 < B T := fun T => lt_of_lt_of_le (by positivity) (hB' T).1
  -- ratio bounded above
  have hrb : IsBoundedUnder (· ≤ ·) atTop (fun T => A T / B T) := by
    refine isBoundedUnder_of ⟨K / δ, fun T => ?_⟩
    rw [div_le_div_iff₀ (hBpos T) hδ]
    nlinarith [(hA' T).2, (hB' T).1, hK1, hK2]
  have hlin : ∀ T : ℕ, (1 / (T : ℝ)) * ∑ t ∈ Finset.range (T + 1),
      expCostR θ i (fun s a => w' s a - m * w'' s a) t = (1 / (T : ℝ)) * (A T - m * B T) := by
    intro T; simp only [dr_exp_lin, Finset.sum_sub_distrib, ← Finset.mul_sum, hAdef, hBdef]
  unfold avgCostR
  simp_rw [hlin]
  -- bounded below
  have hlow : IsBoundedUnder (· ≥ ·) atTop (fun T : ℕ => (1 / (T : ℝ)) * (A T - m * B T)) := by
    refine isBoundedUnder_of ⟨-(2 * (K + |m| * K)), fun T => ?_⟩
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp; positivity
    · have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
      have h1 : -(K + |m| * K) * (T + 1) ≤ A T - m * B T := by
        have : m * B T ≤ |m| * K * (T + 1) := by
          calc m * B T ≤ |m| * B T := mul_le_mul_of_nonneg_right (le_abs_self m) (hBpos T).le
            _ ≤ |m| * (K * (T + 1)) := mul_le_mul_of_nonneg_left (hB' T).2 (abs_nonneg m)
            _ = _ := by ring
        nlinarith [(hA' T).1]
      show -(2 * (K + |m| * K)) ≤ 1 / (T : ℝ) * (A T - m * B T)
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
      have hKm : 0 ≤ K + |m| * K := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (show (T:ℝ) + 1 ≤ 2 * T by linarith) hKm]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ T in atTop, A T / B T < m + ε / (2 * K) :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hψ (by linarith [show 0 < ε / (2*K) by positivity])) hrb
  rw [zero_add]
  refine limsup_le_of_le hlow.isCoboundedUnder_le ?_
  filter_upwards [hev, eventually_ge_atTop 1] with T hT hT1
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  rw [div_lt_iff₀ (hBpos T)] at hT
  have h1 : A T - m * B T ≤ ε / (2 * K) * B T := by linarith
  have h2 : ε / (2 * K) * B T ≤ ε / (2 * K) * (K * (T + 1)) :=
    mul_le_mul_of_nonneg_left (hB' T).2 (by positivity)
  have h3 : ε / (2 * K) * (K * (T + 1)) = ε * (T + 1) / 2 := by
    have : K ≠ 0 := by linarith
    field_simp
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  nlinarith

theorem ratio_le_core {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (w' w'' : S → Act → ℝ) (hw'' : ∀ s a, 0 < w'' s a)
    (θ : Policy M) (i : S) (m : ℝ)
    (hQ : avgCostR θ i (fun s a => w' s a - m * w'' s a) ≤ 0) :
    ratioCost θ i w' w'' ≤ m := by
  have := dr_nonempty_act M
  obtain ⟨δ, hδ, hδw⟩ := dr_pos_lb w'' hw''
  obtain ⟨K1, hK1, hK1w⟩ := dr_abs_ub w'
  obtain ⟨K2, hK2, hK2w⟩ := dr_abs_ub w''
  set K := K1 + K2 with hK
  have hb' : ∀ s a, -K ≤ w' s a ∧ w' s a ≤ K := fun s a => by
    have := abs_le.1 (hK1w s a); constructor <;> linarith
  have hb'' : ∀ s a, δ ≤ w'' s a ∧ w'' s a ≤ K := fun s a => by
    have := abs_le.1 (hK2w s a); constructor <;> linarith [hδw s a]
  set A : ℕ → ℝ := fun T => ∑ t ∈ Finset.range (T + 1), expCostR θ i w' t with hAdef
  set B : ℕ → ℝ := fun T => ∑ t ∈ Finset.range (T + 1), expCostR θ i w'' t with hBdef
  have hA' : ∀ T : ℕ, -K * ((T : ℝ) + 1) ≤ A T ∧ A T ≤ K * (T + 1) := fun T =>
    dr_sums M hA θ i w' (-K) K hb' T
  have hB' : ∀ T : ℕ, δ * ((T : ℝ) + 1) ≤ B T ∧ B T ≤ K * (T + 1) := fun T =>
    dr_sums M hA θ i w'' δ K hb'' T
  have hBpos : ∀ T, 0 < B T := fun T => lt_of_lt_of_le (by positivity) (hB' T).1
  have hrlow : IsBoundedUnder (· ≥ ·) atTop (fun T => A T / B T) := by
    refine isBoundedUnder_of ⟨-K / δ, fun T => ?_⟩
    show -K / δ ≤ A T / B T
    rw [div_le_div_iff₀ hδ (hBpos T)]
    nlinarith [(hA' T).1, (hB' T).1, (hB' T).2, hK1, hK2]
  have hlin : ∀ T : ℕ, (1 / (T : ℝ)) * ∑ t ∈ Finset.range (T + 1),
      expCostR θ i (fun s a => w' s a - m * w'' s a) t = (1 / (T : ℝ)) * (A T - m * B T) := by
    intro T; simp only [dr_exp_lin, Finset.sum_sub_distrib, ← Finset.mul_sum, hAdef, hBdef]
  unfold avgCostR at hQ
  simp_rw [hlin] at hQ
  have hup : IsBoundedUnder (· ≤ ·) atTop (fun T : ℕ => (1 / (T : ℝ)) * (A T - m * B T)) := by
    refine isBoundedUnder_of ⟨2 * (K + |m| * K), fun T => ?_⟩
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp; positivity
    · have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
      have h1 : A T - m * B T ≤ (K + |m| * K) * (T + 1) := by
        have : -(m * B T) ≤ |m| * K * (T + 1) := by
          calc -(m * B T) ≤ |m| * B T := by
                rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs m) (hBpos T).le
            _ ≤ |m| * (K * (T + 1)) := mul_le_mul_of_nonneg_left (hB' T).2 (abs_nonneg m)
            _ = _ := by ring
        nlinarith [(hA' T).2]
      show 1 / (T : ℝ) * (A T - m * B T) ≤ 2 * (K + |m| * K)
      rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      have hKm : 0 ≤ K + |m| * K := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (show (T:ℝ) + 1 ≤ 2 * T by linarith) hKm]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ T : ℕ in atTop, (1 / (T : ℝ)) * (A T - m * B T) < δ * ε :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hQ (by positivity)) hup
  unfold ratioCost
  refine limsup_le_of_le hrlow.isCoboundedUnder_le ?_
  filter_upwards [hev, eventually_ge_atTop 1] with T hT hT1
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ (by positivity)] at hT
  show A T / B T ≤ m + ε
  rw [div_le_iff₀ (hBpos T)]
  have h2 : δ * ε * T ≤ ε * B T := by nlinarith [(hB' T).1]
  nlinarith

section Stat
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- rows of powers of a stochastic matrix. -/
lemma dr_pow_row (P : Matrix S S ℝ) (h0 : ∀ s j, 0 ≤ P s j) (h1 : ∀ s, ∑ j, P s j = 1)
    (k : ℕ) (s : S) : ∑ j, (P ^ k) s j = 1 := by
  induction k generalizing s with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, ih, mul_one, h1]

lemma dr_pow_harm (P : Matrix S S ℝ) (v : S → ℝ) (hv : ∀ s, ∑ j, P s j * v j = v s)
    (k : ℕ) (s : S) : ∑ j, (P ^ k) s j * v j = v s := by
  induction k generalizing s with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    simp_rw [pow_succ', Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]; simp_rw [mul_assoc, ← Finset.mul_sum, ih, hv]

lemma dr_harm_const (P : Matrix S S ℝ) (h1 : ∀ s, ∑ j, P s j = 1)
    (hirr : P.IsIrreducible) (v : S → ℝ) (hv : ∀ s, ∑ j, P s j * v j = v s) [Nonempty S] :
    ∃ c, ∀ s, v s = c := by
  obtain ⟨s0, hs0⟩ := Finite.exists_max v
  refine ⟨v s0, fun j => ?_⟩
  have h0 := hirr.nonneg
  obtain ⟨k, -, hk⟩ := (Matrix.isIrreducible_iff_exists_pow_pos h0).1 hirr s0 j
  have hrow := dr_pow_row P h0 h1 k s0
  have hh := dr_pow_harm P v hv k s0
  have hsum : ∑ l, (P ^ k) s0 l * (v s0 - v l) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, hh]; ring
  have hnn : ∀ l ∈ Finset.univ, 0 ≤ (P ^ k) s0 l * (v s0 - v l) := fun l _ =>
    mul_nonneg (Matrix.pow_apply_nonneg h0 k s0 l) (sub_nonneg.2 (hs0 l))
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-- Cesàro means of the powers. -/
noncomputable def drAvg (P : Matrix S S ℝ) (T : ℕ) : S → S → ℝ :=
  fun s j => (1 / ((T : ℝ) + 1)) * ∑ t ∈ Finset.range (T + 1), (P ^ t) s j

lemma dr_cesaro (P : Matrix S S ℝ) (h1 : ∀ s, ∑ j, P s j = 1)
    (hirr : P.IsIrreducible) [Nonempty S] (π : S → ℝ)
    (hπ : ∀ j, π j - ∑ s, π s * P s j = 0) (hπ1 : ∑ j, π j = 1) :
    Tendsto (drAvg P) atTop (nhds (fun _ j => π j)) := by
  have h0 := hirr.nonneg
  have hent : ∀ t s j, 0 ≤ (P ^ t) s j ∧ (P ^ t) s j ≤ 1 := fun t s j => by
    refine ⟨Matrix.pow_apply_nonneg h0 t s j, ?_⟩
    rw [← dr_pow_row P h0 h1 t s]
    exact Finset.single_le_sum (f := fun j => (P ^ t) s j)
      (fun l _ => Matrix.pow_apply_nonneg h0 t s l) (Finset.mem_univ j)
  -- invariance of π
  have hπt : ∀ t j, ∑ s, π s * (P ^ t) s j = π j := by
    intro t; induction t with
    | zero => intro j; simp [Matrix.one_apply]
    | succ t ih =>
      intro j
      simp_rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul, ih]
      linarith [hπ j]
  have hπA : ∀ T j, ∑ s, π s * drAvg P T s j = π j := by
    intro T j
    simp only [drAvg]
    simp_rw [mul_left_comm (π _), ← Finset.mul_sum]
    have : ∑ s, π s * ∑ t ∈ Finset.range (T+1), (P^t) s j
        = ∑ t ∈ Finset.range (T+1), ∑ s, π s * (P^t) s j := by
      simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    rw [this]; simp_rw [hπt, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; field_simp
  -- the defect
  set E : ℕ → S → S → ℝ := fun T s j => ∑ l, P s l * drAvg P T l j - drAvg P T s j with hE
  have hEeq : ∀ T s j, E T s j = (1 / ((T : ℝ) + 1)) * ((P ^ (T + 1)) s j - (1 : Matrix S S ℝ) s j) := by
    intro T s j
    simp only [hE, drAvg]
    simp_rw [mul_left_comm (P s _), ← Finset.mul_sum, ← mul_sub]
    congr 1
    have h' : ∀ t, ∑ l, P s l * (P ^ t) l j = (P ^ (t + 1)) s j := fun t => by
      rw [pow_succ', Matrix.mul_apply]
    have : ∑ l, P s l * ∑ t ∈ Finset.range (T+1), (P^t) l j
        = ∑ t ∈ Finset.range (T+1), (P ^ (t + 1)) s j := by
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; simp_rw [h']
    rw [this, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (P ^ t) s j)]
    simp
  have hE0 : ∀ s j, Tendsto (fun T => E T s j) atTop (nhds 0) := by
    intro s j
    simp_rw [hEeq]
    have hb : ∀ T : ℕ, |(P ^ (T + 1)) s j - (1 : Matrix S S ℝ) s j| ≤ 2 := by
      intro T
      have := hent (T+1) s j
      have h2 : 0 ≤ (1 : Matrix S S ℝ) s j ∧ (1 : Matrix S S ℝ) s j ≤ 1 := by
        rw [Matrix.one_apply]; split_ifs <;> norm_num
      rw [abs_le]; constructor <;> linarith
    have ht : Tendsto (fun T : ℕ => 1 / ((T : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ht2 : Tendsto (fun T : ℕ => 1 / ((T : ℝ) + 1) * 2) atTop (nhds 0) := by
      simpa using ht.mul_const (2 : ℝ)
    refine squeeze_zero_norm (fun T => ?_) ht2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (hb T) (by positivity)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨L, -, φ, hφ, hL⟩ := tendsto_subseq_of_bounded (x := fun n => drAvg P (ns n))
    (Metric.isBounded_closedBall (x := (0 : S → S → ℝ)) (r := 1)) (fun n => by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro s; rw [pi_norm_le_iff_of_nonneg zero_le_one]; intro j
      rw [Real.norm_eq_abs, abs_le]
      simp only [drAvg]
      have hs0 : 0 ≤ ∑ t ∈ Finset.range (ns n + 1), (P ^ t) s j :=
        Finset.sum_nonneg fun t _ => (hent t s j).1
      have hs1 : ∑ t ∈ Finset.range (ns n + 1), (P ^ t) s j ≤ (ns n : ℝ) + 1 := by
        have := Finset.sum_le_sum (s := Finset.range (ns n + 1)) (fun t _ => (hent t s j).2)
        simpa using this
      constructor
      · have : 0 ≤ 1 / ((ns n : ℝ) + 1) * ∑ t ∈ Finset.range (ns n + 1), (P ^ t) s j := by
          positivity
        linarith
      · rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]; linarith)
  refine ⟨φ, ?_⟩
  have hL' : ∀ s j, Tendsto (fun n => drAvg P (ns (φ n)) s j) atTop (nhds (L s j)) := by
    intro s j
    have := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hL s) j
    exact this
  have hnsφ : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  -- L is harmonic in its columns
  have hharm : ∀ s j, ∑ l, P s l * L l j = L s j := by
    intro s j
    have h1' : Tendsto (fun n => E (ns (φ n)) s j) atTop
        (nhds (∑ l, P s l * L l j - L s j)) := by
      simp only [hE]
      exact (tendsto_finsetSum _ fun l _ => (hL' l j).const_mul (P s l)).sub (hL' s j)
    have h2' := (hE0 s j).comp hnsφ
    have := tendsto_nhds_unique h1' h2'
    linarith
  have hπL : ∀ j, ∑ s, π s * L s j = π j := by
    intro j
    have h1' : Tendsto (fun n => ∑ s, π s * drAvg P (ns (φ n)) s j) atTop
        (nhds (∑ s, π s * L s j)) :=
      tendsto_finsetSum _ fun s _ => (hL' s j).const_mul (π s)
    simp_rw [hπA] at h1'
    exact tendsto_nhds_unique h1' tendsto_const_nhds
  have hLeq : L = fun _ j => π j := by
    funext s j
    obtain ⟨c, hc⟩ := dr_harm_const P h1 hirr (fun l => L l j) (fun l => hharm l j)
    have := hπL j
    simp_rw [hc, ← Finset.sum_mul, hπ1, one_mul] at this
    rw [hc, this]
  rw [← hLeq]
  exact hL

end Stat

lemma dr_prevW_ofFn {S Act : Type*} [Fintype S] (M : MDC S Act) (i : S) {t : ℕ}
    (g : Fin (t + 1) → S × Act) (j : S) :
    prevWeight M i (List.ofFn g) j = M.P (g 0).1 (g 0).2 j := by
  rw [List.ofFn_succ]; rfl

lemma dr_marg {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act] (M : MDC S Act)
    (θ : Policy M) (D : S → Act → ℝ) (hD0 : ∀ s a, 0 ≤ D s a)
    (hθ : IsStationaryRandomized θ D) (i : S) (t : ℕ) (F : S × Act → ℝ) :
    ∑ g : Fin (t + 1) → S × Act, (histProb θ i (List.ofFn g)).toReal * F (g 0) =
      ∑ s, (inducedMatrix M D ^ t) i s * ∑ a, D s a * F (s, a) := by
  have hθ' : ∀ past s a, θ.prob past s a = ENNReal.ofReal (D s a) := hθ
  induction t generalizing F with
  | zero =>
    rw [dr_sum_cons]
    simp [List.ofFn_succ, histProb, prevWeight, hθ', Fintype.sum_prod_type,
      Matrix.one_apply, apply_ite ENNReal.toReal, ite_mul, ENNReal.toReal_ofReal (hD0 _ _)]
  | succ t ih =>
    rw [dr_sum_cons]
    simp only [List.ofFn_cons, Fin.cons_zero, histProb]
    simp only [dr_prevW_ofFn, hθ', ENNReal.toReal_mul, ENNReal.toReal_ofReal (hD0 _ _)]
    set G : S × Act → ℝ := fun p => ∑ x : S × Act, (M.P p.1 p.2 x.1).toReal * D x.1 x.2 * F x
      with hG
    have hL : ∑ x : S × Act, ∑ g : Fin (t + 1) → S × Act, (histProb θ i (List.ofFn g)).toReal *
        (M.P (g 0).1 (g 0).2 x.1).toReal * D x.1 x.2 * F x
        = ∑ g : Fin (t + 1) → S × Act, (histProb θ i (List.ofFn g)).toReal * G (g 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hG, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hL, ih G]
    have key : ∀ s, ∑ b, D s b * G (s, b) =
        ∑ j, inducedMatrix M D s j * ∑ a, D j a * F (j, a) := by
      intro s
      simp only [hG, inducedMatrix, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp_rw [key, pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
    ring

lemma dr_P_row {S Act : Type*} [Fintype S] (M : MDC S Act) (s : S) (a : Act) :
    ∑ j, (M.P s a j).toReal = 1 := by
  have hs : ∑ j, M.P s a j = 1 := by have := M.P_sum s a; rwa [tsum_fintype] at this
  rw [← ENNReal.toReal_sum, hs]; · simp
  intro j _
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← hs]
  exact Finset.single_le_sum (f := fun j => M.P s a j) (fun _ _ => bot_le) (Finset.mem_univ j)

theorem ratio_stat_core {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act)
    (hAssA : AssumptionA M)
    (w' w'' : S → Act → ℝ) (hw'' : ∀ s a, 0 < w'' s a)
    (θ : Policy M) (D : S → Act → ℝ) (hD0 : ∀ s a, 0 ≤ D s a) (hD1 : ∀ s, ∑ a, D s a = 1)
    (hθ : IsStationaryRandomized θ D)
    (π : S → ℝ) (hπ0 : ∀ j, 0 ≤ π j)
    (hπ : ∀ j, π j - ∑ s, π s * inducedMatrix M D s j = 0) (hπ1 : ∑ j, π j = 1) (i : S) :
    ratioCost θ i w' w'' =
      (∑ s, ∑ a, π s * D s a * w' s a) / (∑ s, ∑ a, π s * D s a * w'' s a) := by
  have := dr_nonempty_act M
  set P := inducedMatrix M D with hP
  have h1 : ∀ s, ∑ j, P s j = 1 := by
    intro s
    simp only [hP, inducedMatrix]
    rw [Finset.sum_comm]
    simp_rw [mul_comm _ (D s _), ← Finset.mul_sum, dr_P_row, mul_one, hD1]
  have hirr : P.IsIrreducible := hAssA D hD0 hD1
  have hces := dr_cesaro P h1 hirr π hπ hπ1
  set g : (S → Act → ℝ) → S → ℝ := fun c s => ∑ a, D s a * c s a with hg
  have hexp : ∀ c t, expCostR θ i c t = ∑ s, (P ^ t) i s * g c s := by
    intro c t
    exact dr_marg M θ D hD0 hθ i t (fun p => c p.1 p.2)
  clear_value g
  have hsum : ∀ c (T : ℕ), ∑ t ∈ Finset.range (T + 1), expCostR θ i c t =
      ((T : ℝ) + 1) * ∑ s, drAvg P T i s * g c s := by
    intro c T
    simp only [hexp, drAvg]
    have hT : ((T : ℝ) + 1) ≠ 0 := by positivity
    have e1 : ∀ s, (1 / ((T : ℝ) + 1) * ∑ t ∈ Finset.range (T + 1), (P ^ t) i s) * g c s
        = 1 / ((T : ℝ) + 1) * ∑ t ∈ Finset.range (T + 1), (P ^ t) i s * g c s := by
      intro s; rw [mul_assoc, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun s _ => e1 s), ← Finset.mul_sum, ← mul_assoc,
      mul_one_div_cancel hT, one_mul, Finset.sum_comm]
  have hlim : ∀ c, Tendsto (fun T => ∑ s, drAvg P T i s * g c s) atTop
      (nhds (∑ s, π s * g c s)) := by
    intro c
    refine tendsto_finsetSum _ fun s _ => ?_
    exact ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hces i) s)).mul_const _
  obtain ⟨δ, hδ, hδw⟩ := dr_pos_lb w'' hw''
  have hYpos : 0 < ∑ s, π s * g w'' s := by
    have : ∀ s, π s * δ ≤ π s * g w'' s := by
      intro s
      refine mul_le_mul_of_nonneg_left ?_ (hπ0 s)
      calc δ = ∑ a, D s a * δ := by rw [← Finset.sum_mul, hD1, one_mul]
        _ ≤ g w'' s := by
          rw [hg]; exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hδw s a) (hD0 s a)
    have h2 := Finset.sum_le_sum (s := Finset.univ) fun s _ => this s
    rw [← Finset.sum_mul, hπ1, one_mul] at h2
    linarith
  have hratio : (fun T : ℕ => (∑ t ∈ Finset.range (T + 1), expCostR θ i w' t) /
      (∑ t ∈ Finset.range (T + 1), expCostR θ i w'' t)) =
      fun T => (∑ s, drAvg P T i s * g w' s) / (∑ s, drAvg P T i s * g w'' s) := by
    funext T
    rw [hsum, hsum, mul_div_mul_left _ _ (by positivity)]
  unfold ratioCost
  rw [hratio]
  refine (Tendsto.limsup_eq ((hlim w').div (hlim w'') hYpos.ne')).trans ?_
  simp only [hg, Finset.mul_sum, mul_assoc]

end DermanSeqDecisions.Ratio

open DermanSeqDecisions.Ratio


theorem solution {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (hAssA : AssumptionA M)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a)
    (θ : Policy M) (D : S → Act → ℝ) (hD0 : ∀ s a, 0 ≤ D s a) (hD1 : ∀ s, ∑ a, D s a = 1)
    (hθ : IsStationaryRandomized θ D)
    (π : S → ℝ) (hπ0 : ∀ j, 0 ≤ π j)
    (hπ : ∀ j, π j - ∑ s, π s * inducedMatrix M D s j = 0) (hπ1 : ∑ j, π j = 1) (i : S) :
    ratioCost θ i w' w'' =
      (∑ s, ∑ a, π s * D s a * w' s a) / (∑ s, ∑ a, π s * D s a * w'' s a) := by
  exact ratio_stat_core M hAssA w' w'' hw'' θ D hD0 hD1 hθ π hπ0 hπ hπ1 i
