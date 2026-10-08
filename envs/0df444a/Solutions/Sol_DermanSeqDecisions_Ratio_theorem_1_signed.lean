-- Prove2me | solution 1 for DermanSeqDecisions.Ratio.theorem_1_signed
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:17:56.289627+00:00
-- url     : https://prove2.me/submissions/8138347b-9a07-445e-bc2e-e24812eedef3

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

section Opt
variable {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act] [DecidableEq Act]

lemma dr_prob_real (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ) (θ : Policy M)
    (l : List (S × Act)) (s : S) : ∑ a, (θ.prob l s a).toReal = 1 := by
  have hs : ∑ a, θ.prob l s a = 1 := by have := θ.prob_sum l s; rwa [hA] at this
  rw [← ENNReal.toReal_sum, hs]; · simp
  intro a _
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← hs]
  exact Finset.single_le_sum (f := fun a => θ.prob l s a) (fun _ _ => bot_le) (Finset.mem_univ a)

lemma dr_V0 (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ) (θ : Policy M) (i : S)
    (u : S → ℝ) : expCostR θ i (fun s _ => u s) 0 = u i := by
  unfold expCostR
  rw [dr_sum_cons]
  simp [histProb, prevWeight, Fintype.sum_prod_type, apply_ite ENNReal.toReal, ite_mul]
  rw [← Finset.sum_mul, dr_prob_real M hA, one_mul]

lemma dr_next (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ) (θ : Policy M) (i : S)
    (u : S → ℝ) (n : ℕ) :
    expCostR θ i (fun s a => ∑ j, (M.P s a j).toReal * u j) n =
      expCostR θ i (fun s _ => u s) (n + 1) := by
  unfold expCostR
  rw [dr_sum_cons (n := n + 1)]
  simp only [List.ofFn_cons, Fin.cons_zero, histProb, dr_prevW_ofFn, ENNReal.toReal_mul]
  symm
  rw [Fintype.sum_prod_type]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  symm
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := dr_prob_real M hA θ (List.ofFn g) j
  calc (histProb θ i (List.ofFn g)).toReal * ((M.P (g 0).1 (g 0).2 j).toReal * u j)
      = (histProb θ i (List.ofFn g)).toReal * (M.P (g 0).1 (g 0).2 j).toReal * u j *
          ∑ a, (θ.prob (List.ofFn g) j a).toReal := by rw [this]; ring
    _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring

lemma dr_exp_mono {M : MDC S Act} (θ : Policy M) (i : S) (F G : S → Act → ℝ)
    (h : ∀ s a, F s a ≤ G s a) (t : ℕ) : expCostR θ i F t ≤ expCostR θ i G t :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (h _ _) ENNReal.toReal_nonneg

lemma dr_exp_add {M : MDC S Act} (θ : Policy M) (i : S) (F G : S → Act → ℝ) (β : ℝ)
    (t : ℕ) : expCostR θ i (fun s a => F s a + β * G s a) t =
      expCostR θ i F t + β * expCostR θ i G t := by
  simp only [expCostR, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_; ring

/-- deterministic decision rule of a stationary policy -/
noncomputable def drD {M : MDC S Act} (f : StationaryPolicy M) : S → Act → ℝ :=
  fun s a => if a = f.f s then 1 else 0

lemma dr_det_SR {M : MDC S Act} (f : StationaryPolicy M) :
    IsStationaryRandomized f.toPolicy (drD f) := by
  intro past s a
  simp only [StationaryPolicy.toPolicy, drD]
  split_ifs <;> simp

lemma dr_det_exp {M : MDC S Act} (f : StationaryPolicy M) (i : S) (F : S → Act → ℝ) (t : ℕ) :
    expCostR f.toPolicy i F t = ∑ s, (inducedMatrix M (drD f) ^ t) i s * F s (f.f s) := by
  have := dr_marg M f.toPolicy (drD f) (fun s a => by unfold drD; split_ifs <;> norm_num)
    (dr_det_SR f) i t (fun p => F p.1 p.2)
  unfold expCostR; rw [this]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  simp [drD]

lemma dr_det_exp_congr {M : MDC S Act} (f : StationaryPolicy M) (i : S) (F G : S → Act → ℝ)
    (h : ∀ s, F s (f.f s) = G s (f.f s)) (t : ℕ) :
    expCostR f.toPolicy i F t = expCostR f.toPolicy i G t := by
  rw [dr_det_exp, dr_det_exp]; simp_rw [h]

/-- Bellman fixed point. -/
lemma dr_bellman [Nonempty Act] (M : MDC S Act) (c : S → Act → ℝ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : ∃ v : S → ℝ, ∃ fa : S → Act, ∀ s,
      (∀ a, v s ≤ c s a + β * ∑ j, (M.P s a j).toReal * v j) ∧
      v s = c s (fa s) + β * ∑ j, (M.P s (fa s) j).toReal * v j := by
  let X : (S → ℝ) → S → Act → ℝ := fun u s a => c s a + β * ∑ j, (M.P s a j).toReal * u j
  let Tb : (S → ℝ) → S → ℝ := fun u s => Finset.univ.inf' Finset.univ_nonempty (X u s)
  have hX : ∀ u u' s a, |X u s a - X u' s a| ≤ β * dist u u' := by
    intro u u' s a
    have : X u s a - X u' s a = β * ∑ j, (M.P s a j).toReal * (u j - u' j) := by
      simp only [X, mul_sub, Finset.sum_sub_distrib]; ring
    rw [this, abs_mul, abs_of_nonneg hβ0]
    refine mul_le_mul_of_nonneg_left ?_ hβ0
    calc |∑ j, (M.P s a j).toReal * (u j - u' j)|
        ≤ ∑ j, |(M.P s a j).toReal * (u j - u' j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (M.P s a j).toReal * dist u u' := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          rw [← Real.dist_eq]; exact dist_le_pi_dist u u' j
      _ = dist u u' := by rw [← Finset.sum_mul, dr_P_row, one_mul]
  have hT : ContractingWith ⟨β, hβ0⟩ Tb := by
    refine ⟨by exact_mod_cast hβ1, LipschitzWith.of_dist_le_mul fun u u' => ?_⟩
    rw [dist_pi_le_iff (by positivity)]
    intro s
    simp only [NNReal.coe_mk, Real.dist_eq, Tb]
    obtain ⟨a1, -, ha1⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (X u s)
    obtain ⟨a2, -, ha2⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (X u' s)
    have h1 := Finset.inf'_le (X u s) (Finset.mem_univ a2)
    have h2 := Finset.inf'_le (X u' s) (Finset.mem_univ a1)
    obtain ⟨e1, e1'⟩ := abs_le.1 (hX u u' s a1)
    obtain ⟨e2, e2'⟩ := abs_le.1 (hX u u' s a2)
    change |_ - _| ≤ β * dist u u'
    rw [abs_le]; constructor <;> linarith
  set v := ContractingWith.fixedPoint Tb hT
  have hv : Tb v = v := hT.fixedPoint_isFixedPt
  refine ⟨v, fun s => (Finset.exists_mem_eq_inf' Finset.univ_nonempty (X v s)).choose,
    fun s => ⟨fun a => ?_, ?_⟩⟩
  · have := Finset.inf'_le (X v s) (Finset.mem_univ a)
    have e : Tb v s = v s := by rw [hv]
    simp only [Tb] at e
    rw [← e]; exact this
  · have e : Tb v s = v s := by rw [hv]
    simp only [Tb] at e
    rw [← e]
    exact (Finset.exists_mem_eq_inf' Finset.univ_nonempty (X v s)).choose_spec.2

end Opt

section Disc

lemma dr_summ (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (W : ℕ → ℝ) (K : ℝ)
    (hW : ∀ t, |W t| ≤ K) : Summable (fun t => β ^ t * W t) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K)
    fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  exact mul_le_mul_of_nonneg_left (hW t) (pow_nonneg hβ0 t)

lemma dr_seq_lim (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (W V : ℕ → ℝ) (K Kv : ℝ)
    (hW : ∀ t, |W t| ≤ K) (hV : ∀ t, |V t| ≤ Kv) :
    Tendsto (fun n => ∑ t ∈ Finset.range n, β ^ t * W t + β ^ n * V n) atTop
      (nhds (∑' t, β ^ t * W t)) := by
  rw [← add_zero (∑' t, β ^ t * W t)]
  refine ((dr_summ β hβ0 hβ1 W K hW).hasSum.tendsto_sum_nat).add ?_
  have h0 : Tendsto (fun n : ℕ => β ^ n * Kv) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const Kv
  refine squeeze_zero_norm (fun n => ?_) h0
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n)]
  exact mul_le_mul_of_nonneg_left (hV n) (pow_nonneg hβ0 n)

variable {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act] [DecidableEq Act]

lemma dr_exp_abs (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ) (θ : Policy M) (i : S)
    (c : S → Act → ℝ) (K : ℝ) (hK : ∀ s a, |c s a| ≤ K) (t : ℕ) :
    |expCostR θ i c t| ≤ K := by
  have := dr_exp_bounds M hA θ i c (-K) K (fun s a => abs_le.1 (hK s a)) t
  exact abs_le.2 this

lemma dr_disc (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ) (c : S → Act → ℝ) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (v : S → ℝ) (fa : S → Act)
    (hv : ∀ s, (∀ a, v s ≤ c s a + β * ∑ j, (M.P s a j).toReal * v j) ∧
      v s = c s (fa s) + β * ∑ j, (M.P s (fa s) j).toReal * v j)
    (f : StationaryPolicy M) (hf : f.f = fa) (θ : Policy M) (i : S) :
    ∑' t, β ^ t * expCostR f.toPolicy i c t ≤ ∑' t, β ^ t * expCostR θ i c t := by
  obtain ⟨K, -, hK⟩ := dr_abs_ub c
  obtain ⟨Kv, -, hKv⟩ := dr_abs_ub (fun s (_ : Act) => v s)
  have hKv' : ∀ s, |v s| ≤ Kv := fun s => by
    have := M.A_nonempty s
    exact hKv s this.choose
  -- generic seq
  let V : Policy M → ℕ → ℝ := fun θ n => expCostR θ i (fun s _ => v s) n
  have hVb : ∀ θ n, |V θ n| ≤ Kv := fun θ n =>
    dr_exp_abs M hA θ i (fun s _ => v s) Kv (fun s _ => hKv' s) n
  have hstep : ∀ θ n, V θ n ≤ expCostR θ i c n + β * V θ (n + 1) := by
    intro θ n
    calc V θ n ≤ expCostR θ i (fun s a => c s a + β * ∑ j, (M.P s a j).toReal * v j) n :=
          dr_exp_mono θ i _ _ (fun s a => (hv s).1 a) n
      _ = _ := by rw [dr_exp_add, dr_next M hA]
  have hstepf : ∀ n, V f.toPolicy n = expCostR f.toPolicy i c n + β * V f.toPolicy (n + 1) := by
    intro n
    calc V f.toPolicy n
        = expCostR f.toPolicy i (fun s a => c s a + β * ∑ j, (M.P s a j).toReal * v j) n :=
          dr_det_exp_congr f i _ _ (fun s => by rw [hf]; exact (hv s).2) n
      _ = _ := by rw [dr_exp_add, dr_next M hA]
  have h0 : ∀ θ, V θ 0 = v i := fun θ => dr_V0 M hA θ i v
  have hind : ∀ n, v i ≤ ∑ t ∈ Finset.range n, β ^ t * expCostR θ i c t + β ^ n * V θ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have := mul_le_mul_of_nonneg_left (hstep θ n) (pow_nonneg hβ0 n)
      nlinarith
  have hindf : ∀ n, v i = ∑ t ∈ Finset.range n, β ^ t * expCostR f.toPolicy i c t +
      β ^ n * V f.toPolicy n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ, ih, hstepf n]; ring
  have l1 := dr_seq_lim β hβ0 hβ1 (fun t => expCostR θ i c t) (V θ) K Kv
    (fun t => dr_exp_abs M hA θ i c K hK t) (hVb θ)
  have l2 := dr_seq_lim β hβ0 hβ1 (fun t => expCostR f.toPolicy i c t) (V f.toPolicy) K Kv
    (fun t => dr_exp_abs M hA f.toPolicy i c K hK t) (hVb f.toPolicy)
  have e2 : v i = ∑' t, β ^ t * expCostR f.toPolicy i c t := by
    have : Tendsto (fun n => ∑ t ∈ Finset.range n, β ^ t * expCostR f.toPolicy i c t +
      β ^ n * V f.toPolicy n) atTop (nhds (v i)) := by
      simp_rw [← hindf]; exact tendsto_const_nhds
    exact tendsto_nhds_unique this l2
  rw [← e2]
  exact ge_of_tendsto' l1 hind

end Disc

lemma dr_hasSum_lin (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t : ℕ => ((t : ℝ) + 1) * β ^ t) (1 / (1 - β) ^ 2) := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := β)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)
  have h2 := hasSum_geometric_of_lt_one hβ0 hβ1
  have h3 := h1.add h2
  have hne : (1 - β) ≠ 0 := by linarith
  have hv : 1 / (1 - β) ^ 2 = β / (1 - β) ^ 2 + (1 - β)⁻¹ := by field_simp; ring
  have hf : (fun t : ℕ => ((t : ℝ) + 1) * β ^ t) = fun b : ℕ => (b : ℝ) * β ^ b + β ^ b := by
    funext t; ring
  rw [hf, hv]; exact h3

lemma dr_abel_up (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℕ → ℝ) (K : ℝ)
    (hx : ∀ t, |x t| ≤ K) (a C : ℝ)
    (hS : ∀ T : ℕ, ∑ t ∈ Finset.range (T + 1), x t ≤ a * ((T : ℝ) + 1) + C) :
    (1 - β) * ∑' t, β ^ t * x t ≤ a + C * (1 - β) := by
  set S : ℕ → ℝ := fun T => ∑ t ∈ Finset.range (T + 1), x t with hSdef
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hx 0)
  have hSb : ∀ T, |S T| ≤ K * ((T : ℝ) + 1) := by
    intro T
    calc |S T| ≤ ∑ t ∈ Finset.range (T + 1), |x t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range (T + 1), K := Finset.sum_le_sum fun t _ => hx t
      _ = K * ((T : ℝ) + 1) := by simp; ring
  have hlin := dr_hasSum_lin β hβ0 hβ1
  have hsumS : Summable (fun t => β ^ t * S t) := by
    refine Summable.of_norm_bounded (hlin.summable.mul_left K) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    calc β ^ t * |S t| ≤ β ^ t * (K * ((t : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hSb t) (pow_nonneg hβ0 t)
      _ = K * (((t : ℝ) + 1) * β ^ t) := by ring
  set σ := ∑' t, β ^ t * S t
  have hσ : HasSum (fun t => β ^ t * S t) σ := hsumS.hasSum
  have hS' : HasSum (fun t => β ^ t * ∑ u ∈ Finset.range t, x u) (β * σ) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Finset.range_zero,
      Finset.sum_empty, mul_zero, sub_zero]
    have hf : (fun n : ℕ => β ^ (n + 1) * ∑ u ∈ Finset.range (n + 1), x u) =
        fun t => β * (β ^ t * S t) := by funext t; simp only [hSdef]; ring
    rw [hf]; exact hσ.mul_left β
  have hx' : HasSum (fun t => β ^ t * x t) (σ - β * σ) := by
    have hf : (fun t => β ^ t * x t) =
        fun t => β ^ t * S t - β ^ t * ∑ u ∈ Finset.range t, x u := by
      funext t; simp only [hSdef, Finset.sum_range_succ]; ring
    rw [hf]; exact hσ.sub hS'
  rw [hx'.tsum_eq]
  have hg : HasSum (fun t : ℕ => a * (((t : ℝ) + 1) * β ^ t) + C * β ^ t)
      (a * (1 / (1 - β) ^ 2) + C * (1 - β)⁻¹) :=
    (hlin.mul_left a).add ((hasSum_geometric_of_lt_one hβ0 hβ1).mul_left C)
  have hle : σ ≤ a * (1 / (1 - β) ^ 2) + C * (1 - β)⁻¹ := by
    refine hasSum_le (fun t => ?_) hσ hg
    have := mul_le_mul_of_nonneg_left (hS t) (pow_nonneg hβ0 t)
    calc β ^ t * S t ≤ β ^ t * (a * ((t : ℝ) + 1) + C) := this
      _ = _ := by ring
  have hpos : 0 < 1 - β := by linarith
  have : (1 - β) * (σ - β * σ) = (1 - β) ^ 2 * σ := by ring
  rw [this]
  calc (1 - β) ^ 2 * σ ≤ (1 - β) ^ 2 * (a * (1 / (1 - β) ^ 2) + C * (1 - β)⁻¹) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = a + C * (1 - β) := by field_simp

lemma dr_abel_low (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℕ → ℝ) (K : ℝ)
    (hx : ∀ t, |x t| ≤ K) (a C : ℝ)
    (hS : ∀ T : ℕ, a * ((T : ℝ) + 1) - C ≤ ∑ t ∈ Finset.range (T + 1), x t) :
    a - C * (1 - β) ≤ (1 - β) * ∑' t, β ^ t * x t := by
  have := dr_abel_up β hβ0 hβ1 (fun t => - x t) K (fun t => by rw [abs_neg]; exact hx t) (-a) C
    (fun T => by rw [Finset.sum_neg_distrib]; linarith [hS T])
  rw [tsum_congr (fun t => show β ^ t * -x t = -(β ^ t * x t) by ring), tsum_neg] at this
  linarith

section Ces2
variable {S : Type*} [Fintype S] [DecidableEq S]

lemma dr_avg_bound (P : Matrix S S ℝ) (h0 : ∀ s j, 0 ≤ P s j) (h1 : ∀ s, ∑ j, P s j = 1)
    (T : ℕ) : drAvg P T ∈ Metric.closedBall (0 : S → S → ℝ) 1 := by
  have hent : ∀ t s j, 0 ≤ (P ^ t) s j ∧ (P ^ t) s j ≤ 1 := fun t s j => by
    refine ⟨Matrix.pow_apply_nonneg h0 t s j, ?_⟩
    rw [← dr_pow_row P h0 h1 t s]
    exact Finset.single_le_sum (f := fun j => (P ^ t) s j)
      (fun l _ => Matrix.pow_apply_nonneg h0 t s l) (Finset.mem_univ j)
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro s; rw [pi_norm_le_iff_of_nonneg zero_le_one]; intro j
  rw [Real.norm_eq_abs, abs_le]
  simp only [drAvg]
  have hs0 : 0 ≤ ∑ t ∈ Finset.range (T + 1), (P ^ t) s j :=
    Finset.sum_nonneg fun t _ => (hent t s j).1
  have hs1 : ∑ t ∈ Finset.range (T + 1), (P ^ t) s j ≤ (T : ℝ) + 1 := by
    have := Finset.sum_le_sum (s := Finset.range (T + 1)) (fun t _ => (hent t s j).2)
    simpa using this
  constructor
  · have : 0 ≤ 1 / ((T : ℝ) + 1) * ∑ t ∈ Finset.range (T + 1), (P ^ t) s j := by
      positivity
    linarith
  · rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]; linarith

lemma dr_defect_tendsto (P : Matrix S S ℝ) (h0 : ∀ s j, 0 ≤ P s j) (h1 : ∀ s, ∑ j, P s j = 1)
    (s j : S) :
    Tendsto (fun T : ℕ => (1 / ((T : ℝ) + 1)) * ((P ^ (T + 1)) s j - (1 : Matrix S S ℝ) s j))
      atTop (nhds 0) := by
  have hb : ∀ T : ℕ, |(P ^ (T + 1)) s j - (1 : Matrix S S ℝ) s j| ≤ 2 := by
    intro T
    have e1 : 0 ≤ (P ^ (T + 1)) s j := Matrix.pow_apply_nonneg h0 _ s j
    have e2 : (P ^ (T + 1)) s j ≤ 1 := by
      rw [← dr_pow_row P h0 h1 (T + 1) s]
      exact Finset.single_le_sum (f := fun j => (P ^ (T + 1)) s j)
        (fun l _ => Matrix.pow_apply_nonneg h0 _ s l) (Finset.mem_univ j)
    have h2 : 0 ≤ (1 : Matrix S S ℝ) s j ∧ (1 : Matrix S S ℝ) s j ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> norm_num
    rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
  have ht : Tendsto (fun T : ℕ => 1 / ((T : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht2 : Tendsto (fun T : ℕ => 1 / ((T : ℝ) + 1) * 2) atTop (nhds 0) := by
    simpa using ht.mul_const (2 : ℝ)
  refine squeeze_zero_norm (fun T => ?_) ht2
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (hb T) (by positivity)

lemma dr_defect_R (P : Matrix S S ℝ) (T : ℕ) (s j : S) :
    ∑ l, P s l * drAvg P T l j - drAvg P T s j =
      (1 / ((T : ℝ) + 1)) * ((P ^ (T + 1)) s j - (1 : Matrix S S ℝ) s j) := by
  simp only [drAvg]
  simp_rw [mul_left_comm (P s _), ← Finset.mul_sum, ← mul_sub]
  congr 1
  have h' : ∀ t, ∑ l, P s l * (P ^ t) l j = (P ^ (t + 1)) s j := fun t => by
    rw [pow_succ', Matrix.mul_apply]
  have : ∑ l, P s l * ∑ t ∈ Finset.range (T+1), (P^t) l j
      = ∑ t ∈ Finset.range (T+1), (P ^ (t + 1)) s j := by
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; simp_rw [h']
  rw [this, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (P ^ t) s j)]
  simp

lemma dr_defect_L (P : Matrix S S ℝ) (T : ℕ) (s j : S) :
    ∑ l, drAvg P T s l * P l j - drAvg P T s j =
      (1 / ((T : ℝ) + 1)) * ((P ^ (T + 1)) s j - (1 : Matrix S S ℝ) s j) := by
  simp only [drAvg]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← mul_sub]
  congr 1
  have h' : ∀ t, ∑ l, (P ^ t) s l * P l j = (P ^ (t + 1)) s j := fun t => by
    rw [pow_succ, Matrix.mul_apply]
  have : ∑ l, (∑ t ∈ Finset.range (T+1), (P^t) s l) * P l j
      = ∑ t ∈ Finset.range (T+1), (P ^ (t + 1)) s j := by
    simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; simp_rw [h']
  rw [this, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (P ^ t) s j)]
  simp

lemma dr_limit_facts (P : Matrix S S ℝ) (h0 : ∀ s j, 0 ≤ P s j) (h1 : ∀ s, ∑ j, P s j = 1)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) (L : S → S → ℝ)
    (hL : Tendsto (fun n => drAvg P (ψ n)) atTop (nhds L)) :
    (∀ s j, ∑ l, P s l * L l j = L s j) ∧ (∀ s j, ∑ l, L s l * P l j = L s j) := by
  have hL' : ∀ s j, Tendsto (fun n => drAvg P (ψ n) s j) atTop (nhds (L s j)) := fun s j =>
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hL s) j
  constructor
  · intro s j
    have h1' : Tendsto (fun n => ∑ l, P s l * drAvg P (ψ n) l j - drAvg P (ψ n) s j) atTop
        (nhds (∑ l, P s l * L l j - L s j)) :=
      (tendsto_finsetSum _ fun l _ => (hL' l j).const_mul (P s l)).sub (hL' s j)
    simp_rw [dr_defect_R] at h1'
    have := tendsto_nhds_unique h1' ((dr_defect_tendsto P h0 h1 s j).comp hψ)
    linarith
  · intro s j
    have h1' : Tendsto (fun n => ∑ l, drAvg P (ψ n) s l * P l j - drAvg P (ψ n) s j) atTop
        (nhds (∑ l, L s l * P l j - L s j)) :=
      (tendsto_finsetSum _ fun l _ => (hL' s l).mul_const (P l j)).sub (hL' s j)
    simp_rw [dr_defect_L] at h1'
    have := tendsto_nhds_unique h1' ((dr_defect_tendsto P h0 h1 s j).comp hψ)
    linarith

lemma dr_cesaro_gen (P : Matrix S S ℝ) (h0 : ∀ s j, 0 ≤ P s j) (h1 : ∀ s, ∑ j, P s j = 1) :
    ∃ L : S → S → ℝ, Tendsto (drAvg P) atTop (nhds L) := by
  have hbd := Metric.isBounded_closedBall (x := (0 : S → S → ℝ)) (r := 1)
  obtain ⟨L1, -, φ1, hφ1, hL1⟩ := tendsto_subseq_of_bounded hbd (dr_avg_bound P h0 h1)
  have hf1 := dr_limit_facts P h0 h1 φ1 hφ1.tendsto_atTop L1 hL1
  -- L1 P^t = L1
  have hL1pow : ∀ t s j, ∑ l, L1 s l * (P ^ t) l j = L1 s j := by
    intro t; induction t with
    | zero => intro s j; simp [Matrix.one_apply]
    | succ t ih =>
      intro s j
      simp_rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul, ih]
      exact hf1.2 s j
  have hL1avg : ∀ T s j, ∑ l, L1 s l * drAvg P T l j = L1 s j := by
    intro T s j
    simp only [drAvg]
    simp_rw [mul_left_comm (L1 _ _), ← Finset.mul_sum]
    have : ∑ l, L1 s l * ∑ t ∈ Finset.range (T+1), (P^t) l j
        = ∑ t ∈ Finset.range (T+1), ∑ l, L1 s l * (P^t) l j := by
      simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    rw [this]; simp_rw [hL1pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; field_simp
  refine ⟨L1, tendsto_of_subseq_tendsto fun ns hns => ?_⟩
  obtain ⟨L2, -, φ, hφ, hL2⟩ := tendsto_subseq_of_bounded hbd (fun n => dr_avg_bound P h0 h1 (ns n))
  refine ⟨φ, ?_⟩
  have hψ : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hf2 := dr_limit_facts P h0 h1 (fun n => ns (φ n)) hψ L2 hL2
  have hL2avg : ∀ T s j, ∑ l, drAvg P T s l * L2 l j = L2 s j := by
    intro T s j
    have hp : ∀ t, ∑ l, (P ^ t) s l * L2 l j = L2 s j := fun t =>
      dr_pow_harm P (fun l => L2 l j) (fun l => hf2.1 l j) t s
    simp only [drAvg]
    simp_rw [mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
    have : ∑ l, ∑ t ∈ Finset.range (T+1), (P^t) s l * L2 l j
        = ∑ t ∈ Finset.range (T+1), ∑ l, (P^t) s l * L2 l j := Finset.sum_comm
    rw [this]; simp_rw [hp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; field_simp
  -- limits
  have hA : ∀ s j, ∑ l, L1 s l * L2 l j = L1 s j := by
    intro s j
    have h : Tendsto (fun n => ∑ l, L1 s l * drAvg P (ns (φ n)) l j) atTop
        (nhds (∑ l, L1 s l * L2 l j)) :=
      tendsto_finsetSum _ fun l _ =>
        (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hL2 l) j).const_mul (L1 s l)
    simp_rw [hL1avg] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hB : ∀ s j, ∑ l, L1 s l * L2 l j = L2 s j := by
    intro s j
    have h : Tendsto (fun n => ∑ l, drAvg P (φ1 n) s l * L2 l j) atTop
        (nhds (∑ l, L1 s l * L2 l j)) :=
      tendsto_finsetSum _ fun l _ =>
        (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hL1 s) l).mul_const (L2 l j)
    simp_rw [hL2avg] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have : L2 = L1 := by funext s j; rw [← hA s j, hB s j]
  rw [← this]; exact hL2

end Ces2

section T1

lemma dr_partial_abs (x : ℕ → ℝ) (K : ℝ) (hx : ∀ t, |x t| ≤ K) (T : ℕ) :
    |∑ t ∈ Finset.range (T + 1), x t| ≤ K * ((T : ℝ) + 1) := by
  calc |∑ t ∈ Finset.range (T + 1), x t| ≤ ∑ t ∈ Finset.range (T + 1), |x t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range (T + 1), K := Finset.sum_le_sum fun t _ => hx t
    _ = K * ((T : ℝ) + 1) := by simp; ring

lemma dr_upper_C (x : ℕ → ℝ) (K : ℝ) (hx : ∀ t, |x t| ≤ K) (b : ℝ)
    (hev : ∀ᶠ T : ℕ in atTop, (1 / (T : ℝ)) * ∑ t ∈ Finset.range (T + 1), x t < b) :
    ∃ C, ∀ T : ℕ, ∑ t ∈ Finset.range (T + 1), x t ≤ b * ((T : ℝ) + 1) + C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hx 0)
  refine ⟨(K + |b|) * ((N : ℝ) + 1) + |b|, fun T => ?_⟩
  have hpa := abs_le.1 (dr_partial_abs x K hx T)
  rcases lt_or_ge T (max N 1) with hT | hT
  · have hT' : (T : ℝ) + 1 ≤ (N : ℝ) + 1 := by
      have : T ≤ N := by
        rcases le_or_gt N 1 with h | h
        · have : T < 1 := lt_of_lt_of_le hT (by simp [h]); omega
        · have : T < N := lt_of_lt_of_le hT (by simp [h.le]); omega
      exact_mod_cast Nat.add_le_add_right this 1
    have e1 : K * ((T : ℝ) + 1) ≤ K * ((N : ℝ) + 1) := mul_le_mul_of_nonneg_left hT' hK0
    have e2 : -(|b| * ((N : ℝ) + 1)) ≤ b * ((T : ℝ) + 1) := by
      have := neg_abs_le b
      nlinarith [abs_nonneg b]
    nlinarith [abs_nonneg b]
  · have hTN : N ≤ T := le_trans (le_max_left _ _) hT
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast le_trans (le_max_right _ _) hT
    have := hN T hTN
    rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ (by positivity)] at this
    have e3 : -b ≤ |b| := neg_le_abs b
    nlinarith [abs_nonneg b, hK0]

lemma dr_lower_C (x : ℕ → ℝ) (K : ℝ) (hx : ∀ t, |x t| ≤ K) (b : ℝ)
    (hev : ∀ᶠ T : ℕ in atTop, b < (1 / ((T : ℝ) + 1)) * ∑ t ∈ Finset.range (T + 1), x t) :
    ∃ C, ∀ T : ℕ, b * ((T : ℝ) + 1) - C ≤ ∑ t ∈ Finset.range (T + 1), x t := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hx 0)
  refine ⟨(K + |b|) * ((N : ℝ) + 1), fun T => ?_⟩
  have hpa := abs_le.1 (dr_partial_abs x K hx T)
  rcases lt_or_ge T N with hT | hT
  · have hT' : (T : ℝ) + 1 ≤ (N : ℝ) + 1 := by
      have : T ≤ N := hT.le
      exact_mod_cast Nat.add_le_add_right this 1
    have e1 : K * ((T : ℝ) + 1) ≤ K * ((N : ℝ) + 1) := mul_le_mul_of_nonneg_left hT' hK0
    have e2 : b * ((T : ℝ) + 1) ≤ |b| * ((N : ℝ) + 1) := by
      have := le_abs_self b
      nlinarith [abs_nonneg b]
    nlinarith
  · have := hN T hT
    rw [one_div, ← div_eq_inv_mul, lt_div_iff₀ (by positivity)] at this
    nlinarith [abs_nonneg b, hK0]

variable {S Act : Type*} [Fintype S] [DecidableEq S] [Fintype Act] [DecidableEq Act]

lemma dr_induced_row (M : MDC S Act) (D : S → Act → ℝ) (hD1 : ∀ s, ∑ a, D s a = 1) (s : S) :
    ∑ j, inducedMatrix M D s j = 1 := by
  simp only [inducedMatrix]
  rw [Finset.sum_comm]
  simp_rw [mul_comm _ (D s _), ← Finset.mul_sum, dr_P_row, mul_one, hD1]

theorem t1_core [Nonempty S] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (c : S → Act → ℝ) :
    ∃ f : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
      avgCostR f.toPolicy i c ≤ avgCostR θ i c := by
  have := dr_nonempty_act M
  let β : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hβ0 : ∀ n, 0 ≤ β n := fun n => by
    have : 1 / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    simp only [β]; linarith
  have hβ1 : ∀ n, β n < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [β]; linarith
  have hB := fun n => dr_bellman M c (β n) (hβ0 n) (hβ1 n)
  choose v fa hvfa using hB
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber fa
  have hfreq : ∀ N, ∃ n ≥ N, fa n = y := by
    intro N
    obtain ⟨n, hn, hgt⟩ := (Set.infinite_coe_iff.1 hy).exists_gt N
    exact ⟨n, hgt.le, hn⟩
  let f : StationaryPolicy M := ⟨y, fun s => by rw [hA]; exact Finset.mem_univ _⟩
  refine ⟨f, fun θ i => ?_⟩
  obtain ⟨K, hK0, hK⟩ := dr_abs_ub c
  have hxθ := fun t => dr_exp_abs M hA θ i c K hK t
  have hxf := fun t => dr_exp_abs M hA f.toPolicy i c K hK t
  -- Cesàro limit for f
  set P := inducedMatrix M (drD f)
  have hD0 : ∀ s a, 0 ≤ drD f s a := fun s a => by unfold drD; split_ifs <;> norm_num
  have hD1 : ∀ s, ∑ a, drD f s a = 1 := fun s => by simp [drD]
  have h0 : ∀ s j, 0 ≤ P s j := fun s j =>
    Finset.sum_nonneg fun a _ => mul_nonneg ENNReal.toReal_nonneg (hD0 s a)
  obtain ⟨L, hL⟩ := dr_cesaro_gen P h0 (dr_induced_row M _ hD1)
  set g : S → ℝ := fun s => c s (f.f s)
  have hyf : ∀ T : ℕ, (1 / ((T : ℝ) + 1)) * ∑ t ∈ Finset.range (T + 1), expCostR f.toPolicy i c t
      = ∑ s, drAvg P T i s * g s := by
    intro T
    simp only [dr_det_exp, drAvg]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [g, P, Finset.sum_mul, mul_assoc]
  set Lf := ∑ s, L i s * g s
  have hLf : Tendsto (fun T : ℕ => (1 / ((T : ℝ) + 1)) *
      ∑ t ∈ Finset.range (T + 1), expCostR f.toPolicy i c t) atTop (nhds Lf) := by
    simp_rw [hyf]
    exact tendsto_finsetSum _ fun s _ =>
      (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hL i) s).mul_const _
  have hQf : avgCostR f.toPolicy i c = Lf := by
    unfold avgCostR
    have hr : Tendsto (fun T : ℕ => ((T : ℝ) + 1) / T) atTop (nhds 1) := by
      have : Tendsto (fun T : ℕ => 1 + 1 / (T : ℝ)) atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with T hT
      have : (T : ℝ) ≠ 0 := by positivity
      field_simp
    have := hr.mul hLf
    rw [one_mul] at this
    refine Tendsto.limsup_eq (this.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with T hT
    have : (T : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hQf]
  set Q := avgCostR θ i c
  apply le_of_forall_pos_le_add
  intro ε hε
  -- upper bound for θ
  have hbθ : IsBoundedUnder (· ≤ ·) atTop (fun T : ℕ => (1 / (T : ℝ)) *
      ∑ t ∈ Finset.range (T + 1), expCostR θ i c t) := by
    refine isBoundedUnder_of ⟨2 * K, fun T => ?_⟩
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp; positivity
    · have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
      have := (abs_le.1 (dr_partial_abs _ K hxθ T)).2
      show 1 / (T : ℝ) * _ ≤ 2 * K
      rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      nlinarith
  have hevθ : ∀ᶠ T : ℕ in atTop, (1 / (T : ℝ)) * ∑ t ∈ Finset.range (T + 1),
      expCostR θ i c t < Q + ε / 3 :=
    eventually_lt_of_limsup_lt (lt_add_of_pos_right Q (by positivity : (0:ℝ) < ε / 3)) hbθ
  obtain ⟨C1, hC1⟩ := dr_upper_C _ K hxθ (Q + ε / 3) hevθ
  have hevf : ∀ᶠ T : ℕ in atTop, Lf - ε / 3 < (1 / ((T : ℝ) + 1)) *
      ∑ t ∈ Finset.range (T + 1), expCostR f.toPolicy i c t :=
    hLf.eventually (lt_mem_nhds (by linarith))
  obtain ⟨C2, hC2⟩ := dr_lower_C _ K hxf (Lf - ε / 3) hevf
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((|C1| + |C2|) / (ε / 3))
  obtain ⟨n, hn, hfn⟩ := hfreq N0
  have hdisc := dr_disc M hA c (β n) (hβ0 n) (hβ1 n) (v n) (fa n) (hvfa n) f hfn.symm θ i
  have hup := dr_abel_up (β n) (hβ0 n) (hβ1 n) _ K hxθ (Q + ε / 3) C1 hC1
  have hlow := dr_abel_low (β n) (hβ0 n) (hβ1 n) _ K hxf (Lf - ε / 3) C2 hC2
  have hpos : 0 < 1 - β n := by linarith [hβ1 n]
  have hmid := mul_le_mul_of_nonneg_left hdisc hpos.le
  have h1b : 1 - β n = 1 / ((n : ℝ) + 2) := by simp only [β]; ring
  have hsmall : (|C1| + |C2|) * (1 - β n) ≤ ε / 3 := by
    rw [h1b, mul_one_div, div_le_iff₀ (by positivity)]
    have hn' : (N0 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ (by positivity)] at hN0
    nlinarith
  have e1 : C1 * (1 - β n) ≤ |C1| * (1 - β n) := mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
  have e2 : C2 * (1 - β n) ≤ |C2| * (1 - β n) := mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
  nlinarith

end T1

end DermanSeqDecisions.Ratio

open DermanSeqDecisions.Ratio


theorem solution {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (c : S → Act → ℝ) :
    ∃ f : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
      avgCostR f.toPolicy i c ≤ avgCostR θ i c := by
  exact t1_core M hA c
