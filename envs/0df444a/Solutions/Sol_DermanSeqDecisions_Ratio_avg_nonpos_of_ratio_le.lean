-- Prove2me | solution 1 for DermanSeqDecisions.Ratio.avg_nonpos_of_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T22:59:13.488812+00:00
-- url     : https://prove2.me/submissions/b1786b4e-d107-4204-83bb-52d8736932fe

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

end DermanSeqDecisions.Ratio

open DermanSeqDecisions.Ratio


theorem solution {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a)
    (θ : Policy M) (i : S) (m : ℝ) (hψ : ratioCost θ i w' w'' ≤ m) :
    avgCostR θ i (fun s a => w' s a - m * w'' s a) ≤ 0 := by
  exact avg_nonpos_core M hA w' w'' hw' hw'' θ i m hψ
