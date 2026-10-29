-- Prove2me | solution 1 for GaoImpatientMNL.Pricing.lemma_F_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:31:28.899989+00:00
-- url     : https://prove2.me/submissions/34e6e5f5-0d3f-4227-8c6d-93d82b8f1a67

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Relaxation

open GaoImpatientMNL.Pricing

namespace GaoS226

noncomputable def F (a b : ℝ) : ℝ := (a - b) * Real.log (a * b)
noncomputable def S (l : ℕ) (q : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range l, F (q k) (q (k + 1))
noncomputable def E (T x : ℝ) : ℝ := (1 - x) * Real.log (T / (1 - x))

lemma g_eq (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : relaxationReal T l q = S l q + E T (q l) := by
  unfold relaxationReal S E F
  split_ifs with h
  · simp [h]
  · rfl

lemma relax_eq (T : ℝ) (l : ℕ) (q : ℕ → ℝ) (h : q l ≠ 0) :
    relaxation T l q = ((S l q + E T (q l) : ℝ) : EReal) := by
  unfold relaxation; rw [if_neg h, g_eq]

lemma F_self (a : ℝ) : F a a = 0 := by simp [F]

lemma F_nonpos {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (ha : a ≤ 1) : F a b ≤ 0 := by
  unfold F
  apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
  apply Real.log_nonpos (mul_nonneg (by linarith) hb)
  nlinarith

lemma feas_mono {l : ℕ} {q : ℕ → ℝ} (h : QFeasible l q) {m : ℕ} (hm : m ≤ l) : QFeasible m q :=
  ⟨h.1, fun k hk => h.2 k (by omega)⟩

lemma chain_bounds {l : ℕ} {q : ℕ → ℝ} (h : QFeasible l q) :
    ∀ k ≤ l, 0 ≤ q k ∧ q k ≤ 1 ∧ q l ≤ q k := by
  have up : ∀ k ≤ l, q k ≤ 1 := by
    intro k hk
    induction k with
    | zero => rw [h.1]
    | succ k ih => exact le_trans (h.2 k (by omega)).2 (ih (by omega))
  have low : ∀ n, ∀ k, k + n = l → q l ≤ q k := by
    intro n
    induction n with
    | zero => intro k hk; simp at hk; subst hk; rfl
    | succ n ih =>
      intro k hk
      exact le_trans (ih (k + 1) (by omega)) (h.2 k (by omega)).2
  have hl0 : 0 ≤ q l := by
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0; rw [h.1]; norm_num
    · have := (h.2 (l - 1) (by omega)).1
      rwa [show l - 1 + 1 = l by omega] at this
  intro k hk
  have := low (l - k) k (by omega)
  exact ⟨le_trans hl0 this, up k hk, this⟩

lemma S_nonpos {l : ℕ} {q : ℕ → ℝ} (h : QFeasible l q) : S l q ≤ 0 := by
  unfold S
  apply Finset.sum_nonpos
  intro k hk
  rw [Finset.mem_range] at hk
  have := chain_bounds h k (by omega)
  exact F_nonpos (h.2 k hk).1 (h.2 k hk).2 this.2.1

lemma E_eq (T x : ℝ) (hT : 0 < T) : E T x = (1 - x) * Real.log T + Real.negMulLog (1 - x) := by
  unfold E Real.negMulLog
  by_cases h : 1 - x = 0
  · rw [h]; simp
  · rw [Real.log_div hT.ne' h]; ring

lemma E_le (T x : ℝ) (hT : 0 < T) (h0 : 0 ≤ x) (h1 : x ≤ 1) : E T x ≤ |Real.log T| + 1 := by
  rw [E_eq T x hT]
  have a1 : (1 - x) * Real.log T ≤ |Real.log T| := by
    calc (1 - x) * Real.log T ≤ (1 - x) * |Real.log T| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
      _ ≤ 1 * |Real.log T| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = _ := one_mul _
  have a2 : Real.negMulLog (1 - x) ≤ 1 := by
    unfold Real.negMulLog
    rcases eq_or_lt_of_le (show 0 ≤ 1 - x by linarith) with h | h
    · rw [← h]; simp
    · have := Real.one_sub_inv_le_log_of_pos h
      have : (1 - x) * (1 - (1 - x)⁻¹) ≤ (1 - x) * Real.log (1 - x) :=
        mul_le_mul_of_nonneg_left this h.le
      rw [mul_sub, mul_inv_cancel₀ h.ne'] at this
      nlinarith
  linarith

/-- blow-up near q_m = 0 -/
lemma blowup : ∀ m : ℕ, ∀ M : ℝ, ∃ δ > 0, ∀ q : ℕ → ℝ, QFeasible m q → 0 < q m → q m < δ →
    S m q ≤ -M := by
  intro m
  induction m with
  | zero =>
    intro M; refine ⟨1, one_pos, fun q hq _ h1 => ?_⟩
    rw [hq.1] at h1; exact absurd h1 (lt_irrefl _)
  | succ m ih =>
    intro M
    obtain ⟨δ', hδ', hS⟩ := ih M
    refine ⟨min (δ' / 2) (Real.exp (-2 * M / δ')), lt_min (by linarith) (Real.exp_pos _), ?_⟩
    intro q hq hpos hlt
    have hqm := feas_mono hq (Nat.le_succ m)
    have cb := chain_bounds hq m (by omega)
    have st := hq.2 m (by omega)
    have hpm : 0 < q m := lt_of_lt_of_le hpos st.2
    have hSm : S (m + 1) q = S m q + F (q m) (q (m + 1)) := by
      unfold S; rw [Finset.sum_range_succ]
    rw [hSm]
    by_cases hc : q m < δ'
    · have := hS q hqm hpm hc
      have := F_nonpos st.1 st.2 cb.2.1
      linarith
    · push_neg at hc
      have h1 : q (m + 1) < δ' / 2 := lt_of_lt_of_le hlt (min_le_left _ _)
      have h2 : q (m + 1) < Real.exp (-2 * M / δ') := lt_of_lt_of_le hlt (min_le_right _ _)
      have hlog : Real.log (q (m + 1)) < -2 * M / δ' := by
        rw [Real.log_lt_iff_lt_exp hpos]; exact h2
      have hlogle : Real.log (q m * q (m + 1)) ≤ Real.log (q (m + 1)) := by
        apply Real.log_le_log (mul_pos hpm hpos)
        nlinarith [cb.2.1]
      have hq1 : q (m + 1) < 1 := by linarith [cb.2.1]
      have hneg : Real.log (q (m + 1)) < 0 := Real.log_neg hpos hq1
      have hF : F (q m) (q (m + 1)) ≤ δ' / 2 * Real.log (q (m + 1)) := by
        unfold F
        calc (q m - q (m + 1)) * Real.log (q m * q (m + 1))
            ≤ (q m - q (m + 1)) * Real.log (q (m + 1)) :=
              mul_le_mul_of_nonneg_left hlogle (by linarith)
          _ ≤ δ' / 2 * Real.log (q (m + 1)) := by
              apply mul_le_mul_of_nonpos_right (by linarith) hneg.le
      have : δ' / 2 * Real.log (q (m + 1)) ≤ -M := by
        have := mul_lt_mul_of_pos_left hlog (show 0 < δ' / 2 by linarith)
        have e : δ' / 2 * (-2 * M / δ') = -M := by field_simp
        linarith
      have := S_nonpos hqm
      linarith

/-- reference point -/
noncomputable def x0 (T : ℝ) : ℝ := (T + 2) / (2 * T + 2)
noncomputable def q0 (T : ℝ) : ℕ → ℝ := fun k => if k = 0 then 1 else x0 T

lemma x0_pos (T : ℝ) (hT : 0 < T) : 0 < x0 T := by unfold x0; positivity
lemma x0_lt (T : ℝ) (hT : 0 < T) : x0 T < 1 := by
  unfold x0; rw [div_lt_one (by linarith)]; linarith

lemma q0_feas (T : ℝ) (hT : 0 < T) (l : ℕ) : QFeasible l (q0 T) := by
  refine ⟨by simp [q0], fun k _ => ?_⟩
  have := x0_pos T hT; have := x0_lt T hT
  simp only [q0]; split_ifs <;> (try contradiction) <;> constructor <;> linarith

lemma q0_val (T : ℝ) (hT : 0 < T) (l : ℕ) (hl : 0 < l) :
    0 < S l (q0 T) + E T (q0 T l) := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  have hS : S (n + 1) (q0 T) = (1 - x0 T) * Real.log (x0 T) := by
    unfold S; rw [Finset.sum_range_succ']
    simp [q0, F]
  have hx := x0_pos T hT; have hx1 := x0_lt T hT
  rw [hS]; simp only [q0, if_neg (Nat.succ_ne_zero n), E]
  rw [← mul_add, ← Real.log_mul hx.ne' (div_pos hT (by linarith)).ne']
  apply mul_pos (by linarith)
  apply Real.log_pos
  rw [← mul_div_assoc, one_lt_div (by linarith)]
  unfold x0
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith)]
  field_simp
  nlinarith

/-- update lemmas -/
lemma S_update (q : ℕ → ℝ) (i n : ℕ) (x : ℝ) :
    S (i + 2 + n) (Function.update q (i + 1) x) = S (i + 2 + n) q - F (q i) (q (i + 1))
      - F (q (i + 1)) (q (i + 2)) + F (q i) x + F x (q (i + 2)) := by
  induction n with
  | zero =>
    unfold S
    simp only [Nat.add_zero, Finset.sum_range_succ]
    have : ∑ k ∈ Finset.range i, F (Function.update q (i + 1) x k)
        (Function.update q (i + 1) x (k + 1)) = ∑ k ∈ Finset.range i, F (q k) (q (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk; rw [Finset.mem_range] at hk
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    rw [this]
    simp only [Function.update_self, Function.update_of_ne (show i ≠ i + 1 by omega),
      Function.update_of_ne (show i + 1 + 1 ≠ i + 1 by omega)]
    ring
  | succ n ih =>
    have e : ∀ q : ℕ → ℝ, S (i + 2 + (n + 1)) q = S (i + 2 + n) q +
        F (q (i + 2 + n)) (q (i + 2 + n + 1)) := by
      intro q; unfold S; rw [show i + 2 + (n + 1) = i + 2 + n + 1 by omega, Finset.sum_range_succ]
    rw [e, e, ih, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    ring

lemma S_update_last (q : ℕ → ℝ) (i : ℕ) (x : ℝ) :
    S (i + 1) (Function.update q (i + 1) x) = S (i + 1) q - F (q i) (q (i + 1)) + F (q i) x := by
  unfold S
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have : ∑ k ∈ Finset.range i, F (Function.update q (i + 1) x k)
      (Function.update q (i + 1) x (k + 1)) = ∑ k ∈ Finset.range i, F (q k) (q (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_range] at hk
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  rw [this, Function.update_self, Function.update_of_ne (by omega)]
  ring

lemma feas_update {l : ℕ} {q : ℕ → ℝ} (h : QFeasible l q) (j : ℕ) (hj1 : 1 ≤ j) (hjl : j ≤ l)
    (x : ℝ) (hx0 : 0 ≤ x) (hxu : x ≤ q (j - 1)) (hxd : j < l → q (j + 1) ≤ x) :
    QFeasible l (Function.update q j x) := by
  refine ⟨by rw [Function.update_of_ne (by omega)]; exact h.1, fun k hk => ?_⟩
  have hk' := h.2 k hk
  by_cases e1 : k + 1 = j
  · subst e1
    rw [Function.update_self, Function.update_of_ne (by omega)]
    exact ⟨hx0, by simpa using hxu⟩
  · by_cases e2 : k = j
    · subst e2
      rw [Function.update_self, Function.update_of_ne (by omega)]
      exact ⟨hk'.1, hxd hk⟩
    · rw [Function.update_of_ne e1, Function.update_of_ne e2]; exact hk'

lemma mid_improve {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hc : c = a ∨ c = b) :
    F b c + F c a < F b ((a + b) / 2) + F ((a + b) / 2) a := by
  have hb : 0 < b := by linarith
  have hx : 0 < (a + b) / 2 := by linarith
  have hsum : F b c + F c a = F b a := by
    rcases hc with rfl | rfl
    · rw [F_self]; ring
    · rw [F_self]; ring
  rw [hsum]
  unfold F
  rw [Real.log_mul hb.ne' ha.ne', Real.log_mul hb.ne' hx.ne', Real.log_mul hx.ne' ha.ne']
  have key : Real.log a + Real.log b < 2 * Real.log ((a + b) / 2) := by
    rw [← Real.log_mul ha.ne' hb.ne', ← Real.log_rpow hx, Real.log_lt_log_iff (by positivity)
      (by positivity)]
    rw [show ((a + b) / 2) ^ (2 : ℝ) = ((a + b) / 2) ^ (2 : ℕ) by norm_cast]
    nlinarith [sq_pos_of_pos (show 0 < b - a by linarith)]
  nlinarith

lemma find_j {l : ℕ} {q : ℕ → ℝ} (h : QFeasible l q) (h1 : q l < 1)
    (ht : ∃ k < l, q (k + 1) = q k) :
    ∃ i, i + 2 ≤ l ∧ q (i + 2) < q i ∧ (q (i + 1) = q i ∨ q (i + 2) = q (i + 1)) := by
  by_contra hno
  push_neg at hno
  have prop : ∀ i, i + 2 ≤ l → (q (i + 1) = q i ↔ q (i + 2) = q (i + 1)) := by
    intro i hi
    have s1 := h.2 i (by omega); have s2 := h.2 (i + 1) (by omega)
    constructor
    · intro e
      by_contra ne
      have : q (i + 2) < q i := by
        have := lt_of_le_of_ne s2.2 ne; linarith
      exact (hno i hi this).1 e
    · intro e
      by_contra ne
      have : q (i + 2) < q i := by
        have := lt_of_le_of_ne s1.2 ne; linarith
      exact (hno i hi this).2 e
  obtain ⟨k, hk, hke⟩ := ht
  have all0 : ∀ m < l, (q (m + 1) = q m ↔ q (0 + 1) = q 0) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih => rw [← ih (by omega)]; exact (prop m (by omega)).symm
  have allt : ∀ m < l, q (m + 1) = q m := fun m hm => (all0 m hm).2 ((all0 k hk).1 hke)
  have : ∀ m ≤ l, q m = 1 := by
    intro m hm
    induction m with
    | zero => exact h.1
    | succ m ih => rw [allt m (by omega)]; exact ih (by omega)
  have := this l le_rfl
  linarith

lemma improve (T : ℝ) {l : ℕ} {q : ℕ → ℝ} (h : QFeasible l q) (hp : 0 < q l) (h1 : q l < 1)
    (ht : ∃ k < l, q (k + 1) = q k) :
    ∃ r, QFeasible l r ∧ r l = q l ∧ relaxationReal T l q < relaxationReal T l r := by
  obtain ⟨i, hi, hlt, hor⟩ := find_j h h1 ht
  obtain ⟨n, rfl⟩ : ∃ n, l = i + 2 + n := ⟨l - (i + 2), by omega⟩
  have cb := chain_bounds h (i + 2) (by omega)
  have ha : 0 < q (i + 2) := lt_of_lt_of_le hp cb.2.2
  refine ⟨Function.update q (i + 1) ((q (i + 2) + q i) / 2), ?_, ?_, ?_⟩
  · apply feas_update h (i + 1) (by omega) (by omega)
    · linarith
    · simp; linarith
    · intro _; linarith
  · rw [Function.update_of_ne (by omega)]
  · rw [g_eq, g_eq, S_update, Function.update_of_ne (by omega)]
    have : q (i + 1) = q (i + 2) ∨ q (i + 1) = q i := by
      rcases hor with e | e
      · right; exact e
      · left; exact e.symm
    have := mid_improve ha hlt this
    linarith

lemma max_props (T : ℝ) (hT : 0 < T) (l : ℕ) (hl : 0 < l) (q : ℕ → ℝ)
    (hq : IsRelaxationMax T l q) :
    0 < q l ∧ q l < 1 ∧ (∀ k < l, q (k + 1) < q k) ∧
      0 < S l q + E T (q l) := by
  have hr := hq.2 (q0 T) (q0_feas T hT l)
  have hq0l : q0 T l ≠ 0 := by
    simp only [q0, if_neg hl.ne']; exact (x0_pos T hT).ne'
  rw [relax_eq T l _ hq0l] at hr
  have hne : q l ≠ 0 := by
    intro e
    unfold relaxation at hr; rw [if_pos e] at hr
    exact absurd hr (not_le.2 (EReal.bot_lt_coe _))
  rw [relax_eq T l _ hne, EReal.coe_le_coe_iff] at hr
  have pos := lt_of_lt_of_le (q0_val T hT l hl) hr
  have cb := chain_bounds hq.1 l le_rfl
  have hp : 0 < q l := lt_of_le_of_ne cb.1 (Ne.symm hne)
  have h1 : q l < 1 := by
    rcases lt_or_eq_of_le cb.2.1 with h | h
    · exact h
    · exfalso
      have : E T (q l) = 0 := by simp [E, h]
      have := S_nonpos hq.1
      linarith
  refine ⟨hp, h1, ?_, pos⟩
  by_contra hc
  push_neg at hc
  obtain ⟨k, hk, hke⟩ := hc
  have ht : ∃ k < l, q (k + 1) = q k := ⟨k, hk, le_antisymm (hq.1.2 k hk).2 hke⟩
  obtain ⟨r, hrf, hrl, hlt⟩ := improve T hq.1 hp h1 ht
  have := hq.2 r hrf
  rw [relax_eq T l _ (by rw [hrl]; exact hne), relax_eq T l _ hne, EReal.coe_le_coe_iff,
    ← g_eq, ← g_eq] at this
  linarith

lemma G_congr (T : ℝ) (l : ℕ) (q r : ℕ → ℝ) (h : ∀ k ≤ l, q k = r k) :
    S l q + E T (q l) = S l r + E T (r l) := by
  have : S l q = S l r := by
    unfold S; apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_range] at hk
    rw [h k (by omega), h (k + 1) (by omega)]
  rw [this, h l le_rfl]

noncomputable def trunc (l : ℕ) (q : ℕ → ℝ) : ℕ → ℝ := fun k => if k ≤ l then q k else 0

lemma trunc_feas {l : ℕ} {q : ℕ → ℝ} (h : QFeasible l q) : QFeasible l (trunc l q) := by
  refine ⟨by simp [trunc, h.1], fun k hk => ?_⟩
  simp only [trunc, if_pos (show k ≤ l by omega), if_pos (show k + 1 ≤ l by omega)]
  exact h.2 k hk

lemma exists_max (T : ℝ) (hT : 0 < T) (l : ℕ) (hl : 0 < l) : ∃ q, IsRelaxationMax T l q := by
  set C := |Real.log T| + 1
  set v0 := S l (q0 T) + E T (q0 T l)
  obtain ⟨δ0, hδ0, hb⟩ := blowup l (C - v0 + 1)
  set δ := min δ0 (x0 T)
  have hδ : 0 < δ := lt_min hδ0 (x0_pos T hT)
  set K := {q : ℕ → ℝ | (q 0 = 1 ∧ ∀ k < l, 0 ≤ q (k + 1) ∧ q (k + 1) ≤ q k) ∧ δ ≤ q l ∧
    ∀ k, l < k → q k = 0} with hK
  have hKc : IsCompact K := by
    apply IsCompact.of_isClosed_subset
      (isCompact_univ_pi (fun _ : ℕ => isCompact_Icc (a := (0 : ℝ)) (b := 1)))
    · rw [hK]
      simp only [Set.setOf_and, Set.setOf_forall]
      refine ((isClosed_eq (continuous_apply 0) continuous_const).inter
        (isClosed_iInter fun k => isClosed_iInter fun _ =>
          (isClosed_le continuous_const (continuous_apply _)).inter
          (isClosed_le (continuous_apply _) (continuous_apply _)))).inter
        ((isClosed_le continuous_const (continuous_apply _)).inter
          (isClosed_iInter fun k => isClosed_iInter fun _ =>
            isClosed_eq (continuous_apply _) continuous_const))
    · intro q hq
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      intro k
      by_cases hk : k ≤ l
      · have := chain_bounds (l := l) hq.1 k hk; exact ⟨this.1, this.2.1⟩
      · rw [hq.2.2 k (by omega)]; norm_num
  have hq0K : trunc l (q0 T) ∈ K := by
    refine ⟨trunc_feas (q0_feas T hT l), ?_, ?_⟩
    · simp only [trunc, le_refl, if_true, q0, if_neg hl.ne']; exact min_le_right _ _
    · intro k hk; simp only [trunc, if_neg (show ¬ k ≤ l by omega)]
  have hcont : ContinuousOn (fun q : ℕ → ℝ => S l q + E T (q l)) K := by
    apply ContinuousOn.add
    · unfold S F
      apply continuousOn_finset_sum
      intro k hk
      rw [Finset.mem_range] at hk
      apply ContinuousOn.mul
      · exact ((continuous_apply k).sub (continuous_apply (k + 1))).continuousOn
      · apply ContinuousOn.log
        · exact ((continuous_apply k).mul (continuous_apply (k + 1))).continuousOn
        · intro q hq
          have c1 := chain_bounds (l := l) hq.1 k (by omega)
          have c2 := chain_bounds (l := l) hq.1 (k + 1) (by omega)
          have : 0 < q l := lt_of_lt_of_le hδ hq.2.1
          exact (mul_pos (by linarith) (by linarith)).ne'
    · have : (fun q : ℕ → ℝ => E T (q l)) =
          fun q => (1 - q l) * Real.log T + Real.negMulLog (1 - q l) := by
        funext q; exact E_eq T (q l) hT
      rw [this]
      exact (((continuous_const.sub (continuous_apply l)).mul continuous_const).add
        (Real.continuous_negMulLog.comp (continuous_const.sub (continuous_apply l)))).continuousOn
  obtain ⟨qs, hqsK, hmax⟩ := hKc.exists_isMaxOn ⟨_, hq0K⟩ hcont
  have hqsl : qs l ≠ 0 := (lt_of_lt_of_le hδ hqsK.2.1).ne'
  refine ⟨qs, hqsK.1, fun r hr => ?_⟩
  rw [relax_eq T l qs hqsl]
  by_cases hr0 : r l = 0
  · unfold relaxation; rw [if_pos hr0]; exact bot_le
  rw [relax_eq T l r hr0, EReal.coe_le_coe_iff]
  have v0le : v0 ≤ S l qs + E T (qs l) := by
    have e := G_congr T l (q0 T) (trunc l (q0 T)) (fun k hk => by simp [trunc, hk])
    have := hmax hq0K
    show S l (q0 T) + E T (q0 T l) ≤ _
    rw [e]; exact this
  have cb := chain_bounds hr l le_rfl
  by_cases hrδ : r l < δ
  · have h1 := hb r hr (lt_of_le_of_ne cb.1 (Ne.symm hr0)) (lt_of_lt_of_le hrδ (min_le_left _ _))
    have h2 := E_le T (r l) hT cb.1 cb.2.1
    linarith
  · push_neg at hrδ
    have e := G_congr T l r (trunc l r) (fun k hk => by simp [trunc, hk])
    have hrK : trunc l r ∈ K := by
      refine ⟨trunc_feas hr, ?_, ?_⟩
      · simp only [trunc, le_refl, if_true]; exact hrδ
      · intro k hk; simp only [trunc, if_neg (show ¬ k ≤ l by omega)]
    have := hmax hrK
    simp only [] at this
    rw [e]; exact this

lemma value_eq (T : ℝ) (l : ℕ) (hl : 0 < l) (q : ℕ → ℝ) (hq : IsRelaxationMax T l q) :
    relaxationValue T l = relaxation T l q := by
  unfold relaxationValue; rw [if_neg hl.ne']
  apply IsGreatest.csSup_eq
  exact ⟨⟨q, hq.1, rfl⟩, by rintro _ ⟨r, hr, rfl⟩; exact hq.2 r hr⟩

end GaoS226

open GaoS226 in
theorem solution (T : ℝ) (hT : 0 < T) (l : ℕ) (hl : 0 < l) :
    (∃ q : ℕ → ℝ, ∃ r : ℝ, GaoImpatientMNL.Pricing.IsRelaxationMax T l q ∧
      GaoImpatientMNL.Pricing.relaxation T l q = (r : EReal) ∧
      GaoImpatientMNL.Pricing.relaxationValue T l = (r : EReal)) ∧
    (∀ q, GaoImpatientMNL.Pricing.IsRelaxationMax T l q →
      (∀ k < l, q (k + 1) < q k) ∧ 0 < q l) ∧
    GaoImpatientMNL.Pricing.relaxationValue T (l - 1) <
      GaoImpatientMNL.Pricing.relaxationValue T l := by
  obtain ⟨q, hq⟩ := exists_max T hT l hl
  have mp := max_props T hT l hl q hq
  refine ⟨⟨q, S l q + E T (q l), hq, relax_eq T l q mp.1.ne', ?_⟩, ?_, ?_⟩
  · rw [value_eq T l hl q hq, relax_eq T l q mp.1.ne']
  · intro q' hq'
    have := max_props T hT l hl q' hq'
    exact ⟨this.2.2.1, this.1⟩
  · rw [value_eq T l hl q hq, relax_eq T l q mp.1.ne']
    obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have : relaxationValue T 0 = 0 := by simp [relaxationValue]
      rw [this]
      exact EReal.coe_pos.mpr mp.2.2.2
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨qs, hqs⟩ := exists_max T hT (m + 1) (by omega)
      have mps := max_props T hT (m + 1) (by omega) qs hqs
      rw [value_eq T (m + 1) (by omega) qs hqs, relax_eq T _ qs mps.1.ne']
      set q' := Function.update qs (m + 2) (qs (m + 1)) with hq'
      have hf : QFeasible (m + 1 + 1) q' := by
        refine ⟨by rw [hq', Function.update_of_ne (by omega)]; exact hqs.1.1, fun k hk => ?_⟩
        by_cases hk' : k < m + 1
        · rw [hq', Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hqs.1.2 k hk'
        · obtain rfl : k = m + 1 := by omega
          rw [hq', Function.update_self, Function.update_of_ne (by omega)]
          exact ⟨mps.1.le, le_rfl⟩
      have hq'l : q' (m + 1 + 1) = qs (m + 1) := by rw [hq']; exact Function.update_self _ _ _
      have hG : S (m + 1 + 1) q' + E T (q' (m + 1 + 1)) = S (m + 1) qs + E T (qs (m + 1)) := by
        have e1 : S (m + 1 + 1) q' = S (m + 1) q' + F (q' (m + 1)) (q' (m + 1 + 1)) := by
          unfold S; rw [Finset.sum_range_succ]
        have e2 : S (m + 1) q' = S (m + 1) qs := by
          unfold S; apply Finset.sum_congr rfl
          intro k hk; rw [Finset.mem_range] at hk
          rw [hq', Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        have e3 : q' (m + 1) = qs (m + 1) := by rw [hq', Function.update_of_ne (by omega)]
        rw [e1, e2, e3, hq'l, F_self]; ring
      obtain ⟨r, hrf, hrl, hlt⟩ := improve T hf (by rw [hq'l]; exact mps.1)
        (by rw [hq'l]; exact mps.2.1) ⟨m + 1, by omega, by rw [hq'l, hq', Function.update_of_ne (by omega)]⟩
      rw [g_eq, g_eq, hG] at hlt
      have hrl0 : r (m + 1 + 1) ≠ 0 := by rw [hrl, hq'l]; exact mps.1.ne'
      calc ((S (m + 1) qs + E T (qs (m + 1)) : ℝ) : EReal)
          < ((S (m + 1 + 1) r + E T (r (m + 1 + 1)) : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr hlt
        _ = relaxation T (m + 1 + 1) r := (relax_eq T _ r hrl0).symm
        _ ≤ ((S (m + 1 + 1) q + E T (q (m + 1 + 1)) : ℝ) : EReal) := by
          rw [← relax_eq T _ q mp.1.ne']
          exact hq.2 r hrf
