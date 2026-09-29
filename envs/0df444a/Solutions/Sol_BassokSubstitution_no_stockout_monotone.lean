-- Prove2me | solution 1 for BassokSubstitution.no_stockout_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:00:33.094372+00:00
-- url     : https://prove2.me/submissions/5a635e44-80cd-40c1-841f-22a3feda50f6

import Mathlib
import Definitions.Def_BassokSubstitution_Profit
open MeasureTheory
namespace BassokSubstitution

noncomputable def aux_bsm_T (Y D : ℕ → ℝ) (m : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (aux_bsm_T Y D m n + Y (m + n) - D (m + n)) 0

theorem aux_bsm_inner (i lo : ℕ) : ∀ (n : ℕ) (st : AlgState), (∀ l, 0 ≤ st.v l) →
    (∀ l, 0 ≤ (innerLoop i (n+1) (lo+n) st).v l) ∧
    (∀ l, (l < lo ∨ lo + n < l) → (innerLoop i (n+1) (lo+n) st).v l = st.v l) ∧
    (∀ c, c ≠ i → (innerLoop i (n+1) (lo+n) st).u c = st.u c) ∧
    (innerLoop i (n+1) (lo+n) st).u i
      = max (st.u i - ∑ l ∈ Finset.range (n+1), st.v (lo + l)) 0 ∧
    ∑ l ∈ Finset.range (n+1), (innerLoop i (n+1) (lo+n) st).v (lo + l)
      = max (∑ l ∈ Finset.range (n+1), st.v (lo + l) - st.u i) 0 := by
  intro n
  induction n with
  | zero =>
    intro st hst
    simp only [innerLoop, zero_add, add_zero, Finset.sum_range_one]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro l
      by_cases hl : l = lo
      · subst hl; simp only [Function.update_self]
        have := hst l
        rcases min_cases (st.u i) (st.v l) with h | h <;> rw [h.1] <;> linarith [h.2]
      · simp only [ne_eq, hl, not_false_eq_true, Function.update_of_ne]; exact hst l
    · intro l hl
      have : l ≠ lo := by omega
      simp [this]
    · intro c hc
      simp [hc]
    · simp only [Function.update_self]
      rcases min_cases (st.u i) (st.v lo) with h | h <;> rw [h.1]
      · rw [max_eq_right (by linarith [h.2])]; ring
      · rw [max_eq_left (by linarith [h.2])]
    · simp only [Function.update_self]
      rcases min_cases (st.u i) (st.v lo) with h | h <;> rw [h.1]
      · rw [max_eq_left (by linarith [h.2])]
      · rw [max_eq_right (by linarith [h.2])]; ring
  | succ n ih =>
    intro st hst
    have hunf : innerLoop i (n+1+1) (lo+(n+1)) st = innerLoop i (n+1) (lo+n)
        { v := Function.update st.v (lo+(n+1)) (st.v (lo+(n+1)) - min (st.u i) (st.v (lo+(n+1))))
          u := Function.update st.u i (st.u i - min (st.u i) (st.v (lo+(n+1))))
          w := Function.update st.w (lo+(n+1)) (Function.update (st.w (lo+(n+1))) i
                (min (st.u i) (st.v (lo+(n+1))))) } := by
      rw [innerLoop]
      congr 1
    rw [hunf]
    set st1 : AlgState :=
        { v := Function.update st.v (lo+(n+1)) (st.v (lo+(n+1)) - min (st.u i) (st.v (lo+(n+1))))
          u := Function.update st.u i (st.u i - min (st.u i) (st.v (lo+(n+1))))
          w := Function.update st.w (lo+(n+1)) (Function.update (st.w (lo+(n+1))) i
                (min (st.u i) (st.v (lo+(n+1))))) } with hst1
    have hvtop := hst (lo + (n+1))
    have hmin_nonneg : 0 ≤ st.v (lo+(n+1)) - min (st.u i) (st.v (lo+(n+1))) := by
      linarith [min_le_right (st.u i) (st.v (lo+(n+1)))]
    have hst1v : ∀ l, 0 ≤ st1.v l := by
      intro l
      by_cases hl : l = lo + (n+1)
      · subst hl; simp only [st1, Function.update_self]; exact hmin_nonneg
      · simp only [st1, ne_eq, hl, not_false_eq_true, Function.update_of_ne]; exact hst l
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih st1 hst1v
    have hsum1 : ∑ l ∈ Finset.range (n+1), st1.v (lo + l) = ∑ l ∈ Finset.range (n+1), st.v (lo + l) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hl' := Finset.mem_range.mp hl
      have : lo + l ≠ lo + (n+1) := by omega
      show Function.update st.v _ _ (lo + l) = _
      rw [Function.update_of_ne this]
    have hSnn : 0 ≤ ∑ l ∈ Finset.range (n+1), st.v (lo + l) :=
      Finset.sum_nonneg (fun l _ => hst _)
    have hu1 : st1.u i = st.u i - min (st.u i) (st.v (lo+(n+1))) := by simp [st1]
    have hv1 : st1.v (lo+(n+1)) = st.v (lo+(n+1)) - min (st.u i) (st.v (lo+(n+1))) := by simp [st1]
    refine ⟨h1, ?_, ?_, ?_, ?_⟩
    · intro l hl
      rw [h2 l (by omega)]
      have : l ≠ lo + (n+1) := by omega
      simp [st1, this]
    · intro c hc
      rw [h3 c hc]
      simp [st1, hc]
    · rw [h4, hsum1, hu1, Finset.sum_range_succ (fun l => st.v (lo + l)) (n+1)]
      rcases min_cases (st.u i) (st.v (lo+(n+1))) with h | h <;> rw [h.1]
      · rw [max_eq_right (by linarith [h.2]), max_eq_right (by linarith [h.2])]
      · rcases le_total 0 (st.u i - st.v (lo + (n + 1)) - ∑ l ∈ Finset.range (n+1), st.v (lo + l)) with h' | h'
        · rw [max_eq_left h', max_eq_left (by linarith)]; ring
        · rw [max_eq_right h', max_eq_right (by linarith)]
    · rw [Finset.sum_range_succ (fun l => (innerLoop i (n + 1) (lo + n) st1).v (lo + l)) (n+1), h5,
        hsum1, hu1, h2 (lo + (n+1)) (by omega), hv1, Finset.sum_range_succ (fun l => st.v (lo + l)) (n+1)]
      rcases min_cases (st.u i) (st.v (lo+(n+1))) with h | h <;> rw [h.1]
      · rw [max_eq_left (by linarith [h.2]), max_eq_left (by linarith [h.2])]; ring
      · rcases le_total 0 (∑ l ∈ Finset.range (n+1), st.v (lo + l) - (st.u i - st.v (lo + (n + 1)))) with h' | h'
        · rw [max_eq_left h', max_eq_left (by linarith)]; ring
        · rw [max_eq_right h', max_eq_right (by linarith)]; ring

theorem aux_bsm_run (Y D : ℕ → ℝ) (hY : ∀ l, 0 ≤ Y l) (m : ℕ) : ∀ n : ℕ,
    (∀ l, 0 ≤ (runFrom m Y D n).v l) ∧
    (∀ l, (l < m ∨ m + n ≤ l) → (runFrom m Y D n).v l = Y l) ∧
    ∑ l ∈ Finset.range n, (runFrom m Y D n).v (m + l) = aux_bsm_T Y D m n ∧
    ∀ c < n, (runFrom m Y D n).u (m + c) = max (D (m + c) - Y (m + c) - aux_bsm_T Y D m c) 0 := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l; simp [runFrom, hY l]
    · intro l _; simp [runFrom]
    · simp [aux_bsm_T]
    · intro c hc; omega
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have hunf : runFrom m Y D (n+1) = innerLoop (m + n) (n+1) (m + n)
        { runFrom m Y D n with u := Function.update (runFrom m Y D n).u (m + n) (D (m + n)) } := rfl
    rw [hunf]
    set st0 : AlgState := { runFrom m Y D n with u := Function.update (runFrom m Y D n).u (m + n) (D (m + n)) } with hst0
    have hst0v : ∀ l, 0 ≤ st0.v l := h1
    obtain ⟨g1, g2, g3, g4, g5⟩ := aux_bsm_inner (m + n) m n st0 hst0v
    have hsum0 : ∑ l ∈ Finset.range (n+1), st0.v (m + l) = aux_bsm_T Y D m n + Y (m + n) := by
      rw [Finset.sum_range_succ]
      show ∑ l ∈ Finset.range n, (runFrom m Y D n).v (m + l) + (runFrom m Y D n).v (m + n) = _
      rw [h3, h2 (m + n) (Or.inr le_rfl)]
    refine ⟨g1, ?_, ?_, ?_⟩
    · intro l hl
      rw [g2 l (by omega)]
      exact h2 l (by omega)
    · rw [g5, hsum0]
      have : st0.u (m + n) = D (m + n) := by simp [st0]
      rw [this, aux_bsm_T]
    · intro c hc
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | hc
      · rw [g3 (m + c) (by omega)]
        have : m + c ≠ m + n := by omega
        simp only [st0, Function.update_of_ne this]
        exact h4 c hc
      · subst hc
        rw [g4, hsum0]
        have : st0.u (m + c) = D (m + c) := by simp [st0]
        rw [this]; congr 1; ring

theorem aux_bsm_shortage {N : ℕ} (y d : Fin N → ℝ) (hy : 0 ≤ y) (m : ℕ) (j : Fin N)
    (hmj : m ≤ j.val) :
    shortage y d m j = max (extend d j.val - extend y j.val
      - aux_bsm_T (extend y) (extend d) m (j.val - m)) 0 := by
  have hY : ∀ l, 0 ≤ extend y l := by
    intro l; unfold extend; split_ifs
    · exact hy _
    · exact le_rfl
  unfold shortage
  rw [if_pos hmj]
  have := (aux_bsm_run (extend y) (extend d) hY m (j.val + 1 - m)).2.2.2 (j.val - m) (by omega)
  rw [show m + (j.val - m) = j.val by omega] at this
  exact this

theorem aux_bsm_T_nonneg (Y D : ℕ → ℝ) (m n : ℕ) : 0 ≤ aux_bsm_T Y D m n := by
  cases n with
  | zero => simp [aux_bsm_T]
  | succ n => simp only [aux_bsm_T]; exact le_max_right _ _

theorem aux_bsm_T_step (Y D : ℕ → ℝ) (m : ℕ) : ∀ n, aux_bsm_T Y D (m+1) n ≤ aux_bsm_T Y D m (n+1) := by
  intro n
  induction n with
  | zero => simp only [aux_bsm_T]; simp
  | succ n ih =>
    rw [aux_bsm_T, aux_bsm_T, show m + 1 + n = m + (n + 1) by ring]
    exact max_le_max (by linarith) le_rfl

theorem aux_bsm_T_mono (Y D : ℕ → ℝ) (a : ℕ) : ∀ e n, aux_bsm_T Y D (a + e) n ≤ aux_bsm_T Y D a (e + n) := by
  intro e
  induction e with
  | zero => intro n; simp
  | succ e ih =>
    intro n
    calc aux_bsm_T Y D (a + (e+1)) n = aux_bsm_T Y D (a + e + 1) n := by rw [add_assoc]
      _ ≤ aux_bsm_T Y D (a + e) (n + 1) := aux_bsm_T_step Y D (a + e) n
      _ ≤ aux_bsm_T Y D a (e + (n + 1)) := ih (n+1)
      _ = aux_bsm_T Y D a (e + 1 + n) := by rw [show e + (n+1) = e + 1 + n by ring]

theorem aux_bsm_T_reset (Y D : ℕ → ℝ) (a n0 : ℕ) (h0 : aux_bsm_T Y D a n0 = 0) :
    ∀ n, aux_bsm_T Y D a (n0 + n) = aux_bsm_T Y D (a + n0) n := by
  intro n
  induction n with
  | zero => simpa [aux_bsm_T] using h0
  | succ n ih =>
    rw [← add_assoc, aux_bsm_T, aux_bsm_T, ih, show a + (n0 + n) = a + n0 + n by ring]

theorem aux_bsm_T_congr (Y Y' D : ℕ → ℝ) (m : ℕ) : ∀ n, (∀ l < m + n, Y l = Y' l) →
    aux_bsm_T Y D m n = aux_bsm_T Y' D m n := by
  intro n
  induction n with
  | zero => intro _; simp [aux_bsm_T]
  | succ n ih =>
    intro h
    rw [aux_bsm_T, aux_bsm_T, ih (fun l hl => h l (by omega)), h (m + n) (by omega)]

noncomputable def aux_bsm_S (Y D : ℕ → ℝ) (m j : ℕ) : ℝ :=
  max (D j - Y j - aux_bsm_T Y D m (j - m)) 0

theorem aux_bsm_S_nonneg (Y D : ℕ → ℝ) (m j : ℕ) : 0 ≤ aux_bsm_S Y D m j := le_max_right _ _

theorem aux_bsm_S_anti (Y D : ℕ → ℝ) (a b j : ℕ) (hab : a ≤ b) (hbj : b ≤ j) :
    aux_bsm_S Y D a j ≤ aux_bsm_S Y D b j := by
  unfold aux_bsm_S
  have := aux_bsm_T_mono Y D a (b - a) (j - b)
  rw [show a + (b - a) = b by omega, show b - a + (j - b) = j - a by omega] at this
  exact max_le_max (by linarith) le_rfl

theorem aux_bsm_S_reset (Y D : ℕ → ℝ) (a j : ℕ) (haj : a ≤ j) (hpos : 0 < aux_bsm_S Y D a j) :
    ∀ j', j + 1 ≤ j' → aux_bsm_S Y D a j' = aux_bsm_S Y D (j+1) j' := by
  intro j' hj'
  have h0 : aux_bsm_T Y D a (j - a + 1) = 0 := by
    unfold aux_bsm_S at hpos
    rw [aux_bsm_T, show a + (j - a) = j by omega]
    rcases lt_max_iff.mp hpos with h | h
    · exact max_eq_right (by linarith)
    · exact absurd h (lt_irrefl 0)
  have := aux_bsm_T_reset Y D a (j - a + 1) h0 (j' - j - 1)
  unfold aux_bsm_S
  rw [show j' - a = j - a + 1 + (j' - j - 1) by omega, this,
    show a + (j - a + 1) = j + 1 by omega, show j' - (j + 1) = j' - j - 1 by omega]

theorem aux_bsm_Z (Y D : ℕ → ℝ) (i : ℕ) : ∀ a, a ≤ i → aux_bsm_S Y D a i = 0 →
    ∃ b, a ≤ b ∧ b ≤ i ∧ ∀ j, b ≤ j → j ≤ i → aux_bsm_S Y D b j = 0 := by
  intro a
  induction h : i - a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    intro hai hS
    by_cases hall : ∀ j, a ≤ j → j ≤ i → aux_bsm_S Y D a j = 0
    · exact ⟨a, le_rfl, hai, hall⟩
    · push Not at hall
      obtain ⟨j, haj, hji, hne⟩ := hall
      have hpos : 0 < aux_bsm_S Y D a j := lt_of_le_of_ne (aux_bsm_S_nonneg Y D a j) (Ne.symm hne)
      have hji' : j < i := by
        rcases lt_or_eq_of_le hji with h' | h'
        · exact h'
        · subst h'; exact absurd hS hne
      have hreset := aux_bsm_S_reset Y D a j haj hpos
      obtain ⟨b, hb1, hb2, hb3⟩ := ih (i - (j+1)) (by omega) (j+1) rfl (by omega)
        (by rw [← hreset i (by omega)]; exact hS)
      exact ⟨b, by omega, hb2, hb3⟩

theorem aux_bsm_B (Y D : ℕ → ℝ) (k i : ℕ) : ∀ m, k ≤ m → m ≤ i →
    (∀ j, m ≤ j → j ≤ i → aux_bsm_S Y D m j = 0) →
    aux_bsm_S Y D i i = 0 ∨ ∃ m', k ≤ m' ∧ m' < i ∧ 0 < aux_bsm_S Y D (m'+1) i ∧
      ∀ j, m' ≤ j → j ≤ i → aux_bsm_S Y D m' j = 0 := by
  intro m
  induction h : i - m using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    intro hkm hmi hE
    rcases lt_or_eq_of_le hmi with hmi' | hmi'
    · by_cases hpos : 0 < aux_bsm_S Y D (m+1) i
      · exact Or.inr ⟨m, hkm, hmi', hpos, hE⟩
      · have h0 : aux_bsm_S Y D (m+1) i = 0 :=
          le_antisymm (not_lt.mp hpos) (aux_bsm_S_nonneg Y D _ _)
        obtain ⟨b, hb1, hb2, hb3⟩ := aux_bsm_Z Y D i (m+1) (by omega) h0
        exact ih (i - b) (by omega) b rfl (by omega) hb2 hb3
    · subst hmi'
      exact Or.inl (hE m le_rfl le_rfl)

theorem aux_bsm_C (Y Y' D : ℕ → ℝ) (i : ℕ) (hlt : ∀ l < i, Y l = Y' l) (hi : Y i ≤ Y' i)
    (m : ℕ) (hmi : m ≤ i) (hE : ∀ j, m ≤ j → j ≤ i → aux_bsm_S Y D m j = 0) :
    ∀ j, m ≤ j → j ≤ i → aux_bsm_S Y' D m j = 0 := by
  intro j hmj hji
  have hT : aux_bsm_T Y D m (j - m) = aux_bsm_T Y' D m (j - m) :=
    aux_bsm_T_congr Y Y' D m (j - m) (fun l hl => hlt l (by omega))
  have := hE j hmj hji
  unfold aux_bsm_S at this ⊢
  rw [← hT]
  rcases lt_or_eq_of_le hji with h' | h'
  · rw [← hlt j h']; exact this
  · subst h'
    apply le_antisymm _ (le_max_right _ _)
    refine le_trans (max_le_max (?_ : _ ≤ D j - Y j - aux_bsm_T Y D m (j - m)) le_rfl) this.le
    linarith

theorem aux_bsm_extend_meas {N : ℕ} (l : ℕ) : Measurable (fun d : Fin N → ℝ => extend d l) := by
  unfold extend
  by_cases h : l < N
  · simp only [h, dif_pos]; exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

theorem aux_bsm_T_meas {N : ℕ} (Y : ℕ → ℝ) (m : ℕ) :
    ∀ n, Measurable (fun d : Fin N → ℝ => aux_bsm_T Y (extend d) m n) := by
  intro n
  induction n with
  | zero => simp only [aux_bsm_T]; exact measurable_const
  | succ n ih =>
    simp only [aux_bsm_T]
    exact ((ih.add measurable_const).sub (aux_bsm_extend_meas _)).max measurable_const

theorem aux_bsm_S_meas {N : ℕ} (Y : ℕ → ℝ) (m j : ℕ) :
    Measurable (fun d : Fin N → ℝ => aux_bsm_S Y (extend d) m j) := by
  unfold aux_bsm_S
  exact (((aux_bsm_extend_meas j).sub measurable_const).sub (aux_bsm_T_meas Y m _)).max
    measurable_const

theorem aux_bsm_main {N : ℕ} (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] (Y Y' : ℕ → ℝ)
    (k i : Fin N) (hki : k < i) (hlt : ∀ l < i.val, Y l = Y' l) (hi : Y i ≤ Y' i) :
    μ.real {d | aux_bsm_S Y (extend d) i i = 0}
      + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
        μ.real {d | 0 < aux_bsm_S Y (extend d) (m+1) i ∧
          ∀ j : ℕ, m.val ≤ j → j ≤ i.val → aux_bsm_S Y (extend d) m j = 0}
    ≤ μ.real {d | aux_bsm_S Y' (extend d) i i = 0}
      + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
        μ.real {d | 0 < aux_bsm_S Y' (extend d) (m+1) i ∧
          ∀ j : ℕ, m.val ≤ j → j ≤ i.val → aux_bsm_S Y' (extend d) m j = 0} := by
  set F := Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i) with hF
  set B : (ℕ → ℝ) → Set (Fin N → ℝ) := fun Z => {d | aux_bsm_S Z (extend d) i i = 0} with hB
  set A : (ℕ → ℝ) → Fin N → Set (Fin N → ℝ) := fun Z m => {d | 0 < aux_bsm_S Z (extend d) (m+1) i ∧
          ∀ j : ℕ, m.val ≤ j → j ≤ i.val → aux_bsm_S Z (extend d) m j = 0} with hA
  show μ.real (B Y) + ∑ m ∈ F, μ.real (A Y m) ≤ μ.real (B Y') + ∑ m ∈ F, μ.real (A Y' m)
  have hmemF : ∀ m, m ∈ F ↔ k ≤ m ∧ m < i := by intro m; simp [hF]
  have hBmeas : MeasurableSet (B Y) := (aux_bsm_S_meas Y i i) (measurableSet_singleton 0)
  have hAmeas : ∀ m, MeasurableSet (A Y m) := by
    intro m
    refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
    · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const (aux_bsm_S_meas Y _ _))
    · refine Measurable.forall fun j => Measurable.imp measurable_const
        (Measurable.imp measurable_const ?_)
      exact measurableSet_setOfPred.1 ((aux_bsm_S_meas Y m j) (measurableSet_singleton 0))
  have hpd : (↑F : Set (Fin N)).PairwiseDisjoint (A Y) := by
    have aux : ∀ m m' : Fin N, m ∈ F → m' ∈ F → m < m' → Disjoint (A Y m) (A Y m') := by
      intro m m' hm hm' hlt'
      rw [Set.disjoint_left]
      rintro d ⟨hpos, _⟩ ⟨_, hE'⟩
      have hm'i := ((hmemF m').mp hm').2
      have hle := aux_bsm_S_anti Y (extend d) (m.val + 1) m'.val i.val
        (by have := Fin.lt_def.mp hlt'; omega) (le_of_lt (Fin.lt_def.mp hm'i))
      have h0' := hE' i.val (le_of_lt (Fin.lt_def.mp hm'i)) le_rfl
      linarith
    intro m hm m' hm' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact aux m m' hm hm' h
    · exact (aux m' m hm' hm h).symm
  have hdisj : Disjoint (B Y) (⋃ m ∈ F, A Y m) := by
    rw [Set.disjoint_left]
    intro d hd hd'
    simp only [Set.mem_iUnion] at hd'
    obtain ⟨m, hm, hpos, _⟩ := hd'
    have hmi := ((hmemF m).mp hm).2
    have hle := aux_bsm_S_anti Y (extend d) (m.val + 1) i.val i.val
      (Fin.lt_def.mp hmi) le_rfl
    have h0 : aux_bsm_S Y (extend d) i i = 0 := hd
    linarith
  rw [← measureReal_biUnion_finset hpd (fun m _ => hAmeas m) (fun m _ => measure_ne_top _ _),
    ← measureReal_union' hdisj hBmeas (measure_ne_top _ _) (measure_ne_top _ _)]
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) ((measureReal_union_le _ _).trans
    (add_le_add_right (measureReal_biUnion_finset_le _ _) _))
  -- set inclusion
  intro d hd
  have hE : ∃ m0 : ℕ, k.val ≤ m0 ∧ m0 ≤ i.val ∧
      ∀ j : ℕ, m0 ≤ j → j ≤ i.val → aux_bsm_S Y (extend d) m0 j = 0 := by
    rcases hd with hd | hd
    · refine ⟨i.val, le_of_lt (Fin.lt_def.mp hki), le_rfl, ?_⟩
      intro j h1 h2
      have : j = i.val := le_antisymm h2 h1
      subst this
      exact hd
    · simp only [Set.mem_iUnion] at hd
      obtain ⟨m, hm, _, hE⟩ := hd
      have := (hmemF m).mp hm
      exact ⟨m.val, Fin.le_iff_val_le_val.mp this.1, le_of_lt (Fin.lt_def.mp this.2), hE⟩
  obtain ⟨m0, hk0, h0i, hE0⟩ := hE
  have hE0' := aux_bsm_C Y Y' (extend d) i.val hlt hi m0 h0i hE0
  rcases aux_bsm_B Y' (extend d) k.val i.val m0 hk0 h0i hE0' with h | ⟨m', hkm', hm'i, hpos, hE'⟩
  · exact Or.inl h
  · right
    simp only [Set.mem_iUnion]
    have hm'N : m' < N := lt_trans hm'i i.isLt
    refine ⟨⟨m', hm'N⟩, ?_, hpos, hE'⟩
    rw [hmemF]
    exact ⟨Fin.le_iff_val_le_val.mpr hkm', Fin.lt_def.mpr hm'i⟩

theorem aux_bsm_nonneg_upd {N : ℕ} (y : Fin N → ℝ) (hy : 0 ≤ y) (i : Fin N) (t : ℝ)
    (ht : 0 ≤ t) : 0 ≤ Function.update y i t := by
  intro l
  by_cases h : l = i
  · subst h; simpa using ht
  · simpa [h] using hy l

theorem aux_bsm_trans {N : ℕ} (y d : Fin N → ℝ) (hy : 0 ≤ y) (m : ℕ) (j : Fin N)
    (hmj : m ≤ j.val) : shortage y d m j = aux_bsm_S (extend y) (extend d) m j.val := by
  rw [aux_bsm_shortage y d hy m j hmj]; rfl

theorem aux_bsm_svz {N : ℕ} (y d : Fin N → ℝ) (hy : 0 ≤ y) (m : ℕ) (i : Fin N) :
    ShortVecZero y d m m i ↔
      ∀ j : ℕ, m ≤ j → j ≤ i.val → aux_bsm_S (extend y) (extend d) m j = 0 := by
  constructor
  · intro h j hmj hji
    have hjN : j < N := lt_of_le_of_lt hji i.isLt
    have := h ⟨j, hjN⟩ hmj hji
    rw [aux_bsm_trans y d hy m ⟨j, hjN⟩ hmj] at this
    exact this
  · intro h j hmj hji
    rw [aux_bsm_trans y d hy m j hmj]
    exact h j.val hmj hji

end BassokSubstitution

open BassokSubstitution

theorem solution {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (k i : Fin N) (hki : k < i) :
    MonotoneOn
      (fun t : ℝ =>
        (Measure.pi ν).real {d | shortage (Function.update y i t) d i i = 0}
          + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
              (Measure.pi ν).real {d | 0 < shortage (Function.update y i t) d (m + 1) i ∧
                ShortVecZero (Function.update y i t) d m m i})
      (Set.Ici 0) := by
  intro t ht t' ht' htt'
  have ht0 : (0:ℝ) ≤ t := ht
  have ht0' : (0:ℝ) ≤ t' := ht'
  have key : ∀ s : ℝ, 0 ≤ s →
      ((Measure.pi ν).real {d | shortage (Function.update y i s) d i i = 0}
          + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
              (Measure.pi ν).real {d | 0 < shortage (Function.update y i s) d (m + 1) i ∧
                ShortVecZero (Function.update y i s) d m m i})
      = (Measure.pi ν).real {d | aux_bsm_S (extend (Function.update y i s)) (extend d) i i = 0}
      + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
        (Measure.pi ν).real {d | 0 < aux_bsm_S (extend (Function.update y i s)) (extend d) (m+1) i ∧
          ∀ j : ℕ, m.val ≤ j → j ≤ i.val →
            aux_bsm_S (extend (Function.update y i s)) (extend d) m j = 0} := by
    intro s hs
    have hys := aux_bsm_nonneg_upd y hy i s hs
    congr 1
    · congr 1; ext d; simp only [Set.mem_ofPred_eq]; rw [aux_bsm_trans _ d hys i i le_rfl]
    · apply Finset.sum_congr rfl
      intro m hm
      have hmi : m < i := (Finset.mem_filter.mp hm).2.2
      congr 1; ext d; simp only [Set.mem_ofPred_eq]
      rw [aux_bsm_trans _ d hys (m.val + 1) i (Fin.lt_def.mp hmi), aux_bsm_svz _ d hys m i]
  simp only
  rw [key t ht0, key t' ht0']
  apply aux_bsm_main (Measure.pi ν) _ _ k i hki
  · intro l hl
    unfold BassokSubstitution.extend
    split_ifs with h
    · have : (⟨l, h⟩ : Fin N) ≠ i := fun he => by
        rw [← he] at hl; exact lt_irrefl _ hl
      simp [Function.update_of_ne this]
    · rfl
  · unfold BassokSubstitution.extend; simp [htt']
