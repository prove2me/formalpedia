-- Prove2me | solution 1 for ClosedLoopBass.Immediate.theorem_1a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:04:14.480172+00:00
-- url     : https://prove2.me/submissions/301eeeff-2a55-418f-b66b-a6958ccba8a5

import Mathlib
import Definitions.Def_ClosedLoopBass_Immediate_Model

open ClosedLoopBass.Immediate

namespace CLBSol1a

lemma S_succ (n r : ℕ → ℝ) (k : ℕ) :
    S n r (k + 1 + 1) = S n r (k + 1) + sales n r (k + 1) := by
  unfold S
  rw [Finset.sum_Ico_succ_top (by omega)]

lemma Dc_succ (P : Params) (n r : ℕ → ℝ) (k : ℕ) :
    Dc P n r (k + 1) = Dc P n r k + (P.p + P.q * S n r (k + 1) / P.m) * (P.m - Dc P n r k) :=
  rfl

lemma d_succ (P : Params) (n r : ℕ → ℝ) (k : ℕ) :
    d P n r (k + 1) = (P.p + P.q * S n r (k + 1) / P.m) * (P.m - Dc P n r k) := by
  simp [d, D]

lemma bass_succ (P : Params) (k : ℕ) :
    bassCumc P.p P.q P.m (k + 1) = bassCumc P.p P.q P.m k +
      (P.p + P.q * bassCumc P.p P.q P.m k / P.m) * (P.m - bassCumc P.p P.q P.m k) := rfl

lemma dB_eq (P : Params) (t : ℕ) :
    dB P t = (P.p + P.q * bassCumc P.p P.q P.m (t - 1) / P.m) *
      (P.m - bassCumc P.p P.q P.m (t - 1)) := rfl

lemma dB_succ (P : Params) (k : ℕ) :
    dB P (k + 1) = (P.p + P.q * bassCumc P.p P.q P.m k / P.m) *
      (P.m - bassCumc P.p P.q P.m k) := by
  rw [dB_eq]; simp

lemma DB_succ (P : Params) (k : ℕ) : DB P (k + 1) = bassCumc P.p P.q P.m k := by
  simp [DB, bassCum]

lemma f_le_m (P : Params) (hP : Standing P) (x : ℝ) (hx : x ≤ P.m) :
    x + (P.p + P.q * x / P.m) * (P.m - x) ≤ P.m := by
  have hm := hP.m_pos
  have hqm : P.q / P.m * P.m = P.q := div_mul_cancel₀ _ hm.ne'
  have h1 : P.q * x / P.m ≤ P.q := by
    have e : P.q * x / P.m = P.q / P.m * x := by ring
    rw [e]
    have : P.q / P.m * x ≤ P.q / P.m * P.m :=
      mul_le_mul_of_nonneg_left hx (div_nonneg hP.q_pos.le hm.le)
    linarith
  have h2 : P.m - (x + (P.p + P.q * x / P.m) * (P.m - x)) =
      (P.m - x) * (1 - P.p - P.q * x / P.m) := by ring
  have h3 : 0 ≤ (P.m - x) * (1 - P.p - P.q * x / P.m) :=
    mul_nonneg (by linarith) (by linarith [hP.p_add_q_le_one])
  linarith

lemma f_mono (P : Params) (hP : Standing P) (x y : ℝ) (hxy : x ≤ y) (hy : y ≤ P.m) :
    x + (P.p + P.q * x / P.m) * (P.m - x) ≤ y + (P.p + P.q * y / P.m) * (P.m - y) := by
  have hm := hP.m_pos
  have hqm : P.q / P.m * P.m = P.q := div_mul_cancel₀ _ hm.ne'
  have hqm0 : 0 ≤ P.q / P.m := div_nonneg hP.q_pos.le hm.le
  have h2 : (y + (P.p + P.q * y / P.m) * (P.m - y)) - (x + (P.p + P.q * x / P.m) * (P.m - x))
      = (y - x) * (1 - P.p + P.q / P.m * (P.m - x - y)) := by ring
  have h3 : P.q / P.m * (-P.m) ≤ P.q / P.m * (P.m - x - y) :=
    mul_le_mul_of_nonneg_left (by linarith) hqm0
  have h5 : P.q / P.m * (-P.m) = -P.q := by rw [mul_neg, hqm]
  have h4 : 0 ≤ (y - x) * (1 - P.p + P.q / P.m * (P.m - x - y)) :=
    mul_nonneg (by linarith) (by linarith [hP.p_add_q_le_one])
  linarith

lemma bass_bounds (P : Params) (hP : Standing P) :
    ∀ k, 0 ≤ bassCumc P.p P.q P.m k ∧ bassCumc P.p P.q P.m k ≤ P.m := by
  intro k
  induction k with
  | zero =>
    show (0:ℝ) ≤ 0 ∧ (0:ℝ) ≤ P.m
    exact ⟨le_refl _, hP.m_pos.le⟩
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    rw [bass_succ]
    refine ⟨?_, f_le_m P hP _ h1⟩
    have hq : 0 ≤ P.q * bassCumc P.p P.q P.m k / P.m :=
      div_nonneg (mul_nonneg hP.q_pos.le h0) hP.m_pos.le
    have : 0 ≤ (P.p + P.q * bassCumc P.p P.q P.m k / P.m) * (P.m - bassCumc P.p P.q P.m k) :=
      mul_nonneg (by linarith [hP.p_pos]) (by linarith)
    linarith

lemma dB_nonneg (P : Params) (hP : Standing P) (t : ℕ) : 0 ≤ dB P t := by
  rw [dB_eq]
  obtain ⟨h0, h1⟩ := bass_bounds P hP (t - 1)
  have hq : 0 ≤ P.q * bassCumc P.p P.q P.m (t - 1) / P.m :=
    div_nonneg (mul_nonneg hP.q_pos.le h0) hP.m_pos.le
  exact mul_nonneg (by linarith [hP.p_pos]) (by linarith)

lemma bc_sum (P : Params) (n r : ℕ → ℝ) (k : ℕ) :
    (bc P n r (k + 1)).1 + (bc P n r (k + 1)).2 =
      P.alpha * (d P n r (k + 1) + (bc P n r k).1 + (bc P n r k).2 - sales n r (k + 1)) := by
  simp only [bc]
  split_ifs <;> simp only [Params.gamma1, sales] <;> ring

/-- Invariant of an arbitrary feasible plan. -/
lemma gen_inv (P : Params) (hP : Standing P) (n r : ℕ → ℝ) (hfeas : Feasible P n r) :
    ∀ k, k ≤ P.T → 0 ≤ S n r (k + 1) ∧ 0 ≤ (bc P n r k).1 + (bc P n r k).2 ∧
      S n r (k + 1) + ((bc P n r k).1 + (bc P n r k).2) ≤ Dc P n r k ∧
      Dc P n r k ≤ bassCumc P.p P.q P.m k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [S, bc, Dc, bassCumc]
  | succ k ih =>
    intro hk
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
    obtain ⟨hb0, hb1⟩ := bass_bounds P hP k
    have hf := hfeas (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
    simp only [b1, b2, Nat.add_sub_cancel] at hf
    obtain ⟨hs0, hs1, -, -, -⟩ := hf
    have hbc := bc_sum P n r k
    have hd := d_succ P n r k
    have hS := S_succ n r k
    have hX0 : 0 ≤ d P n r (k + 1) + (bc P n r k).1 + (bc P n r k).2 - sales n r (k + 1) := by
      linarith
    have ha := hP.alpha_nonneg
    have ha1 := hP.alpha_le_one
    have hαX : P.alpha * (d P n r (k + 1) + (bc P n r k).1 + (bc P n r k).2 - sales n r (k + 1))
        ≤ d P n r (k + 1) + (bc P n r k).1 + (bc P n r k).2 - sales n r (k + 1) := by
      nlinarith
    have hαX0 := mul_nonneg ha hX0
    refine ⟨by rw [hS]; linarith, by rw [hbc]; exact hαX0, ?_, ?_⟩
    · rw [hS, hbc, Dc_succ, ← hd]; linarith
    · rw [Dc_succ, bass_succ]
      have hσ : S n r (k + 1) ≤ Dc P n r k := by linarith
      have step1 : (P.p + P.q * S n r (k + 1) / P.m) * (P.m - Dc P n r k) ≤
          (P.p + P.q * Dc P n r k / P.m) * (P.m - Dc P n r k) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        have : P.q * S n r (k + 1) / P.m ≤ P.q * Dc P n r k / P.m :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσ hP.q_pos.le) hP.m_pos.le
        linarith
      have := f_mono P hP _ _ i4 hb1
      linarith

lemma S_le_DB (P : Params) (hP : Standing P) (n r : ℕ → ℝ) (hfeas : Feasible P n r)
    (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ P.T + 1) : S n r t ≤ DB P t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  obtain ⟨i1, i2, i3, i4⟩ := gen_inv P hP n r hfeas k (by omega)
  rw [DB_succ]
  linarith

/-- Returns released in period `j + 1` by sales `s`. -/
noncomputable def Rs (P : Params) (s : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 j, P.beta i * s (j + 1 - i)

lemma ec_tele (P : Params) (n r : ℕ → ℝ) : ∀ k,
    ec P n r k + ∑ j ∈ Finset.Ico 1 (k + 1), r j =
      ∑ j ∈ Finset.Ico 1 (k + 1), Rs P (sales n r) j := by
  intro k
  induction k with
  | zero => simp [ec]
  | succ k ih =>
    rw [Finset.sum_Ico_succ_top (show 1 ≤ k + 1 by omega) r,
      Finset.sum_Ico_succ_top (show 1 ≤ k + 1 by omega) (Rs P (sales n r)), ← ih]
    have e1 : ec P n r (k + 1) = ec P n r k - r (k + 1) + Rs P (sales n r) (k + 1) := rfl
    rw [e1]
    ring

lemma swap_sum (β s : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Ico 1 N, ∑ i ∈ Finset.Icc 1 j, β i * s (j + 1 - i) =
      ∑ i ∈ Finset.Ico 1 N, β i * ∑ k ∈ Finset.Ico 1 (N + 1 - i), s k := by
  have h : ∀ (j i : ℕ), j ∈ Finset.Ico 1 N ∧ i ∈ Finset.Icc 1 j ↔
      j ∈ (fun i => Finset.Ico i N) i ∧ i ∈ Finset.Ico 1 N := by
    intro j i
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [Finset.sum_comm' h]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have : N + 1 - i - 1 = N - i := by omega
  rw [this]
  apply Finset.sum_congr rfl
  intro x _
  have : i + x + 1 - i = 1 + x := by omega
  rw [this]

lemma L_eq (P : Params) (n r : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Ico 1 N, Rs P (sales n r) j =
      ∑ i ∈ Finset.Ico 1 N, P.beta i * S n r (N + 1 - i) :=
  swap_sum P.beta (sales n r) N

/-! The immediate-fulfillment plan. -/

lemma sales_IF (P : Params) (t : ℕ) : sales (nIF P) (rIF P) t = dB P t := by
  simp [sales, nIF]

lemma S_IF (P : Params) : ∀ k, S (nIF P) (rIF P) (k + 1) = bassCumc P.p P.q P.m k := by
  intro k
  induction k with
  | zero => simp [S, bassCumc]
  | succ k ih =>
    rw [S_succ, ih, sales_IF, dB_succ, bass_succ]

lemma S_IF_DB (P : Params) (t : ℕ) (ht : 1 ≤ t) : S (nIF P) (rIF P) t = DB P t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rw [S_IF, DB_succ]

lemma Dc_IF (P : Params) : ∀ k, Dc P (nIF P) (rIF P) k = bassCumc P.p P.q P.m k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Dc_succ, ih, S_IF, bass_succ]

lemma d_IF (P : Params) (k : ℕ) : d P (nIF P) (rIF P) (k + 1) = dB P (k + 1) := by
  rw [d_succ, S_IF, Dc_IF, dB_succ]

lemma bc_IF (P : Params) : ∀ k, bc P (nIF P) (rIF P) k = (0, 0) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bc, ih, d_IF]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      have hs := sales_IF P (k + 1)
      simp only [sales, Params.gamma1] at hs h1
      have e1 : P.gamma2 * dB P (k + 1) + 0 - rIF P (k + 1) = 0 := by linarith
      have e2 : (1 - P.gamma2) * dB P (k + 1) + 0 - nIF P (k + 1) = 0 := by linarith
      simp only [Params.gamma1, e1, e2, mul_zero]
    · have hs := sales_IF P (k + 1)
      simp only [sales] at hs
      have e3 : dB P (k + 1) + 0 + 0 - nIF P (k + 1) - rIF P (k + 1) = 0 := by linarith
      simp only [e3, mul_zero]

lemma ec_IF (P : Params) : ∀ k, ec P (nIF P) (rIF P) k = eIFc P k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ec, eIFc, ih, sales_IF]
    simp [rIF, eIF]

lemma eIFc_nonneg (P : Params) (hP : Standing P) : ∀ k, 0 ≤ eIFc P k := by
  intro k
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
    simp only [eIFc]
    have h1 : 0 ≤ eIFc P k - min (eIFc P k) (P.gamma2 * dB P (k + 1)) := by
      linarith [min_le_left (eIFc P k) (P.gamma2 * dB P (k + 1))]
    have h2 : 0 ≤ ∑ i ∈ Finset.Icc 1 (k + 1), P.beta i * dB P (k + 2 - i) := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hP.beta_nonneg i (Finset.mem_Icc.1 hi).1) (dB_nonneg P hP _)
    linarith

lemma feas_IF (P : Params) (hP : Standing P) : Feasible P (nIF P) (rIF P) := by
  intro t ht
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by have := (Finset.mem_Icc.1 ht).1; omega⟩
  have hb : b1 P (nIF P) (rIF P) (k + 1) = 0 ∧ b2 P (nIF P) (rIF P) (k + 1) = 0 := by
    simp [b1, b2, bc_IF]
  have he : e P (nIF P) (rIF P) (k + 1) = eIF P (k + 1) := by
    simp [e, eIF, ec_IF]
  rw [hb.1, hb.2, he, d_IF, sales_IF]
  have hd0 := dB_nonneg P hP (k + 1)
  have he0 : 0 ≤ eIF P (k + 1) := eIFc_nonneg P hP _
  have hg := hP.gamma2_nonneg
  refine ⟨hd0, by linarith, ?_, ?_, ?_⟩
  · exact le_min he0 (mul_nonneg hg hd0)
  · simp only [rIF]; linarith [min_le_right (eIF P (k + 1)) (P.gamma2 * dB P (k + 1))]
  · exact min_le_left _ _

lemma profit_eq (P : Params) (n r : ℕ → ℝ) :
    profit P n r = (P.pn - P.cn) * S n r (P.T + 1) +
      ((P.pr - P.cr) - (P.pn - P.cn)) * ∑ t ∈ Finset.Icc 1 P.T, r t := by
  simp only [profit, S, Finset.Ico_add_one_right_eq_Icc, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [sales]
  ring

end CLBSol1a

open CLBSol1a in
theorem solution (P : Params) (hP : Standing P)
    (hcond : ∀ t ∈ Finset.Icc 1 P.T, eIF P t ≤ P.gamma2 * dB P t) :
    Feasible P (nIF P) (rIF P) ∧
    ∀ n r : ℕ → ℝ, Feasible P n r → profit P n r ≤ profit P (nIF P) (rIF P) := by
  refine ⟨feas_IF P hP, fun n r hf => ?_⟩
  rw [profit_eq, profit_eq]
  have ha : 0 < P.pn - P.cn := by linarith [hP.cn_lt_pn]
  have hΔ : 0 < (P.pr - P.cr) - (P.pn - P.cn) := by linarith [hP.margin_lt]
  have hS1 : S n r (P.T + 1) ≤ S (nIF P) (rIF P) (P.T + 1) := by
    rw [S_IF_DB P _ (by omega)]
    exact S_le_DB P hP n r hf _ (by omega) le_rfl
  obtain hT | ⟨K, hK⟩ : P.T = 0 ∨ ∃ K, P.T = K + 1 :=
    (Nat.eq_zero_or_pos P.T).imp id (fun h => ⟨P.T - 1, by omega⟩)
  · rw [hT] at hS1 ⊢
    simp only [Finset.Icc_eq_empty_of_lt, zero_lt_one, Finset.sum_empty,
      mul_zero, add_zero] at *
    nlinarith
  · -- bound on remanufactured sales of an arbitrary feasible plan
    have hsplit : ∀ x : ℕ → ℝ, ∑ t ∈ Finset.Icc 1 P.T, x t =
        ∑ t ∈ Finset.Ico 1 (K + 1), x t + x (K + 1) := by
      intro x
      rw [hK, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top (by omega)]
    have hfK := hf (K + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    obtain ⟨-, -, -, -, hre⟩ := hfK
    have hteleK := ec_tele P n r K
    have hr : ∑ t ∈ Finset.Icc 1 P.T, r t ≤
        ∑ i ∈ Finset.Ico 1 (K + 1), P.beta i * S n r (K + 1 + 1 - i) := by
      rw [hsplit, ← L_eq, ← hteleK]
      have : e P n r (K + 1) = ec P n r K := by simp [e]
      linarith
    -- the immediate-fulfillment plan attains this bound
    have hrIF : ∑ t ∈ Finset.Icc 1 P.T, rIF P t =
        ∑ i ∈ Finset.Ico 1 (K + 1), P.beta i * S (nIF P) (rIF P) (K + 1 + 1 - i) := by
      rw [hsplit, ← L_eq, ← ec_tele P (nIF P) (rIF P) K, ec_IF]
      have hc := hcond (K + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      have : rIF P (K + 1) = eIFc P K := by
        simp only [rIF]
        rw [min_eq_left hc]
        simp [eIF]
      rw [this]
      ring
    have hcmp : ∑ i ∈ Finset.Ico 1 (K + 1), P.beta i * S n r (K + 1 + 1 - i) ≤
        ∑ i ∈ Finset.Ico 1 (K + 1), P.beta i * S (nIF P) (rIF P) (K + 1 + 1 - i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Ico.1 hi
      apply mul_le_mul_of_nonneg_left _ (hP.beta_nonneg i hi'.1)
      rw [S_IF_DB P _ (by omega)]
      exact S_le_DB P hP n r hf _ (by omega) (by omega)
    rw [hrIF]
    have h1 := mul_le_mul_of_nonneg_left hS1 ha.le
    have h2 := mul_le_mul_of_nonneg_left (hr.trans hcmp) hΔ.le
    linarith
