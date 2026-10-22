-- Prove2me | solution 1 for CCPCollateral.Incentive.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T05:09:56.185986+00:00
-- url     : https://prove2.me/submissions/2ea35637-8606-4d3b-9366-4d870a44978f

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

set_option autoImplicit false

namespace CCPProp2

open CCPCollateral.Incentive Finset

/-- binomial weight -/
noncomputable def bw (n : ℕ) (p : ℝ) (i : ℕ) : ℝ := (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

lemma bw_nonneg (n : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (i : ℕ) : 0 ≤ bw n p i := by
  unfold bw
  have : 0 ≤ 1 - p := by linarith
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg h0 _)) (pow_nonneg this _)

lemma bw_zero_pos (n : ℕ) {p : ℝ} (h1 : p < 1) : 0 < bw n p 0 := by
  unfold bw
  have : 0 < 1 - p := by linarith
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
  exact pow_pos this _

lemma bw_pascal (n : ℕ) (p : ℝ) (χ : ℕ → ℝ) :
    ∑ i ∈ range (n + 1 + 1), bw (n + 1) p i * χ i =
      ∑ i ∈ range (n + 1), bw n p i * (p * χ (i + 1) + (1 - p) * χ i) := by
  have hA : ∑ i ∈ range (n + 1), bw n p i * (p * χ (i + 1) + (1 - p) * χ i)
      = ∑ i ∈ range (n + 1), (n.choose i : ℝ) * p ^ (i + 1) * (1 - p) ^ (n - i) * χ (i + 1)
        + ∑ i ∈ range (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n + 1 - i) * χ i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    unfold bw
    rw [show n + 1 - i = (n - i) + 1 by omega]
    ring
  have hB : ∑ i ∈ range (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n + 1 - i) * χ i
      = ∑ i ∈ range (n + 1 + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n + 1 - i) * χ i := by
    rw [Finset.sum_range_succ (fun i => (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n + 1 - i) * χ i)
      (n + 1), Nat.choose_succ_self]
    simp
  rw [hA, hB, Finset.sum_range_succ' _ (n + 1),
    Finset.sum_range_succ' (fun i => (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n + 1 - i) * χ i)
      (n + 1), ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    unfold bw
    rw [Nat.choose_succ_succ', show n + 1 - (i + 1) = n - i by omega]
    push_cast
    ring
  · unfold bw
    simp

/-- double-sum expectation of `ψ (j + l)` under two independent binomials -/
noncomputable def E2 (g M : ℕ) (a b : ℝ) (ψ : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (g + 1), ∑ l ∈ range (M + 1), bw g a j * bw M b l * ψ (j + l)

lemma E2_step (g M : ℕ) (a b : ℝ) (ψ : ℕ → ℝ) :
    E2 g (M + 1) a b ψ - E2 (g + 1) M a b ψ =
      ∑ j ∈ range (g + 1), ∑ l ∈ range (M + 1),
        (b - a) * (bw g a j * bw M b l * (ψ (j + l + 1) - ψ (j + l))) := by
  have h1 : E2 g (M + 1) a b ψ = ∑ j ∈ range (g + 1), ∑ l ∈ range (M + 1),
      bw g a j * bw M b l * (b * ψ (j + l + 1) + (1 - b) * ψ (j + l)) := by
    unfold E2
    apply Finset.sum_congr rfl
    intro j _
    have := bw_pascal M b (fun l => bw g a j * ψ (j + l))
    beta_reduce at this
    rw [show ∑ l ∈ range (M + 1 + 1), bw g a j * bw (M + 1) b l * ψ (j + l)
        = ∑ l ∈ range (M + 1 + 1), bw (M + 1) b l * (bw g a j * ψ (j + l)) from
          Finset.sum_congr rfl (fun l _ => by ring), this]
    apply Finset.sum_congr rfl
    intro l _
    rw [show j + (l + 1) = j + l + 1 by omega]
    ring
  have h2 : E2 (g + 1) M a b ψ = ∑ j ∈ range (g + 1), ∑ l ∈ range (M + 1),
      bw g a j * bw M b l * (a * ψ (j + l + 1) + (1 - a) * ψ (j + l)) := by
    have := bw_pascal g a (fun j => ∑ l ∈ range (M + 1), bw M b l * ψ (j + l))
    beta_reduce at this
    unfold E2
    have hre : ∑ j ∈ range (g + 1 + 1), ∑ l ∈ range (M + 1), bw (g + 1) a j * bw M b l * ψ (j + l)
        = ∑ j ∈ range (g + 1 + 1), bw (g + 1) a j * ∑ l ∈ range (M + 1), bw M b l * ψ (j + l) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hre, this]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [show j + 1 + l = j + l + 1 by omega]
    ring
  rw [h1, h2, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma E2_step_le (g M : ℕ) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) (ψ : ℕ → ℝ)
    (hψ : ∀ k, k + 1 ≤ g + M + 1 → ψ k ≤ ψ (k + 1)) :
    E2 (g + 1) M a b ψ ≤ E2 g (M + 1) a b ψ := by
  have h := E2_step g M a b ψ
  have : 0 ≤ ∑ j ∈ range (g + 1), ∑ l ∈ range (M + 1),
        (b - a) * (bw g a j * bw M b l * (ψ (j + l + 1) - ψ (j + l))) := by
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro l hl
    have hj' := Finset.mem_range.mp hj
    have hl' := Finset.mem_range.mp hl
    have := hψ (j + l) (by omega)
    have h1 := bw_nonneg g ha0 (by linarith) j
    have h2 := bw_nonneg M (by linarith : 0 ≤ b) hb1 l
    have : 0 ≤ b - a := by linarith
    have : 0 ≤ ψ (j + l + 1) - ψ (j + l) := by linarith
    positivity
  linarith

lemma E2_step_lt (g M : ℕ) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b < 1) (ψ : ℕ → ℝ)
    (hψ : ∀ k, k + 1 ≤ g + M + 1 → ψ k < ψ (k + 1)) :
    E2 (g + 1) M a b ψ < E2 g (M + 1) a b ψ := by
  have h := E2_step g M a b ψ
  have : 0 < ∑ j ∈ range (g + 1), ∑ l ∈ range (M + 1),
        (b - a) * (bw g a j * bw M b l * (ψ (j + l + 1) - ψ (j + l))) := by
    apply Finset.sum_pos'
    · intro j hj
      apply Finset.sum_nonneg
      intro l hl
      have hj' := Finset.mem_range.mp hj
      have hl' := Finset.mem_range.mp hl
      have := hψ (j + l) (by omega)
      have h1 := bw_nonneg g ha0 (by linarith) j
      have h2 := bw_nonneg M (by linarith : 0 ≤ b) hb1.le l
      have : 0 ≤ b - a := by linarith
      have : 0 ≤ ψ (j + l + 1) - ψ (j + l) := by linarith
      positivity
    · refine ⟨0, by simp, ?_⟩
      apply Finset.sum_pos'
      · intro l hl
        have hl' := Finset.mem_range.mp hl
        have := hψ (0 + l) (by omega)
        have h1 := bw_nonneg g ha0 (by linarith) 0
        have h2 := bw_nonneg M (by linarith : 0 ≤ b) hb1.le l
        have : 0 ≤ b - a := by linarith
        have : 0 ≤ ψ (0 + l + 1) - ψ (0 + l) := by linarith
        positivity
      · refine ⟨0, by simp, ?_⟩
        have := hψ (0 + 0) (by omega)
        have h1 := bw_zero_pos g (by linarith : a < 1)
        have h2 := bw_zero_pos M hb1
        have : 0 < b - a := by linarith
        have : 0 < ψ (0 + 0 + 1) - ψ (0 + 0) := by linarith
        positivity
  linarith

/-- iterate: shifting all `d` remaining `b`-trials to `a`-trials -/
lemma E2_chain_le {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) (ψ : ℕ → ℝ) (n : ℕ)
    (hψ : ∀ k, k + 1 ≤ n → ψ k ≤ ψ (k + 1)) :
    ∀ d g, g + d = n → E2 (g + d) 0 a b ψ ≤ E2 g d a b ψ := by
  intro d
  induction d with
  | zero => intro g _; simp
  | succ d ih =>
    intro g hg
    have h1 := ih (g + 1) (by omega)
    have h2 := E2_step_le g d ha0 hab hb1 ψ (fun k hk => hψ k (by omega))
    rw [show g + (d + 1) = g + 1 + d by omega]
    linarith

lemma E2_chain_lt {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b < 1) (ψ : ℕ → ℝ) (n : ℕ)
    (hψ : ∀ k, k + 1 ≤ n → ψ k < ψ (k + 1)) :
    ∀ d g, g + d + 1 = n → E2 (g + d + 1) 0 a b ψ < E2 g (d + 1) a b ψ := by
  intro d g hg
  have h1 := E2_chain_le ha0 hab.le hb1.le ψ n (fun k hk => (hψ k hk).le) d (g + 1) (by omega)
  have h2 := E2_step_lt g d ha0 hab hb1 ψ (fun k hk => hψ k (by omega))
  rw [show g + d + 1 = g + 1 + d by omega]
  linarith

/-- convolution sum to double sum -/
lemma conv_swap (n g M : ℕ) (hn : n = g + M + 1) (h : ℕ → ℕ → ℝ)
    (hz : ∀ j l, (g < j ∨ M < l) → h j l = 0) :
    ∑ k ∈ range n, ∑ j ∈ range (k + 1), h j (k - j) =
      ∑ j ∈ range (g + 1), ∑ l ∈ range (M + 1), h j l := by
  rw [Finset.sum_sigma', ← Finset.sum_product']
  apply Finset.sum_bij_ne_zero (fun x _ _ => (x.2, x.1 - x.2))
  · rintro ⟨k, j⟩ hx hne
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_product, Finset.mem_range]
    by_contra hc
    apply hne
    apply hz
    dsimp only at hc ⊢
    omega
  · rintro ⟨k1, j1⟩ hx _ ⟨k2, j2⟩ hy _ hxy
    simp only [Finset.mem_sigma, Finset.mem_range] at hx hy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨e1, e2⟩ := hxy
    have : k1 = k2 := by omega
    subst e1
    subst this
    rfl
  · rintro ⟨j, l⟩ hy hne
    simp only [Finset.mem_product, Finset.mem_range] at hy
    refine ⟨⟨j + l, j⟩, ?_, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · simpa using hne
    · simp
  · intro x _ _
    rfl

section Model

variable (m : Params)

noncomputable def phi (c F : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * c / ((m.N : ℝ) - k) + m.α * max ((k : ℝ) * c / ((m.N : ℝ) - k) - F) 0

noncomputable def Xc (g : ℕ) (c F : ℝ) : ℝ := ∑ k ∈ range m.N, m.defaultLaw g k * phi m c F k

lemma X_eq (g : ℕ) (I F : ℝ) : m.X g I F = Xc m g (m.D - I - F) F := rfl

lemma defaultLaw_eq (g k : ℕ) : m.defaultLaw g k =
    ∑ j ∈ range (k + 1), bw g m.qs j * bw (m.N - 1 - g) m.qr (k - j) := by
  unfold Params.defaultLaw bw
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bw_eq_zero (n : ℕ) (p : ℝ) (i : ℕ) (h : n < i) : bw n p i = 0 := by
  unfold bw
  rw [Nat.choose_eq_zero_of_lt h]
  simp

lemma Xc_eq_E2 (g : ℕ) (hg : g ≤ m.N - 1) (hN : 1 ≤ m.N) (c F : ℝ) :
    Xc m g c F = E2 g (m.N - 1 - g) m.qs m.qr (phi m c F) := by
  unfold Xc E2
  have hc : ∀ k ∈ range m.N, m.defaultLaw g k * phi m c F k = ∑ j ∈ range (k + 1),
      (fun j l => bw g m.qs j * bw (m.N - 1 - g) m.qr l * phi m c F (j + l)) j (k - j) := by
    intro k _
    rw [defaultLaw_eq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have : j + (k - j) = k := by
      have := Finset.mem_range.mp hj
      omega
    simp only [this]
  rw [Finset.sum_congr rfl hc]
  refine conv_swap m.N g (m.N - 1 - g) (by omega)
    (fun j l => bw g m.qs j * bw (m.N - 1 - g) m.qr l * phi m c F (j + l)) ?_
  intro j l hjl
  rcases hjl with h | h
  · simp [bw_eq_zero g m.qs j h]
  · simp [bw_eq_zero _ m.qr l h]

/-- `G^g(I,F)`: (LHS − RHS) of the hedging condition -/
noncomputable def Gg (g : ℕ) (I F : ℝ) : ℝ :=
  m.D - I - F + m.X g I F - (m.Accp - I - F) * m.pledge

lemma IC_iff (g : ℕ) (I F : ℝ) : m.IsIC g I F ↔ Gg m g I F ≤ 0 := by
  unfold Params.IsIC Gg
  constructor <;> intro h <;> linarith

lemma Eq18_iff (I F : ℝ) : m.Eq18 I F ↔ Gg m (m.N - 1) I F = 0 := by
  unfold Params.Eq18 Gg
  constructor <;> intro h <;> linarith

lemma Gg_eq (g : ℕ) (I F : ℝ) : Gg m g I F = (m.D - I - F) * (1 - m.pledge)
    - (m.Accp - m.D) * m.pledge + Xc m g (m.D - I - F) F := by
  unfold Gg
  rw [X_eq]
  ring

lemma Gg_cont_F (g : ℕ) (I : ℝ) : Continuous (fun F => Gg m g I F) := by
  unfold Gg Params.X
  fun_prop

lemma Gg_cont_I (g : ℕ) (F : ℝ) : Continuous (fun I => Gg m g I F) := by
  unfold Gg Params.X
  fun_prop

lemma phi_zero (F : ℝ) (hF : 0 ≤ F) (k : ℕ) : phi m 0 F k = 0 := by
  unfold phi
  rw [mul_zero, zero_div, zero_sub, max_eq_right (by linarith)]
  ring

variable {m}

lemma qs_pos (hm : Standing m) : 0 < m.qs := hm.cond1.1
lemma qs_lt_qr (hm : Standing m) : m.qs < m.qr := hm.cond1.2.1
lemma qr_lt_one (hm : Standing m) : m.qr < 1 := hm.qr_lt_one

lemma P_pos (hm : Standing m) : 0 < m.pledge := by
  unfold Params.pledge
  apply div_pos
  · linarith [hm.cond2.2]
  · exact mul_pos hm.pc_mem.1 (by linarith [hm.cond1.2.1])

lemma Accp_gt (hm : Standing m) : m.D < m.Accp := by
  unfold Params.Accp Params.Pccp
  have h1 := hm.pc_mem.1
  have h2 := hm.pc_mem.2
  have h3 := hm.D_pos
  have h4 := hm.γ_pos
  have h5 : 0 < 1 + m.γ * m.D * (1 - m.pc) := by
    have := mul_pos (mul_pos h4 h3) (sub_pos.2 h2)
    linarith
  have := mul_pos (mul_pos h1 h3) h5
  linarith [hm.A0_gt_D]

lemma PA_lt (hm : Standing m) : m.Accp * m.pledge < m.D := by
  have hA : 0 < m.Accp := by linarith [Accp_gt hm, hm.D_pos]
  have := hm.assumption2
  rw [lt_div_iff₀ hA] at this
  linarith

lemma P_lt_one (hm : Standing m) : m.pledge < 1 := by
  have := PA_lt hm
  have := Accp_gt hm
  have := P_pos hm
  have := hm.D_pos
  nlinarith

lemma K_pos (hm : Standing m) : 0 < (m.Accp - m.D) * m.pledge :=
  mul_pos (sub_pos.2 (Accp_gt hm)) (P_pos hm)

lemma defaultLaw_nonneg (hm : Standing m) (g k : ℕ) : 0 ≤ m.defaultLaw g k := by
  rw [defaultLaw_eq]
  apply Finset.sum_nonneg
  intro j _
  have h1 := qs_pos hm
  have h2 := qs_lt_qr hm
  have h3 := qr_lt_one hm
  exact mul_nonneg (bw_nonneg _ h1.le (by linarith) _) (bw_nonneg _ (by linarith) h3.le _)

lemma ratio_le (N k : ℕ) (hk : k + 1 < N) {c : ℝ} (hc : 0 ≤ c) :
    (k : ℝ) * c / ((N : ℝ) - k) ≤ ((k + 1 : ℕ) : ℝ) * c / ((N : ℝ) - ((k + 1 : ℕ) : ℝ)) := by
  have hk' : (k : ℝ) + 1 < N := by exact_mod_cast hk
  have h1 : (0 : ℝ) < N - k := by linarith
  have h2 : (0 : ℝ) < N - (k + 1) := by linarith
  push_cast
  rw [div_le_div_iff₀ h1 h2]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith [mul_nonneg hc hN]

lemma ratio_lt (N k : ℕ) (hk : k + 1 < N) {c : ℝ} (hc : 0 < c) :
    (k : ℝ) * c / ((N : ℝ) - k) < ((k + 1 : ℕ) : ℝ) * c / ((N : ℝ) - ((k + 1 : ℕ) : ℝ)) := by
  have hk' : (k : ℝ) + 1 < N := by exact_mod_cast hk
  have h1 : (0 : ℝ) < N - k := by linarith
  have h2 : (0 : ℝ) < N - (k + 1) := by linarith
  push_cast
  rw [div_lt_div_iff₀ h1 h2]
  have hN : (0 : ℝ) < N := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  nlinarith [mul_pos hc hN]

lemma phi_le_succ (hm : Standing m) (c F : ℝ) (hc : 0 ≤ c) (k : ℕ) (hk : k + 1 < m.N) :
    phi m c F k ≤ phi m c F (k + 1) := by
  unfold phi
  have h := ratio_le m.N k hk hc
  have hα := hm.cond3.1
  have h2 : max ((k : ℝ) * c / ((m.N : ℝ) - k) - F) 0 ≤
      max (((k + 1 : ℕ) : ℝ) * c / ((m.N : ℝ) - ((k + 1 : ℕ) : ℝ)) - F) 0 :=
    max_le_max (by linarith) le_rfl
  have := mul_le_mul_of_nonneg_left h2 hα.le
  linarith

lemma phi_lt_succ (hm : Standing m) (c F : ℝ) (hc : 0 < c) (k : ℕ) (hk : k + 1 < m.N) :
    phi m c F k < phi m c F (k + 1) := by
  unfold phi
  have h := ratio_lt m.N k hk hc
  have hα := hm.cond3.1
  have h2 : max ((k : ℝ) * c / ((m.N : ℝ) - k) - F) 0 ≤
      max (((k + 1 : ℕ) : ℝ) * c / ((m.N : ℝ) - ((k + 1 : ℕ) : ℝ)) - F) 0 :=
    max_le_max (by linarith) le_rfl
  have := mul_le_mul_of_nonneg_left h2 hα.le
  linarith

lemma Xc_le (hm : Standing m) (g : ℕ) (hg : g ≤ m.N - 1) (c F : ℝ) (hc : 0 ≤ c) :
    Xc m (m.N - 1) c F ≤ Xc m g c F := by
  have hN := hm.two_le_N
  rw [Xc_eq_E2 m g hg (by omega), Xc_eq_E2 m (m.N - 1) le_rfl (by omega), Nat.sub_self]
  have := E2_chain_le (qs_pos hm).le (qs_lt_qr hm).le (qr_lt_one hm).le (phi m c F) (m.N - 1)
    (fun k hk => phi_le_succ hm c F hc k (by omega)) (m.N - 1 - g) g (by omega)
  rwa [show g + (m.N - 1 - g) = m.N - 1 by omega] at this

lemma Xc_lt (hm : Standing m) (g : ℕ) (hg : g < m.N - 1) (c F : ℝ) (hc : 0 < c) :
    Xc m (m.N - 1) c F < Xc m g c F := by
  have hN := hm.two_le_N
  rw [Xc_eq_E2 m g hg.le (by omega), Xc_eq_E2 m (m.N - 1) le_rfl (by omega), Nat.sub_self]
  have := E2_chain_lt (qs_pos hm).le (qs_lt_qr hm) (qr_lt_one hm) (phi m c F) (m.N - 1)
    (fun k hk => phi_lt_succ hm c F hc k (by omega)) (m.N - 2 - g) g (by omega)
  rwa [show g + (m.N - 2 - g) + 1 = m.N - 1 by omega,
    show m.N - 2 - g + 1 = m.N - 1 - g by omega] at this

lemma phi_mono2 (hm : Standing m) (k : ℕ) (hk : k < m.N) {c c' F F' : ℝ} (hc : c ≤ c')
    (hF : F' ≤ F) : phi m c F k ≤ phi m c' F' k := by
  unfold phi
  have h1 : (0 : ℝ) < (m.N : ℝ) - k := by
    have : (k : ℝ) < m.N := by exact_mod_cast hk
    linarith
  have h2 : (k : ℝ) * c / ((m.N : ℝ) - k) ≤ (k : ℝ) * c' / ((m.N : ℝ) - k) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg k)) h1.le
  have h3 : max ((k : ℝ) * c / ((m.N : ℝ) - k) - F) 0 ≤
      max ((k : ℝ) * c' / ((m.N : ℝ) - k) - F') 0 := max_le_max (by linarith) le_rfl
  have := mul_le_mul_of_nonneg_left h3 hm.cond3.1.le
  linarith

lemma phi_nonneg (hm : Standing m) (k : ℕ) (hk : k < m.N) {c : ℝ} (hc : 0 ≤ c) (F : ℝ) :
    0 ≤ phi m c F k := by
  unfold phi
  have h1 : (0 : ℝ) < (m.N : ℝ) - k := by
    have : (k : ℝ) < m.N := by exact_mod_cast hk
    linarith
  have := div_nonneg (mul_nonneg (Nat.cast_nonneg k) hc) h1.le
  have := mul_nonneg hm.cond3.1.le (le_max_right ((k : ℝ) * c / ((m.N : ℝ) - k) - F) 0)
  linarith

lemma Xc_mono (hm : Standing m) (g : ℕ) {c c' F F' : ℝ} (hc : c ≤ c') (hF : F' ≤ F) :
    Xc m g c F ≤ Xc m g c' F' :=
  Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
    (phi_mono2 hm k (Finset.mem_range.mp hk) hc hF) (defaultLaw_nonneg hm g k))

lemma Xc_nonneg (hm : Standing m) (g : ℕ) {c : ℝ} (hc : 0 ≤ c) (F : ℝ) : 0 ≤ Xc m g c F :=
  Finset.sum_nonneg (fun k hk => mul_nonneg (defaultLaw_nonneg hm g k)
    (phi_nonneg hm k (Finset.mem_range.mp hk) hc F))

lemma Gg_anti (hm : Standing m) (g : ℕ) {I I' F F' : ℝ} (hI : I ≤ I') (hF : F ≤ F') :
    Gg m g I' F' ≤ Gg m g I F - (1 - m.pledge) * ((I' + F') - (I + F)) := by
  rw [Gg_eq, Gg_eq]
  have := Xc_mono hm g (show m.D - I' - F' ≤ m.D - I - F by linarith) hF
  linarith

lemma Gg_top (hm : Standing m) (g : ℕ) (I : ℝ) (hI : I ≤ m.D) : Gg m g I (m.D - I) < 0 := by
  rw [Gg_eq, show m.D - I - (m.D - I) = 0 by ring]
  have : Xc m g 0 (m.D - I) = 0 := by
    unfold Xc
    apply Finset.sum_eq_zero
    intro k _
    rw [phi_zero m _ (by linarith)]
    ring
  rw [this]
  have := K_pos hm
  linarith

lemma Fhat_mem (hm : Standing m) (I : ℝ) (hI : I ≤ m.D) :
    0 ≤ m.Fhat I ∧ m.Fhat I ≤ m.D - I ∧ Gg m (m.N - 1) I (m.Fhat I) ≤ 0 := by
  have hne : ({F | 0 ≤ F ∧ F ≤ m.D - I ∧ m.IsIC (m.N - 1) I F} : Set ℝ).Nonempty :=
    ⟨m.D - I, by linarith, le_rfl, (IC_iff m _ _ _).2 (Gg_top hm _ I hI).le⟩
  have hbdd : BddBelow ({F | 0 ≤ F ∧ F ≤ m.D - I ∧ m.IsIC (m.N - 1) I F} : Set ℝ) :=
    ⟨0, fun F hF => hF.1⟩
  have hcl : IsClosed ({F | 0 ≤ F ∧ F ≤ m.D - I ∧ m.IsIC (m.N - 1) I F} : Set ℝ) := by
    have : ({F | 0 ≤ F ∧ F ≤ m.D - I ∧ m.IsIC (m.N - 1) I F} : Set ℝ) =
        Set.Icc 0 (m.D - I) ∩ {F | Gg m (m.N - 1) I F ≤ 0} := by
      ext F
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, IC_iff, and_assoc]
    rw [this]
    exact isClosed_Icc.inter (isClosed_le (Gg_cont_F m _ I) continuous_const)
  have := hcl.csInf_mem hne hbdd
  obtain ⟨h1, h2, h3⟩ := this
  exact ⟨h1, h2, (IC_iff m _ _ _).1 h3⟩

lemma Fhat_le (I F : ℝ) (h0 : 0 ≤ F) (hF : F ≤ m.D - I) (hG : Gg m (m.N - 1) I F ≤ 0) :
    m.Fhat I ≤ F :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨h0, hF, (IC_iff m _ _ _).2 hG⟩

lemma IC_iff_Fhat (hm : Standing m) (I F : ℝ) (hF0 : 0 ≤ F) (hIF : I + F ≤ m.D) :
    Gg m (m.N - 1) I F ≤ 0 ↔ m.Fhat I ≤ F := by
  constructor
  · intro h
    exact Fhat_le I F hF0 (by linarith) h
  · intro h
    obtain ⟨-, -, hic⟩ := Fhat_mem hm I (by linarith)
    have := Gg_anti hm (m.N - 1) (le_refl I) h
    have h1 := P_lt_one hm
    nlinarith

end Model

section Game

variable {m : Params}

lemma V_diff (hm : Standing m) (g : ℕ) (I F : ℝ) :
    m.V .s g I F - m.V .r g I F = -(m.pc * (m.qr - m.qs)) * Gg m g I F := by
  have hpc := hm.pc_mem.1
  have hq : m.qr - m.qs ≠ 0 := (sub_pos.2 (qs_lt_qr hm)).ne'
  have hmu : m.mu .s - m.mu .r = (1 - m.qs) * m.Rs - (1 - m.qr) * m.Rr := by
    simp [Params.mu, Params.q, Params.R]
  have hP : m.pledge * (m.pc * (m.qr - m.qs)) = (1 - m.qs) * m.Rs - (1 - m.qr) * m.Rr := by
    rw [← hmu]
    unfold Params.pledge
    field_simp
  simp only [Params.V, Params.q, Params.R, Gg]
  linear_combination (-(m.Accp - I - F)) * hP

lemma V_g (a : Action) (g g' : ℕ) (I F : ℝ) :
    m.V a g I F - m.V a g' I F = (1 - m.q a) * m.pc * (m.X g' I F - m.X g I F) := by
  simp only [Params.V]
  ring

lemma one_sub_q_pos (hm : Standing m) (a : Action) : 0 < 1 - m.q a := by
  have := qs_lt_qr hm
  have := qr_lt_one hm
  cases a <;> simp only [Params.q] <;> linarith

lemma hedgers_le (a : Fin m.N → Action) (i : Fin m.N) : m.hedgers a i ≤ m.N - 1 := by
  unfold Params.hedgers
  calc _ ≤ (univ.erase i).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Finset.mem_erase.2 ⟨hj.1, Finset.mem_univ _⟩
    _ = m.N - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]

lemma hedgers_lt (a : Fin m.N → Action) (i j : Fin m.N) (hij : i ≠ j) (hr : a i = .r) :
    m.hedgers a j < m.N - 1 := by
  unfold Params.hedgers
  calc _ < (univ.erase j).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i, Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩, ?_⟩
          simp [hr]
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact Finset.mem_erase.2 ⟨hk.1, Finset.mem_univ _⟩
    _ = m.N - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]

lemma hedgers_all_s (i : Fin m.N) : m.hedgers (fun _ => Action.s) i = m.N - 1 := by
  unfold Params.hedgers
  have : (univ.filter (fun j : Fin m.N => j ≠ i ∧ Action.s = Action.s)) = univ.erase i := by
    ext j
    simp
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

lemma hedgers_update (a : Fin m.N → Action) (i : Fin m.N) (x : Action) :
    m.hedgers (Function.update a i x) i = m.hedgers a i := by
  unfold Params.hedgers
  congr 1
  apply Finset.filter_congr
  intro j _
  constructor
  · rintro ⟨hj, h⟩
    refine ⟨hj, ?_⟩
    simpa [Function.update_apply, hj] using h
  · rintro ⟨hj, h⟩
    refine ⟨hj, ?_⟩
    simpa [Function.update_apply, hj] using h

lemma isNash_iff (I F : ℝ) (a : Fin m.N → Action) :
    m.IsNash I F a ↔ ∀ i x, m.V x (m.hedgers a i) I F ≤ m.V (a i) (m.hedgers a i) I F := by
  unfold Params.IsNash CarbonDoubleCount.Planner.IsPureNash
  constructor
  · rintro ⟨-, h⟩ i x
    have := h i x (Set.mem_univ _)
    simpa [Params.payoff, hedgers_update] using this
  · intro h
    refine ⟨fun _ => Set.mem_univ _, fun i x _ => ?_⟩
    simpa [Params.payoff, hedgers_update] using h i x

lemma part1 (hm : Standing m) (I F : ℝ) (hI : 0 ≤ I) (hF : 0 ≤ F) (hIF : I + F ≤ m.D)
    (a : Fin m.N → Action) :
    m.IsParetoDominantNash I F a ↔ a = fun _ => if F < m.Fhat I then Action.r else Action.s := by
  have hN := hm.two_le_N
  have hc : 0 ≤ m.D - I - F := by linarith
  have hpc := hm.pc_mem.1
  have hpq : 0 < m.pc * (m.qr - m.qs) := mul_pos hpc (sub_pos.2 (qs_lt_qr hm))
  have hXg : ∀ g, g ≤ m.N - 1 → m.X (m.N - 1) I F ≤ m.X g I F := fun g hg => by
    rw [X_eq, X_eq]
    exact Xc_le hm g hg _ F hc
  have hVg : ∀ x g, g ≤ m.N - 1 → m.V x g I F ≤ m.V x (m.N - 1) I F := by
    intro x g hg
    have h1 := V_g (m := m) x g (m.N - 1) I F
    have h2 := hXg g hg
    have h3 := one_sub_q_pos hm x
    have := mul_nonneg (mul_pos h3 hpc).le (sub_nonneg.2 h2)
    linarith
  by_cases hlt : F < m.Fhat I
  · simp only [if_pos hlt]
    have hG : 0 < Gg m (m.N - 1) I F := by
      by_contra h
      push_neg at h
      exact absurd ((IC_iff_Fhat hm I F hF hIF).1 h) (not_le.2 hlt)
    have hdom : ∀ g, g ≤ m.N - 1 → m.V .s g I F < m.V .r g I F := fun g hg => by
      have h1 := V_diff hm g I F
      have h2 := hXg g hg
      have h3 : 0 < Gg m g I F := by
        unfold Gg
        unfold Gg at hG
        linarith
      have := mul_pos hpq h3
      linarith
    have hnash : ∀ b, m.IsNash I F b → b = fun _ => Action.r := by
      intro b hb
      funext i
      rw [isNash_iff] at hb
      have := hb i .r
      cases h : b i with
      | r => rfl
      | s =>
        rw [h] at this
        exact absurd this (not_le.2 (hdom _ (hedgers_le b i)))
    have hallr : m.IsNash I F (fun _ => Action.r) := by
      rw [isNash_iff]
      intro i x
      cases x with
      | r => exact le_refl _
      | s => exact (hdom _ (hedgers_le _ i)).le
    constructor
    · intro h
      exact hnash a h.1
    · rintro rfl
      refine ⟨hallr, fun b hb i => ?_⟩
      rw [hnash b hb]
  · simp only [if_neg hlt]
    push_neg at hlt
    have hG : Gg m (m.N - 1) I F ≤ 0 := (IC_iff_Fhat hm I F hF hIF).2 hlt
    have hrs : m.V .r (m.N - 1) I F ≤ m.V .s (m.N - 1) I F := by
      have h1 := V_diff hm (m.N - 1) I F
      have := mul_nonneg hpq.le (neg_nonneg.2 hG)
      linarith
    have hle : ∀ x : Action, m.V x (m.N - 1) I F ≤ m.V .s (m.N - 1) I F := by
      intro x
      cases x
      · exact le_refl _
      · exact hrs
    have hbound : ∀ b i, m.payoff I F b i ≤ m.V .s (m.N - 1) I F := by
      intro b i
      unfold Params.payoff
      exact (hVg (b i) _ (hedgers_le b i)).trans (hle (b i))
    have halls : m.IsNash I F (fun _ => Action.s) := by
      rw [isNash_iff]
      intro i x
      rw [hedgers_all_s]
      exact hle x
    have hpay_s : ∀ i, m.payoff I F (fun _ => Action.s) i = m.V .s (m.N - 1) I F := fun i => by
      unfold Params.payoff
      rw [hedgers_all_s]
    constructor
    · rintro ⟨ha, hpd⟩
      by_contra hne
      obtain ⟨i0, hi0⟩ : ∃ i0, a i0 = Action.r := by
        by_contra hall
        push_neg at hall
        apply hne
        funext i
        show a i = Action.s
        cases h : a i
        · rfl
        · exact absurd h (hall i)
      rcases eq_or_lt_of_le hc with hc0 | hcpos
      · have hF' : F = m.D - I := by linarith
        have hGneg : Gg m (m.hedgers a i0) I F < 0 := by
          rw [hF']
          exact Gg_top hm _ I (by linarith)
        rw [isNash_iff] at ha
        have h1 := ha i0 .s
        rw [hi0] at h1
        have h2 := V_diff hm (m.hedgers a i0) I F
        have := mul_pos hpq (neg_pos.2 hGneg)
        linarith
      · obtain ⟨j, hj⟩ : ∃ j : Fin m.N, j ≠ i0 := by
          by_cases h0 : i0.val = 0
          · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
          · exact ⟨⟨0, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
        have hlt' := hedgers_lt a i0 j hj.symm hi0
        have h1 := hpd _ halls j
        rw [hpay_s] at h1
        have hX := Xc_lt hm (m.hedgers a j) hlt' (m.D - I - F) F hcpos
        rw [← X_eq, ← X_eq] at hX
        unfold Params.payoff at h1
        have hq := one_sub_q_pos hm (a j)
        have hv := V_g (m := m) (a j) (m.hedgers a j) (m.N - 1) I F
        have := mul_pos (mul_pos hq hpc) (sub_pos.2 hX)
        have := hle (a j)
        linarith
    · rintro rfl
      exact ⟨halls, fun b _ i => by rw [hpay_s]; exact hbound b i⟩

end Game

section Shape

variable {m : Params}

lemma G00_pos (hm : Standing m) : 0 < Gg m (m.N - 1) 0 0 := by
  rw [Gg_eq]
  have := Xc_nonneg hm (m.N - 1) (show 0 ≤ m.D - 0 - 0 by linarith [hm.D_pos]) 0
  have := PA_lt hm
  linarith

lemma Ihat0_mem (hm : Standing m) :
    0 ≤ m.Ihat0 ∧ m.Ihat0 ≤ m.D ∧ Gg m (m.N - 1) m.Ihat0 0 ≤ 0 := by
  have htop : Gg m (m.N - 1) m.D 0 < 0 := by
    have := Gg_top hm (m.N - 1) m.D le_rfl
    rwa [sub_self] at this
  have hne : ({I | 0 ≤ I ∧ I ≤ m.D ∧ m.IsIC (m.N - 1) I 0} : Set ℝ).Nonempty :=
    ⟨m.D, hm.D_pos.le, le_rfl, (IC_iff m _ _ _).2 htop.le⟩
  have hbdd : BddBelow ({I | 0 ≤ I ∧ I ≤ m.D ∧ m.IsIC (m.N - 1) I 0} : Set ℝ) :=
    ⟨0, fun I hI => hI.1⟩
  have hcl : IsClosed ({I | 0 ≤ I ∧ I ≤ m.D ∧ m.IsIC (m.N - 1) I 0} : Set ℝ) := by
    have : ({I | 0 ≤ I ∧ I ≤ m.D ∧ m.IsIC (m.N - 1) I 0} : Set ℝ) =
        Set.Icc 0 m.D ∩ {I | Gg m (m.N - 1) I 0 ≤ 0} := by
      ext I
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, IC_iff, and_assoc]
    rw [this]
    exact isClosed_Icc.inter (isClosed_le (Gg_cont_I m _ 0) continuous_const)
  obtain ⟨h1, h2, h3⟩ := hcl.csInf_mem hne hbdd
  exact ⟨h1, h2, (IC_iff m _ _ _).1 h3⟩

lemma Ihat0_le (I : ℝ) (h0 : 0 ≤ I) (hD : I ≤ m.D) (hG : Gg m (m.N - 1) I 0 ≤ 0) :
    m.Ihat0 ≤ I :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨h0, hD, (IC_iff m _ _ _).2 hG⟩

lemma Ihat0_pos (hm : Standing m) : 0 < m.Ihat0 := by
  obtain ⟨h0, -, h2⟩ := Ihat0_mem hm
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h] at h2
    exact absurd h2 (not_le.2 (G00_pos hm))
  · exact h

lemma G_Ihat0 (hm : Standing m) : Gg m (m.N - 1) m.Ihat0 0 = 0 := by
  obtain ⟨h0, hD, hle⟩ := Ihat0_mem hm
  by_contra hne
  have hlt : Gg m (m.N - 1) m.Ihat0 0 < 0 := lt_of_le_of_ne hle hne
  have hcont : ContinuousOn (fun I => Gg m (m.N - 1) I 0) (Set.Icc 0 m.Ihat0) :=
    (Gg_cont_I m _ 0).continuousOn
  obtain ⟨x, ⟨hx0, hx1⟩, hx⟩ := intermediate_value_Icc' h0 hcont ⟨hlt.le, (G00_pos hm).le⟩
  have h1 := Ihat0_le x hx0 (by linarith) (le_of_eq hx)
  have h2 : x = m.Ihat0 := le_antisymm hx1 h1
  rw [h2] at hx
  exact hne hx

lemma G_I0_nonneg (hm : Standing m) (I : ℝ) (hI : I ≤ m.Ihat0) : 0 ≤ Gg m (m.N - 1) I 0 := by
  have := Gg_anti hm (m.N - 1) hI (le_refl (0 : ℝ))
  rw [G_Ihat0 hm] at this
  have := P_lt_one hm
  nlinarith [mul_nonneg (sub_nonneg.2 this.le) (sub_nonneg.2 hI)]

lemma Ihat0_le_D (hm : Standing m) : m.Ihat0 ≤ m.D := (Ihat0_mem hm).2.1

lemma Fhat_root (hm : Standing m) (I : ℝ) (hI : I ≤ m.Ihat0) :
    Gg m (m.N - 1) I (m.Fhat I) = 0 := by
  have hID : I ≤ m.D := hI.trans (Ihat0_le_D hm)
  obtain ⟨h0, h1, h2⟩ := Fhat_mem hm I hID
  have hcont : ContinuousOn (fun F => Gg m (m.N - 1) I F) (Set.Icc 0 (m.Fhat I)) :=
    (Gg_cont_F m _ I).continuousOn
  obtain ⟨x, ⟨hx0, hx1⟩, hx⟩ := intermediate_value_Icc' h0 hcont ⟨h2, G_I0_nonneg hm I hI⟩
  have h3 := Fhat_le I x hx0 (by linarith) (le_of_eq hx)
  have h4 : x = m.Fhat I := le_antisymm hx1 h3
  rw [← h4]
  exact hx

lemma Gg_strict_F (hm : Standing m) (g : ℕ) (I : ℝ) {F F' : ℝ} (h : F < F') :
    Gg m g I F' < Gg m g I F := by
  have := Gg_anti hm g (le_refl I) h.le
  have := P_lt_one hm
  nlinarith [mul_pos (sub_pos.2 this) (sub_pos.2 h)]

lemma Fhat_lt (hm : Standing m) (I : ℝ) (hI : I ≤ m.Ihat0) : m.Fhat I < m.D - I := by
  have hID : I ≤ m.D := hI.trans (Ihat0_le_D hm)
  obtain ⟨_, h1, _⟩ := Fhat_mem hm I hID
  rcases eq_or_lt_of_le h1 with h | h
  · have h2 := Fhat_root hm I hI
    rw [h] at h2
    have := Gg_top hm (m.N - 1) I hID
    linarith
  · exact h

lemma part2 (hm : Standing m) : ∀ I ∈ Set.Icc 0 m.Ihat0, 0 ≤ m.Fhat I ∧ m.Fhat I < m.D - I ∧
    m.Eq18 I (m.Fhat I) ∧ ∀ F, 0 ≤ F → F < m.D - I → m.Eq18 I F → F = m.Fhat I := by
  intro I ⟨hI0, hI⟩
  have hID : I ≤ m.D := hI.trans (Ihat0_le_D hm)
  refine ⟨(Fhat_mem hm I hID).1, Fhat_lt hm I hI, (Eq18_iff m _ _).2 (Fhat_root hm I hI), ?_⟩
  intro F _ _ hE
  rw [Eq18_iff] at hE
  have hr := Fhat_root hm I hI
  rcases lt_trichotomy F (m.Fhat I) with h | h | h
  · have := Gg_strict_F hm (m.N - 1) I h
    linarith
  · exact h
  · have := Gg_strict_F hm (m.N - 1) I h
    linarith

lemma part4 (hm : Standing m) : StrictAntiOn m.Fhat (Set.Icc 0 m.Ihat0) := by
  intro I hI I' hI' hlt
  by_contra h
  push_neg at h
  have h1 := Gg_anti hm (m.N - 1) hlt.le h
  rw [Fhat_root hm I hI.2, Fhat_root hm I' hI'.2] at h1
  have := P_lt_one hm
  nlinarith [mul_pos (sub_pos.2 this) (show 0 < (I' + m.Fhat I') - (I + m.Fhat I) by linarith)]

/-- root equation in `c`-form -/
lemma root_c (hm : Standing m) (I : ℝ) (hI : I ≤ m.Ihat0) :
    (m.D - I - m.Fhat I) * (1 - m.pledge) - (m.Accp - m.D) * m.pledge
      + Xc m (m.N - 1) (m.D - I - m.Fhat I) (m.Fhat I) = 0 := by
  rw [← Gg_eq]
  exact Fhat_root hm I hI

lemma part5 (hm : Standing m) : MonotoneOn (fun I => m.Fhat I + I) (Set.Icc 0 m.Ihat0) := by
  intro I hI I' hI' hle
  simp only
  rcases eq_or_lt_of_le hle with h | h
  · rw [h]
  · have hF := part4 hm hI hI' h
    by_contra hc
    push_neg at hc
    have r1 := root_c hm I hI.2
    have r2 := root_c hm I' hI'.2
    have hX := Xc_mono hm (m.N - 1)
      (show m.D - I - m.Fhat I ≤ m.D - I' - m.Fhat I' by linarith) hF.le
    have := P_lt_one hm
    nlinarith [mul_pos (sub_pos.2 this)
      (show 0 < (m.D - I' - m.Fhat I') - (m.D - I - m.Fhat I) by linarith)]

lemma dl_top_pos (hm : Standing m) : 0 < m.defaultLaw (m.N - 1) (m.N - 1) := by
  have hN := hm.two_le_N
  rw [defaultLaw_eq]
  apply Finset.sum_pos'
  · intro j _
    have h1 := qs_pos hm
    have h2 := qs_lt_qr hm
    have h3 := qr_lt_one hm
    exact mul_nonneg (bw_nonneg _ h1.le (by linarith) _) (bw_nonneg _ (by linarith) h3.le _)
  · refine ⟨m.N - 1, Finset.mem_range.2 (by omega), ?_⟩
    simp only [Nat.sub_self, bw, Nat.choose_self, Nat.choose_zero_right, Nat.cast_one,
      pow_zero, one_mul, mul_one]
    exact pow_pos (qs_pos hm) _

lemma Xc_strict_F (hm : Standing m) {c F F' : ℝ} (hF : F < F')
    (hF' : F' ≤ ((m.N : ℝ) - 1) * c) : Xc m (m.N - 1) c F' < Xc m (m.N - 1) c F := by
  have hN := hm.two_le_N
  unfold Xc
  apply Finset.sum_lt_sum
  · intro k hk
    exact mul_le_mul_of_nonneg_left (phi_mono2 hm k (Finset.mem_range.mp hk) le_rfl hF.le)
      (defaultLaw_nonneg hm _ k)
  · refine ⟨m.N - 1, Finset.mem_range.2 (by omega), ?_⟩
    apply mul_lt_mul_of_pos_left _ (dl_top_pos hm)
    unfold phi
    have hcast : ((m.N - 1 : ℕ) : ℝ) = (m.N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hcast, show (m.N : ℝ) - ((m.N : ℝ) - 1) = 1 by ring, div_one,
      max_eq_left (by linarith), max_eq_left (by linarith)]
    have := hm.cond3.1
    nlinarith

lemma Xc_flat (hm : Standing m) {c F F' : ℝ} (hc : 0 ≤ c) (hF : ((m.N : ℝ) - 1) * c ≤ F)
    (hF' : ((m.N : ℝ) - 1) * c ≤ F') : Xc m (m.N - 1) c F = Xc m (m.N - 1) c F' := by
  unfold Xc
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : (k : ℝ) + 1 ≤ m.N := by exact_mod_cast Finset.mem_range.mp hk
  have h1 : (0 : ℝ) < (m.N : ℝ) - k := by linarith
  have hr : (k : ℝ) * c / ((m.N : ℝ) - k) ≤ ((m.N : ℝ) - 1) * c := by
    rw [div_le_iff₀ h1]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hc (mul_nonneg hk0 (show (0 : ℝ) ≤ (m.N : ℝ) - k - 1 by linarith)),
      mul_nonneg hc (show (0 : ℝ) ≤ (m.N : ℝ) - k - 1 by linarith)]
  unfold phi
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]

lemma inv6 (hm : Standing m) (h6 : (m.N : ℝ) * m.Fhat 0 ≤ ((m.N : ℝ) - 1) * m.D)
    (I : ℝ) (hI : I ∈ Set.Icc 0 m.Ihat0) :
    m.Fhat I ≤ ((m.N : ℝ) - 1) * (m.D - I - m.Fhat I) := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 m.Ihat0 := ⟨le_rfl, (Ihat0_pos hm).le⟩
  rcases eq_or_lt_of_le hI.1 with h | h
  · rw [← h]
    linarith
  · by_contra hc
    push_neg at hc
    have hF := part4 hm h0 hI h
    have r0 := root_c hm 0 h0.2
    have rI := root_c hm I hI.2
    have hcI : 0 ≤ m.D - I - m.Fhat I := (sub_pos.2 (Fhat_lt hm I hI.2)).le
    have hflat := Xc_flat hm hcI (F := m.Fhat I) (F' := m.Fhat 0) hc.le (by linarith)
    have hP := P_lt_one hm
    have hc0 : m.D - 0 - m.Fhat 0 ≤ m.D - I - m.Fhat I := by
      by_contra hlt
      push_neg at hlt
      have hX := Xc_mono hm (m.N - 1) hlt.le (le_refl (m.Fhat 0))
      nlinarith [mul_pos (sub_pos.2 hP) (sub_pos.2 hlt)]
    have hN : (2 : ℝ) ≤ m.N := by exact_mod_cast hm.two_le_N
    nlinarith

lemma part6 (hm : Standing m) (h6 : (m.N : ℝ) * m.Fhat 0 ≤ ((m.N : ℝ) - 1) * m.D) :
    StrictMonoOn (fun I => m.Fhat I + I) (Set.Icc 0 m.Ihat0) := by
  intro I hI I' hI' hlt
  simp only
  have hF := part4 hm hI hI' hlt
  have h5 := part5 hm hI hI' hlt.le
  simp only at h5
  by_contra hc
  push_neg at hc
  have heq : m.D - I' - m.Fhat I' = m.D - I - m.Fhat I := by linarith
  have hinv := inv6 hm h6 I hI
  have hs := Xc_strict_F hm (c := m.D - I - m.Fhat I) hF hinv
  have r1 := root_c hm I hI.2
  have r2 := root_c hm I' hI'.2
  rw [heq] at r2
  linarith

lemma lip (hm : Standing m) {I I' : ℝ} (hI : I ∈ Set.Icc 0 m.Ihat0)
    (hI' : I' ∈ Set.Icc 0 m.Ihat0) (hle : I ≤ I') :
    m.Fhat I' ≤ m.Fhat I ∧ m.Fhat I ≤ m.Fhat I' + (I' - I) := by
  rcases eq_or_lt_of_le hle with h | h
  · subst h
    constructor <;> linarith
  · have h4 := part4 hm hI hI' h
    have h5 := part5 hm hI hI' hle
    simp only at h5
    constructor <;> linarith

lemma part7 (hm : Standing m) : ContinuousOn m.Fhat (Set.Icc 0 m.Ihat0) := by
  apply LipschitzOnWith.continuousOn (K := 1)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  rcases le_total x y with h | h
  · obtain ⟨h1, h2⟩ := lip hm hx hy h
    rw [abs_of_nonpos (by linarith)]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := lip hm hy hx h
    rw [abs_of_nonneg (by linarith)]
    constructor <;> linarith

lemma phi_convex (hm : Standing m) (k : ℕ) (c1 c2 F1 F2 a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    phi m (a * c1 + b * c2) (a * F1 + b * F2) k ≤ a * phi m c1 F1 k + b * phi m c2 F2 k := by
  unfold phi
  set r1 := (k : ℝ) * c1 / ((m.N : ℝ) - k)
  set r2 := (k : ℝ) * c2 / ((m.N : ℝ) - k)
  have hr : (k : ℝ) * (a * c1 + b * c2) / ((m.N : ℝ) - k) = a * r1 + b * r2 := by
    simp only [r1, r2]
    ring
  rw [hr]
  have hmax : max (a * r1 + b * r2 - (a * F1 + b * F2)) 0 ≤
      a * max (r1 - F1) 0 + b * max (r2 - F2) 0 := by
    apply max_le
    · have := mul_le_mul_of_nonneg_left (le_max_left (r1 - F1) 0) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (r2 - F2) 0) hb
      linarith
    · have := mul_nonneg ha (le_max_right (r1 - F1) 0)
      have := mul_nonneg hb (le_max_right (r2 - F2) 0)
      linarith
  have := mul_le_mul_of_nonneg_left hmax hm.cond3.1.le
  nlinarith

lemma Gg_convex (hm : Standing m) (I1 I2 F1 F2 a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    Gg m (m.N - 1) (a * I1 + b * I2) (a * F1 + b * F2) ≤
      a * Gg m (m.N - 1) I1 F1 + b * Gg m (m.N - 1) I2 F2 := by
  rw [Gg_eq, Gg_eq, Gg_eq]
  have hc : m.D - (a * I1 + b * I2) - (a * F1 + b * F2) =
      a * (m.D - I1 - F1) + b * (m.D - I2 - F2) := by
    linear_combination (-m.D) * hab
  rw [hc]
  have hX : Xc m (m.N - 1) (a * (m.D - I1 - F1) + b * (m.D - I2 - F2)) (a * F1 + b * F2) ≤
      a * Xc m (m.N - 1) (m.D - I1 - F1) F1 + b * Xc m (m.N - 1) (m.D - I2 - F2) F2 := by
    unfold Xc
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k _
    have := mul_le_mul_of_nonneg_left (phi_convex hm k (m.D - I1 - F1) (m.D - I2 - F2) F1 F2 a b
      ha hb) (defaultLaw_nonneg hm (m.N - 1) k)
    linarith
  have hK : (a + b) * ((m.Accp - m.D) * m.pledge) = (m.Accp - m.D) * m.pledge := by
    rw [hab, one_mul]
  nlinarith

lemma part8 (hm : Standing m) : ConvexOn ℝ (Set.Icc 0 m.Ihat0) m.Fhat := by
  refine ⟨convex_Icc 0 m.Ihat0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hxD := Fhat_lt hm x hx.2
  have hyD := Fhat_lt hm y hy.2
  have hx0 := (Fhat_mem hm x (hx.2.trans (Ihat0_le_D hm))).1
  have hy0 := (Fhat_mem hm y (hy.2.trans (Ihat0_le_D hm))).1
  apply Fhat_le
  · positivity
  · have h1 := mul_le_mul_of_nonneg_left hxD.le ha
    have h2 := mul_le_mul_of_nonneg_left hyD.le hb
    have : (a + b) * m.D = m.D := by rw [hab, one_mul]
    nlinarith
  · have := Gg_convex hm x y (m.Fhat x) (m.Fhat y) a b ha hb hab
    rw [Fhat_root hm x hx.2, Fhat_root hm y hy.2] at this
    linarith

end Shape

section Piecewise

noncomputable def uk (m : Params) (k : ℕ) (I : ℝ) : ℝ :=
  (k : ℝ) * (m.D - I - m.Fhat I) / ((m.N : ℝ) - k) - m.Fhat I

noncomputable def zk (m : Params) (k : ℕ) : ℝ := by
  classical
  exact if h : ∃ I, I ∈ Set.Icc 0 m.Ihat0 ∧ uk m k I = 0 then Classical.choose h else 0

noncomputable def Bset (m : Params) : Finset ℝ :=
  insert 0 (insert m.Ihat0 ((range m.N).image (zk m)))

variable {m : Params}

lemma phi_homog (k : ℕ) (c F t : ℝ) (ht : 0 ≤ t) : phi m (t * c) (t * F) k = t * phi m c F k := by
  unfold phi
  have e1 : (k : ℝ) * (t * c) / ((m.N : ℝ) - k) = t * ((k : ℝ) * c / ((m.N : ℝ) - k)) := by ring
  rw [e1, show t * ((k : ℝ) * c / ((m.N : ℝ) - k)) - t * F
      = t * ((k : ℝ) * c / ((m.N : ℝ) - k) - F) by ring]
  rw [show max (t * ((k : ℝ) * c / ((m.N : ℝ) - k) - F)) 0
      = t * max ((k : ℝ) * c / ((m.N : ℝ) - k) - F) 0 by rw [mul_max_of_nonneg _ _ ht, mul_zero]]
  ring

lemma Xc_homog (g : ℕ) (c F t : ℝ) (ht : 0 ≤ t) : Xc m g (t * c) (t * F) = t * Xc m g c F := by
  unfold Xc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [phi_homog k c F t ht]
  ring

lemma uk_zero_unique (hm : Standing m) (k : ℕ) (hk : k < m.N) {I I' : ℝ}
    (hI : I ∈ Set.Icc 0 m.Ihat0) (hI' : I' ∈ Set.Icc 0 m.Ihat0)
    (h1 : uk m k I = 0) (h2 : uk m k I' = 0) : I = I' := by
  have hc : 0 < m.D - I - m.Fhat I := sub_pos.2 (Fhat_lt hm I hI.2)
  have hc' : 0 < m.D - I' - m.Fhat I' := sub_pos.2 (Fhat_lt hm I' hI'.2)
  obtain ⟨t, ht, hct⟩ : ∃ t : ℝ, 0 ≤ t ∧ m.D - I' - m.Fhat I' = t * (m.D - I - m.Fhat I) :=
    ⟨(m.D - I' - m.Fhat I') / (m.D - I - m.Fhat I), (div_pos hc' hc).le, by field_simp⟩
  unfold uk at h1 h2
  have hF : m.Fhat I = (k : ℝ) * (m.D - I - m.Fhat I) / ((m.N : ℝ) - k) := by linarith
  have hF' : m.Fhat I' = t * m.Fhat I := by
    have : m.Fhat I' = (k : ℝ) * (m.D - I' - m.Fhat I') / ((m.N : ℝ) - k) := by linarith
    rw [this, hct, show t * m.Fhat I = t * ((k : ℝ) * (m.D - I - m.Fhat I) / ((m.N : ℝ) - k))
      from by rw [← hF]]
    ring
  have r1 := root_c hm I hI.2
  have r2 := root_c hm I' hI'.2
  rw [hct, hF', Xc_homog _ _ _ _ ht] at r2
  have e : t * ((m.Accp - m.D) * m.pledge) = (m.Accp - m.D) * m.pledge := by
    linear_combination r2 - t * r1
  have hK := K_pos hm
  have ht1 : t = 1 := by
    have := mul_right_cancel₀ hK.ne' (show t * ((m.Accp - m.D) * m.pledge)
      = 1 * ((m.Accp - m.D) * m.pledge) by rw [e, one_mul])
    exact this
  have hFF : m.Fhat I' = m.Fhat I := by rw [hF', ht1, one_mul]
  rcases lt_trichotomy I I' with h | h | h
  · have := part4 hm hI hI' h
    linarith
  · exact h
  · have := part4 hm hI' hI h
    linarith

lemma zk_spec (hm : Standing m) (k : ℕ) (hk : k < m.N) (I : ℝ) (hI : I ∈ Set.Icc 0 m.Ihat0)
    (h0 : uk m k I = 0) : I = zk m k := by
  have hex : ∃ I, I ∈ Set.Icc 0 m.Ihat0 ∧ uk m k I = 0 := ⟨I, hI, h0⟩
  have hz : zk m k = Classical.choose hex := by
    unfold zk
    rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  rw [hz]
  exact uk_zero_unique hm k hk hI hs.1 h0 hs.2

lemma zk_mem (hm : Standing m) (k : ℕ) : zk m k ∈ Set.Icc 0 m.Ihat0 := by
  by_cases hex : ∃ I, I ∈ Set.Icc 0 m.Ihat0 ∧ uk m k I = 0
  · have hz : zk m k = Classical.choose hex := by
      unfold zk
      rw [dif_pos hex]
    rw [hz]
    exact (Classical.choose_spec hex).1
  · have hz : zk m k = 0 := by
      unfold zk
      rw [dif_neg hex]
    rw [hz]
    exact ⟨le_rfl, (Ihat0_pos hm).le⟩

lemma Bset_sub (hm : Standing m) : ∀ x ∈ Bset m, x ∈ Set.Icc 0 m.Ihat0 := by
  intro x hx
  unfold Bset at hx
  rcases Finset.mem_insert.1 hx with h | h
  · rw [h]
    exact ⟨le_rfl, (Ihat0_pos hm).le⟩
  rcases Finset.mem_insert.1 h with h | h
  · rw [h]
    exact ⟨(Ihat0_pos hm).le, le_rfl⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
  exact zk_mem hm k

lemma Bset_zero : (0 : ℝ) ∈ Bset m := Finset.mem_insert_self _ _

lemma Bset_top : m.Ihat0 ∈ Bset m :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

lemma Bset_zeros (hm : Standing m) (k : ℕ) (hk : k < m.N) (I : ℝ)
    (hI : I ∈ Set.Icc 0 m.Ihat0) (h0 : uk m k I = 0) : I ∈ Bset m := by
  rw [zk_spec hm k hk I hI h0]
  unfold Bset
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, rfl⟩))

lemma no_cross (f : ℝ → ℝ) {L R mid I : ℝ} (hLm : L < mid) (hmR : mid < R)
    (hI : I ∈ Set.Icc L R) (hcont : ContinuousOn f (Set.Icc L R))
    (hz : ∀ x ∈ Set.Icc L R, f x = 0 → x = L ∨ x = R) (hfI : f I ≠ 0)
    (h0 : (0 : ℝ) ∈ Set.uIcc (f I) (f mid)) : False := by
  have hsub : Set.uIcc I mid ⊆ Set.Icc L R := Set.uIcc_subset_Icc hI ⟨hLm.le, hmR.le⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_uIcc (hcont.mono hsub) h0
  have hxLR := hsub hx
  have hI1 := hI.1
  have hI2 := hI.2
  rcases hz x hxLR hfx with h | h <;> rcases Set.mem_uIcc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hxI : x = I := le_antisymm (by linarith) (by linarith)
    rw [hxI] at hfx
    exact hfI hfx
  · linarith
  · linarith
  · have hxI : x = I := le_antisymm (by linarith) (by linarith)
    rw [hxI] at hfx
    exact hfI hfx

lemma part3 (hm : Standing m) :
    ∃ (n : ℕ) (c : Fin (n + 2) → ℝ), StrictMono c ∧ c 0 = 0 ∧ c (Fin.last _) = m.Ihat0 ∧
      ∀ j : Fin (n + 1), ∃ u v : ℝ,
        ∀ I ∈ Set.Icc (c j.castSucc) (c j.succ), m.Fhat I = u * I + v := by
  have hpos := Ihat0_pos hm
  have hcard2 : 2 ≤ (Bset m).card := by
    have hsub : ({0, m.Ihat0} : Finset ℝ) ⊆ Bset m := by
      intro x hx
      rcases Finset.mem_insert.1 hx with h | h
      · rw [h]
        exact Bset_zero
      · rw [Finset.mem_singleton.1 h]
        exact Bset_top
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hpos.ne] at this
  obtain ⟨n, hn⟩ : ∃ n, (Bset m).card = n + 2 := ⟨(Bset m).card - 2, by omega⟩
  set c := (Bset m).orderEmbOfFin hn with hcdef
  have hcmem : ∀ i, c i ∈ Bset m := fun i => Finset.orderEmbOfFin_mem _ hn i
  have hcsurj : ∀ x ∈ Bset m, ∃ i, c i = x := by
    intro x hx
    have : x ∈ Set.range c := by
      rw [hcdef, Finset.range_orderEmbOfFin]
      exact hx
    exact this
  refine ⟨n, c, c.strictMono, ?_, ?_, ?_⟩
  · have h0 : (0 : Fin (n + 2)) = ⟨0, by omega⟩ := rfl
    rw [h0, hcdef, Finset.orderEmbOfFin_zero hn (by omega)]
    exact le_antisymm (Finset.min'_le _ _ Bset_zero)
      (Finset.le_min' _ _ _ (fun y hy => (Bset_sub hm y hy).1))
  · have hl : (Fin.last (n + 1)) = ⟨n + 2 - 1, by omega⟩ := Fin.ext (by simp)
    rw [hl, hcdef, Finset.orderEmbOfFin_last hn (by omega)]
    exact le_antisymm (Finset.max'_le _ _ _ (fun y hy => (Bset_sub hm y hy).2))
      (Finset.le_max' _ _ Bset_top)
  · intro j
    set L := c j.castSucc with hL
    set R := c j.succ with hR
    have hLR : L < R := c.strictMono Fin.castSucc_lt_succ
    have hLm := Bset_sub hm L (hcmem _)
    have hRm := Bset_sub hm R (hcmem _)
    have hsubI : Set.Icc L R ⊆ Set.Icc 0 m.Ihat0 := Set.Icc_subset_Icc hLm.1 hRm.2
    have hnoB : ∀ x ∈ Bset m, ¬ (L < x ∧ x < R) := by
      intro x hx ⟨h1, h2⟩
      obtain ⟨i, rfl⟩ := hcsurj x hx
      have a1 := c.lt_iff_lt.1 h1
      have a2 := c.lt_iff_lt.1 h2
      rw [Fin.lt_def] at a1 a2
      simp only [Fin.val_castSucc, Fin.val_succ] at a1 a2
      omega
    have hz : ∀ k < m.N, ∀ x ∈ Set.Icc L R, uk m k x = 0 → x = L ∨ x = R := by
      intro k hk x hx h0
      have hxB := Bset_zeros hm k hk x (hsubI hx) h0
      have := hnoB x hxB
      rcases eq_or_lt_of_le hx.1 with h | h
      · exact Or.inl h.symm
      rcases eq_or_lt_of_le hx.2 with h' | h'
      · exact Or.inr h'
      exact absurd ⟨h, h'⟩ this
    have hFc : ContinuousOn m.Fhat (Set.Icc L R) := (part7 hm).mono hsubI
    have hukc : ∀ k, ContinuousOn (uk m k) (Set.Icc L R) := by
      intro k
      unfold uk
      exact ((continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).sub hFc)).div_const
        _).sub hFc
    set mid := (L + R) / 2 with hmid
    have hLmid : L < mid := by rw [hmid]; linarith
    have hmidR : mid < R := by rw [hmid]; linarith
    have hpos_sign : ∀ k < m.N, 0 ≤ uk m k mid → ∀ I ∈ Set.Icc L R, 0 ≤ uk m k I := by
      intro k hk hs I hI
      by_contra hneg
      push_neg at hneg
      exact no_cross (uk m k) hLmid hmidR hI (hukc k) (hz k hk) hneg.ne
        (Set.mem_uIcc.2 (Or.inl ⟨hneg.le, hs⟩))
    have hneg_sign : ∀ k < m.N, uk m k mid < 0 → ∀ I ∈ Set.Icc L R, uk m k I ≤ 0 := by
      intro k hk hs I hI
      by_contra hp
      push_neg at hp
      exact no_cross (uk m k) hLmid hmidR hI (hukc k) (hz k hk) hp.ne'
        (Set.mem_uIcc.2 (Or.inr ⟨hs.le, hp.le⟩))
    classical
    set ind : ℕ → ℝ := fun k => if 0 ≤ uk m k mid then 1 else 0 with hind
    have hind0 : ∀ k, 0 ≤ ind k := by
      intro k
      simp only [hind]
      split_ifs <;> norm_num
    set β := ∑ k ∈ range m.N, m.defaultLaw (m.N - 1) k * ((k : ℝ) / ((m.N : ℝ) - k)) *
      (1 + m.α * ind k) with hβ
    set σ := ∑ k ∈ range m.N, m.α * m.defaultLaw (m.N - 1) k * ind k with hσ
    have hα := hm.cond3.1
    have hβ0 : 0 ≤ β := by
      apply Finset.sum_nonneg
      intro k hk
      have hk' : (k : ℝ) < m.N := by exact_mod_cast Finset.mem_range.1 hk
      have h1 : 0 ≤ (k : ℝ) / ((m.N : ℝ) - k) := div_nonneg (Nat.cast_nonneg k) (by linarith)
      have h2 : 0 ≤ 1 + m.α * ind k := by
        have := mul_nonneg hα.le (hind0 k)
        linarith
      exact mul_nonneg (mul_nonneg (defaultLaw_nonneg hm _ k) h1) h2
    have hσ0 : 0 ≤ σ := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (mul_nonneg hα.le (defaultLaw_nonneg hm _ k)) (hind0 k)
    have hrep : ∀ I ∈ Set.Icc L R, Xc m (m.N - 1) (m.D - I - m.Fhat I) (m.Fhat I) =
        β * (m.D - I - m.Fhat I) - σ * m.Fhat I := by
      intro I hI
      unfold Xc
      rw [hβ, hσ, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.1 hk
      unfold phi
      by_cases hs : 0 ≤ uk m k mid
      · have h1 : 0 ≤ uk m k I := hpos_sign k hk' hs I hI
        have h1' : 0 ≤ (k : ℝ) * (m.D - I - m.Fhat I) / ((m.N : ℝ) - k) - m.Fhat I := h1
        have hi : ind k = 1 := by simp only [hind, if_pos hs]
        rw [max_eq_left h1', hi]
        ring
      · push_neg at hs
        have h1 : uk m k I ≤ 0 := hneg_sign k hk' hs I hI
        have h1' : (k : ℝ) * (m.D - I - m.Fhat I) / ((m.N : ℝ) - k) - m.Fhat I ≤ 0 := h1
        have hi : ind k = 0 := by simp only [hind, if_neg (not_le.2 hs)]
        rw [max_eq_right h1', hi]
        ring
    have hP := P_lt_one hm
    have hden : 0 < 1 - m.pledge + β + σ := by linarith
    refine ⟨-(1 - m.pledge + β) / (1 - m.pledge + β + σ),
      (m.D * (1 - m.pledge + β) - (m.Accp - m.D) * m.pledge) / (1 - m.pledge + β + σ), ?_⟩
    intro I hI
    have r := root_c hm I (hsubI hI).2
    rw [hrep I hI] at r
    rw [div_mul_eq_mul_div, ← add_div, eq_div_iff hden.ne']
    linear_combination (-1 : ℝ) * r

end Piecewise

end CCPProp2

open CCPCollateral.Incentive in
theorem solution (m : Params) (hm : Standing m) :
    (∀ I F : ℝ, 0 ≤ I → 0 ≤ F → I + F ≤ m.D → ∀ a : Fin m.N → Action,
      m.IsParetoDominantNash I F a ↔
        a = fun _ => if F < m.Fhat I then Action.r else Action.s) ∧
    (∀ I ∈ Set.Icc 0 m.Ihat0, 0 ≤ m.Fhat I ∧ m.Fhat I < m.D - I ∧ m.Eq18 I (m.Fhat I) ∧
      ∀ F, 0 ≤ F → F < m.D - I → m.Eq18 I F → F = m.Fhat I) ∧
    (∃ (n : ℕ) (c : Fin (n + 2) → ℝ), StrictMono c ∧ c 0 = 0 ∧ c (Fin.last _) = m.Ihat0 ∧
      ∀ j : Fin (n + 1), ∃ u v : ℝ,
        ∀ I ∈ Set.Icc (c j.castSucc) (c j.succ), m.Fhat I = u * I + v) ∧
    StrictAntiOn m.Fhat (Set.Icc 0 m.Ihat0) ∧
    MonotoneOn (fun I => m.Fhat I + I) (Set.Icc 0 m.Ihat0) ∧
    ((m.N : ℝ) * m.Fhat 0 ≤ ((m.N : ℝ) - 1) * m.D →
      StrictMonoOn (fun I => m.Fhat I + I) (Set.Icc 0 m.Ihat0)) ∧
    ContinuousOn m.Fhat (Set.Icc 0 m.Ihat0) ∧
    ConvexOn ℝ (Set.Icc 0 m.Ihat0) m.Fhat := by
  exact ⟨fun I F hI hF hIF a => CCPProp2.part1 hm I F hI hF hIF a, CCPProp2.part2 hm,
    CCPProp2.part3 hm, CCPProp2.part4 hm, CCPProp2.part5 hm, CCPProp2.part6 hm,
    CCPProp2.part7 hm, CCPProp2.part8 hm⟩
