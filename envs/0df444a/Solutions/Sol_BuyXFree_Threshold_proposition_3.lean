-- Prove2me | solution 1 for BuyXFree.Threshold.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:12:09.409816+00:00
-- url     : https://prove2.me/submissions/446f47ee-9613-4452-bf13-e70e0c5fbfb2

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model
import Theorems.Thm_BuyXFree_Threshold_corollary_1
import Theorems.Thm_BuyXFree_Threshold_lemma_4
import Theorems.Thm_BuyXFree_Threshold_lemma_5
import Theorems.Thm_BuyXFree_Threshold_converse_a
import Theorems.Thm_BuyXFree_Threshold_converse_b
import Theorems.Thm_BuyXFree_Threshold_converse_c
import Theorems.Thm_BuyXFree_Threshold_converse_d
import Theorems.Thm_BuyXFree_Threshold_case_a_d_bounds
import Theorems.Thm_BuyXFree_Threshold_lemma_2
import Theorems.Thm_BuyXFree_Threshold_lemma_3
import Theorems.Thm_BuyXFree_Threshold_q_le_A

namespace BuyXFree.Threshold.P3Aux
open BuyXFree.Threshold Matrix

lemma moveProb_nonneg (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (x : ℕ) :
    0 ≤ moveProb P p X J x ∧ moveProb P p X J x ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP
  have key : ∀ a b : ℝ, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
      0 ≤ P.lam * (P.q * a + (1 - P.q) * b) ∧ P.lam * (P.q * a + (1 - P.q) * b) ≤ 1 := by
    intro a b ha hb
    have h0 : 0 ≤ P.q * a + (1 - P.q) * b := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> nlinarith
    have h1' : P.q * a + (1 - P.q) * b ≤ 1 := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> nlinarith
    exact ⟨mul_nonneg h1 h0, by nlinarith⟩
  unfold moveProb
  split_ifs <;> exact key _ _ (by simp) (by simp)

lemma nextState_val (X : ℕ) (i : Fin (X + 1)) :
    (nextState X i).val = if i.val < X then i.val + 1 else 0 := by
  unfold nextState
  split_ifs <;> simp

lemma trans_mulVec (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (h : Fin (X + 1) → ℝ)
    (i : Fin (X + 1)) :
    (trans P p X J *ᵥ h) i =
      moveProb P p X J i * h (nextState X i) + (1 - moveProb P p X J i) * h i := by
  simp [trans, mulVec, dotProduct, add_mul, Finset.sum_add_distrib, ite_mul]

lemma distAt_succ (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (n : ℕ) :
    distAt P p X J (n + 1) = distAt P p X J n ᵥ* trans P p X J := by
  simp only [distAt, pow_succ, vecMul_vecMul]

lemma distAt_prop (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (n : ℕ) :
    (∀ i, 0 ≤ distAt P p X J n i) ∧ ∑ i, distAt P p X J n i = 1 := by
  induction n with
  | zero =>
    refine ⟨fun i => ?_, ?_⟩
    · simp only [distAt, pow_zero, vecMul_one]
      by_cases h : i = 0
      · subst h; simp
      · simp [h]
    · simp [distAt]
  | succ n ih =>
    obtain ⟨hnn, hs⟩ := ih
    rw [distAt_succ]
    refine ⟨fun j => ?_, ?_⟩
    · simp only [vecMul, dotProduct]
      refine Finset.sum_nonneg fun i _ => mul_nonneg (hnn i) ?_
      have hm := moveProb_nonneg P hP p X J i
      simp only [trans]
      split_ifs <;> linarith
    · have : (distAt P p X J n ᵥ* trans P p X J) ⬝ᵥ (fun _ => (1 : ℝ)) =
          distAt P p X J n ⬝ᵥ (fun _ => (1 : ℝ)) := by
        rw [← dotProduct_mulVec]
        congr 1
        funext i
        rw [trans_mulVec]
        ring
      simpa [dotProduct, hs] using this

lemma abs_dot_le {X : ℕ} (μ h : Fin (X + 1) → ℝ) (hnn : ∀ i, 0 ≤ μ i) (hs : ∑ i, μ i = 1) :
    |μ ⬝ᵥ h| ≤ ∑ i, |h i| := by
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (hnn i)]
  have : μ i ≤ 1 := hs ▸ Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  exact mul_le_of_le_one_left (abs_nonneg _) this

/-- Poisson-inequality bound on the Cesàro averages. -/
theorem avg_le (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (R : ℝ)
    (h : Fin (X + 1) → ℝ)
    (hh : ∀ i : Fin (X + 1),
      revenue P p X J i - R ≤ moveProb P p X J i * (h i - h (nextState X i))) :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, avgRevenue P p X J N ≤ R + ε := by
  set M := ∑ i, |h i| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  have step : ∀ n, distAt P p X J n ⬝ᵥ revenue P p X J ≤
      R + (distAt P p X J n ⬝ᵥ h - distAt P p X J (n + 1) ⬝ᵥ h) := by
    intro n
    obtain ⟨hnn, hs⟩ := distAt_prop P hP p X J n
    rw [distAt_succ, ← dotProduct_mulVec]
    have : distAt P p X J n ⬝ᵥ revenue P p X J ≤
        distAt P p X J n ⬝ᵥ (fun i => R + (h i - (trans P p X J *ᵥ h) i)) := by
      unfold dotProduct
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hnn i)
      show _ ≤ R + (h i - (trans P p X J *ᵥ h) i)
      rw [trans_mulVec]
      have := hh i
      nlinarith
    refine this.trans (le_of_eq ?_)
    simp only [dotProduct, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hs]
    ring
  have hsum : ∀ N, ∑ n ∈ Finset.range N, distAt P p X J n ⬝ᵥ revenue P p X J ≤
      N * R + 2 * M := by
    intro N
    have h1 := Finset.sum_le_sum (s := Finset.range N) fun n _ => step n
    rw [Finset.sum_add_distrib, Finset.sum_range_sub'] at h1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    obtain ⟨a0, b0⟩ := distAt_prop P hP p X J 0
    obtain ⟨aN, bN⟩ := distAt_prop P hP p X J N
    have e0 := abs_le.1 (abs_dot_le _ h a0 b0)
    have eN := abs_le.1 (abs_dot_le _ h aN bN)
    linarith [e0.1, e0.2, eN.1, eN.2]
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * M / ε)
  refine Filter.eventually_atTop.2 ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0' : (N0 : ℝ) + 1 ≤ N := by exact_mod_cast hN
  unfold avgRevenue
  rw [div_le_iff₀ hNpos]
  have h2 : 2 * M ≤ ε * N := by
    rw [div_lt_iff₀ hε] at hN0
    nlinarith
  linarith [hsum N]


lemma revenue_eq (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (i : Fin (X + 1)) :
    revenue P p X J i = if i.val < X then p * moveProb P p X J i else 0 := by
  unfold revenue buyProb
  split_ifs <;> simp

/-- Stuck case: some state is absorbing. -/
theorem stuck_bound (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (j : ℕ) (hj : j ≤ X) (hj0 : moveProb P p X J j = 0) :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, avgRevenue P p X J N ≤ R + ε := by
  refine avg_le P hP p X J R
    (fun i => -(i.val : ℝ) * p + (if j < i.val then (X : ℝ) * p else 0)) (fun i => ?_)
  rw [revenue_eq, nextState_val]
  have hi := i.isLt
  have hm := (moveProb_nonneg P hP p X J i).1
  by_cases hiX : i.val < X
  · rw [if_pos hiX, if_pos hiX]
    by_cases hij : i.val = j
    · rw [hij, hj0]; simp; linarith
    · have : (-(i.val : ℝ) * p + (if j < i.val then (X : ℝ) * p else 0)) -
          (-((i.val + 1 : ℕ) : ℝ) * p + (if j < i.val + 1 then (X : ℝ) * p else 0)) = p := by
        by_cases h1 : j < i.val
        · rw [if_pos h1, if_pos (by omega)]; push_cast; ring
        · rw [if_neg h1, if_neg (by omega)]; push_cast; ring
      rw [this]; nlinarith
  · rw [if_neg hiX, if_neg hiX]
    have hiX' : i.val = X := by omega
    by_cases hjX : j = X
    · rw [hiX']; rw [hjX] at hj0; rw [hj0]; simp; linarith
    · rw [hiX', if_pos (show j < X by omega)]
      simp; linarith

/-- Positive case: all states transient, renewal-reward bound. -/
theorem pos_bound (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (R : ℝ)
    (w : ℕ → ℝ) (hw : ∀ i ≤ X, moveProb P p X J i * w i = 1)
    (hsum : p * X ≤ R * ∑ l ∈ Finset.range (X + 1), w l) :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, avgRevenue P p X J N ≤ R + ε := by
  refine avg_le P hP p X J R
    (fun i => -(i.val : ℝ) * p + R * ∑ l ∈ Finset.range i.val, w l) (fun i => ?_)
  rw [revenue_eq, nextState_val]
  have hi := i.isLt
  have hm := (moveProb_nonneg P hP p X J i).1
  by_cases hiX : i.val < X
  · rw [if_pos hiX, if_pos hiX]
    simp only [Finset.sum_range_succ]
    have := hw i.val (by omega)
    push_cast
    have e : moveProb P p X J i * (-(i.val : ℝ) * p + R * ∑ l ∈ Finset.range i.val, w l -
        (-((i.val : ℝ) + 1) * p + R * (∑ l ∈ Finset.range i.val, w l + w i.val))) =
        p * moveProb P p X J i - R := by linear_combination (-R) * this
    rw [e]
  · rw [if_neg hiX, if_neg hiX]
    have hiX' : i.val = X := by omega
    rw [hiX'] at hm ⊢
    rw [Finset.sum_range_succ] at hsum
    have := hw X le_rfl
    simp only [Finset.range_zero, Finset.sum_empty, CharP.cast_eq_zero, neg_zero, zero_mul,
      mul_zero, add_zero]
    have h3 : 0 ≤ moveProb P p X J X *
        (-(X : ℝ) * p + R * ∑ l ∈ Finset.range X, w l + R * w X) :=
      mul_nonneg hm (by linarith)
    have e : moveProb P p X J X *
        (-(X : ℝ) * p + R * ∑ l ∈ Finset.range X, w l + R * w X) =
        moveProb P p X J X * (-(X : ℝ) * p + R * ∑ l ∈ Finset.range X, w l - 0) + R := by
      linear_combination R * this
    linarith

lemma sum_ite_range (n τ : ℕ) (hτ : τ ≤ n) (a b : ℝ) :
    ∑ i ∈ Finset.range n, (if i < τ then a else b) = τ * a + ((n : ℝ) - τ) * b := by
  rw [← Finset.sum_range_add_sum_Ico _ hτ]
  rw [Finset.sum_congr rfl (g := fun _ => a) (fun i hi => if_pos (Finset.mem_range.1 hi)),
    Finset.sum_congr rfl (g := fun _ => b)
      (fun i hi => if_neg (by have := (Finset.mem_Ico.1 hi).1; omega))]
  simp [Nat.cast_sub hτ]

/-- Structured case: moving probabilities `λq` below `τ'` and `λ` from `τ'` on. -/
theorem case_bound (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (R : ℝ)
    (hlam : 0 < P.lam) (hq : 0 < P.q) (τ : ℕ) (hτ : τ ≤ X + 1)
    (hmf : ∀ i ≤ X, moveProb P p X J i = if i < τ then P.lam * P.q else P.lam)
    (hineq : p * X ≤ R * (τ * (1 / (P.lam * P.q)) + ((X + 1 : ℕ) - τ : ℝ) * (1 / P.lam))) :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, avgRevenue P p X J N ≤ R + ε := by
  refine pos_bound P hP p X J R (fun i => if i < τ then 1 / (P.lam * P.q) else 1 / P.lam)
    (fun i hi => ?_) ?_
  · rw [hmf i hi]
    have : P.lam * P.q ≠ 0 := by positivity
    split_ifs <;> field_simp
  · rw [sum_ite_range _ _ hτ]; exact hineq

lemma alg (L D R p X : ℝ) (hL : 0 < L) (hD : 0 < D) (h : L * X / D * p ≤ R) :
    p * X ≤ R * (D / L) := by
  rw [mul_div_assoc', le_div_iff₀ hL]
  rw [div_mul_eq_mul_div, div_le_iff₀ hD] at h
  linarith

end BuyXFree.Threshold.P3Aux

open BuyXFree.Threshold BuyXFree.Threshold.P3Aux in
theorem solution (P : Params) (hP : P.Standing) (hk : P.k = 0)
    (hcond : (P.q ≤ 1 / 2 ∧ 2 / (2 + P.lam) ≤ P.δ) ∨
      (1 / 2 < P.q ∧ P.v - P.vbar ≤ min (A P * P.v) (P.v / (1 + A1 P))))
    (p : ℝ) (X : ℕ) (hX : 1 ≤ X) (J : ℕ → ℝ) (hJ : IsValueFn P p X J) :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, avgRevenue P p X J N ≤ noProgramProfit P + ε := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvbv, hk0⟩ := id hP
  have hR0 : 0 ≤ noProgramProfit P :=
    (mul_nonneg hl0 (sub_nonneg.2 hvbv)).trans (le_max_right _ _)
  by_cases hst : ∃ j ≤ X, moveProb P p X J j = 0
  · obtain ⟨j, hj, hj0⟩ := hst
    exact stuck_bound P hP p X J _ hR0 j hj hj0
  push Not at hst
  have hpos : ∀ j ≤ X, 0 < moveProb P p X J j := fun j hj =>
    lt_of_le_of_ne (moveProb_nonneg P hP p X J j).1 (Ne.symm (hst j hj))
  have hlam : 0 < P.lam := by
    rcases hl0.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hpos 0 (by omega)
      unfold moveProb at this
      rw [← h] at this
      simp at this
  have hHL : ∀ x, BuysHigh P p J x → BuysLow P p J x := fun x h => by
    unfold BuysHigh at h; unfold BuysLow; linarith
  rcases hq0.lt_or_eq with hq | hq
  · -- q > 0
    have hBL : ∀ x < X, BuysLow P p J x := by
      intro x hx
      by_contra hn
      have hn' : ¬ BuysHigh P p J x := fun h => hn (hHL x h)
      have := hpos x hx.le
      unfold moveProb at this
      simp [hx, hn, hn'] at this
    have hRL : RedeemsLow P X J := by
      have := lemma_4 P hP p X hX J hJ; unfold RedeemsLow; linarith
    have hmL : ∀ x < X, ¬ BuysHigh P p J x → moveProb P p X J x = P.lam * P.q := by
      intro x hx hn; unfold moveProb; simp [hx, hBL x hx, hn]
    have hmH : ∀ x < X, BuysHigh P p J x → moveProb P p X J x = P.lam := by
      intro x hx h; unfold moveProb; simp [hx, hBL x hx, h]
    have hmXH : RedeemsHigh P X J → moveProb P p X J X = P.lam := by
      intro h; unfold moveProb; simp [hRL, h]
    have hmXL : ¬ RedeemsHigh P X J → moveProb P p X J X = P.lam * P.q := by
      intro h; unfold moveProb; simp [hRL, h]
    have hup : ∀ a b, a ≤ b → b < X → BuysHigh P p J a → BuysHigh P p J b := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => intro _ h; exact h
      | succ b hab ih =>
        intro hb h
        exact (corollary_1 P hP p X hX J hJ b (by omega)).2 (ih (by omega) h)
    have hR5 : BuysHigh P p J (X - 1) → RedeemsHigh P X J := by
      intro h
      unfold BuysHigh at h
      rw [Nat.sub_add_cancel hX] at h
      have := lemma_5 P hP p X hX J hJ (by linarith)
      unfold RedeemsHigh; linarith
    by_cases hex : ∃ x, x < X ∧ BuysHigh P p J x
    · classical
      have hτspec := Nat.find_spec hex
      set τ := Nat.find hex with hτdef
      have hiff : ∀ x < X, BuysHigh P p J x ↔ τ ≤ x := fun x hx =>
        ⟨fun h => Nat.find_min' hex ⟨hx, h⟩, fun h => hup τ x h hx hτspec.2⟩
      have hRH : RedeemsHigh P X J := hR5 ((hiff (X - 1) (by omega)).2 (by omega))
      have hmf : ∀ i ≤ X, moveProb P p X J i = if i < τ then P.lam * P.q else P.lam := by
        intro i hi
        rcases hi.lt_or_eq with hi | rfl
        · by_cases h : i < τ
          · rw [if_pos h, hmL i hi (fun hh => by have := (hiff i hi).1 hh; omega)]
          · rw [if_neg h, hmH i hi ((hiff i hi).2 (by omega))]
        · rw [if_neg (by omega), hmXH hRH]
      refine case_bound P hP p X J _ hlam hq τ (by omega) hmf ?_
      by_cases hτ0 : τ = 0
      · -- case (a)
        have hb := converse_a P hP hlam hq p X hX J hJ (hτ0 ▸ hτspec.2)
        have h1 := (case_a_d_bounds P hP hk X hX).1 p hb
        have := alg P.lam ((X : ℝ) + 1) (noProgramProfit P) p X hlam (by positivity)
          (h1.trans (le_max_right _ _))
        rw [hτ0]
        convert this using 2
        push_cast
        ring
      · -- case (b)
        have hcb := converse_b P hP hlam hq p X J hJ τ (by omega) (by omega)
          (hBL 0 (by omega)) hτspec.2
          (fun h => Nat.find_min hex (show τ - 1 < τ by omega) ⟨by omega, h⟩)
        have hc2 : P.q ≤ 1 / 2 ∨ (1 / 2 < P.q ∧ P.v - P.vbar ≤ P.v / (1 + A1 P)) := by
          rcases hcond with h | h
          · exact Or.inl h.1
          · exact Or.inr ⟨h.1, h.2.trans (min_le_right _ _)⟩
        have h1 := lemma_2 P hP hk hc2 X τ (by omega) (by omega) p hcb.2.2
          (le_min hcb.1 hcb.2.1)
        have hD : (0 : ℝ) < (τ : ℝ) + P.q * ((X : ℝ) - τ + 1) := by
          have : (τ : ℝ) + 1 ≤ X := by exact_mod_cast (show τ + 1 ≤ X by omega)
          have : (1 : ℝ) ≤ τ := by exact_mod_cast (show 1 ≤ τ by omega)
          nlinarith
        have := alg (P.lam * P.q) ((τ : ℝ) + P.q * ((X : ℝ) - τ + 1)) _ p X (by positivity) hD
          h1
        convert this using 2
        push_cast [Nat.cast_add]
        field_simp
        ring
    · push Not at hex
      have hc3 : P.q ≤ A P ∨ (A P < P.q ∧ P.v - P.vbar ≤ A P * P.v) := by
        rcases hcond with h | h
        · exact Or.inl (q_le_A P hP h.1 h.2)
        · by_cases hqa : P.q ≤ A P
          · exact Or.inl hqa
          · exact Or.inr ⟨lt_of_not_ge hqa, h.2.trans (min_le_left _ _)⟩
      by_cases hRH : RedeemsHigh P X J
      · -- case (c)
        have hmf : ∀ i ≤ X, moveProb P p X J i = if i < X then P.lam * P.q else P.lam := by
          intro i hi
          rcases hi.lt_or_eq with hi | rfl
          · rw [if_pos hi, hmL i hi (hex i hi)]
          · rw [if_neg (lt_irrefl _), hmXH hRH]
        refine case_bound P hP p X J _ hlam hq X (by omega) hmf ?_
        have hcc := converse_c P hP hlam hq p X hX J hJ (hBL 0 (by omega))
          (hex (X - 1) (by omega)) hRH
        have h1 := lemma_3 P hP hk hc3 X hX p hcc.2.1 (le_min hcc.1 hcc.2.2)
        have := alg (P.lam * P.q) ((X : ℝ) + P.q) _ p X (by positivity) (by positivity) h1
        convert this using 2
        push_cast
        field_simp
        ring
      · -- case (d)
        have hmf : ∀ i ≤ X, moveProb P p X J i =
            if i < X + 1 then P.lam * P.q else P.lam := by
          intro i hi
          rw [if_pos (by omega)]
          rcases hi.lt_or_eq with hi | rfl
          · rw [hmL i hi (hex i hi)]
          · rw [hmXL hRH]
        refine case_bound P hP p X J _ hlam hq (X + 1) le_rfl hmf ?_
        have hcd := converse_d P hP hlam hq p X hX J hJ (hBL 0 (by omega)) hRH
        have h1 := (case_a_d_bounds P hP hk X hX).2 p hcd.1
        have := alg (P.lam * P.q) ((X : ℝ) + 1) (noProgramProfit P) p X (by positivity)
          (by positivity) (h1.trans (le_max_left _ _))
        convert this using 2
        push_cast
        field_simp
        ring
  · -- q = 0
    have hBH : ∀ x < X, BuysHigh P p J x := by
      intro x hx
      by_contra hn
      have := hpos x hx.le
      unfold moveProb at this
      simp [hx, hn, ← hq] at this
    have hRH : RedeemsHigh P X J := by
      by_contra hn
      have := hpos X le_rfl
      unfold moveProb at this
      simp [hn, ← hq] at this
    have hE : ∀ x < X, J x = P.lam * (P.v - p + P.δ * J (x + 1)) + (1 - P.lam) * P.δ * J x := by
      intro x hx
      have := hJ.1 x hx
      rw [← hq, max_eq_left (hBH x hx)] at this
      linarith
    have hI : ∀ x < X, P.lam * P.vbar ≤ (1 - P.δ) * J x := by
      intro x hx
      have := hE x hx
      have h := hBH x hx
      unfold BuysHigh at h
      have := mul_le_mul_of_nonneg_left h hl0
      nlinarith
    have hEX : J X = P.lam * (P.v + P.δ * J 0) + (1 - P.lam) * P.δ * J X := by
      have := hJ.2
      have h2 : P.vbar + P.δ * J X ≤ P.v + 0 + P.δ * J 0 := by
        unfold RedeemsHigh at hRH; rw [hk] at hRH; exact hRH
      rw [← hq, hk, max_eq_left h2] at this
      linarith
    have hIX : P.lam * P.vbar ≤ (1 - P.δ) * J X := by
      have h := hRH
      unfold RedeemsHigh at h
      rw [hk] at h
      have := mul_le_mul_of_nonneg_left h hl0
      nlinarith
    have hS : ∑ x ∈ Finset.range X, J x = X * (P.lam * (P.v - p)) +
        P.lam * P.δ * ∑ x ∈ Finset.range X, J (x + 1) +
        (1 - P.lam) * P.δ * ∑ x ∈ Finset.range X, J x := by
      calc ∑ x ∈ Finset.range X, J x = ∑ x ∈ Finset.range X,
          (P.lam * (P.v - p) + P.lam * P.δ * J (x + 1) + (1 - P.lam) * P.δ * J x) :=
            Finset.sum_congr rfl fun x hx => (hE x (Finset.mem_range.1 hx)).trans (by ring)
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
    have hIs : X * (P.lam * P.vbar) ≤ (1 - P.δ) * ∑ x ∈ Finset.range X, J x := by
      have := Finset.sum_le_sum (s := Finset.range X) fun x hx => hI x (Finset.mem_range.1 hx)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at this
      exact this
    have hST : ∑ x ∈ Finset.range X, J x + J X = ∑ x ∈ Finset.range X, J (x + 1) + J 0 := by
      rw [← Finset.sum_range_succ, Finset.sum_range_succ']
    have key : (1 - P.δ) * (∑ x ∈ Finset.range X, J x + J X) =
        P.lam * (X * (P.v - p) + P.v) := by
      linear_combination hS + hEX - P.lam * P.δ * hST
    have hmain : P.lam * X / ((X : ℝ) + 1) * p ≤ P.lam * (P.v - P.vbar) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    refine pos_bound P hP p X J _ (fun _ => 1 / P.lam) (fun i hi => ?_) ?_
    · have : moveProb P p X J i = P.lam := by
        unfold moveProb
        rcases hi.lt_or_eq with hi | rfl
        · simp [hi, hBH i hi, ← hq]
        · simp [hRH, ← hq]
      rw [this]; field_simp
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have := alg P.lam ((X : ℝ) + 1) (noProgramProfit P) p X hlam (by positivity)
        (hmain.trans (le_max_right _ _))
      convert this using 2
      push_cast
      ring
