-- Prove2me | solution 1 for FixpNash.Blocks.purePayoff_ge_of_matching_prob_max
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:47:42.747326+00:00
-- url     : https://prove2.me/submissions/48038f50-2a21-4370-9bdd-3ffadc2bf59c

import Definitions.Def_FixpNash_Blocks_Form
import Definitions.Def_DGPNash_NashMap_nashMap

open scoped BigOperators
open FixpNash.Blocks DGPNash.NashMap AGT
set_option maxHeartbeats 1600000

private lemma nf_prof {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (x : ∀ i, S i → ℝ) (i : ι) (w : S i → ℝ)
    (s : ∀ i, S i) : profileProb (Function.update x i w) s =
      w (s i) * ∏ k ∈ Finset.univ.erase i, x k (s k) := by
  classical
  unfold profileProb
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

private lemma nf_mix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) (w : S i → ℝ) :
    expectedPayoff u (Function.update x i w) i = ∑ j, w j * purePayoff u x i j := by
  classical
  unfold purePayoff expectedPayoff
  simp_rw [nf_prof, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp [mul_ite, ite_mul, mul_assoc]

private lemma nf_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) :
    expectedPayoff u x i = ∑ j, x i j * purePayoff u x i j := by
  simpa only [Function.update_eq_self] using nf_mix u x i (x i)

private lemma nf_pure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) :
    IsMixedNash u x ↔ IsMixedProfile x ∧ ∀ i j, purePayoff u x i j ≤ expectedPayoff u x i := by
  classical
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun i j => h i (fun k => if k=j then 1 else 0) ?_⟩
    constructor
    · intro k; dsimp; split_ifs <;> norm_num
    · simp
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    intro i w hw
    rw [nf_mix]
    calc
      (∑ j, w j * purePayoff u x i j) ≤ ∑ j, w j * expectedPayoff u x i :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h i j) (hw.1 j))
      _ = expectedPayoff u x i := by rw [← Finset.sum_mul, hw.2, one_mul]

private lemma nf_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hNE : IsMixedNash u x) :
    ∀ i j, 0 < x i j → purePayoff u x i j = expectedPayoff u x i := by
  classical
  have h := (nf_pure u x).mp hNE
  intro i j hj
  have hz : ∑ k, x i k * (expectedPayoff u x i - purePayoff u x i k) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (h.1 i).2, one_mul, ← nf_self]
    ring
  have hp (k : S i) : 0 ≤ x i k * (expectedPayoff u x i-purePayoff u x i k) :=
    mul_nonneg ((h.1 i).1 k) (sub_nonneg.mpr (h.2 i k))
  have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hp k) (Finset.mem_univ j)
  rw [hz] at hh
  nlinarith [h.2 i j]

section Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]

private lemma bl_marginal (x : ∀ k, S k → ℝ) (hx : IsMixedProfile x)
    (i : ι) (g : S i → ℝ) :
    (∑ s : ∀ k, S k, profileProb x s * g (s i)) = ∑ a, x i a * g a := by
  classical
  let y := Function.update x i (fun a => x i a * g a)
  have he (s : ∀ k, S k) : profileProb y s = profileProb x s * g (s i) := by
    have h := nf_prof x i (x i) s
    simp only [Function.update_eq_self] at h
    rw [h, nf_prof]
    ring
  calc
    _ = ∑ s : ∀ k, S k, profileProb y s := Finset.sum_congr rfl (fun s _ => (he s).symm)
    _ = ∏ k, ∑ a, y k a := (Fintype.prod_sum y).symm
    _ = (∑ a, x i a * g a) * ∏ k ∈ Finset.univ.erase i, (∑ a, x k a) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [y, Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro k hk
      rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
    _ = _ := by simp_rw [(hx _).2]; simp

private lemma bl_pure_prof (x : ∀ k, S k → ℝ) (hx : IsMixedProfile x)
    (i : ι) (j : S i) : IsMixedProfile (Function.update x i (fun a => if a = j then 1 else 0)) := by
  classical
  intro k
  by_cases hk : k = i
  · subst k
    simp only [Function.update_self]
    constructor
    · intro a; dsimp; split_ifs <;> norm_num
    · simp
  · rw [Function.update_of_ne hk]
    exact hx k

private lemma bl_pure_congr (x : ∀ k, S k → ℝ) (i : ι) (j : S i)
    (a b : (∀ k, S k) → ℝ) (h : ∀ s, s i = j → a s = b s) :
    (∑ s, profileProb (Function.update x i (fun a => if a = j then 1 else 0)) s * a s) =
      ∑ s, profileProb (Function.update x i (fun a => if a = j then 1 else 0)) s * b s := by
  classical
  apply Finset.sum_congr rfl
  intro s hs
  rw [nf_prof]
  by_cases hj : s i = j
  · rw [h s hj]
  · simp [hj]

private lemma bl_prime_pay (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : IsMixedProfile x) (k : S i') :
    purePayoff u x i' k = -M * blockProb β x k := by
  classical
  unfold purePayoff expectedPayoff
  rw [bl_pure_congr x i' k (u i') (fun s => if β (s i) = k then -M else 0) (by
    intro s hs
    rw [hG.payoff_i' s, hs]
    simp only [eq_comm])]
  rw [bl_marginal _ (bl_pure_prof x hx i' k) i (fun a => if β a = k then -M else 0)]
  simp only [Function.update_of_ne hG.ne, mul_ite, mul_zero]
  rw [blockProb, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

private lemma bl_first_bonus (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : IsMixedProfile x) (j : S i) :
    purePayoff u x i j =
      (∑ s, profileProb (Function.update x i (fun a => if a = j then 1 else 0)) s * μ s) +
        M * x i' (β j) := by
  classical
  unfold purePayoff expectedPayoff
  simp_rw [hG.payoff_i, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [bl_pure_congr x i j (fun s => if β (s i) = s i' then M else 0)
    (fun s => if s i' = β j then M else 0) (by
      intro s hs
      rw [hs]
      simp only [eq_comm])]
  rw [bl_marginal _ (bl_pure_prof x hx i j) i' (fun a => if a = β j then M else 0)]
  simp only [Function.update_of_ne hG.ne.symm, mul_ite, mul_zero]
  simp [mul_comm]

private lemma bl_weights (x : ∀ k, S k → ℝ) (hx : IsMixedProfile x) :
    (∀ s, 0 ≤ profileProb x s) ∧ (∑ s, profileProb x s) = 1 := by
  classical
  constructor
  · intro s
    exact Finset.prod_nonneg (fun k _ => (hx k).1 (s k))
  · unfold profileProb
    rw [← Fintype.prod_sum]
    simp_rw [fun k => (hx k).2]
    simp

private lemma bl_mu_bounds (x : ∀ k, S k → ℝ) (hx : IsMixedProfile x)
    (μ : (∀ k, S k) → ℝ) :
    -(⨆ s : (∀ k, S k), |μ s|) ≤ (∑ s, profileProb x s * μ s) ∧
      (∑ s, profileProb x s * μ s) ≤ (⨆ s : (∀ k, S k), |μ s|) := by
  classical
  have hw := bl_weights x hx
  have hb (s : ∀ k, S k) := le_ciSup (Set.finite_range (fun s => |μ s|)).bddAbove s
  constructor
  · calc
      _ = ∑ s, profileProb x s * -(⨆ s : (∀ k, S k), |μ s|) := by
        rw [← Finset.sum_mul, hw.2, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (by linarith [neg_abs_le (μ s), hb s]) (hw.1 s)
  · calc
      _ ≤ ∑ s, profileProb x s * (⨆ s : (∀ k, S k), |μ s|) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
          ((le_abs_self (μ s)).trans (hb s)) (hw.1 s)
      _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]

private lemma bl_positive {α : Type*} [Fintype α] (p : α → ℝ) (hp : IsLottery p) :
    ∃ a, 0 < p a := by
  by_contra! hn
  have h := Finset.sum_nonpos (fun a (_ : a ∈ Finset.univ) => hn a)
  rw [hp.2] at h
  norm_num at h

private lemma bl_constants (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : IsMixedProfile x) :
    0 < (3 * (n : ℝ)) ∧ 0 < M ∧
      (⨆ s : (∀ k, S k), |μ s|) < M / (3 * (n : ℝ)) - (⨆ s : (∀ k, S k), |μ s|) := by
  classical
  let a : ∀ k, S k := fun k => (bl_positive (x k) (hx k)).choose
  have hb : 0 ≤ (⨆ s : (∀ k, S k), |μ s|) :=
    (abs_nonneg (μ a)).trans (le_ciSup (Set.finite_range (fun s => |μ s|)).bddAbove a)
  have hc : 0 < Fintype.card (S i') := Fintype.card_pos_iff.mpr ⟨a i'⟩
  have hn : 0 < n := by have := hG.card_le; omega
  have hnr : 0 < (3 * (n : ℝ)) := by positivity
  have hM : 0 < M := lt_of_le_of_lt (by positivity) hG.M_gt
  refine ⟨hnr, hM, ?_⟩
  have hh : 2 * (⨆ s : (∀ k, S k), |μ s|) < M / (3 * (n : ℝ)) := by
    apply (lt_div_iff₀ hnr).mpr
    nlinarith [hG.M_gt]
  linarith

private lemma bl_upper (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : IsMixedProfile x) (j : S i) (hj : x i' (β j) = 0) :
    purePayoff u x i j ≤ (⨆ s : (∀ k, S k), |μ s|) := by
  rw [bl_first_bonus u i i' β μ M n hG x hx j, hj, mul_zero, add_zero]
  exact (bl_mu_bounds _ (bl_pure_prof x hx i j) μ).2

private lemma bl_lower (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : IsMixedProfile x)
    (j : S i) (hj : ∀ k : S i', x i' k ≤ x i' (β j)) :
    M / (3 * (n : ℝ)) - (⨆ s : (∀ k, S k), |μ s|) ≤ purePayoff u x i j := by
  have hc := bl_constants u i i' β μ M n hG x hx
  have hp : 1 ≤ (3 * (n : ℝ)) * x i' (β j) := calc
    1 = ∑ k, x i' k := (hx i').2.symm
    _ ≤ ∑ _ : S i', x i' (β j) := Finset.sum_le_sum (fun k _ => hj k)
    _ = (Fintype.card (S i') : ℝ) * x i' (β j) := by simp
    _ ≤ (3 * (n : ℝ)) * x i' (β j) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hG.card_le) ((hx i').1 (β j))
  have hbonus : M / (3 * (n : ℝ)) ≤ M * x i' (β j) := by
    apply (div_le_iff₀ hc.1).mpr
    nlinarith [mul_le_mul_of_nonneg_left hp hc.2.1.le]
  rw [bl_first_bonus u i i' β μ M n hG x hx j]
  have hμ := (bl_mu_bounds _ (bl_pure_prof x hx i j) μ).1
  linarith

private lemma bl_no_active (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : IsMixedNash u x)
    (j : S i) (hj : x i' (β j) = 0) : x i j = 0 := by
  classical
  obtain ⟨a, ha⟩ := bl_positive (x i') (hx.1 i')
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (x i') ⟨a, Finset.mem_univ a⟩
  obtain ⟨j', hj'⟩ := hG.surjective k
  have hu := bl_upper u i i' β μ M n hG x hx.1 j hj
  have hl := bl_lower u i i' β μ M n hG x hx.1 j'
    (fun b => by rw [hj']; exact hk b (Finset.mem_univ b))
  have hgap := (bl_constants u i i' β μ M n hG x hx.1).2.2
  have hne := ((nf_pure u x).mp hx).2 i j'
  by_contra hzero
  have hp : 0 < x i j := lt_of_le_of_ne ((hx.1 i).1 j) (Ne.symm hzero)
  have he := nf_support u x hx i j hp
  linarith

private lemma bl_matching_zero (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : IsMixedNash u x)
    (hunequal : ∃ k₁ k₂ : S i', blockProb β x k₁ ≠ blockProb β x k₂)
    (k : S i') (hk : ∀ k', blockProb β x k' ≤ blockProb β x k) : x i' k = 0 := by
  obtain ⟨l, hl⟩ : ∃ l, blockProb β x l < blockProb β x k := by
    by_contra! hn
    obtain ⟨a, b, hab⟩ := hunequal
    exact hab ((le_antisymm (hk a) (hn a)).trans (le_antisymm (hk b) (hn b)).symm)
  have hM := (bl_constants u i i' β μ M n hG x hx.1).2.1
  by_contra hn
  have hp : 0 < x i' k := lt_of_le_of_ne ((hx.1 i').1 k) (Ne.symm hn)
  have he := nf_support u x hx i' k hp
  have hle := ((nf_pure u x).mp hx).2 i' l
  rw [bl_prime_pay u i i' β μ M n hG x hx.1 k] at he
  rw [bl_prime_pay u i i' β μ M n hG x hx.1 l] at hle
  nlinarith [mul_lt_mul_of_pos_left hl hM]

private lemma bl_total (i i' : ι) (β : S i → S i') (x : ∀ k, S k → ℝ)
    (hx : IsMixedProfile x) : (∑ k, blockProb β x k) = 1 := by
  classical
  unfold blockProb
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simpa using (hx i).2

private lemma bl_equal (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : IsMixedNash u x) :
    ∀ k k' : S i', blockProb β x k = blockProb β x k' := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨a, ha⟩ := bl_positive (x i') (hx.1 i')
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (blockProb β x) ⟨a, Finset.mem_univ a⟩
  have hz := bl_matching_zero u i i' β μ M n hG x hx h k (fun b => hk b (Finset.mem_univ b))
  have hb : blockProb β x k = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjk := (Finset.mem_filter.mp hj).2
    exact bl_no_active u i i' β μ M n hG x hx j (by rwa [hjk])
  have hsum : (∑ b, blockProb β x b) ≤ 0 := Finset.sum_nonpos
    (fun b _ => by have := hk b (Finset.mem_univ b); linarith)
  rw [bl_total i i' β x hx.1] at hsum
  norm_num at hsum

private lemma bl_full_support (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : IsMixedNash u x) : ∀ k : S i', x i' k ≠ 0 := by
  classical
  intro k hk
  have he := bl_equal u i i' β μ M n hG x hx
  have hb : blockProb β x k = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjk := (Finset.mem_filter.mp hj).2
    exact bl_no_active u i i' β μ M n hG x hx j (by rwa [hjk])
  have hz : (∑ b, blockProb β x b) = 0 := Finset.sum_eq_zero (fun b _ => (he b k).trans hb)
  rw [bl_total i i' β x hx.1] at hz
  norm_num at hz

end Blocks

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : AGT.IsMixedProfile x)
    (j' : S i) (hj' : ∀ k : S i', x i' k ≤ x i' (β j')) :
    M / (3 * (n : ℝ)) - (⨆ s : (∀ k, S k), |μ s|) ≤ DGPNash.NashMap.purePayoff u x i j' := by
  exact bl_lower u i i' β μ M n hG x hx j' hj'
