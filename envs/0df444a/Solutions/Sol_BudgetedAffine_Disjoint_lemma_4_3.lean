-- Prove2me | solution 1 for BudgetedAffine.Disjoint.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:01:59.043214+00:00
-- url     : https://prove2.me/submissions/6c03f378-5320-47a7-b729-18d26d17fd6e

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction
import Theorems.Thm_BudgetedAffine_Disjoint_lemma_4_1

set_option autoImplicit false
open Matrix BudgetedAffine.Disjoint

theorem affdisj43_beta8_pos (n : ℕ) (hn : 3 ≤ n) : 0 < beta8 n := by
  unfold beta8
  have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have : 0 < Real.log (Real.log n) := Real.log_pos hlog
  have : 0 < Real.log n := by linarith
  positivity

theorem affdisj43_dot_yLin {m n : ℕ} (d : Fin n → ℝ) (I : Finset (Fin m)) (α : Fin m → ℝ)
    (v : Fin m → Fin n → ℝ) (h : Fin m → ℝ) :
    d ⬝ᵥ BudgetedAffine.Budget.yLin I α v h = ∑ i ∈ I, (α i * h i) * (d ⬝ᵥ v i) := by
  simp only [BudgetedAffine.Budget.yLin, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem affdisj43_prefix_succ {m L : ℕ} (a : Fin L → Finset (Fin m)) (ℓ : Fin L) :
    seqPrefix a (ℓ.val + 1) = seqPrefix a ℓ.val ++ [a ℓ] := by
  unfold seqPrefix
  rw [List.take_succ]
  congr 1
  simp

theorem affdisj43_nuInc_nonneg {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ}
    {ρ : ℝ} (hd : 0 ≤ d) (alg : OnlineCover M d ρ) (a : Fin L → Finset (Fin m)) (ℓ : Fin L) :
    0 ≤ nuInc alg a ℓ := by
  unfold nuInc nu OnlineCover.cost
  rw [affdisj43_prefix_succ, sub_nonneg]
  unfold dotProduct
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
    (alg.mono (seqPrefix a ℓ.val) (a ℓ) j) (hd j))

theorem affdisj43_sum_nuInc {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ}
    {ρ : ℝ} (alg : OnlineCover M d ρ) (a : Fin L → Finset (Fin m)) :
    ∑ ℓ : Fin L, nuInc alg a ℓ = nu alg a L := by
  unfold nuInc
  rw [Fin.sum_univ_eq_sum_range (fun k => nu alg a (k + 1) - nu alg a k) L,
    Finset.sum_range_sub (fun k => nu alg a k)]
  have : nu alg a 0 = 0 := by
    unfold nu OnlineCover.cost seqPrefix
    simp [alg.sol_nil]
  rw [this, sub_zero]

theorem solution {m n L : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : BudgetedAffine.Budget.IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hS : IsPartition S) (hw : ∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1)
    (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ)
    (hopt : BudgetedAffine.Budget.IsOptimalAR A B c d X (disjointBudgetSet S w) xs ys)
    (OPT : ℝ) (hOPT : BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) = (OPT : EReal))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (alg : OnlineCover (Btil A B xs) d ρ)
    (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m))
    (ha : IsGreedyRun alg w (hatS S A xs) σ a)
    (hn : 3 ≤ n) (v : Fin m → Fin n → ℝ)
    (hv : ∀ i ∈ Iset A B d S w xs σ (nuInc alg a), BudgetedAffine.Budget.IsCoverOpt B d (Pi.single i 1) (v i)) :
    ∀ h ∈ disjointBudgetSet S w,
      d ⬝ᵥ BudgetedAffine.Budget.yLin (Iset A B d S w xs σ (nuInc alg a)) (BudgetedAffine.Budget.alpha A xs) v h ≤ beta8 n * ρ * OPT := by
  intro h hh
  obtain ⟨hh01, hhsum⟩ := hh
  set I := Iset A B d S w xs σ (nuInc alg a) with hI
  set α := BudgetedAffine.Budget.alpha A xs with hαdef
  set Δ := nuInc alg a with hΔ
  have hβ := affdisj43_beta8_pos n hn
  have hΔ0 : ∀ ℓ, 0 ≤ Δ ℓ := fun ℓ => affdisj43_nuInc_nonneg hd alg a ℓ
  have h41 := BudgetedAffine.Disjoint.lemma_4_1 A B c d X S w hB hc hd hX hcX hS hw xs ys hopt
    OPT hOPT ρ hρ alg σ a ha
  -- block assignment
  have hex : ∀ i : Fin m, ∃ ℓ : Fin L, i ∈ S (σ ℓ) := by
    intro i
    obtain ⟨ℓ0, h0⟩ := hS.2 i
    exact ⟨σ.symm ℓ0, by simpa using h0⟩
  choose g hg using hex
  have huniq : ∀ i ℓ, i ∈ S (σ ℓ) → ℓ = g i := by
    intro i ℓ hiℓ
    by_contra hne
    have : σ ℓ ≠ σ (g i) := fun e => hne (σ.injective e)
    exact Finset.disjoint_left.mp (hS.1 _ _ this) hiℓ (hg i)
  -- key bound per index
  have hkey : ∀ i ∈ I, 0 < α i ∧ α i * (d ⬝ᵥ v i) ≤ w (σ (g i)) i * beta8 n * Δ (g i) := by
    intro i hi
    obtain ⟨ℓ, hiS, hpos, hle⟩ := (Finset.mem_filter.1 hi).2
    have hℓ := huniq i ℓ hiS
    subst hℓ
    refine ⟨hpos, ?_⟩
    have h2 := (hv i hi).2.2
    rw [← h2, ← EReal.coe_mul] at hle
    exact_mod_cast hle
  have hf0 : ∀ i ∈ I, 0 ≤ (α i * h i) * (d ⬝ᵥ v i) := by
    intro i hi
    exact mul_nonneg (mul_nonneg (hkey i hi).1.le (hh01 i).1)
      (dotProduct_nonneg_of_nonneg hd (hv i hi).1)
  rw [affdisj43_dot_yLin]
  calc ∑ i ∈ I, (α i * h i) * (d ⬝ᵥ v i)
      ≤ ∑ i ∈ I, h i * (w (σ (g i)) i * beta8 n * Δ (g i)) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have := mul_le_mul_of_nonneg_left (hkey i hi).2 (hh01 i).1
        linarith
    _ = ∑ ℓ : Fin L, ∑ i ∈ I with g i = ℓ, h i * (w (σ (g i)) i * beta8 n * Δ (g i)) :=
        (Finset.sum_fiberwise I g _).symm
    _ = ∑ ℓ : Fin L, beta8 n * Δ ℓ * ∑ i ∈ I with g i = ℓ, w (σ ℓ) i * h i := by
        refine Finset.sum_congr rfl (fun ℓ _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [(Finset.mem_filter.1 hi).2]
        ring
    _ ≤ ∑ ℓ : Fin L, beta8 n * Δ ℓ * 1 := by
        refine Finset.sum_le_sum (fun ℓ _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hβ.le (hΔ0 ℓ))
        refine le_trans ?_ (hhsum (σ ℓ))
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro i hi
          have := (Finset.mem_filter.1 hi).2
          rw [← this]; exact hg i
        · intro i _ _
          exact mul_nonneg (hw _ _).1 (hh01 i).1
    _ = beta8 n * nu alg a L := by
        rw [← affdisj43_sum_nuInc alg a, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ℓ _ => by ring)
    _ ≤ beta8 n * (ρ * OPT) := mul_le_mul_of_nonneg_left h41 hβ.le
    _ = beta8 n * ρ * OPT := by ring
