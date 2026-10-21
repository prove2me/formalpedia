-- Prove2me | solution 1 for BudgetedAffine.Disjoint.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:36:10.981981+00:00
-- url     : https://prove2.me/submissions/e629b388-dc67-4711-ab34-331c27b809c0

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction

set_option autoImplicit false

open Matrix BudgetedAffine.Disjoint

lemma bad_mem_reqUnion {m : ℕ} (s : List (Finset (Fin m))) (i : Fin m) :
    i ∈ reqUnion s ↔ ∃ S ∈ s, i ∈ S := by
  induction s with
  | nil => simp [reqUnion]
  | cons S s ih =>
    have : reqUnion (S :: s) = S ∪ reqUnion s := by simp [reqUnion]
    rw [this, Finset.mem_union, ih]
    simp

theorem solution {m n L : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : BudgetedAffine.Budget.IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hS : IsPartition S) (hw : ∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1)
    (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ)
    (hopt : BudgetedAffine.Budget.IsOptimalAR A B c d X (disjointBudgetSet S w) xs ys)
    (OPT : ℝ) (hOPT : BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) = (OPT : EReal))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (alg : OnlineCover (Btil A B xs) d ρ)
    (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m))
    (ha : IsGreedyRun alg w (hatS S A xs) σ a) :
    nu alg a L ≤ ρ * OPT := by
  obtain ⟨hfeas, hworst⟩ := hopt
  obtain ⟨ha1, -⟩ := ha
  -- the sequence and its union
  set s : List (Finset (Fin m)) := List.ofFn a with hs
  have hpre : seqPrefix a L = s := by
    unfold seqPrefix
    exact List.take_of_length_le (by simp [hs])
  have hnu : nu alg a L = d ⬝ᵥ alg.sol s := by
    unfold nu OnlineCover.cost
    rw [hpre]
  set W : Finset (Fin m) := reqUnion s with hWdef
  have hW : ∀ i, i ∈ W ↔ ∃ k, i ∈ a k := by
    intro i
    rw [hWdef, bad_mem_reqUnion, hs]
    constructor
    · rintro ⟨T, hT, hiT⟩
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hT
      exact ⟨k, hiT⟩
    · rintro ⟨k, hk⟩
      exact ⟨a k, List.mem_ofFn.mpr ⟨k, rfl⟩, hk⟩
  have haS : ∀ k, a k ⊆ S (σ k) := fun k i hi =>
    (Finset.mem_filter.mp ((ha1 k).1 hi)).1
  have haα : ∀ k, ∀ i ∈ a k, 0 < BudgetedAffine.Budget.alpha A xs i := fun k i hi =>
    (Finset.mem_filter.mp ((ha1 k).1 hi)).2
  have hdisj : ∀ k k', k ≠ k' → Disjoint (a k) (a k') := by
    intro k k' hkk
    have hσ : σ k ≠ σ k' := fun h => hkk (σ.injective h)
    exact Finset.disjoint_of_subset_left (haS k) (Finset.disjoint_of_subset_right (haS k') (hS.1 _ _ hσ))
  -- h ∈ U
  have hU : BudgetedAffine.Budget.indic W ∈ disjointBudgetSet S w := by
    refine ⟨fun i => ?_, fun ℓ => ?_⟩
    · unfold BudgetedAffine.Budget.indic
      split_ifs <;> simp
    · obtain ⟨k, rfl⟩ := σ.surjective ℓ
      have : ∀ i ∈ S (σ k), w (σ k) i * BudgetedAffine.Budget.indic W i =
          if i ∈ a k then w (σ k) i else 0 := by
        intro i hi
        unfold BudgetedAffine.Budget.indic
        by_cases hik : i ∈ a k
        · have : i ∈ W := (hW i).mpr ⟨k, hik⟩
          simp [hik, this]
        · have : i ∉ W := by
            intro hiW
            obtain ⟨k', hk'⟩ := (hW i).mp hiW
            by_cases hkk : k = k'
            · subst hkk; exact hik hk'
            · have h1 : σ k ≠ σ k' := fun h => hkk (σ.injective h)
              exact Finset.disjoint_left.mp (hS.1 _ _ h1) hi (haS k' hk')
          simp [hik, this]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_mem, Finset.inter_eq_right.mpr (haS k)]
      exact (ha1 k).2
  -- coverage
  obtain ⟨hy0, hycov⟩ := hfeas.2 _ hU
  set y := ys (BudgetedAffine.Budget.indic W) with hy
  have hBtil_nn : ∀ i j, 0 ≤ Btil A B xs i j := by
    intro i j
    unfold Btil
    simp only [Matrix.of_apply]
    split_ifs with h
    · exact div_nonneg (hB i j) h.le
    · exact hB i j
  have hcov : BudgetedAffine.Budget.indic W ≤ Btil A B xs *ᵥ y := by
    intro i
    by_cases hi : i ∈ W
    · obtain ⟨k, hk⟩ := (hW i).mp hi
      have hα := haα k i hk
      have h1 : BudgetedAffine.Budget.indic W i = 1 := by simp [BudgetedAffine.Budget.indic, hi]
      have h2 := hycov i
      rw [Pi.add_apply] at h2
      have h3 : (Btil A B xs *ᵥ y) i = (B *ᵥ y) i / BudgetedAffine.Budget.alpha A xs i := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_div]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp [Btil, hα, div_mul_eq_mul_div]
      rw [h3, h1, le_div_iff₀ hα]
      unfold BudgetedAffine.Budget.alpha
      linarith
    · have h1 : BudgetedAffine.Budget.indic W i = 0 := by simp [BudgetedAffine.Budget.indic, hi]
      rw [h1]
      show 0 ≤ ∑ j, Btil A B xs i j * y j
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hBtil_nn i j) (hy0 j))
  -- bound d·y ≤ OPT
  have hdy : d ⬝ᵥ y ≤ OPT := by
    have h1 : ((c ⬝ᵥ xs + d ⬝ᵥ y : ℝ) : EReal) ≤ BudgetedAffine.Budget.worstCost c d (disjointBudgetSet S w) xs ys :=
      le_iSup₂ (f := fun h (_ : h ∈ disjointBudgetSet S w) => ((c ⬝ᵥ xs + d ⬝ᵥ ys h : ℝ) : EReal))
        (BudgetedAffine.Budget.indic W) hU
    rw [hworst, hOPT] at h1
    have h2 := EReal.coe_le_coe_iff.mp h1
    have h3 := hcX xs hfeas.1
    linarith
  have hdy0 : 0 ≤ d ⬝ᵥ y := dotProduct_nonneg_of_nonneg hd hy0
  have hcc_le : BudgetedAffine.Budget.coverCost (Btil A B xs) d (BudgetedAffine.Budget.indic W) ≤ ((d ⬝ᵥ y : ℝ) : EReal) :=
    iInf₂_le y ⟨hy0, hcov⟩
  have hcc_ge : (0 : EReal) ≤ BudgetedAffine.Budget.coverCost (Btil A B xs) d (BudgetedAffine.Budget.indic W) := by
    refine le_iInf₂ (fun y' hy' => ?_)
    exact_mod_cast dotProduct_nonneg_of_nonneg hd hy'.1
  have hcc_ne_top : BudgetedAffine.Budget.coverCost (Btil A B xs) d (BudgetedAffine.Budget.indic W) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hcc_le
  obtain ⟨r, hr⟩ : ∃ r : ℝ, BudgetedAffine.Budget.coverCost (Btil A B xs) d (BudgetedAffine.Budget.indic W) = (r : EReal) :=
    ⟨_, (EReal.coe_toReal hcc_ne_top (ne_bot_of_le_ne_bot (by simp) hcc_ge)).symm⟩
  have hr_le : r ≤ d ⬝ᵥ y := by
    rw [hr] at hcc_le
    exact EReal.coe_le_coe_iff.mp hcc_le
  have hpw : s.Pairwise Disjoint := by
    rw [hs, List.pairwise_ofFn]
    intro i j hij
    exact hdisj i j hij.ne
  have hcomp := alg.compet s hpw (by rw [← hWdef]; exact hcc_ne_top)
  rw [← hWdef, hr, ← EReal.coe_mul] at hcomp
  have h4 := EReal.coe_le_coe_iff.mp hcomp
  rw [hnu]
  nlinarith
