-- Prove2me | solution 1 for BudgetedAffine.Disjoint.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:11:24.170876+00:00
-- url     : https://prove2.me/submissions/86e11ade-1e31-426d-9f3a-3020220073fe

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction
import Theorems.Thm_BudgetedAffine_Disjoint_lemma_4_1
import Theorems.Thm_BudgetedAffine_Disjoint_lemma_3_3

set_option autoImplicit false
open Matrix BudgetedAffine.Disjoint

namespace AffDisj44

theorem mem_reqUnion {m : ℕ} (s : List (Finset (Fin m))) (i : Fin m) :
    i ∈ reqUnion s ↔ ∃ S ∈ s, i ∈ S := by
  induction s with
  | nil => simp [reqUnion]
  | cons S s ih =>
    have : reqUnion (S :: s) = S ∪ reqUnion s := by simp [reqUnion]
    rw [this, Finset.mem_union, ih]
    simp

theorem mem_seqPrefix {m L : ℕ} (a : Fin L → Finset (Fin m)) (ℓ : ℕ) (T : Finset (Fin m)) :
    T ∈ seqPrefix a ℓ ↔ ∃ k : Fin L, k.val < ℓ ∧ a k = T := by
  unfold seqPrefix
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_ofFn, lt_min_iff] at hi
    exact ⟨⟨i, hi.2⟩, hi.1, by simp⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.val, by simp [hk, k.isLt], by simp⟩

theorem prefix_succ {m L : ℕ} (a : Fin L → Finset (Fin m)) (ℓ : Fin L) :
    seqPrefix a (ℓ.val + 1) = seqPrefix a ℓ.val ++ [a ℓ] := by
  unfold seqPrefix
  rw [List.take_succ]
  congr 1
  simp

theorem sol_mono {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ}
    {ρ : ℝ} (alg : OnlineCover M d ρ) (a : Fin L → Finset (Fin m)) :
    Monotone (fun k => alg.sol (seqPrefix a k)) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show alg.sol (seqPrefix a k) ≤ alg.sol (seqPrefix a (k + 1))
  by_cases hk : k < L
  · have := prefix_succ a ⟨k, hk⟩
    simp only at this
    rw [this]
    exact alg.mono _ _
  · have h1 : seqPrefix a (k + 1) = seqPrefix a k := by
      unfold seqPrefix
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
    rw [h1]

theorem nuInc_nonneg {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ}
    {ρ : ℝ} (hd : 0 ≤ d) (alg : OnlineCover M d ρ) (a : Fin L → Finset (Fin m)) (ℓ : Fin L) :
    0 ≤ nuInc alg a ℓ := by
  unfold nuInc nu OnlineCover.cost
  rw [prefix_succ, sub_nonneg]
  unfold dotProduct
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
    (alg.mono (seqPrefix a ℓ.val) (a ℓ) j) (hd j))

theorem sum_nuInc {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ}
    {ρ : ℝ} (alg : OnlineCover M d ρ) (a : Fin L → Finset (Fin m)) :
    ∑ ℓ : Fin L, nuInc alg a ℓ = nu alg a L := by
  unfold nuInc
  rw [Fin.sum_univ_eq_sum_range (fun k => nu alg a (k + 1) - nu alg a k) L,
    Finset.sum_range_sub (fun k => nu alg a k)]
  have : nu alg a 0 = 0 := by
    unfold nu OnlineCover.cost seqPrefix
    simp [alg.sol_nil]
  rw [this, sub_zero]

theorem beta8_pos (n : ℕ) (hn : 3 ≤ n) : 0 < Real.log n / Real.log (Real.log n) := by
  have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have : 0 < Real.log (Real.log n) := Real.log_pos hlog
  have : 0 < Real.log n := by linarith
  positivity

theorem coverCost_nonneg {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ) (hd : 0 ≤ d)
    (h : Fin m → ℝ) : (0 : EReal) ≤ BudgetedAffine.Budget.coverCost M d h := by
  refine le_iInf₂ (fun y hy => ?_)
  exact_mod_cast dotProduct_nonneg_of_nonneg hd hy.1

theorem Btil_nonneg {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) : ∀ i j, 0 ≤ Btil A B x i j := by
  intro i j
  unfold Btil
  simp only [Matrix.of_apply]
  split_ifs with h
  · exact div_nonneg (hB i j) h.le
  · exact hB i j

theorem Btil_row {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (y : Fin n → ℝ)
    (i : Fin m) (hα : 0 < BudgetedAffine.Budget.alpha A x i) :
    (Btil A B x *ᵥ y) i = (B *ᵥ y) i / BudgetedAffine.Budget.alpha A x i := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Btil, hα, div_mul_eq_mul_div]

theorem mulVec_nonneg' {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (y : Fin n → ℝ) (hy : 0 ≤ y) : 0 ≤ M *ᵥ y := by
  intro i
  show 0 ≤ ∑ j, M i j * y j
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hM i j) (hy j))

theorem indic_single {m : ℕ} (i : Fin m) :
    BudgetedAffine.Budget.indic {i} = (Pi.single i 1 : Fin m → ℝ) := by
  funext k
  by_cases h : k = i
  · subst h; simp [BudgetedAffine.Budget.indic]
  · simp [BudgetedAffine.Budget.indic, h]

/-- `α z(eᵢ) ≤ Θ(eᵢ)`, or rather: if `t < α z(eᵢ)` then `t < Θ(eᵢ)`. -/
theorem theta_gt {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (d : Fin n → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hd : 0 ≤ d) (i : Fin m) (hα : 0 < BudgetedAffine.Budget.alpha A x i) (t : ℝ)
    (ht : (t : EReal) < ((BudgetedAffine.Budget.alpha A x i : ℝ) : EReal) *
      BudgetedAffine.Budget.coverCost B d (Pi.single i 1)) :
    (t : EReal) < BudgetedAffine.Budget.coverCost (Btil A B x) d (Pi.single i 1) := by
  set α := BudgetedAffine.Budget.alpha A x i with hαd
  -- any feasible y for Θ gives z ≤ d y / α
  have hfe : ∀ y : Fin n → ℝ, 0 ≤ y ∧ (Pi.single i 1 : Fin m → ℝ) ≤ Btil A B x *ᵥ y →
      BudgetedAffine.Budget.coverCost B d (Pi.single i 1) ≤ ((d ⬝ᵥ y / α : ℝ) : EReal) := by
    intro y hy
    have hy' : 0 ≤ α⁻¹ • y ∧ (Pi.single i 1 : Fin m → ℝ) ≤ B *ᵥ (α⁻¹ • y) := by
      refine ⟨fun j => mul_nonneg (inv_nonneg.2 hα.le) (hy.1 j), fun k => ?_⟩
      by_cases hk : k = i
      · subst hk
        have h1 := hy.2 k
        rw [Btil_row A B x y k hα] at h1
        simp only [Pi.single_eq_same] at h1 ⊢
        rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        rw [le_div_iff₀ hα] at h1
        calc (1:ℝ) = α⁻¹ * α := by field_simp
          _ ≤ α⁻¹ * (B *ᵥ y) k := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hα.le)
      · simp only [Pi.single_eq_of_ne hk]
        rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 hα.le) (mulVec_nonneg' B hB y hy.1 k)
    refine le_trans (iInf₂_le (α⁻¹ • y) hy') ?_
    rw [dotProduct_smul, smul_eq_mul]
    exact_mod_cast le_of_eq (by ring)
  by_cases hz : BudgetedAffine.Budget.coverCost B d (Pi.single i 1) = ⊤
  · have : BudgetedAffine.Budget.coverCost (Btil A B x) d (Pi.single i 1) = ⊤ := by
      refine top_le_iff.1 (le_iInf₂ (fun y hy => ?_))
      have := hfe y hy
      rw [hz] at this
      exact absurd this (by simp)
    rw [this]; exact EReal.coe_lt_top t
  · have hbot : BudgetedAffine.Budget.coverCost B d (Pi.single i 1) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (by simp) (coverCost_nonneg B d hd _)
    obtain ⟨r, hr⟩ : ∃ r : ℝ, BudgetedAffine.Budget.coverCost B d (Pi.single i 1) = (r : EReal) :=
      ⟨_, (EReal.coe_toReal hz hbot).symm⟩
    rw [hr, ← EReal.coe_mul] at ht
    refine lt_of_lt_of_le ht (le_iInf₂ (fun y hy => ?_))
    have h1 := hfe y hy
    rw [hr] at h1
    have h2 : r ≤ d ⬝ᵥ y / α := EReal.coe_le_coe_iff.1 h1
    rw [le_div_iff₀ hα] at h2
    exact_mod_cast (by linarith : α * r ≤ d ⬝ᵥ y)


theorem mulVec_mono' {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (u v : Fin n → ℝ) (huv : u ≤ v) : M *ᵥ u ≤ M *ᵥ v := by
  intro i
  show ∑ j, M i j * u j ≤ ∑ j, M i j * v j
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (huv j) (hM i j))

theorem exists_pos_lt_all {ι : Type} (s : Finset ι) (f : ι → EReal) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, (t : EReal) < f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert j s hj ih =>
    obtain ⟨t, ht, hts⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨u, hu0, hu⟩ := EReal.lt_iff_exists_real_btwn.1 (hf j (Finset.mem_insert_self j s))
    have hu0' : (0:ℝ) < u := by exact_mod_cast hu0
    refine ⟨min t u, lt_min ht hu0', fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact lt_of_le_of_lt (by exact_mod_cast min_le_right t u) hu
    · exact lt_of_le_of_lt (by exact_mod_cast min_le_left t u) (hts i hi)

theorem coverCost_empty {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ) :
    BudgetedAffine.Budget.coverCost M d (BudgetedAffine.Budget.indic (∅ : Finset (Fin m))) ≤ 0 := by
  refine le_trans (iInf₂_le (0 : Fin n → ℝ) ⟨le_rfl, fun i => ?_⟩) (by simp)
  simp [BudgetedAffine.Budget.indic]

end AffDisj44

open AffDisj44 in
theorem solution :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (m L : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
      (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → BudgetedAffine.Budget.IsPolyhedral X →
      (∀ x ∈ X, 0 ≤ c ⬝ᵥ x) → IsPartition S → (∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1) →
      ∀ (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ),
      BudgetedAffine.Budget.IsOptimalAR A B c d X (disjointBudgetSet S w) xs ys →
      ∀ OPT : ℝ, BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) = (OPT : EReal) →
      ∀ (ρ : ℝ), 0 ≤ ρ → ∀ (alg : OnlineCover (Btil A B xs) d ρ)
        (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m)),
      IsGreedyRun alg w (hatS S A xs) σ a →
      BudgetedAffine.Budget.staticValue A B c d X (BudgetedAffine.Budget.staRhs (Iset A B d S w xs σ (nuInc alg a)) (BudgetedAffine.Budget.alpha A xs)) ≤
        (((1 + 2 * ρ + beta8 n * ρ) * OPT : ℝ) : EReal) := by
  classical
  obtain ⟨N₀, hN₀⟩ := BudgetedAffine.Disjoint.lemma_3_3
  refine ⟨max N₀ 3, ?_⟩
  intro n hn m L A B c d X S w hB hc hd hX hcX hS hw xs ys hopt OPT hOPT ρ hρ alg σ a ha
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : n ≥ N₀ := le_trans (le_max_left _ _) hn
  have h41 := BudgetedAffine.Disjoint.lemma_4_1 A B c d X S w hB hc hd hX hcX hS hw xs ys hopt
    OPT hOPT ρ hρ alg σ a ha
  set α := BudgetedAffine.Budget.alpha A xs with hαdef
  set I := Iset A B d S w xs σ (nuInc alg a) with hI
  set Δ := nuInc alg a with hΔ
  set yA := alg.sol (seqPrefix a L) with hyA
  set r := Real.log n / Real.log (Real.log n) with hr
  have hr0 : 0 < r := beta8_pos n hn3
  have hβeq : beta8 n = 8 * r := by unfold beta8; rw [hr]; ring
  have hβ0 : 0 ≤ beta8 n := by rw [hβeq]; positivity
  have hΔ0 : ∀ ℓ, 0 ≤ Δ ℓ := nuInc_nonneg hd alg a
  have hnuL : nu alg a L = d ⬝ᵥ yA := rfl
  obtain ⟨hfeas, hworst⟩ := hopt
  have h0U : (0 : Fin m → ℝ) ∈ disjointBudgetSet S w :=
    ⟨fun i => ⟨le_rfl, zero_le_one⟩, fun ℓ => by simp⟩
  obtain ⟨hys0, hcov0⟩ := hfeas.2 0 h0U
  have hOPT0 : c ⬝ᵥ xs + d ⬝ᵥ ys 0 ≤ OPT := by
    have hge : (((c ⬝ᵥ xs + d ⬝ᵥ ys 0 : ℝ)) : EReal) ≤
        BudgetedAffine.Budget.worstCost c d (disjointBudgetSet S w) xs ys := by
      unfold BudgetedAffine.Budget.worstCost
      exact le_iSup₂_of_le (0 : Fin m → ℝ) h0U le_rfl
    rw [hworst, hOPT] at hge
    exact_mod_cast hge
  have hBtnn : ∀ i j, 0 ≤ (Btil A B xs) i j := Btil_nonneg A B xs hB
  have hyA0 : 0 ≤ yA := alg.nonneg _
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
  have hsame : ∀ i k k', i ∈ S (σ k) → i ∈ S (σ k') → k = k' := fun i k k' h1 h2 =>
    (huniq i k h1).trans (huniq i k' h2).symm
  have ha1 := ha.1
  have haS : ∀ k, a k ⊆ S (σ k) := fun k i hi => (Finset.mem_filter.mp ((ha1 k).1 hi)).1
  have haα : ∀ k, ∀ i ∈ a k, 0 < α i := fun k i hi => (Finset.mem_filter.mp ((ha1 k).1 hi)).2
  -- coverability of `a₁, …, a_{ℓ-1}, W`
  have hcoverable : ∀ (ℓ : Fin L) (W : Finset (Fin m)), W ⊆ hatS S A xs (σ ℓ) →
      ∑ i ∈ W, w (σ ℓ) i ≤ 1 →
      BudgetedAffine.Budget.coverCost (Btil A B xs) d
        (BudgetedAffine.Budget.indic (reqUnion (seqPrefix a ℓ.val ++ [W]))) ≠ ⊤ := by
    intro ℓ W hW hWw
    set H := reqUnion (seqPrefix a ℓ.val ++ [W]) with hHdef
    have hH : ∀ i, i ∈ H ↔ (∃ k : Fin L, k.val < ℓ.val ∧ i ∈ a k) ∨ i ∈ W := by
      intro i
      rw [hHdef, mem_reqUnion]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨T, hT | rfl, hiT⟩
        · obtain ⟨k, hk, rfl⟩ := (mem_seqPrefix a ℓ.val T).1 hT
          exact Or.inl ⟨k, hk, hiT⟩
        · exact Or.inr hiT
      · rintro (⟨k, hk, hik⟩ | hiW)
        · exact ⟨a k, Or.inl ((mem_seqPrefix a ℓ.val _).2 ⟨k, hk, rfl⟩), hik⟩
        · exact ⟨W, Or.inr rfl, hiW⟩
    have hWS : W ⊆ S (σ ℓ) := fun i hi => (Finset.mem_filter.mp (hW hi)).1
    have hWα : ∀ i ∈ W, 0 < α i := fun i hi => (Finset.mem_filter.mp (hW hi)).2
    have hHα : ∀ i ∈ H, 0 < α i := by
      intro i hi
      rcases (hH i).1 hi with ⟨k, -, hik⟩ | hiW
      · exact haα k i hik
      · exact hWα i hiW
    have key : ∀ (k' : Fin L) (T : Finset (Fin m)), (∀ i ∈ S (σ k'), i ∈ H → i ∈ T) →
        ∑ i ∈ T, w (σ k') i ≤ 1 →
        ∑ i ∈ S (σ k'), w (σ k') i * BudgetedAffine.Budget.indic H i ≤ 1 := by
      intro k' T hT hTw
      calc ∑ i ∈ S (σ k'), w (σ k') i * BudgetedAffine.Budget.indic H i
          ≤ ∑ i ∈ S (σ k') ∩ T, w (σ k') i := by
            rw [← Finset.sum_filter_add_sum_filter_not (S (σ k')) (fun i => i ∈ T)]
            have h1 : ∑ i ∈ (S (σ k')).filter (fun i => i ∉ T),
                w (σ k') i * BudgetedAffine.Budget.indic H i = 0 := by
              refine Finset.sum_eq_zero (fun i hi => ?_)
              obtain ⟨hiS, hiT⟩ := Finset.mem_filter.1 hi
              have : i ∉ H := fun hiH => hiT (hT i hiS hiH)
              simp [BudgetedAffine.Budget.indic, this]
            rw [h1, add_zero, Finset.filter_mem_eq_inter]
            refine Finset.sum_le_sum (fun i _ => ?_)
            unfold BudgetedAffine.Budget.indic
            split_ifs <;> simp [(hw (σ k') i).1]
        _ ≤ ∑ i ∈ T, w (σ k') i :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
              (fun i _ _ => (hw _ _).1)
        _ ≤ 1 := hTw
    have hU : BudgetedAffine.Budget.indic H ∈ disjointBudgetSet S w := by
      refine ⟨fun i => ?_, fun ℓ' => ?_⟩
      · unfold BudgetedAffine.Budget.indic
        split_ifs <;> simp
      · obtain ⟨k', rfl⟩ := σ.surjective ℓ'
        rcases lt_trichotomy k' ℓ with hlt | heq | hgt
        · refine key k' (a k') (fun i hiS hiH => ?_) (ha1 k').2
          rcases (hH i).1 hiH with ⟨k, -, hik⟩ | hiW
          · have := hsame i k k' (haS k hik) hiS
            subst this; exact hik
          · exact absurd (hsame i ℓ k' (hWS hiW) hiS) (ne_of_gt hlt)
        · subst heq
          refine key k' W (fun i hiS hiH => ?_) hWw
          rcases (hH i).1 hiH with ⟨k, hk, hik⟩ | hiW
          · have := hsame i k k' (haS k hik) hiS
            subst this; exact absurd hk (lt_irrefl _)
          · exact hiW
        · refine key k' ∅ (fun i hiS hiH => ?_) (by simp)
          exfalso
          rcases (hH i).1 hiH with ⟨k, hk, hik⟩ | hiW
          · have := hsame i k k' (haS k hik) hiS
            subst this
            exact absurd (lt_trans hk hgt) (lt_irrefl _)
          · exact absurd (hsame i ℓ k' (hWS hiW) hiS) (ne_of_lt hgt)
    obtain ⟨hy0, hycov⟩ := hfeas.2 _ hU
    have hcov : BudgetedAffine.Budget.indic H ≤ (Btil A B xs) *ᵥ ys (BudgetedAffine.Budget.indic H) := by
      intro i
      by_cases hi : i ∈ H
      · have hα := hHα i hi
        have h1 : BudgetedAffine.Budget.indic H i = 1 := by simp [BudgetedAffine.Budget.indic, hi]
        have h2 := hycov i
        rw [Pi.add_apply, h1] at h2
        rw [Btil_row A B xs _ i hα, h1, le_div_iff₀ hα]
        have : α i = 1 - (A *ᵥ xs) i := rfl
        linarith
      · have h1 : BudgetedAffine.Budget.indic H i = 0 := by simp [BudgetedAffine.Budget.indic, hi]
        rw [h1]
        exact mulVec_nonneg' (Btil A B xs) hBtnn _ hy0 i
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (iInf₂_le _ ⟨hy0, hcov⟩)
  -- the sets `V_ℓ`
  set V : Fin L → Finset (Fin m) := fun ℓ => Finset.univ.filter
    (fun i => i ∉ I ∧ 0 < α i ∧ ((Btil A B xs) *ᵥ yA) i < 1 / 2 ∧ i ∈ S (σ ℓ)) with hVdef
  -- condition 2 of Lemma 3.3
  have hcond2 : ∀ (ℓ : Fin L) (W : Finset (Fin m)), W ⊆ V ℓ → ∑ i ∈ W, w (σ ℓ) i ≤ 1 →
      BudgetedAffine.Budget.coverCost (Btil A B xs) d (BudgetedAffine.Budget.indic W) ≤
        ((2 * Δ ℓ : ℝ) : EReal) := by
    intro ℓ W hWV hWw
    have hWh : W ⊆ hatS S A xs (σ ℓ) := by
      intro i hi
      obtain ⟨-, hα, -, hiS⟩ := (Finset.mem_filter.1 (hWV hi)).2
      exact Finset.mem_filter.2 ⟨hiS, hα⟩
    set s0 := seqPrefix a ℓ.val with hs0
    set y1 := alg.sol (s0 ++ [W]) with hy1
    set y0 := alg.sol s0 with hy0
    have hcovW := alg.covers (s0 ++ [W]) (hcoverable ℓ W hWh hWw) W (by simp)
    have hm1 : y0 ≤ yA := sol_mono alg a (show ℓ.val ≤ L from ℓ.isLt.le)
    have hm2 : y0 ≤ y1 := alg.mono s0 W
    have hyo : 0 ≤ (2:ℝ) • (y1 - y0) := fun j => by
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
      linarith [hm2 j]
    have hfe : 0 ≤ (2:ℝ) • (y1 - y0) ∧
        BudgetedAffine.Budget.indic W ≤ (Btil A B xs) *ᵥ ((2:ℝ) • (y1 - y0)) := by
      refine ⟨hyo, fun i => ?_⟩
      by_cases hi : i ∈ W
      · have h1 : BudgetedAffine.Budget.indic W i = 1 := by simp [BudgetedAffine.Budget.indic, hi]
        rw [h1, Matrix.mulVec_smul, Matrix.mulVec_sub]
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        have ha' := hcovW i hi
        have hb := mulVec_mono' (Btil A B xs) hBtnn y0 yA hm1 i
        have hc' := (Finset.mem_filter.1 (hWV hi)).2.2.2.1
        linarith
      · have h1 : BudgetedAffine.Budget.indic W i = 0 := by simp [BudgetedAffine.Budget.indic, hi]
        rw [h1]
        exact mulVec_nonneg' (Btil A B xs) hBtnn _ hyo i
    have hgr := ha.2 ℓ (σ ℓ) (fun k hk e => absurd (σ.injective e ▸ hk) (lt_irrefl _)) W hWh hWw
    have haug : alg.augCost s0 (a ℓ) = Δ ℓ := by
      rw [hΔ]
      unfold nuInc nu OnlineCover.augCost OnlineCover.cost
      rw [prefix_succ]
    refine le_trans (iInf₂_le ((2:ℝ) • (y1 - y0)) hfe) ?_
    have : d ⬝ᵥ ((2:ℝ) • (y1 - y0)) = 2 * alg.augCost s0 W := by
      unfold OnlineCover.augCost OnlineCover.cost
      rw [dotProduct_smul, dotProduct_sub, smul_eq_mul]
    rw [this]
    exact_mod_cast (by linarith : 2 * alg.augCost s0 W ≤ 2 * Δ ℓ)
  -- Lemma 3.3 on each block
  have hVbound : ∀ ℓ, BudgetedAffine.Budget.coverCost (Btil A B xs) d (BudgetedAffine.Budget.indic (V ℓ)) ≤
      ((beta8 n * Δ ℓ : ℝ) : EReal) := by
    intro ℓ
    have hbase : ∀ i ∈ V ℓ, ((w (σ ℓ) i * beta8 n * Δ ℓ : ℝ) : EReal) <
        BudgetedAffine.Budget.coverCost (Btil A B xs) d (Pi.single i 1) := by
      intro i hi
      obtain ⟨hiI, hα, -, hiS⟩ := (Finset.mem_filter.1 hi).2
      have hnot : ¬ (((α i : ℝ) : EReal) * BudgetedAffine.Budget.coverCost B d (Pi.single i 1) ≤
          ((w (σ ℓ) i * beta8 n * Δ ℓ : ℝ) : EReal)) := fun hle =>
        hiI (Finset.mem_filter.2 ⟨Finset.mem_univ _, ℓ, hiS, hα, hle⟩)
      exact theta_gt A B xs d hB hd i hα _ (not_le.1 hnot)
    rcases (hΔ0 ℓ).eq_or_lt with h0 | hpos
    · have hVe : V ℓ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro i hi
        have h1 := hbase i hi
        have h2 := hcond2 ℓ {i} (by simpa using hi) (by simpa using (hw (σ ℓ) i).2)
        rw [indic_single, ← h0] at h2
        rw [← h0] at h1
        simp only [mul_zero] at h1 h2
        exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
      rw [hVe, ← h0, mul_zero]
      exact_mod_cast coverCost_empty (Btil A B xs) d
    · set γ := 2 * Δ ℓ with hγ
      have hγ0 : 0 < γ := by positivity
      set Z := (V ℓ).filter (fun i => w (σ ℓ) i = 0) with hZ
      obtain ⟨t, ht0, ht⟩ := exists_pos_lt_all Z
        (fun i => BudgetedAffine.Budget.coverCost (Btil A B xs) d (Pi.single i 1)) (by
          intro i hi
          obtain ⟨hiV, hw0⟩ := Finset.mem_filter.1 hi
          have := hbase i hiV
          rw [hw0, zero_mul, zero_mul] at this
          exact_mod_cast this)
      set ε0 := min 1 (t / (4 * γ * r)) with hε0
      have hε0pos : 0 < ε0 := lt_min one_pos (by positivity)
      have hε0le : ε0 ≤ 1 := min_le_left _ _
      have hε0t : 4 * γ * r * ε0 ≤ t := by
        have h1 : ε0 ≤ t / (4 * γ * r) := min_le_right _ _
        have h2 : 0 < 4 * γ * r := by positivity
        calc 4 * γ * r * ε0 ≤ 4 * γ * r * (t / (4 * γ * r)) := mul_le_mul_of_nonneg_left h1 h2.le
          _ = t := by field_simp
      set w' : Fin m → ℝ := fun i => if w (σ ℓ) i = 0 then ε0 else w (σ ℓ) i with hw'
      have hww' : ∀ i, w (σ ℓ) i ≤ w' i := by
        intro i
        simp only [hw']
        split_ifs with h
        · rw [h]; exact hε0pos.le
        · exact le_rfl
      have hw'b : ∀ i ∈ V ℓ, 0 < w' i ∧ w' i ≤ 1 := by
        intro i _
        simp only [hw']
        split_ifs with h
        · exact ⟨hε0pos, hε0le⟩
        · exact ⟨lt_of_le_of_ne (hw _ _).1 (Ne.symm h), (hw _ _).2⟩
      have hc1 : ∀ i ∈ V ℓ, ((4 * γ * r * w' i : ℝ) : EReal) <
          BudgetedAffine.Budget.coverCost (Btil A B xs) d (Pi.single i 1) := by
        intro i hi
        by_cases h : w (σ ℓ) i = 0
        · have : w' i = ε0 := by simp [hw', h]
          rw [this]
          exact lt_of_le_of_lt (by exact_mod_cast hε0t) (ht i (Finset.mem_filter.2 ⟨hi, h⟩))
        · have : w' i = w (σ ℓ) i := by simp [hw', h]
          rw [this]
          have e : 4 * γ * r * w (σ ℓ) i = w (σ ℓ) i * beta8 n * Δ ℓ := by
            rw [hγ, hβeq]; ring
          rw [e]
          exact hbase i hi
      have hc2 : ∀ W ⊆ V ℓ, ∑ i ∈ W, w' i ≤ 1 →
          BudgetedAffine.Budget.coverCost (Btil A B xs) d (BudgetedAffine.Budget.indic W) ≤ (γ : EReal) := by
        intro W hW hWw
        exact hcond2 ℓ W hW (le_trans (Finset.sum_le_sum (fun i _ => hww' i)) hWw)
      have := hN₀ n hnN m (Btil A B xs) d (V ℓ) γ w' hBtnn hd hγ0 hw'b hc1 hc2
      refine le_trans this (le_of_eq ?_)
      congr 1
      rw [hγ, hβeq]; ring
  -- final ε-argument
  have hmain : ∀ δ : ℝ, 0 < δ →
      BudgetedAffine.Budget.staticValue A B c d X (BudgetedAffine.Budget.staRhs I α) ≤
        (((1 + 2 * ρ + beta8 n * ρ) * OPT + L * δ : ℝ) : EReal) := by
    intro δ hδ
    have hex : ∀ ℓ, ∃ y : Fin n → ℝ, (0 ≤ y ∧ BudgetedAffine.Budget.indic (V ℓ) ≤ (Btil A B xs) *ᵥ y) ∧
        d ⬝ᵥ y < beta8 n * Δ ℓ + δ := by
      intro ℓ
      have h1 : BudgetedAffine.Budget.coverCost (Btil A B xs) d (BudgetedAffine.Budget.indic (V ℓ)) <
          ((beta8 n * Δ ℓ + δ : ℝ) : EReal) :=
        lt_of_le_of_lt (hVbound ℓ) (by exact_mod_cast (by linarith : beta8 n * Δ ℓ < beta8 n * Δ ℓ + δ))
      unfold BudgetedAffine.Budget.coverCost at h1
      rw [iInf_lt_iff] at h1
      obtain ⟨y, hy⟩ := h1
      rw [iInf_lt_iff] at hy
      obtain ⟨hyf, hylt⟩ := hy
      exact ⟨y, hyf, by exact_mod_cast hylt⟩
    choose yl hylf hylt using hex
    set ySt : Fin n → ℝ := ys 0 + (2:ℝ) • yA + ∑ ℓ, yl ℓ with hySt
    have hyl0 : ∀ ℓ, 0 ≤ yl ℓ := fun ℓ => (hylf ℓ).1
    have hySt0 : 0 ≤ ySt :=
      add_nonneg (add_nonneg hys0 (smul_nonneg zero_le_two hyA0))
        (Finset.sum_nonneg (fun ℓ _ => hyl0 ℓ))
    have hBy : ∀ i, (B *ᵥ ySt) i = (B *ᵥ ys 0) i + 2 * (B *ᵥ yA) i + ∑ ℓ, (B *ᵥ yl ℓ) i := by
      intro i
      simp only [hySt, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sum, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    have hfeasSt : 0 ≤ ySt ∧ BudgetedAffine.Budget.staRhs I α ≤ A *ᵥ xs + B *ᵥ ySt := by
      refine ⟨hySt0, fun i => ?_⟩
      rw [Pi.add_apply, hBy i]
      have hαi : α i = 1 - (A *ᵥ xs) i := rfl
      have hB0 : 0 ≤ (B *ᵥ ys 0) i := mulVec_nonneg' B hB _ hys0 i
      have hBA : 0 ≤ (B *ᵥ yA) i := mulVec_nonneg' B hB _ hyA0 i
      have hBl : 0 ≤ ∑ ℓ, (B *ᵥ yl ℓ) i :=
        Finset.sum_nonneg (fun ℓ _ => mulVec_nonneg' B hB _ (hyl0 ℓ) i)
      have hc0 := hcov0 i
      simp only [Pi.zero_apply, Pi.add_apply] at hc0
      by_cases hiI : i ∈ I
      · have hst : BudgetedAffine.Budget.staRhs I α i = max (1 - α i) 0 := by
          simp [BudgetedAffine.Budget.staRhs, hiI]
        rw [hst]
        refine max_le ?_ ?_ <;> linarith
      · have hst : BudgetedAffine.Budget.staRhs I α i = 1 := by
          simp [BudgetedAffine.Budget.staRhs, hiI]
        rw [hst]
        by_cases hα : 0 < α i
        · have hrow := Btil_row A B xs yA i hα
          by_cases hhalf : ((Btil A B xs) *ᵥ yA) i < 1 / 2
          · have hiV : i ∈ V (g i) := Finset.mem_filter.2
              ⟨Finset.mem_univ _, hiI, hα, hhalf, hg i⟩
            have h1 := (hylf (g i)).2 i
            have h1' : BudgetedAffine.Budget.indic (V (g i)) i = 1 := by
              simp [BudgetedAffine.Budget.indic, hiV]
            rw [h1', Btil_row A B xs _ i hα, le_div_iff₀ hα, one_mul] at h1
            have h2 : (B *ᵥ yl (g i)) i ≤ ∑ ℓ, (B *ᵥ yl ℓ) i :=
              Finset.single_le_sum (f := fun ℓ => (B *ᵥ yl ℓ) i)
                (fun ℓ _ => mulVec_nonneg' B hB _ (hyl0 ℓ) i) (Finset.mem_univ _)
            linarith
          · push_neg at hhalf
            rw [hrow, le_div_iff₀ hα] at hhalf
            linarith
        · push_neg at hα
          linarith
    have hreal : c ⬝ᵥ xs + d ⬝ᵥ ySt ≤ (1 + 2 * ρ + beta8 n * ρ) * OPT + L * δ := by
      have hd1 : d ⬝ᵥ ySt = d ⬝ᵥ ys 0 + 2 * (d ⬝ᵥ yA) + ∑ ℓ, d ⬝ᵥ yl ℓ := by
        simp only [hySt, dotProduct_add, dotProduct_smul, dotProduct_sum, smul_eq_mul]
      have hsum : ∑ ℓ, d ⬝ᵥ yl ℓ ≤ beta8 n * nu alg a L + L * δ := by
        calc ∑ ℓ, d ⬝ᵥ yl ℓ ≤ ∑ ℓ : Fin L, (beta8 n * Δ ℓ + δ) :=
              Finset.sum_le_sum (fun ℓ _ => (hylt ℓ).le)
          _ = beta8 n * nu alg a L + L * δ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, hΔ, sum_nuInc alg a]
              simp
      have hb1 : beta8 n * nu alg a L ≤ beta8 n * (ρ * OPT) := mul_le_mul_of_nonneg_left h41 hβ0
      rw [hd1]
      rw [hnuL] at h41 hsum hb1
      nlinarith
    calc BudgetedAffine.Budget.staticValue A B c d X (BudgetedAffine.Budget.staRhs I α)
        ≤ ((c ⬝ᵥ xs + d ⬝ᵥ ySt : ℝ) : EReal) :=
          le_trans (iInf₂_le xs hfeas.1) (iInf₂_le ySt hfeasSt)
      _ ≤ (((1 + 2 * ρ + beta8 n * ρ) * OPT + L * δ : ℝ) : EReal) := by exact_mod_cast hreal
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hx1, hx2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hx1' : (1 + 2 * ρ + beta8 n * ρ) * OPT < x := by exact_mod_cast hx1
  set K := (1 + 2 * ρ + beta8 n * ρ) * OPT
  have hL : (0:ℝ) ≤ L := Nat.cast_nonneg L
  have hδ : 0 < (x - K) / (L + 1) := div_pos (by linarith) (by linarith)
  have h1 := hmain _ hδ
  have h2 : K + L * ((x - K) / (L + 1)) ≤ x := by
    have : L * ((x - K) / (L + 1)) ≤ x - K := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have := lt_of_le_of_lt (le_trans h1 (by exact_mod_cast h2)) hx2
  exact lt_irrefl _ this
