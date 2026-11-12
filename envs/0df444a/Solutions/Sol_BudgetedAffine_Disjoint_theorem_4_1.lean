-- Prove2me | solution 1 for BudgetedAffine.Disjoint.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:18:40.050305+00:00
-- url     : https://prove2.me/submissions/f8447c27-eb6e-46f4-a911-ae03f05e10ab

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction
import Theorems.Thm_BudgetedAffine_Disjoint_lemma_4_2
import Theorems.Thm_BudgetedAffine_Disjoint_lemma_4_3
import Theorems.Thm_BudgetedAffine_Disjoint_lemma_4_4
import Theorems.Thm_BudgetedAffine_Disjoint_online_cover_exists
import Theorems.Thm_BudgetedAffine_Disjoint_greedy_run_exists
import Theorems.Thm_BudgetedAffine_Disjoint_zAR_attained
import Theorems.Thm_BudgetedAffine_Budget_coverCost_attained
import Theorems.Thm_BudgetedAffine_Budget_staticValue_attained

set_option autoImplicit false
open Matrix BudgetedAffine.Disjoint

namespace AffDisj41

theorem linMatrix_mulVec {m n : ℕ} (I : Finset (Fin m)) (α : Fin m → ℝ) (v : Fin m → Fin n → ℝ)
    (h : Fin m → ℝ) : BudgetedAffine.Budget.linMatrix I α v *ᵥ h = BudgetedAffine.Budget.yLin I α v h := by
  funext j
  simp only [BudgetedAffine.Budget.yLin, mulVec, dotProduct, BudgetedAffine.Budget.linMatrix,
    Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun i => i ∈ I) = I := by ext; simp
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem log_facts (n : ℕ) (hn : 3 ≤ n) :
    1 < Real.log n ∧ 0 < Real.log (Real.log n) ∧ Real.log (Real.log n) < Real.log n := by
  have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  refine ⟨hlog, Real.log_pos hlog, ?_⟩
  have := Real.log_le_sub_one_of_pos (show 0 < Real.log n by linarith)
  linarith

end AffDisj41

open AffDisj41 in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m L : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
      (c d : Fin n → ℝ) (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m))
      (w : Fin L → Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → BudgetedAffine.Budget.IsPolyhedral X →
      (∀ x ∈ X, 0 ≤ c ⬝ᵥ x) → IsPartition S → (∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1) →
      BudgetedAffine.Budget.zAff A B c d X (disjointBudgetSet S w) ≤
        ((C * (Real.log n ^ 2 / Real.log (Real.log n)) : ℝ) : EReal) *
          BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) := by
  classical
  obtain ⟨K, hK, N1, hN1⟩ := BudgetedAffine.Disjoint.online_cover_exists
  obtain ⟨N2, hN2⟩ := BudgetedAffine.Disjoint.lemma_4_4
  refine ⟨1 + 18 * K, by linarith, max N1 (max N2 3), ?_⟩
  intro n hn m L A B c d X S w hB hc hd hX hcX hS hw
  have hn1 : n ≥ N1 := le_trans (le_max_left _ _) hn
  have hn2 : n ≥ N2 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hl1, hll0, hlll⟩ := log_facts n hn3
  set U := disjointBudgetSet S w with hU
  set q := Real.log n ^ 2 / Real.log (Real.log n) with hq
  have hq_ge_log : Real.log n ≤ q := by
    rw [hq, le_div_iff₀ hll0]
    nlinarith
  have hq1 : 1 ≤ q := by linarith
  have hCq : 0 < (1 + 18 * K) * q := by positivity
  by_cases htop : BudgetedAffine.Budget.zAR A B c d X U = ⊤
  · rw [htop, EReal.coe_mul_top_of_pos hCq]
    exact le_top
  obtain ⟨xs, ys, hopt⟩ := BudgetedAffine.Disjoint.zAR_attained A B c d X S w hB hc hd hX hcX hS hw htop
  have h0U : (0 : Fin m → ℝ) ∈ U := ⟨fun i => ⟨le_rfl, zero_le_one⟩, fun ℓ => by simp⟩
  have hge0 : (0 : EReal) ≤ BudgetedAffine.Budget.zAR A B c d X U := by
    rw [← hopt.2]
    unfold BudgetedAffine.Budget.worstCost
    refine le_iSup₂_of_le (0 : Fin m → ℝ) h0U ?_
    have := hcX xs hopt.1.1
    have := dotProduct_nonneg_of_nonneg hd (hopt.1.2 0 h0U).1
    exact_mod_cast (by linarith : (0:ℝ) ≤ c ⬝ᵥ xs + d ⬝ᵥ ys 0)
  obtain ⟨OPT, hOPT⟩ : ∃ OPT : ℝ, BudgetedAffine.Budget.zAR A B c d X U = (OPT : EReal) :=
    ⟨_, (EReal.coe_toReal htop (ne_bot_of_le_ne_bot (by simp) hge0)).symm⟩
  have hOPT0 : 0 ≤ OPT := by rw [hOPT] at hge0; exact_mod_cast hge0
  -- online algorithm
  have hBtnn : ∀ i j, 0 ≤ Btil A B xs i j := by
    intro i j
    unfold Btil
    simp only [Matrix.of_apply]
    split_ifs with h
    · exact div_nonneg (hB i j) h.le
    · exact hB i j
  set ρ := K * Real.log n with hρdef
  have hρ : 0 ≤ ρ := by positivity
  obtain ⟨alg⟩ := hN1 n hn1 m (Btil A B xs) d hBtnn hd
  obtain ⟨σ, a, ha⟩ := BudgetedAffine.Disjoint.greedy_run_exists alg w (hatS S A xs)
  set I := Iset A B d S w xs σ (nuInc alg a) with hI
  set α := BudgetedAffine.Budget.alpha A xs with hα
  -- optimal covers of `eᵢ`, `i ∈ I`
  have hvex : ∀ i ∈ I, ∃ y, BudgetedAffine.Budget.IsCoverOpt B d (Pi.single i 1) y := by
    intro i hi
    obtain ⟨ℓ, -, hpos, hle⟩ := (Finset.mem_filter.1 hi).2
    refine BudgetedAffine.Budget.coverCost_attained B d _ hd (fun htop' => ?_)
    rw [htop', EReal.coe_mul_top_of_pos hpos] at hle
    exact absurd (top_le_iff.1 hle) (EReal.coe_ne_top _)
  set v : Fin m → Fin n → ℝ := fun i => if hi : i ∈ I then (hvex i hi).choose else 0 with hvdef
  have hv : ∀ i ∈ I, BudgetedAffine.Budget.IsCoverOpt B d (Pi.single i 1) (v i) := by
    intro i hi
    simp only [hvdef, dif_pos hi]
    exact (hvex i hi).choose_spec
  -- static part
  have h44 := hN2 n hn2 m L A B c d X S w hB hc hd hX hcX hS hw xs ys hopt OPT hOPT ρ hρ alg σ a ha
  obtain ⟨xSta, ySta, hSta⟩ := BudgetedAffine.Budget.staticValue_attained A B c d X
    (BudgetedAffine.Budget.staRhs I α) hX hd hcX
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) h44)
  have hfeas := BudgetedAffine.Disjoint.lemma_4_2 A B c d X S w hB hc hd hX hcX hS hw xs ys hopt
    OPT hOPT ρ hρ alg σ a ha v hv xSta ySta hSta
  have h43 := BudgetedAffine.Disjoint.lemma_4_3 A B c d X S w hB hc hd hX hcX hS hw xs ys hopt
    OPT hOPT ρ hρ alg σ a ha hn3 v hv
  have hStaV : c ⬝ᵥ xSta + d ⬝ᵥ ySta ≤ (1 + 2 * ρ + beta8 n * ρ) * OPT := by
    have := hSta.2.2.2
    rw [← this] at h44
    exact_mod_cast h44
  have hβ : beta8 n = 8 * (Real.log n / Real.log (Real.log n)) := by unfold beta8; ring
  -- the final real bound
  have hfinal : ∀ h ∈ U, c ⬝ᵥ xSta + d ⬝ᵥ (BudgetedAffine.Budget.linMatrix I α v *ᵥ h + ySta) ≤
      (1 + 18 * K) * q * OPT := by
    intro h hh
    rw [dotProduct_add, linMatrix_mulVec]
    have hl := h43 h hh
    have e1 : beta8 n * ρ = 8 * K * q := by
      rw [hβ, hρdef, hq]; field_simp
    have e2 : 2 * ρ ≤ 2 * K * q := by
      rw [hρdef]; nlinarith
    have : (1 + 2 * ρ + beta8 n * ρ) * OPT + beta8 n * ρ * OPT ≤ (1 + 18 * K) * q * OPT := by
      rw [e1]
      have : 1 + 2 * ρ + 8 * K * q + 8 * K * q ≤ (1 + 18 * K) * q := by nlinarith
      nlinarith
    linarith
  calc BudgetedAffine.Budget.zAff A B c d X U
      ≤ BudgetedAffine.Budget.worstCost c d U xSta
          (fun h => BudgetedAffine.Budget.linMatrix I α v *ᵥ h + ySta) := by
        unfold BudgetedAffine.Budget.zAff
        exact le_trans (iInf_le _ xSta) (le_trans (iInf_le _ (BudgetedAffine.Budget.linMatrix I α v))
          (le_trans (iInf_le _ ySta) (iInf_le _ hfeas)))
    _ ≤ (((1 + 18 * K) * q * OPT : ℝ) : EReal) := by
        unfold BudgetedAffine.Budget.worstCost
        exact iSup₂_le (fun h hh => by exact_mod_cast hfinal h hh)
    _ = (((1 + 18 * K) * q : ℝ) : EReal) * BudgetedAffine.Budget.zAR A B c d X U := by
        rw [hOPT, ← EReal.coe_mul]
