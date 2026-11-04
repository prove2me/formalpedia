-- Prove2me | solution 1 for BudgetedAffine.Budget.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:26:41.237063+00:00
-- url     : https://prove2.me/submissions/bae6fb19-927b-49c7-913c-bec16bf06475

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Theorems.Thm_BudgetedAffine_Budget_lemma_3_1
import Theorems.Thm_BudgetedAffine_Budget_lemma_3_2
import Theorems.Thm_BudgetedAffine_Budget_lemma_3_4
import Theorems.Thm_BudgetedAffine_Budget_coverCost_attained
import Theorems.Thm_BudgetedAffine_Budget_staticValue_attained
import Theorems.Thm_BudgetedAffine_Disjoint_zAR_attained

open Matrix BudgetedAffine.Budget

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
      (c d : Fin n → ℝ) (X : Set (Fin n → ℝ)) (w : Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → IsPolyhedral X →
      (∀ x ∈ X, 0 ≤ c ⬝ᵥ x) → (∀ i, 0 ≤ w i ∧ w i ≤ 1) →
      zAff A B c d X (budgetSet w) ≤
        ((C * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) *
          zAR A B c d X (budgetSet w) := by
  obtain ⟨C, hC, N, hN⟩ := lemma_3_4
  refine ⟨4 * (C + 1), by linarith, max N 3, ?_⟩
  intro n hn m A B c d X w hB hc hd hX hcX hw
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  have hnN : n ≥ N := le_of_max_le_left hn
  -- positivity of log n / log log n
  have hlog1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have := Real.exp_one_lt_d9
    linarith
  have hloglog : 0 < Real.log (Real.log n) := Real.log_pos hlog1
  have hL : 0 < Real.log n / Real.log (Real.log n) := div_pos (by linarith) hloglog
  have hK : 0 < 4 * (C + 1) * (Real.log n / Real.log (Real.log n)) := by
    have : 0 < 4 * (C + 1) := by linarith
    positivity
  set U := budgetSet w with hU
  by_cases htop : zAR A B c d X U = ⊤
  · rw [htop, EReal.coe_mul_top_of_pos hK]
    exact le_top
  -- attainment of the adjustable problem (budget set = disjoint budgeted set with one block)
  have hUeq : U = BudgetedAffine.Disjoint.disjointBudgetSet
      (fun _ : Fin 1 => (Finset.univ : Finset (Fin m))) (fun _ => w) := by
    ext h; simp [hU, budgetSet, BudgetedAffine.Disjoint.disjointBudgetSet]
  have hpart : BudgetedAffine.Disjoint.IsPartition
      (fun _ : Fin 1 => (Finset.univ : Finset (Fin m))) := by
    refine ⟨fun l l' hll' => absurd (Subsingleton.elim l l') hll', fun i => ⟨0, by simp⟩⟩
  obtain ⟨xs, ys, hopt⟩ := BudgetedAffine.Disjoint.zAR_attained A B c d X
    (fun _ : Fin 1 => (Finset.univ : Finset (Fin m))) (fun _ => w) hB hc hd hX hcX hpart
    (fun _ i => hw i) (by rw [← hUeq]; exact htop)
  rw [← hUeq] at hopt
  -- zAR ≥ 0
  have h0U : (0 : Fin m → ℝ) ∈ U := by
    simp [hU, budgetSet]
  have hnonneg : (0 : EReal) ≤ zAR A B c d X U := by
    rw [← hopt.2]
    have hf := hopt.1
    have h1 : (0 : ℝ) ≤ c ⬝ᵥ xs + d ⬝ᵥ ys 0 := by
      have := hcX xs hf.1
      have := dotProduct_nonneg_of_nonneg hd (hf.2 0 h0U).1
      linarith
    unfold worstCost
    exact le_trans (by exact_mod_cast h1) (le_biSup (fun h => ((c ⬝ᵥ xs + d ⬝ᵥ ys h : ℝ) : EReal)) h0U)
  have hbot : zAR A B c d X U ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hnonneg
  set OPT := (zAR A B c d X U).toReal with hOPTdef
  have hOPT : zAR A B c d X U = (OPT : EReal) := (EReal.coe_toReal htop hbot).symm
  have hOPT0 : 0 ≤ OPT := by
    have : ((0:ℝ) : EReal) ≤ (OPT : EReal) := by rw [← hOPT]; simpa using hnonneg
    exact_mod_cast this
  -- static part
  have hsta := hN n hnN m A B c d X w hB hc hd hX hcX hw xs ys hopt OPT hOPT
  set I := Iset A B d w xs OPT with hI
  have hstafin : staticValue A B c d X (staRhs I (alpha A xs)) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hsta
  obtain ⟨xSta, ySta, hSO⟩ := staticValue_attained A B c d X (staRhs I (alpha A xs)) hX hd hcX
    hstafin
  -- optimal covers of the unit vectors
  classical
  let v : Fin m → Fin n → ℝ := fun i =>
    if hi : coverCost B d (Pi.single i 1) ≠ ⊤ then
      Classical.choose (coverCost_attained B d (Pi.single i 1) hd hi) else 0
  have hv : ∀ i ∈ I, IsCoverOpt B d (Pi.single i 1) (v i) := by
    intro i hiI
    have hi : coverCost B d (Pi.single i 1) ≠ ⊤ := by
      intro htop'
      have hmem := hiI
      rw [hI, Iset, Finset.mem_filter] at hmem
      obtain ⟨_, hpos, hle⟩ := hmem
      rw [htop', EReal.coe_mul_top_of_pos hpos] at hle
      exact EReal.coe_ne_top _ (top_le_iff.mp hle)
    simp only [v, dif_pos hi]
    exact Classical.choose_spec (coverCost_attained B d (Pi.single i 1) hd hi)
  have hfeas := lemma_3_1 A B c d X w hB hc hd hX hcX hw xs ys hopt OPT hOPT v hv xSta ySta hSO
  have hlin := lemma_3_2 hn3 A B c d X w hB hc hd hX hcX hw xs ys hopt OPT hOPT v hv
  -- P h = y_Lin(h)
  have hPh : ∀ h : Fin m → ℝ, linMatrix I (alpha A xs) v *ᵥ h = yLin I (alpha A xs) v h := by
    intro h
    funext j
    simp only [mulVec, dotProduct, linMatrix, yLin, Matrix.of_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ I)]
    have h2 : ∑ x ∈ Finset.univ.filter (fun i => i ∉ I),
        (if x ∈ I then alpha A xs x * v x j else 0) * h x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_filter] at hx
      simp [hx.2]
    rw [h2, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos hx]; ring
  -- bound the worst-case cost of the affine solution
  have hstatic_val : c ⬝ᵥ xSta + d ⬝ᵥ ySta ≤ C * beta n * OPT := by
    have : ((c ⬝ᵥ xSta + d ⬝ᵥ ySta : ℝ) : EReal) ≤ ((C * beta n * OPT : ℝ) : EReal) := by
      rw [hSO.2.2.2]; exact hsta
    exact_mod_cast this
  have hwc : worstCost c d U xSta (fun h => linMatrix I (alpha A xs) v *ᵥ h + ySta) ≤
      (((C + 1) * beta n * OPT : ℝ) : EReal) := by
    unfold worstCost
    refine iSup₂_le fun h hh => ?_
    have := hlin h hh
    show ((c ⬝ᵥ xSta + d ⬝ᵥ (linMatrix I (alpha A xs) v *ᵥ h + ySta) : ℝ) : EReal) ≤ _
    rw [hPh h, dotProduct_add]
    have key : c ⬝ᵥ xSta + (d ⬝ᵥ yLin I (alpha A xs) v h + d ⬝ᵥ ySta) ≤
        (C + 1) * beta n * OPT := by linarith
    exact_mod_cast key
  have hzAff : zAff A B c d X U ≤ worstCost c d U xSta
      (fun h => linMatrix I (alpha A xs) v *ᵥ h + ySta) := by
    unfold zAff
    exact le_trans (iInf_le _ xSta) (le_trans (iInf_le _ (linMatrix I (alpha A xs) v))
      (le_trans (iInf_le _ ySta) (iInf_le _ hfeas)))
  rw [hOPT, ← EReal.coe_mul]
  refine le_trans hzAff (le_trans hwc (le_of_eq ?_))
  congr 1
  unfold beta
  ring
