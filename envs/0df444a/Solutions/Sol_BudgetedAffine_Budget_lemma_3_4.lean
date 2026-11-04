-- Prove2me | solution 1 for BudgetedAffine.Budget.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:30:21.7827+00:00
-- url     : https://prove2.me/submissions/8c7ff432-6e15-4056-a8b5-453e46118a85

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Theorems.Thm_BudgetedAffine_Budget_lemma_3_3
import Theorems.Thm_BudgetedAffine_Budget_coverCost_attained

open Matrix BudgetedAffine.Budget

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ)
      (c d : Fin n → ℝ) (X : Set (Fin n → ℝ)) (w : Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ c → 0 ≤ d → IsPolyhedral X →
      (∀ x ∈ X, 0 ≤ c ⬝ᵥ x) → (∀ i, 0 ≤ w i ∧ w i ≤ 1) →
      ∀ (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ),
      IsOptimalAR A B c d X (budgetSet w) xs ys →
      ∀ OPT : ℝ, zAR A B c d X (budgetSet w) = (OPT : EReal) →
      staticValue A B c d X (staRhs (Iset A B d w xs OPT) (alpha A xs)) ≤
        ((C * beta n * OPT : ℝ) : EReal) := by
  classical
  obtain ⟨N₀, hN₀⟩ := lemma_3_3
  refine ⟨2, by norm_num, max N₀ 3, ?_⟩
  intro n hn m A B c d X w hB hc hd hX hcX hw xs ys hopt OPT hOPT
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  have hnN : n ≥ N₀ := le_of_max_le_left hn
  have hlog1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have := Real.exp_one_lt_d9
    linarith
  have hloglog : 0 < Real.log (Real.log n) := Real.log_pos hlog1
  have hll : Real.log (Real.log n) < Real.log n := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log n by linarith)
    linarith
  have hbeta : 1 ≤ beta n := by
    unfold beta
    rw [le_div_iff₀ hloglog]
    linarith
  set U := budgetSet w with hU
  set α := alpha A xs with hα
  set I := Iset A B d w xs OPT with hI
  have hfeas := hopt.1
  have hxs : xs ∈ X := hfeas.1
  -- membership of indicator vectors in U
  have hindU : ∀ W : Finset (Fin m), ∑ i ∈ W, w i ≤ 1 → indic W ∈ U := by
    intro W hW
    refine ⟨fun i => ?_, ?_⟩
    · unfold indic; split_ifs <;> norm_num
    · have : ∑ i, w i * indic W i = ∑ i ∈ W, w i := by
        unfold indic
        simp [mul_ite, Finset.sum_ite_mem]
      rw [this]; exact hW
  -- the cost of any scenario is at most OPT
  have hcostU : ∀ h ∈ U, c ⬝ᵥ xs + d ⬝ᵥ ys h ≤ OPT := by
    intro h hh
    have h1 : ((c ⬝ᵥ xs + d ⬝ᵥ ys h : ℝ) : EReal) ≤ worstCost c d U xs ys :=
      le_biSup (fun h => ((c ⬝ᵥ xs + d ⬝ᵥ ys h : ℝ) : EReal)) hh
    rw [hopt.2, hOPT] at h1
    exact_mod_cast h1
  have hOPT0 : 0 ≤ OPT := by
    have h0 : (0 : Fin m → ℝ) ∈ U := by simp [hU, budgetSet]
    have := hcostU 0 h0
    have := hcX xs hxs
    have := dotProduct_nonneg_of_nonneg hd (hfeas.2 0 h0).1
    linarith
  -- row coverage from feasibility: (B y*(h))_i ≥ h_i - (A x*)_i
  have hAx : ∀ i, (A *ᵥ xs) i = 1 - α i := by intro i; simp [hα, alpha]
  have hrow : ∀ h ∈ U, ∀ i, h i - (1 - α i) ≤ (B *ᵥ ys h) i := by
    intro h hh i
    have := (hfeas.2 h hh).2 i
    simp only [Pi.add_apply] at this
    rw [hAx i] at this
    linarith
  have hBnn : ∀ y : Fin n → ℝ, 0 ≤ y → ∀ i, 0 ≤ (B *ᵥ y) i := by
    intro y hy i
    simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hB i j) (hy j)
  -- the index sets
  set J2p : Finset (Fin m) := Finset.univ.filter (fun i => 0 < α i ∧ i ∉ I ∧ 0 < w i) with hJ2p
  set K0 : Finset (Fin m) := Finset.univ.filter (fun i => 0 < α i ∧ i ∉ I ∧ w i = 0) with hK0
  -- the scaled matrix B̃ (rows of J2p divided by αᵢ)
  set Bt : Matrix (Fin m) (Fin n) ℝ :=
    Matrix.of fun i j => if i ∈ J2p then B i j / α i else B i j with hBtdef
  have hαpos : ∀ i ∈ J2p, 0 < α i := by
    intro i hi; rw [hJ2p, Finset.mem_filter] at hi; exact hi.2.1
  have hBt : ∀ i j, 0 ≤ Bt i j := by
    intro i j
    simp only [hBtdef, Matrix.of_apply]
    split_ifs with hi
    · exact div_nonneg (hB i j) (hαpos i hi).le
    · exact hB i j
  have hBtnn : ∀ y : Fin n → ℝ, 0 ≤ y → ∀ i, 0 ≤ (Bt *ᵥ y) i := by
    intro y hy i
    simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hBt i j) (hy j)
  have hBtrow : ∀ i ∈ J2p, ∀ y : Fin n → ℝ, (Bt *ᵥ y) i = (B *ᵥ y) i / α i := by
    intro i hi y
    simp only [mulVec, dotProduct, hBtdef, Matrix.of_apply, if_pos hi]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hBtge : ∀ i ∈ J2p, ∀ y : Fin n → ℝ, 1 ≤ (Bt *ᵥ y) i ↔ α i ≤ (B *ᵥ y) i := by
    intro i hi y
    rw [hBtrow i hi y, le_div_iff₀ (hαpos i hi), one_mul]
  -- condition 1 of Lemma 3.3
  have hF1 : ∀ i ∈ J2p, ((w i * beta n * OPT : ℝ) : EReal) < coverCost Bt d (Pi.single i 1) := by
    intro i hi
    have hi' := hi
    rw [hJ2p, Finset.mem_filter] at hi'
    obtain ⟨_, hαi, hiI, _⟩ := hi'
    have hnot : ¬ (((α i : ℝ) : EReal) * coverCost B d (Pi.single i 1) ≤
        ((w i * beta n * OPT : ℝ) : EReal)) := by
      intro hle
      apply hiI
      rw [hI, Iset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hαi, hle⟩
    have hlow : ((α i : ℝ) : EReal) * coverCost B d (Pi.single i 1) ≤
        coverCost Bt d (Pi.single i 1) := by
      show _ ≤ ⨅ (y : Fin n → ℝ) (_ : 0 ≤ y ∧ Pi.single i 1 ≤ Bt *ᵥ y), ((d ⬝ᵥ y : ℝ) : EReal)
      refine le_iInf₂ fun y hy => ?_
      have hyi : α i ≤ (B *ᵥ y) i := by
        have := hy.2 i
        simp only [Pi.single_eq_same] at this
        exact (hBtge i hi y).1 this
      set y' := (α i)⁻¹ • y with hy'
      have hy'nn : 0 ≤ y' := smul_nonneg (inv_nonneg.2 hαi.le) hy.1
      have hcov : Pi.single i 1 ≤ B *ᵥ y' := by
        intro k
        by_cases hk : k = i
        · subst hk
          simp only [Pi.single_eq_same, hy', mulVec_smul, Pi.smul_apply, smul_eq_mul]
          rw [inv_mul_eq_div, le_div_iff₀ hαi, one_mul]; exact hyi
        · rw [Pi.single_eq_of_ne hk]; exact hBnn y' hy'nn k
      have h1 : coverCost B d (Pi.single i 1) ≤ ((d ⬝ᵥ y' : ℝ) : EReal) :=
        iInf₂_le (f := fun (y : Fin n → ℝ) (_ : 0 ≤ y ∧ Pi.single i 1 ≤ B *ᵥ y) =>
          ((d ⬝ᵥ y : ℝ) : EReal)) y' ⟨hy'nn, hcov⟩
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : EReal) ≤ ((α i : ℝ) : EReal) by
        exact_mod_cast hαi.le)
      refine le_trans h2 (le_of_eq ?_)
      rw [← EReal.coe_mul, hy', dotProduct_smul, smul_eq_mul]
      congr 1
      field_simp
    exact lt_of_lt_of_le (not_le.mp hnot) hlow
  -- condition 2 of Lemma 3.3
  have hF2 : ∀ W ⊆ J2p, ∑ i ∈ W, w i ≤ 1 → coverCost Bt d (indic W) ≤ (OPT : EReal) := by
    intro W hW hsum
    have hh := hindU W hsum
    have hcovW : indic W ≤ Bt *ᵥ ys (indic W) := by
      intro k
      by_cases hk : k ∈ W
      · have hkJ := hW hk
        have e1 : indic W k = 1 := by simp [indic, hk]
        rw [e1, hBtge k hkJ]
        have := hrow _ hh k
        rw [e1] at this
        linarith
      · have e0 : indic W k = 0 := by simp [indic, hk]
        rw [e0]; exact hBtnn _ (hfeas.2 _ hh).1 k
    have h1 : coverCost Bt d (indic W) ≤ ((d ⬝ᵥ ys (indic W) : ℝ) : EReal) :=
      iInf₂_le (f := fun (y : Fin n → ℝ) (_ : 0 ≤ y ∧ indic W ≤ Bt *ᵥ y) =>
          ((d ⬝ᵥ y : ℝ) : EReal)) _ ⟨(hfeas.2 _ hh).1, hcovW⟩
    refine le_trans h1 ?_
    have := hcostU _ hh
    have := hcX xs hxs
    exact_mod_cast (by linarith : d ⬝ᵥ ys (indic W) ≤ OPT)
  -- the second cover y₂ of the expensive components with positive weight
  have hy2 : ∃ y2 : Fin n → ℝ, 0 ≤ y2 ∧ (∀ i ∈ J2p, α i ≤ (B *ᵥ y2) i) ∧
      d ⬝ᵥ y2 ≤ beta n * OPT := by
    by_cases hJ : J2p = ∅
    · refine ⟨0, le_refl _, by simp [hJ], ?_⟩
      simp only [dotProduct_zero]
      exact mul_nonneg (by linarith) hOPT0
    obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.2 hJ
    have hOPTpos : 0 < OPT := by
      rcases hOPT0.lt_or_eq with h | h
      · exact h
      exfalso
      have a1 := hF1 i0 hi0
      have hsing : indic {i0} = Pi.single i0 (1 : ℝ) := by
        funext k; by_cases hk : k = i0
        · subst hk; simp [indic]
        · simp [indic, hk, Pi.single_eq_of_ne hk]
      have a2 := hF2 {i0} (by simpa using hi0) (by simpa using (hw i0).2)
      rw [hsing] at a2
      rw [← h] at a2 a1
      simp at a1
      exact absurd (lt_of_lt_of_le a1 a2) (lt_irrefl _)
    have hc3 := hN₀ n hnN m Bt d J2p OPT w hBt hd hOPTpos
      (fun i hi => by
        have hi' := hi
        rw [hJ2p, Finset.mem_filter] at hi'
        exact ⟨hi'.2.2.2, (hw i).2⟩)
      (fun i hi => by
        have := hF1 i hi
        have e : 4 * OPT * (Real.log n / Real.log (Real.log n)) * w i = w i * beta n * OPT := by
          unfold beta; ring
        rw [e]; exact this)
      hF2
    have hfin : coverCost Bt d (indic J2p) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hc3
    obtain ⟨y2, hy2nn, hy2cov, hy2val⟩ := coverCost_attained Bt d (indic J2p) hd hfin
    refine ⟨y2, hy2nn, fun i hi => ?_, ?_⟩
    · have := hy2cov i
      have e1 : indic J2p i = 1 := by simp [indic, hi]
      rw [e1] at this
      exact (hBtge i hi y2).1 this
    · have : ((d ⬝ᵥ y2 : ℝ) : EReal) ≤ ((4 * OPT * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) := by
        rw [hy2val]; exact hc3
      have h' : d ⬝ᵥ y2 ≤ 4 * OPT * (Real.log n / Real.log (Real.log n)) := by exact_mod_cast this
      have e : 4 * OPT * (Real.log n / Real.log (Real.log n)) = beta n * OPT := by
        unfold beta; ring
      linarith
  obtain ⟨y2, hy2nn, hy2cov, hy2val⟩ := hy2
  -- the scenario covering the zero-weight expensive components
  have hK0U : indic K0 ∈ U := by
    apply hindU
    have : ∑ i ∈ K0, w i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi; rw [hK0, Finset.mem_filter] at hi; exact hi.2.2.2
    rw [this]; norm_num
  set y0 := ys (indic K0) with hy0
  have hy0nn : 0 ≤ y0 := (hfeas.2 _ hK0U).1
  have hy0row := hrow _ hK0U
  -- feasibility of (x*, y0 + y2) for the static problem
  have hstat : staRhs I α ≤ A *ᵥ xs + B *ᵥ (y0 + y2) := by
    intro i
    simp only [Pi.add_apply, mulVec_add]
    rw [hAx i]
    have b0 := hBnn y0 hy0nn i
    have b2 := hBnn y2 hy2nn i
    have r0 := hy0row i
    have ind0 : 0 ≤ indic K0 i := by unfold indic; split_ifs <;> norm_num
    unfold staRhs
    split_ifs with hiI
    · apply max_le <;> linarith
    · by_cases hα0 : α i ≤ 0
      · linarith
      push_neg at hα0
      by_cases hw0 : w i = 0
      · have hiK : i ∈ K0 := by rw [hK0, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hα0, hiI, hw0⟩
        have e1 : indic K0 i = 1 := by simp [indic, hiK]
        rw [e1] at r0
        linarith
      · have hwpos : 0 < w i := lt_of_le_of_ne (hw i).1 (Ne.symm hw0)
        have hiJ : i ∈ J2p := by rw [hJ2p, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hα0, hiI, hwpos⟩
        have := hy2cov i hiJ
        linarith
  have hval : staticValue A B c d X (staRhs I α) ≤ ((c ⬝ᵥ xs + d ⬝ᵥ (y0 + y2) : ℝ) : EReal) := by
    unfold staticValue
    exact le_trans (iInf_le _ xs) (le_trans (iInf_le _ hxs) (le_trans (iInf_le _ (y0 + y2))
      (iInf_le_of_le ⟨add_nonneg hy0nn hy2nn, hstat⟩ le_rfl)))
  refine le_trans hval ?_
  have hc0 := hcostU _ hK0U
  have hOb : OPT ≤ beta n * OPT := le_mul_of_one_le_left hOPT0 hbeta
  have : c ⬝ᵥ xs + d ⬝ᵥ (y0 + y2) ≤ 2 * beta n * OPT := by
    rw [dotProduct_add]; linarith
  exact_mod_cast this
