-- Prove2me | solution 1 for DynamicOnlineLP.DLA.Supplement.multidim_dla_competitive_ratio
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:59.782201+00:00
-- url     : https://prove2.me/submissions/e81ea4fd-b949-4404-86eb-43282ab7f88b

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_DynamicOnlineLP_DLA_Algorithm
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SimplexPackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SurplusRule
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_GeneralPosition
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_MultiInstance
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_MultiAlgorithm

open DynamicOnlineLP
open DynamicOnlineLP.DLA
open DynamicOnlineLP.DLA.Supplement
set_option maxHeartbeats 0

/-- Theorem 3 (Agrawal–Wang–Ye 2014, p. 878), with absolute constants `C₁, C₂` in place of the
paper's `Ω(·)` and `O(·)`: for every `ε > 0`, every input of the general online LP (3) in general
position with `b ≥ 0` and `min_i b_i ≥ C₁ m log(nk/ε)/ε²`, and every valid selection of dual
prices and of ties, the multidimensional DLA satisfies
`E_σ[∑_t f_tᵀ x_t] ≥ (1 - C₂ ε) OPT`. -/
theorem solution :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (m n k : ℕ) (ε : ℝ) (I : MultiInstance m n k) (rule : MultiDualRule m n k)
        (tie : TieRule m n k),
        1 ≤ m → 1 ≤ n → 1 ≤ k → 0 < ε →
        I.GeneralPosition → IsValidMultiDualRule rule → IsValidTieRule tie →
        (∀ i : Fin m, 0 ≤ I.b i) →
        (∀ i : Fin m, C₁ * (m : ℝ) * Real.log ((n : ℝ) * (k : ℝ) / ε) / ε ^ 2 ≤ I.b i) →
        (1 - C₂ * ε) * I.OPT ≤
          avgPerm (fun σ : Equiv.Perm (Fin n) => multiValue I rule tie ε σ) := by
            classical
            have hchoice : ∀ {k : ℕ} (c : Option (Fin k)) (j : Fin k),
                0 ≤ choiceVec c j := by
              intro k c j
              unfold choiceVec
              split <;> norm_num
            have hproposal : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ)
                (σ : Equiv.Perm (Fin n)) (t : Fin n) (j : Fin k),
                0 ≤ multiProposal I rule tie ε σ t j := by
              intro m n k I rule tie ε σ t j
              unfold multiProposal
              split
              · exact hchoice _ _
              · split
                · exact le_rfl
                · exact hchoice _ _
            have hdecision : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ)
                (σ : Equiv.Perm (Fin n)) (used : Fin m → ℝ) (t : Fin n) (j : Fin k),
                0 ≤ multiDecision I rule tie ε σ used t j := by
              intro m n k I rule tie ε σ used t j
              unfold multiDecision
              split
              · exact hproposal _ _ _ _ _ _ _
              · exact le_rfl
            have hvalue : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ)
                (σ : Equiv.Perm (Fin n)), 0 ≤ multiValue I rule tie ε σ := by
              intro m n k I rule tie ε σ
              exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun j _ =>
                mul_nonneg (I.f_nonneg _ _) (hdecision I rule tie ε σ _ t j)
            have havg : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ),
                0 ≤ avgPerm (fun σ => multiValue I rule tie ε σ) := by
              intro m n k I rule tie ε
              exact div_nonneg (Finset.sum_nonneg fun σ _ => hvalue I rule tie ε σ)
                (Nat.cast_nonneg _)
            have hopt : ∀ {m n k : ℕ} (I : MultiInstance m n k),
                (∀ i, 0 ≤ I.b i) → 0 ≤ I.OPT := by
              intro m n k I hb
              have hzero : IsBlockFeasible Finset.univ I.g I.b (fun _ _ => 0) := by
                constructor
                · intro i
                  simpa using hb i
                · intro t ht
                  simp
              have hbounded : BddAbove (blockPrimalObj Finset.univ I.f ''
                  {x | IsBlockFeasible Finset.univ I.g I.b x}) := by
                refine ⟨∑ t : Fin n, ∑ j : Fin k, I.f t j, ?_⟩
                rintro y ⟨x, hx, rfl⟩
                apply Finset.sum_le_sum
                intro t ht
                apply Finset.sum_le_sum
                intro j hj
                have hxj : x t j ≤ 1 := le_trans
                  (Finset.single_le_sum (fun j _ => (hx.2 t ht).1 j) (Finset.mem_univ j))
                  (hx.2 t ht).2
                exact mul_le_of_le_one_right (I.f_nonneg t j) hxj
              have hz : (0 : ℝ) ∈ blockPrimalObj Finset.univ I.f ''
                  {x | IsBlockFeasible Finset.univ I.g I.b x} := by
                exact ⟨fun _ _ => 0, hzero, by simp [blockPrimalObj]⟩
              exact le_csSup hbounded hz
            have hchoiceSum : ∀ {k : ℕ} (c : Option (Fin k)),
                ∑ j : Fin k, choiceVec c j ≤ 1 := by
              intro k c
              cases c with
              | none => simp [choiceVec]
              | some r => simp [choiceVec, eq_comm]
            have hproposalSum : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ)
                (σ : Equiv.Perm (Fin n)) (t : Fin n),
                ∑ j : Fin k, multiProposal I rule tie ε σ t j ≤ 1 := by
              intro m n k I rule tie ε σ t
              unfold multiProposal
              split
              · exact hchoiceSum _
              · split
                · simp
                · exact hchoiceSum _
            have hdecisionSum : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ)
                (σ : Equiv.Perm (Fin n)) (used : Fin m → ℝ) (t : Fin n),
                ∑ j : Fin k, multiDecision I rule tie ε σ used t j ≤ 1 := by
              intro m n k I rule tie ε σ used t
              unfold multiDecision
              split
              · exact hproposalSum _ _ _ _ _ _
              · simp
            have hproposalUse : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ)
                (σ : Equiv.Perm (Fin n)) (t : Fin n) (i : Fin m),
                ∑ j : Fin k, I.arrG σ t i j * multiProposal I rule tie ε σ t j ≤ 1 := by
              intro m n k I rule tie ε σ t i
              exact le_trans (Finset.sum_le_sum fun j _ =>
                mul_le_of_le_one_left (hproposal I rule tie ε σ t j) (I.g_le_one _ _ _))
                (hproposalSum I rule tie ε σ t)
            have husedTime : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ)
                (σ : Equiv.Perm (Fin n)) (τ : ℕ) (i : Fin m),
                multiUsed I rule tie ε σ τ i ≤ (τ : ℝ) := by
              intro m n k I rule tie ε σ τ
              induction τ with
              | zero => simp [multiUsed]
              | succ τ ih =>
                intro i
                simp only [multiUsed]
                split
                · have hu : ∑ j : Fin k, I.arrG σ ⟨τ, ‹τ < n›⟩ i j *
                      multiDecision I rule tie ε σ (multiUsed I rule tie ε σ τ) ⟨τ, ‹τ < n›⟩ j ≤ 1 :=
                    le_trans (Finset.sum_le_sum fun j _ =>
                      mul_le_of_le_one_left (hdecision I rule tie ε σ _ _ j) (I.g_le_one _ _ _))
                      (hdecisionSum I rule tie ε σ _ _)
                  push_cast
                  linarith [ih i]
                · push_cast
                  linarith [ih i]
            have hfullBudget : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ)
                (σ : Equiv.Perm (Fin n)), (∀ i, (n : ℝ) ≤ I.b i) →
                ∀ t, multiX I rule tie ε σ t = multiProposal I rule tie ε σ t := by
              intro m n k I rule tie ε σ hbudget t
              unfold multiX multiDecision
              rw [if_pos]
              intro i
              have htn : (t.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast t.isLt
              linarith [husedTime I rule tie ε σ t.val i, hbudget i,
                hproposalUse I rule tie ε σ t i]
            have hbestChoice : ∀ {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ)
                (c : Option (Fin k)) (x : Fin k → ℝ),
                (∀ j, 0 ≤ f j) → IsSurplusChoice f g (fun _ => 0) c →
                (∀ j, 0 ≤ x j) → (∑ j, x j ≤ 1) →
                ∑ j, f j * x j ≤ ∑ j, f j * choiceVec c j := by
              intro m k f g c x hf hc hx hsum
              cases c with
              | none =>
                have hzero : ∀ j, f j = 0 := by
                  intro j
                  have := hc j
                  simp [surplus] at this
                  exact le_antisymm this (hf j)
                simp [hzero]
              | some r =>
                have hmax : ∀ j, f j ≤ f r := by
                  intro j
                  have := hc.2 j
                  simpa [surplus] using this
                have hle : ∑ j, f j * x j ≤ f r * ∑ j, x j := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hmax j) (hx j)
                have hle' : f r * ∑ j, x j ≤ f r := mul_le_of_le_one_right (hf r) hsum
                simpa [choiceVec, eq_comm] using le_trans hle hle'
            have hshort : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ),
                (∀ i, (n : ℝ) ≤ I.b i) → IsValidTieRule tie →
                eps (accuracyExp ε) * (n : ℝ) < 1 →
                ∀ σ : Equiv.Perm (Fin n), I.OPT ≤ multiValue I rule tie ε σ := by
              intro m n k I rule tie ε hbudget ht hwindow σ
              apply csSup_le
              · refine ⟨0, fun _ _ => 0, ?_, ?_⟩
                · constructor
                  · intro i
                    simpa using le_trans (Nat.cast_nonneg n) (hbudget i)
                  · simp
                · simp [blockPrimalObj]
              · rintro y ⟨x, hx, rfl⟩
                have hperm : blockPrimalObj Finset.univ I.f x =
                    ∑ t : Fin n, ∑ j : Fin k, I.arrF σ t j * x (σ t) j := by
                  exact (Equiv.sum_comp σ (fun t => ∑ j : Fin k, I.f t j * x t j)).symm
                rw [hperm]
                apply Finset.sum_le_sum
                intro t ht'
                have hX := hfullBudget I rule tie ε σ hbudget t
                have hX' : multiX I rule tie ε σ t =
                    choiceVec (tie t (I.arrF σ) (I.arrG σ) (fun _ => 0)) := by
                  rw [hX]
                  simp only [multiProposal, if_pos hwindow]
                simpa only [hX'] using
                  hbestChoice (I.arrF σ t) (I.arrG σ t)
                    (tie t (I.arrF σ) (I.arrG σ) (fun _ => 0)) (x (σ t))
                    (I.f_nonneg (σ t)) (ht.2 _ _ _ _)
                    (hx.2 (σ t) (Finset.mem_univ _)).1 (hx.2 (σ t) (Finset.mem_univ _)).2
            have hweakDual : ∀ {m n k : ℕ} (S : Finset (Fin n))
                (f : Fin n → Fin k → ℝ) (g : Fin n → Fin m → Fin k → ℝ)
                (b p : Fin m → ℝ) (y : Fin n → ℝ) (x : Fin n → Fin k → ℝ),
                IsBlockFeasible S g b x → IsBlockDualFeasible S f g p y →
                blockPrimalObj S f x ≤ blockDualObj S b p y := by
              intro m n k S f g b p y x hx hp
              have hlocal : ∀ t ∈ S, ∑ j, f t j * x t j ≤
                  ∑ i, p i * ∑ j, g t i j * x t j + y t := by
                intro t ht
                have hle : ∑ j, f t j * x t j ≤
                    ∑ j, (∑ i, p i * g t i j + y t) * x t j :=
                  Finset.sum_le_sum fun j _ =>
                    mul_le_mul_of_nonneg_right ((hp.2 t ht).2 j) ((hx.2 t ht).1 j)
                have heq : ∑ j, (∑ i, p i * g t i j + y t) * x t j =
                    (∑ i, p i * ∑ j, g t i j * x t j) + y t * ∑ j, x t j := by
                  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
                  rw [Finset.sum_comm]
                  simp only [mul_assoc]
                rw [heq] at hle
                have := mul_le_of_le_one_right (hp.2 t ht).1 (hx.2 t ht).2
                linarith only [hle, this]
              have hglobal := Finset.sum_le_sum hlocal
              have heq : ∑ t ∈ S, ((∑ i, p i * ∑ j, g t i j * x t j) + y t) =
                  (∑ i, p i * ∑ t ∈ S, ∑ j, g t i j * x t j) + ∑ t ∈ S, y t := by
                rw [Finset.sum_add_distrib, Finset.sum_comm]
                simp only [Finset.mul_sum]
              rw [heq] at hglobal
              have hresource : ∑ i, p i * ∑ t ∈ S, ∑ j, g t i j * x t j ≤ ∑ i, b i * p i := by
                apply Finset.sum_le_sum
                intro i hi
                simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hx.1 i) (hp.1 i)
              change (∑ t ∈ S, ∑ j, f t j * x t j) ≤ (∑ i, b i * p i) + ∑ t ∈ S, y t
              linarith only [hglobal, hresource]
            have hoptDual : ∀ {m n k : ℕ} (I : MultiInstance m n k) (p : Fin m → ℝ)
                (y : Fin n → ℝ), (∀ i, 0 ≤ I.b i) →
                IsBlockDualFeasible Finset.univ I.f I.g p y →
                I.OPT ≤ blockDualObj Finset.univ I.b p y := by
              intro m n k I p y hb hp
              apply csSup_le
              · refine ⟨0, fun _ _ => 0, ?_, by simp [blockPrimalObj]⟩
                constructor
                · intro i
                  simpa using hb i
                · simp
              · rintro z ⟨x, hx, rfl⟩
                exact hweakDual _ _ _ _ _ _ _ hx hp
            have hchoiceSurplus : ∀ {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ)
                (p : Fin m → ℝ) (c : Option (Fin k)), IsSurplusChoice f g p c →
                0 ≤ ∑ j, surplus f g p j * choiceVec c j ∧
                ∀ j, surplus f g p j ≤ ∑ j, surplus f g p j * choiceVec c j := by
              intro m k f g p c hc
              cases c with
              | none => simpa [choiceVec, IsSurplusChoice] using hc
              | some r => simpa [choiceVec, eq_comm] using And.intro hc.1.le hc.2
            have hpricePerformance : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (p : Fin m → ℝ) (c : Fin n → Option (Fin k)) (ρ V : ℝ),
                (∀ i, 0 ≤ I.b i) → (∀ i, 0 ≤ p i) → 0 ≤ ρ → ρ ≤ 1 →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c t)) →
                (∀ i, 0 < p i → ρ * I.b i ≤ ∑ t, ∑ j, I.g t i j * choiceVec (c t) j) →
                (∀ p' y, IsBlockDualFeasible Finset.univ I.f I.g p' y → V ≤ blockDualObj Finset.univ I.b p' y) →
                ρ * V ≤ ∑ t, ∑ j, I.f t j * choiceVec (c t) j := by
              intro m n k I p c ρ V hb hp hρ hρ1 hc huse hV
              let y : Fin n → ℝ := fun t => ∑ j, surplus (I.f t) (I.g t) p j * choiceVec (c t) j
              have hy : ∀ t, 0 ≤ y t := fun t => (hchoiceSurplus _ _ _ _ (hc t)).1
              have hdual : IsBlockDualFeasible Finset.univ I.f I.g p y := by
                refine ⟨hp, ?_⟩
                intro t ht
                refine ⟨hy t, ?_⟩
                intro j
                have := (hchoiceSurplus _ _ _ _ (hc t)).2 j
                change I.f t j - ∑ i, p i * I.g t i j ≤ y t at this
                linarith only [this]
              have hid : (∑ t, y t) = (∑ t, ∑ j, I.f t j * choiceVec (c t) j) -
                  ∑ i, p i * ∑ t, ∑ j, I.g t i j * choiceVec (c t) j := by
                simp only [y, surplus, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
                congr 1
                conv_rhs => rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro t ht
                rw [Finset.sum_comm]
                simp only [mul_assoc]
              have hpuse : ρ * (∑ i, I.b i * p i) ≤
                  ∑ i, p i * ∑ t, ∑ j, I.g t i j * choiceVec (c t) j := by
                rw [Finset.mul_sum]
                apply Finset.sum_le_sum
                intro i hi
                by_cases hpi : p i = 0
                · simp [hpi]
                · have := mul_le_mul_of_nonneg_left (huse i (lt_of_le_of_ne (hp i) (Ne.symm hpi))) (hp i)
                  nlinarith only [this]
              have hysum : ρ * (∑ t, y t) ≤ ∑ t, y t :=
                mul_le_of_le_one_left (Finset.sum_nonneg fun t _ => hy t) hρ1
              have hopt' := mul_le_mul_of_nonneg_left (hV p y hdual) hρ
              simp only [blockDualObj] at hopt'
              nlinarith only [hid, hpuse, hysum, hopt']
            have hsurplusExists : ∀ {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ)
                (p : Fin m → ℝ), ∃ c, IsSurplusChoice f g p c := by
              intro m k f g p
              by_cases h : ∀ j, surplus f g p j ≤ 0
              · exact ⟨none, h⟩
              · push Not at h
                obtain ⟨j, hj⟩ := h
                obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image Finset.univ (surplus f g p)
                  ⟨j, Finset.mem_univ j⟩
                exact ⟨some r, lt_of_lt_of_le hj (hmax j (Finset.mem_univ j)),
                  fun i => hmax i (Finset.mem_univ i)⟩
            have hchoicesTied : ∀ {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ)
                (p : Fin m → ℝ) (c c' : Option (Fin k)),
                IsSurplusChoice f g p c → IsSurplusChoice f g p c' →
                c ≠ c' → IsTied f g p := by
              intro m k f g p c c' hc hc' hne
              cases c with
              | none =>
                cases c' with
                | none => exact False.elim (hne rfl)
                | some r => exact False.elim (not_lt_of_ge (hc r) hc'.1)
              | some r =>
                cases c' with
                | none => exact False.elim (not_lt_of_ge (hc' r) hc.1)
                | some r' =>
                  refine ⟨some r, some r', hne, ?_, ?_⟩
                  · exact le_antisymm (hc'.2 r) (hc.2 r')
                  · rintro (_ | j)
                    · exact hc.1.le
                    · exact hc.2 j
            have hchoicesDiffer : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (p : Fin m → ℝ) (c c' : Fin n → Option (Fin k)),
                I.GeneralPosition →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c t)) →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c' t)) →
                (Finset.univ.filter (fun t => c t ≠ c' t)).card ≤ m := by
              intro m n k I p c c' hgp hc hc'
              apply le_trans (Finset.card_le_card ?_) (hgp p)
              intro t ht
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
              exact hchoicesTied _ _ _ _ _ (hc t) (hc' t) ht
            have hhalfspaceVC : ∀ {α : Type} [Fintype α] [DecidableEq α] {d : ℕ} (v : α → Fin d → ℝ)
                (A : Finset (Finset α)),
                (∀ s ∈ A, ∃ w : Fin d → ℝ, ∀ a, a ∈ s ↔ 0 < ∑ i, w i * v a i) →
                A.vcDim ≤ d := by
              intro α _ _ d v A hreal
              apply Finset.sup_le
              intro s hs
              have hshat := Finset.mem_shatterer.mp hs
              have hLI : LinearIndependent ℝ (fun a : s => v a.val) := by
                rw [Fintype.linearIndependent_iff]
                have hnonpos : ∀ c : s → ℝ, (∑ a : s, c a • v a.val) = 0 → ∀ a, c a ≤ 0 := by
                  intro c hc a
                  by_contra hca
                  have hca' : 0 < c a := lt_of_not_ge hca
                  let target := s.filter (fun b => 0 < if h : b ∈ s then c ⟨b, h⟩ else 0)
                  obtain ⟨u, hu, hsu⟩ := hshat (Finset.filter_subset _ _ : target ⊆ s)
                  obtain ⟨w, hw⟩ := hreal u hu
                  have hsign : ∀ b : s, (0 < ∑ i, w i * v b.val i) ↔ 0 < c b := by
                    intro b
                    rw [← hw]
                    have heq := congrArg (fun z : Finset α => b.val ∈ z) hsu
                    simpa [target, b.property] using heq
                  have hsum0 : (∑ b : s, c b * ∑ i, w i * v b.val i) = 0 := by
                    have hci : ∀ i, (∑ b : s, c b * v b.val i) = 0 := by
                      intro i
                      have h := congrFun hc i
                      simpa using h
                    calc
                      (∑ b : s, c b * ∑ i, w i * v b.val i) =
                          ∑ i, w i * ∑ b : s, c b * v b.val i := by
                        simp only [Finset.mul_sum]
                        rw [Finset.sum_comm]
                        apply Finset.sum_congr rfl
                        intro i hi
                        apply Finset.sum_congr rfl
                        intro b hb
                        ring
                      _ = 0 := by simp only [hci, mul_zero, Finset.sum_const_zero]
                  have hnonneg : ∀ b : s, 0 ≤ c b * ∑ i, w i * v b.val i := by
                    intro b
                    by_cases hb : 0 < c b
                    · exact mul_nonneg hb.le ((hsign b).2 hb).le
                    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hb)
                        (le_of_not_gt fun h => hb ((hsign b).1 h))
                  have hsumpos : 0 < ∑ b : s, c b * ∑ i, w i * v b.val i := by
                    exact Finset.sum_pos' (fun b _ => hnonneg b)
                      ⟨a, Finset.mem_univ _, mul_pos hca' ((hsign a).2 hca')⟩
                  linarith only [hsum0, hsumpos]
                intro c hc a
                apply le_antisymm (hnonpos c hc a)
                have hn : (∑ b : s, (-c b) • v b.val) = 0 := by
                  simp only [neg_smul, Finset.sum_neg_distrib, hc, neg_zero]
                have := hnonpos (fun b => -c b) hn a
                linarith only [this]
              have hcard := hLI.fintype_card_le_finrank
              simpa [Module.finrank_pi] using hcard
            have hhalfspaceCount : ∀ {α : Type} [Fintype α] [DecidableEq α] {d : ℕ} (v : α → Fin d → ℝ)
                (A : Finset (Finset α)),
                (∀ s ∈ A, ∃ w : Fin d → ℝ, ∀ a, a ∈ s ↔ 0 < ∑ i, w i * v a i) →
                A.card ≤ ∑ j ∈ Finset.Iic d, (Fintype.card α).choose j := by
              intro α _ _ d v A hreal
              have hvcd := hhalfspaceVC v A hreal
              exact le_trans (Finset.card_le_card_shatterer A)
                (le_trans (by simpa using (Finset.card_shatterer_le_sum_vcDim (𝒜 := A)))
                  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hvcd)
                    (fun _ _ _ => Nat.zero_le _)))
            have hscoreLinear : ∀ {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ)
                (p : Fin m → ℝ) (c : Option (Fin k)),
                score f g p c = c.elim 0 f - ∑ i, p i * c.elim 0 (g i) := by
              intro m k f g p c
              cases c <;> simp [score, surplus]
            have hpriceCover : ∀ {m n k : ℕ} (I : MultiInstance m n k),
                ∃ A : Finset (Fin n → Option (Fin k)),
                  A.card ≤ ∑ j ∈ Finset.Iic (m + 1), (n * (k + 1) ^ 2).choose j ∧
                  ∀ p : Fin m → ℝ, ∃ c ∈ A, ∀ t, IsSurplusChoice (I.f t) (I.g t) p (c t) := by
              intro m n k I
              let α := Fin n × Option (Fin k) × Option (Fin k)
              let pat : (Fin m → ℝ) → Finset α := fun p => Finset.univ.filter
                (fun z => score (I.f z.1) (I.g z.1) p z.2.1 < score (I.f z.1) (I.g z.1) p z.2.2)
              let feat : α → Fin (m + 1) → ℝ := fun z => Fin.cons
                (z.2.2.elim 0 (I.f z.1) - z.2.1.elim 0 (I.f z.1))
                (fun i => z.2.1.elim 0 (I.g z.1 i) - z.2.2.elim 0 (I.g z.1 i))
              let S : Finset (Finset α) := Finset.univ.filter (fun s => ∃ p, pat p = s)
              have hS : ∀ s : S, ∃ p, pat p = s.val := by
                intro s
                exact (Finset.mem_filter.mp s.property).2
              choose q hq using hS
              have hc : ∀ (s : S) (t : Fin n), ∃ c, IsSurplusChoice (I.f t) (I.g t) (q s) c :=
                fun s t => hsurplusExists _ _ _
              choose c hc using hc
              refine ⟨Finset.univ.image c, ?_, ?_⟩
              · apply le_trans (Finset.card_image_le)
                have hlin : ∀ s ∈ S, ∃ w : Fin (m + 1) → ℝ, ∀ z : α,
                    z ∈ s ↔ 0 < ∑ i, w i * feat z i := by
                  intro s hs
                  obtain ⟨p, rfl⟩ := (Finset.mem_filter.mp hs).2
                  refine ⟨Fin.cons 1 p, ?_⟩
                  intro z
                  simp only [pat, feat, Finset.mem_filter, Finset.mem_univ, true_and,
                    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, one_mul]
                  rw [hscoreLinear, hscoreLinear]
                  simp only [mul_sub, Finset.sum_sub_distrib]
                  constructor <;> intro h <;> linarith only [h]
                have hcount := hhalfspaceCount feat S hlin
                simpa [α, pow_two, mul_assoc] using hcount
              · intro p
                have hsp : pat p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, rfl⟩
                let s : S := ⟨pat p, hsp⟩
                refine ⟨c s, Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩, ?_⟩
                intro t
                have hpat : pat (q s) = pat p := hq s
                have horder : ∀ u v : Option (Fin k),
                    score (I.f t) (I.g t) (q s) u < score (I.f t) (I.g t) (q s) v ↔
                    score (I.f t) (I.g t) p u < score (I.f t) (I.g t) p v := by
                  intro u v
                  have := congrArg (fun z : Finset α => (t, u, v) ∈ z) hpat
                  simpa [pat] using this
                have hchoice := hc s t
                cases hcs : c s t with
                | none =>
                  rw [hcs] at hchoice
                  intro j
                  apply le_of_not_gt
                  intro h
                  have h' := (horder none (some j)).mpr h
                  exact not_lt_of_ge (hchoice j) h'
                | some r =>
                  rw [hcs] at hchoice
                  refine ⟨(horder none (some r)).mp hchoice.1, ?_⟩
                  intro j
                  apply le_of_not_gt
                  intro h
                  have h' := (horder (some r) (some j)).mpr h
                  exact not_lt_of_ge (hchoice.2 j) h'
            have hbinomialMode : ∀ (n ℓ : ℕ), 0 < ℓ → ℓ < n →
                1 ≤ (n + 1 : ℝ) * (n.choose ℓ : ℝ) * ((ℓ : ℝ) / n) ^ ℓ *
                  (1 - (ℓ : ℝ) / n) ^ (n - ℓ) := by
              intro n ℓ hℓ hℓn
              let q : ℝ := (ℓ : ℝ) / n
              have hn : (0 : ℝ) < n := by exact_mod_cast (lt_trans hℓ hℓn)
              have hq0 : 0 < q := div_pos (by exact_mod_cast hℓ) hn
              have hq1 : q < 1 := (div_lt_one hn).mpr (by exact_mod_cast hℓn)
              have hqeq : (n : ℝ) * q = ℓ := by dsimp [q]; field_simp
              let t : ℕ → ℝ := fun j => (n.choose j : ℝ) * q ^ j * (1 - q) ^ (n - j)
              have ht0 : ∀ j, 0 ≤ t j := by intro j; dsimp [t]; positivity
              have hrec : ∀ j < n, ((j : ℝ) + 1) * (1 - q) * t (j + 1) =
                  ((n : ℝ) - j) * q * t j := by
                intro j hj
                have heq : n - j = n - (j + 1) + 1 := by omega
                have hc : (n.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
                    (n.choose j : ℝ) * ((n : ℝ) - j) := by
                  have hc' := congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_succ_right_eq n j)
                  push_cast [Nat.cast_sub hj.le] at hc'
                  exact hc' 
                have hpow : (1 - q) ^ (n - j) = (1 - q) ^ (n - (j + 1)) * (1 - q) := by
                  rw [heq, pow_succ]
                dsimp only [t]
                rw [hpow, pow_succ]
                linear_combination q ^ j * (1 - q) ^ (n - (j + 1)) * q * (1 - q) * hc
              have hup : ∀ j < ℓ, t j ≤ t (j + 1) := by
                intro j hj
                have hjn : j < n := lt_trans hj hℓn
                have hcoef : ((j : ℝ) + 1) * (1 - q) ≤ ((n : ℝ) - j) * q := by
                  have hj' : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast hj
                  nlinarith only [hqeq, hj', hq0]
                have hm := mul_le_mul_of_nonneg_right hcoef (ht0 j)
                have he := hrec j hjn
                have hpos : 0 < ((j : ℝ) + 1) * (1 - q) := by positivity
                exact (mul_le_mul_iff_right₀ hpos).mp (by linarith only [hm, he])
              have hdown : ∀ j, ℓ ≤ j → j < n → t (j + 1) ≤ t j := by
                intro j hj hjn
                have hcoef : ((n : ℝ) - j) * q ≤ ((j : ℝ) + 1) * (1 - q) := by
                  have hj' : (ℓ : ℝ) ≤ j := by exact_mod_cast hj
                  nlinarith only [hqeq, hj', hq1]
                have hm := mul_le_mul_of_nonneg_right hcoef (ht0 j)
                have he := hrec j hjn
                have hpos : 0 < ((j : ℝ) + 1) * (1 - q) := by positivity
                exact (mul_le_mul_iff_right₀ hpos).mp (by linarith only [hm, he])
              have hmax : ∀ j ≤ n, t j ≤ t ℓ := by
                intro j hjn
                by_cases hj : j ≤ ℓ
                · have hu : ∀ r, j + r ≤ ℓ → t j ≤ t (j + r) := by
                    intro r
                    induction r with
                    | zero => simp
                    | succ r ih =>
                      intro h
                      exact le_trans (ih (by omega)) (hup (j + r) (by omega))
                  simpa [Nat.add_sub_of_le hj] using hu (ℓ - j) (by omega)
                · have hd : ∀ r, ℓ + r ≤ n → t (ℓ + r) ≤ t ℓ := by
                    intro r
                    induction r with
                    | zero => simp
                    | succ r ih =>
                      intro h
                      exact le_trans (hdown (ℓ + r) (by omega) (by omega)) (ih (by omega))
                  simpa [Nat.add_sub_of_le (le_of_not_ge hj)] using hd (j - ℓ) (by omega)
              have hsum : ∑ j ∈ Finset.range (n + 1), t j = 1 := by
                have hp := add_pow q (1 - q) n
                have heq : q + (1 - q) = 1 := by ring
                rw [heq, one_pow] at hp
                convert hp.symm using 1
                apply Finset.sum_congr rfl
                intro j hj
                dsimp only [t]
                ring
              have hle := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range (n + 1)) =>
                hmax j (by simpa using hj))
              rw [hsum] at hle
              simpa [t, q, mul_assoc] using hle
            have hbernoulliGen : ∀ {n : ℕ} (a : Fin n → ℝ) (q θ : ℝ),
                (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
                  q ^ s.card * (1 - q) ^ (n - s.card) * Real.exp (θ * ∑ i ∈ s, a i)) =
                ∏ i : Fin n, (1 - q + q * Real.exp (θ * a i)) := by
              intro n a q θ
              simp_rw [add_comm (1 - q)]
              rw [Finset.prod_add]
              apply Finset.sum_congr rfl
              intro s hs
              have he : (∏ i ∈ s, q * Real.exp (θ * a i)) =
                  q ^ s.card * Real.exp (θ * ∑ i ∈ s, a i) := by
                rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.mul_sum, Real.exp_sum]
              simp only [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, ← Finset.mul_sum,
                Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
              ring
            have hbernoulliProduct : ∀ {n : ℕ} (a : Fin n → ℝ) (q θ : ℝ),
                (∀ i, 0 ≤ a i ∧ a i ≤ 1) → 0 ≤ q → q ≤ 1 → |θ| ≤ 1 →
                (∏ i : Fin n, (1 - q + q * Real.exp (θ * a i))) ≤
                  Real.exp (q * (θ + θ ^ 2) * ∑ i, a i) := by
              intro n a q θ ha hq hq1 hθ
              have he : Real.exp θ ≤ 1 + θ + θ ^ 2 := by
                have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hθ)).2
                linarith only [this]
              have hi : ∀ i, 1 - q + q * Real.exp (θ * a i) ≤
                  Real.exp (q * (θ + θ ^ 2) * a i) := by
                intro i
                have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ θ)
                  (by linarith [(ha i).2] : 0 ≤ 1 - a i) (ha i).1 (by ring : 1 - a i + a i = 1)
                simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
                have hc' : Real.exp (θ * a i) ≤ 1 - a i + a i * Real.exp θ := by
                  simpa only [mul_comm] using hc
                have he' := mul_le_mul_of_nonneg_left he (ha i).1
                have hbound : 1 - q + q * Real.exp (θ * a i) ≤
                    1 + q * (θ + θ ^ 2) * a i := by
                  have := mul_le_mul_of_nonneg_left hc' hq
                  have := mul_le_mul_of_nonneg_left he' hq
                  nlinarith only [this, ‹q * Real.exp (θ * a i) ≤ q * (1 - a i + a i * Real.exp θ)›]
                exact le_trans hbound (by simpa [add_comm] using Real.add_one_le_exp (q * (θ + θ ^ 2) * a i))
              have hprod := Finset.prod_le_prod
                (fun i (_ : i ∈ Finset.univ) => by positivity : ∀ i ∈ Finset.univ, 0 ≤ 1 - q + q * Real.exp (θ * a i))
                (fun i _ => hi i)
              simpa only [← Real.exp_sum, ← Finset.mul_sum] using hprod
            have hsubsetMGF : ∀ (n ℓ : ℕ) (a : Fin n → ℝ) (θ : ℝ),
                0 < ℓ → ℓ < n → (∀ i, 0 ≤ a i ∧ a i ≤ 1) → |θ| ≤ 1 →
                (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard ℓ,
                  Real.exp (θ * ((∑ i ∈ s, a i) - (ℓ : ℝ) / n * ∑ i, a i))) /
                    (n.choose ℓ : ℝ) ≤
                  (n + 1 : ℝ) * Real.exp (((ℓ : ℝ) / n) * θ ^ 2 * ∑ i, a i) := by
              intro n ℓ a θ hℓ hℓn ha hθ
              let q : ℝ := (ℓ : ℝ) / n
              let Z : ℝ := Real.exp (-θ * q * ∑ i, a i)
              let c : ℝ := q ^ ℓ * (1 - q) ^ (n - ℓ)
              have hn : (0 : ℝ) < n := by exact_mod_cast (lt_trans hℓ hℓn)
              have hq : 0 < q := div_pos (by exact_mod_cast hℓ) hn
              have hq1 : q < 1 := (div_lt_one hn).mpr (by exact_mod_cast hℓn)
              have hc : 0 < c := by dsimp [c]; positivity
              have hchoose : 0 < (n.choose ℓ : ℝ) := by exact_mod_cast Nat.choose_pos hℓn.le
              have hsum : c * ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard ℓ,
                  Real.exp (θ * ∑ i ∈ s, a i) ≤
                  ∏ i : Fin n, (1 - q + q * Real.exp (θ * a i)) := by
                rw [← hbernoulliGen a q θ]
                have hsub : (Finset.univ : Finset (Fin n)).powersetCard ℓ ⊆ Finset.univ.powerset := by
                  intro s hs
                  exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hs).1
                have hle : (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard ℓ,
                    q ^ s.card * (1 - q) ^ (n - s.card) * Real.exp (θ * ∑ i ∈ s, a i)) ≤
                    ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
                    q ^ s.card * (1 - q) ^ (n - s.card) * Real.exp (θ * ∑ i ∈ s, a i) :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub
                    (fun s hs hsn => by positivity)
                apply le_trans ?_ hle
                rw [Finset.mul_sum]
                apply Finset.sum_le_sum
                intro s hs
                rw [(Finset.mem_powersetCard.mp hs).2]
              have hmode : 1 ≤ ((n : ℝ) + 1) * (n.choose ℓ : ℝ) * c := by
                simpa only [c, q, mul_assoc] using hbinomialMode n ℓ hℓ hℓn
              have hsum0 : 0 ≤ ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard ℓ,
                  Real.exp (θ * ∑ i ∈ s, a i) := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
              have hmain : (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard ℓ,
                  Real.exp (θ * ∑ i ∈ s, a i)) / (n.choose ℓ : ℝ) ≤
                  ((n : ℝ) + 1) * Real.exp (q * (θ + θ ^ 2) * ∑ i, a i) := by
                rw [div_le_iff₀ hchoose]
                have hprod := hbernoulliProduct a q θ ha hq.le hq1.le hθ
                have hm := mul_le_mul_of_nonneg_right hmode hsum0
                have hh := mul_le_mul_of_nonneg_left (le_trans hsum hprod)
                  (by positivity : 0 ≤ ((n : ℝ) + 1) * (n.choose ℓ : ℝ))
                nlinarith only [hm, hh]
              have hZ : 0 ≤ Z := (Real.exp_pos _).le
              have hmain' := mul_le_mul_of_nonneg_left hmain hZ
              have heq : ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard ℓ,
                  Real.exp (θ * ((∑ i ∈ s, a i) - (ℓ : ℝ) / n * ∑ i, a i)) =
                  Z * ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard ℓ,
                    Real.exp (θ * ∑ i ∈ s, a i) := by
                conv_rhs => rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro s hs
                change Real.exp _ = Real.exp _ * Real.exp _
                rw [← Real.exp_add]
                congr 1
                dsimp [q]
                ring
              rw [heq, mul_div_assoc]
              apply le_trans hmain'
              apply le_of_eq
              dsimp [Z]
              rw [show Real.exp (-θ * q * ∑ i, a i) * (((n : ℝ) + 1) *
                Real.exp (q * (θ + θ ^ 2) * ∑ i, a i)) = ((n : ℝ) + 1) *
                (Real.exp (-θ * q * ∑ i, a i) * Real.exp (q * (θ + θ ^ 2) * ∑ i, a i)) by ring,
                ← Real.exp_add]
              congr 2
              dsimp [q]
              ring
            have hpermSubsetAverage : ∀ {n : ℕ} (S : Finset (Fin n)) (F : Finset (Fin n) → ℝ),
                avgPerm (fun σ => F (S.image σ)) =
                (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard S.card, F T) /
                  (n.choose S.card : ℝ) := by
              intro n S F
              let B := (Finset.univ : Finset (Fin n)).powersetCard S.card
              have hmaps : ∀ σ : Equiv.Perm (Fin n), (∑ T ∈ B, F (T.image σ)) = ∑ T ∈ B, F T := by
                intro σ
                refine Finset.sum_bij (fun T hT => T.image σ) ?_ ?_ ?_ (fun T hT => rfl)
                · intro T hT
                  apply Finset.mem_powersetCard.mpr
                  exact ⟨Finset.subset_univ _, by
                    rw [Finset.card_image_of_injective _ σ.injective]
                    exact (Finset.mem_powersetCard.mp hT).2⟩
                · intro T hT U hU he
                  exact (Finset.image_inj σ.injective).mp he
                · intro T hT
                  refine ⟨T.image σ.symm, ?_, ?_⟩
                  · apply Finset.mem_powersetCard.mpr
                    exact ⟨Finset.subset_univ _, by
                      rw [Finset.card_image_of_injective _ σ.symm.injective]
                      exact (Finset.mem_powersetCard.mp hT).2⟩
                  · simp [Finset.image_image, Function.comp_def]
              have hconstant : ∀ T ∈ B, (∑ σ : Equiv.Perm (Fin n), F (T.image σ)) =
                  ∑ σ : Equiv.Perm (Fin n), F (S.image σ) := by
                intro T hT
                have hcard : S.card = T.card := (Finset.mem_powersetCard.mp hT).2.symm
                obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
                rw [Finset.map_eq_image] at hτ
                rw [← hτ]
                calc
                  (∑ σ : Equiv.Perm (Fin n), F ((S.image τ).image σ)) =
                      ∑ σ : Equiv.Perm (Fin n), F (S.image (σ * τ)) := by
                    simp only [Finset.image_image]
                    rfl
                  _ = ∑ σ : Equiv.Perm (Fin n), F (S.image σ) :=
                    Equiv.sum_comp (Equiv.mulRight τ) (fun σ => F (S.image σ))
              have heq : (B.card : ℝ) * (∑ σ : Equiv.Perm (Fin n), F (S.image σ)) =
                  (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (∑ T ∈ B, F T) := by
                calc
                  (B.card : ℝ) * (∑ σ : Equiv.Perm (Fin n), F (S.image σ)) =
                      ∑ T ∈ B, ∑ σ : Equiv.Perm (Fin n), F (T.image σ) := by
                    symm
                    calc
                      (∑ T ∈ B, ∑ σ : Equiv.Perm (Fin n), F (T.image σ)) =
                          ∑ T ∈ B, ∑ σ : Equiv.Perm (Fin n), F (S.image σ) :=
                        Finset.sum_congr rfl (fun T hT => hconstant T hT)
                      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
                  _ = ∑ σ : Equiv.Perm (Fin n), ∑ T ∈ B, F (T.image σ) := Finset.sum_comm
                  _ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (∑ T ∈ B, F T) := by
                    simp only [hmaps, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              have hBcard : B.card = n.choose S.card := by simp [B]
              have hpos : 0 < (n.choose S.card : ℝ) := by
                exact_mod_cast Nat.choose_pos (by simpa using Finset.card_le_card (Finset.subset_univ S))
              unfold avgPerm
              apply (div_eq_div_iff (by exact_mod_cast (ne_of_gt Fintype.card_pos)) (ne_of_gt hpos)).mpr
              rw [hBcard] at heq
              linarith only [heq]
            have hpermMGF : ∀ {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) (θ : ℝ),
                0 < S.card → S.card < n → (∀ i, 0 ≤ a i ∧ a i ≤ 1) → |θ| ≤ 1 →
                avgPerm (fun σ => Real.exp (θ * ((∑ t ∈ S, a (σ t)) -
                  (S.card : ℝ) / n * ∑ i, a i))) ≤
                  (n + 1 : ℝ) * Real.exp (((S.card : ℝ) / n) * θ ^ 2 * ∑ i, a i) := by
              intro n S a θ hS hSn ha hθ
              have hpoint : ∀ σ : Equiv.Perm (Fin n),
                  Real.exp (θ * ((∑ i ∈ S.image σ, a i) - (S.card : ℝ) / n * ∑ i, a i)) =
                  Real.exp (θ * ((∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i)) := by
                intro σ
                rw [Finset.sum_image]
                exact fun a ha b hb hab => σ.injective hab
              have heq := hpermSubsetAverage S
                (fun T => Real.exp (θ * ((∑ i ∈ T, a i) - (S.card : ℝ) / n * ∑ i, a i)))
              simp only [hpoint] at heq
              rw [heq]
              exact hsubsetMGF n S.card a θ hS hSn ha hθ
            have hmarkov : ∀ {n : ℕ} (P : Equiv.Perm (Fin n) → Prop)
                (f : Equiv.Perm (Fin n) → ℝ) (c : ℝ),
                (∀ σ, 0 ≤ f σ) → (∀ σ, P σ → c ≤ f σ) →
                c * probPerm P ≤ avgPerm f := by
              intro n P f c hf hPf
              have hsum : c * ((Finset.univ.filter P).card : ℝ) ≤ ∑ σ : Equiv.Perm (Fin n), f σ := by
                calc
                  c * ((Finset.univ.filter P).card : ℝ) = ∑ σ ∈ Finset.univ.filter P, c := by
                    simp [mul_comm]
                  _ ≤ ∑ σ ∈ Finset.univ.filter P, f σ :=
                    Finset.sum_le_sum (fun σ hσ => hPf σ (Finset.mem_filter.mp hσ).2)
                  _ ≤ ∑ σ : Equiv.Perm (Fin n), f σ :=
                    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                      (fun σ _ _ => hf σ)
              unfold probPerm avgPerm
              rw [← mul_div_assoc]
              exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
            have hpermTail : ∀ {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) (θ T : ℝ),
                0 < S.card → S.card < n → (∀ i, 0 ≤ a i ∧ a i ≤ 1) → 0 < θ → θ ≤ 1 →
                probPerm (fun σ => T ≤ (∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i) ≤
                  (n + 1 : ℝ) * Real.exp (((S.card : ℝ) / n) * θ ^ 2 * ∑ i, a i - θ * T) := by
              intro n S a θ T hS hSn ha hθ hθ1
              have hm := hmarkov
                (fun σ => T ≤ (∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i)
                (fun σ => Real.exp (θ * ((∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i)))
                (Real.exp (θ * T)) (fun σ => (Real.exp_pos _).le)
                (fun σ hσ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ hθ.le))
              have hbound := le_trans hm (hpermMGF S a θ hS hSn ha (by simpa [abs_of_pos hθ] using hθ1))
              have hdiv : probPerm (fun σ => T ≤ (∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i) ≤
                  ((n + 1 : ℝ) * Real.exp (((S.card : ℝ) / n) * θ ^ 2 * ∑ i, a i)) / Real.exp (θ * T) := by
                apply (le_div_iff₀ (Real.exp_pos (θ * T))).mpr
                rw [mul_comm]
                exact hbound
              simpa only [Real.exp_sub, mul_div_assoc] using hdiv
            have hpermExpTail : ∀ {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) (θ T : ℝ),
                0 < S.card → S.card < n → (∀ i, 0 ≤ a i ∧ a i ≤ 1) → |θ| ≤ 1 →
                probPerm (fun σ => T ≤ θ * ((∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i)) ≤
                  (n + 1 : ℝ) * Real.exp (((S.card : ℝ) / n) * θ ^ 2 * ∑ i, a i - T) := by
              intro n S a θ T hS hSn ha hθ
              have hm := hmarkov
                (fun σ => T ≤ θ * ((∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i))
                (fun σ => Real.exp (θ * ((∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i)))
                (Real.exp T) (fun σ => (Real.exp_pos _).le)
                (fun σ hσ => Real.exp_le_exp.mpr hσ)
              have hbound := le_trans hm (hpermMGF S a θ hS hSn ha hθ)
              have hdiv : probPerm (fun σ => T ≤ θ * ((∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i)) ≤
                  ((n + 1 : ℝ) * Real.exp (((S.card : ℝ) / n) * θ ^ 2 * ∑ i, a i)) / Real.exp T := by
                apply (le_div_iff₀ (Real.exp_pos T)).mpr
                rw [mul_comm]
                exact hbound
              simpa only [Real.exp_sub, mul_div_assoc] using hdiv
            have hprobMono : ∀ {n : ℕ} (P Q : Equiv.Perm (Fin n) → Prop),
                (∀ σ, P σ → Q σ) → probPerm P ≤ probPerm Q := by
              intro n P Q h
              unfold probPerm
              apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
              have hs : Finset.univ.filter P ⊆ Finset.univ.filter Q := by
                intro σ hσ
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h σ (Finset.mem_filter.mp hσ).2⟩
              exact_mod_cast Finset.card_le_card hs
            have hprobOr : ∀ {n : ℕ} (P Q : Equiv.Perm (Fin n) → Prop),
                probPerm (fun σ => P σ ∨ Q σ) ≤ probPerm P + probPerm Q := by
              intro n P Q
              have heq : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => P σ ∨ Q σ) =
                  (Finset.univ.filter P) ∪ (Finset.univ.filter Q) := by ext σ; simp
              have hcard : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => P σ ∨ Q σ)).card ≤
                  (Finset.univ.filter P).card + (Finset.univ.filter Q).card := by
                rw [heq]
                exact Finset.card_union_le _ _
              have hnum : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => P σ ∨ Q σ)).card : ℝ) ≤
                  ((Finset.univ.filter P).card : ℝ) + ((Finset.univ.filter Q).card : ℝ) := by exact_mod_cast hcard
              unfold probPerm
              rw [← add_div]
              apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
              convert hnum using 1 <;> congr 2 <;> (ext σ; simp)
            have hpermConcentration : ∀ {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) (h B : ℝ),
                0 < S.card → S.card < n → (∀ i, 0 ≤ a i ∧ a i ≤ 1) → 0 < h → h ≤ 1 → 0 ≤ B →
                probPerm (fun σ => h * ((S.card : ℝ) / n) * max B (∑ i, a i) ≤
                  |(∑ t ∈ S, a (σ t)) - (S.card : ℝ) / n * ∑ i, a i|) ≤
                  2 * (n + 1 : ℝ) * Real.exp (-h ^ 2 * ((S.card : ℝ) / n) * B / 4) := by
              intro n S a h B hS hSn ha hh hh1 hB
              let q : ℝ := (S.card : ℝ) / n
              let A : ℝ := ∑ i, a i
              let D : ℝ := max B A
              let Z : Equiv.Perm (Fin n) → ℝ := fun σ => (∑ t ∈ S, a (σ t)) - q * A
              have hq : 0 ≤ q := by dsimp [q]; positivity
              have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => (ha i).1
              have hD : 0 ≤ D := le_trans hB (le_max_left _ _)
              have hθ : |h / 2| ≤ 1 := by rw [abs_of_pos (half_pos hh)]; linarith only [hh1]
              have ht1 := hpermExpTail S a (h / 2) (h ^ 2 * q * D / 2) hS hSn ha hθ
              have ht2 := hpermExpTail S a (-h / 2) (h ^ 2 * q * D / 2) hS hSn ha
                (by simpa only [neg_div, abs_neg] using hθ)
              have hbexp : q * (h / 2) ^ 2 * A - h ^ 2 * q * D / 2 ≤ -h ^ 2 * q * B / 4 := by
                have hDA := mul_le_mul_of_nonneg_left (le_max_right B A)
                  (by positivity : 0 ≤ q * h ^ 2)
                have hDB := mul_le_mul_of_nonneg_left (le_max_left B A)
                  (by positivity : 0 ≤ q * h ^ 2)
                dsimp [D] at *
                nlinarith only [hDA, hDB]
              have hmonoExp := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbexp)
                (by positivity : 0 ≤ (n : ℝ) + 1)
              have ht1' : probPerm (fun σ => h * q * D ≤ Z σ) ≤
                  ((n : ℝ) + 1) * Real.exp (-h ^ 2 * q * B / 4) := by
                apply le_trans (hprobMono _ _ (fun σ hσ => ?_)) (le_trans ht1 hmonoExp)
                change h ^ 2 * q * D / 2 ≤ h / 2 * Z σ
                nlinarith only [hσ, hh]
              have ht2' : probPerm (fun σ => h * q * D ≤ -Z σ) ≤
                  ((n : ℝ) + 1) * Real.exp (-h ^ 2 * q * B / 4) := by
                have heq : (-h / 2) ^ 2 = (h / 2) ^ 2 := by ring
                rw [heq] at ht2
                apply le_trans (hprobMono _ _ (fun σ hσ => ?_)) (le_trans ht2 hmonoExp)
                change h ^ 2 * q * D / 2 ≤ -h / 2 * Z σ
                nlinarith only [hσ, hh]
              have hsplit := hprobMono
                (fun σ => h * q * D ≤ |Z σ|)
                (fun σ => h * q * D ≤ Z σ ∨ h * q * D ≤ -Z σ)
                (fun σ hσ => by rcases le_abs.mp hσ with h | h; exact Or.inl h; exact Or.inr (by linarith only [h]))
              have hor := hprobOr (fun σ => h * q * D ≤ Z σ) (fun σ => h * q * D ≤ -Z σ)
              change probPerm (fun σ => h * q * D ≤ |Z σ|) ≤ _
              linarith only [hsplit, hor, ht1', ht2']
            have hprobUnion : ∀ {n : ℕ} {α : Type} [DecidableEq α] (A : Finset α)
                (P : α → Equiv.Perm (Fin n) → Prop),
                probPerm (fun σ => ∃ c ∈ A, P c σ) ≤ ∑ c ∈ A, probPerm (P c) := by
              intro n α _ A P
              induction A using Finset.induction_on with
              | empty => simp [probPerm]
              | @insert c A hc ih =>
                have heq : (fun σ => ∃ d ∈ insert c A, P d σ) =
                    (fun σ => P c σ ∨ ∃ d ∈ A, P d σ) := by funext σ; simp
                rw [heq, Finset.sum_insert hc]
                have hor := hprobOr (P c) (fun σ => ∃ d ∈ A, P d σ)
                linarith only [hor, ih]
            have huniformConcentration : ∀ {n : ℕ} {α : Type} [DecidableEq α]
                (A : Finset α) (S : Finset (Fin n)) (a : α → Fin n → ℝ) (h B : ℝ),
                0 < S.card → S.card < n → (∀ c ∈ A, ∀ i, 0 ≤ a c i ∧ a c i ≤ 1) →
                0 < h → h ≤ 1 → 0 ≤ B →
                probPerm (fun σ => ∃ c ∈ A, h * ((S.card : ℝ) / n) * max B (∑ i, a c i) ≤
                  |(∑ t ∈ S, a c (σ t)) - (S.card : ℝ) / n * ∑ i, a c i|) ≤
                  (A.card : ℝ) * (2 * (n + 1 : ℝ) * Real.exp (-h ^ 2 * ((S.card : ℝ) / n) * B / 4)) := by
              intro n α _ A S a h B hS hSn ha hh hh1 hB
              apply le_trans (hprobUnion A _) ?_
              have hsum := Finset.sum_le_sum (fun c (hc : c ∈ A) =>
                hpermConcentration S (a c) h B hS hSn (ha c hc) hh hh1 hB)
              simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
            have havgSum : ∀ {n : ℕ} {α : Type} (T : Finset α)
                (f : Equiv.Perm (Fin n) → α → ℝ),
                avgPerm (fun σ => ∑ t ∈ T, f σ t) = ∑ t ∈ T, avgPerm (fun σ => f σ t) := by
              intro n α T f
              unfold avgPerm
              rw [Finset.sum_comm, Finset.sum_div]
            have hswapAverage : ∀ {n : ℕ} {β : Type} (ℓ : ℕ)
                (p : Equiv.Perm (Fin n) → β) (R : β → Fin n → ℝ),
                (∀ (σ : Equiv.Perm (Fin n)) (t u : Fin n), ℓ ≤ t.val → ℓ ≤ u.val →
                  p (σ * Equiv.swap t u) = p σ) →
                ∀ (t u : Fin n), ℓ ≤ t.val → ℓ ≤ u.val →
                  avgPerm (fun σ => R (p σ) (σ t)) = avgPerm (fun σ => R (p σ) (σ u)) := by
              intro n β ℓ p R hp t u ht hu
              unfold avgPerm
              congr 1
              calc
                (∑ σ : Equiv.Perm (Fin n), R (p σ) (σ t)) =
                    ∑ σ : Equiv.Perm (Fin n), R (p (σ * Equiv.swap t u)) ((σ * Equiv.swap t u) t) :=
                  (Equiv.sum_comp (Equiv.mulRight (Equiv.swap t u)) (fun σ => R (p σ) (σ t))).symm
                _ = ∑ σ : Equiv.Perm (Fin n), R (p σ) (σ u) := by
                  apply Finset.sum_congr rfl
                  intro σ hσ
                  rw [hp σ t u ht hu, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
            have hsegmentAverage : ∀ {n : ℕ} {β : Type} (ℓ : ℕ) (T : Finset (Fin n))
                (p : Equiv.Perm (Fin n) → β) (R : β → Fin n → ℝ),
                ℓ < n → (∀ t ∈ T, ℓ ≤ t.val) →
                (∀ (σ : Equiv.Perm (Fin n)) (t u : Fin n), ℓ ≤ t.val → ℓ ≤ u.val →
                  p (σ * Equiv.swap t u) = p σ) →
                avgPerm (fun σ => ∑ t ∈ T, R (p σ) (σ t)) =
                  (T.card : ℝ) / (n - ℓ : ℕ) *
                  avgPerm (fun σ => ∑ t ∈ Finset.univ.filter (fun t : Fin n => ℓ ≤ t.val), R (p σ) (σ t)) := by
              intro n β ℓ T p R hℓ hT hp
              let U := Finset.univ.filter (fun t : Fin n => ℓ ≤ t.val)
              let u : Fin n := ⟨ℓ, hℓ⟩
              have hconst : ∀ t, ℓ ≤ t.val →
                  avgPerm (fun σ => R (p σ) (σ t)) = avgPerm (fun σ => R (p σ) (σ u)) :=
                fun t ht => hswapAverage ℓ p R hp t u ht le_rfl
              have hTc : avgPerm (fun σ => ∑ t ∈ T, R (p σ) (σ t)) =
                  (T.card : ℝ) * avgPerm (fun σ => R (p σ) (σ u)) := by
                rw [havgSum]
                calc
                  (∑ t ∈ T, avgPerm (fun σ => R (p σ) (σ t))) =
                      ∑ t ∈ T, avgPerm (fun σ => R (p σ) (σ u)) :=
                    Finset.sum_congr rfl (fun t ht => hconst t (hT t ht))
                  _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
              have hUc : avgPerm (fun σ => ∑ t ∈ U, R (p σ) (σ t)) =
                  (U.card : ℝ) * avgPerm (fun σ => R (p σ) (σ u)) := by
                rw [havgSum]
                calc
                  (∑ t ∈ U, avgPerm (fun σ => R (p σ) (σ t))) =
                      ∑ t ∈ U, avgPerm (fun σ => R (p σ) (σ u)) :=
                    Finset.sum_congr rfl (fun t ht => hconst t (Finset.mem_filter.mp ht).2)
                  _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
              have hUcard : U.card = n - ℓ := by
                have heq : U = (firstTimes n ℓ)ᶜ := by ext t; simp [U, firstTimes, not_lt]
                rw [heq, Finset.card_compl]
                have hfirst : (firstTimes n ℓ).card = ℓ := by
                  unfold firstTimes
                  simp only [Fin.card_filter_val_lt, min_eq_right hℓ.le]
                simp [hfirst]
              change _ = (T.card : ℝ) / (n - ℓ : ℕ) * avgPerm (fun σ => ∑ t ∈ U, R (p σ) (σ t))
              rw [hTc, hUc, hUcard]
              have hne : ((n - ℓ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hℓ).ne'
              field_simp
            have hlearnedSwap : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (E ℓ : ℕ), IsValidMultiDualRule rule →
                ∀ (σ : Equiv.Perm (Fin n)) (t u : Fin n), ℓ ≤ t.val → ℓ ≤ u.val →
                  multiLearnedPrice I rule E (σ * Equiv.swap t u) ℓ = multiLearnedPrice I rule E σ ℓ := by
              intro m n k I rule E ℓ hr σ t u ht hu
              unfold multiLearnedPrice
              apply hr.1
              intro v hv
              have hvt : v ≠ t := by intro he; subst v; omega
              have hvu : v ≠ u := by intro he; subst v; omega
              simp only [MultiInstance.arrF, MultiInstance.arrG, Equiv.Perm.mul_apply,
                Equiv.swap_apply_of_ne_of_ne hvt hvu, and_self]
            have hsampleSwap : ∀ {n : ℕ} (ℓ : ℕ) (σ : Equiv.Perm (Fin n)) (t u : Fin n),
                ℓ ≤ t.val → ℓ ≤ u.val →
                (firstTimes n ℓ).image (σ * Equiv.swap t u) = (firstTimes n ℓ).image σ := by
              intro n ℓ σ t u ht hu
              apply Finset.image_congr
              intro v hv
              have hv' : v.val < ℓ := (Finset.mem_filter.mp hv).2
              have hvt : v ≠ t := by intro he; subst v; omega
              have hvu : v ≠ u := by intro he; subst v; omega
              rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hvt hvu]
            have hsurplusStable : ∀ {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ)
                (p : Fin m → ℝ) (c : Option (Fin k)), IsSurplusChoice f g p c →
                ¬ IsTied f g p → ∀ᶠ q in nhds p, IsSurplusChoice f g q c := by
              intro m k f g p c hc hnt
              have hcont : ∀ j, Continuous (fun q : Fin m → ℝ => surplus f g q j) := by
                intro j
                unfold surplus
                fun_prop
              cases c with
              | none =>
                have hneg : ∀ j, surplus f g p j < 0 := by
                  intro j
                  refine lt_of_le_of_ne (hc j) ?_
                  intro he
                  apply hnt
                  refine ⟨none, some j, by simp, by simp [score, he], ?_⟩
                  rintro (_ | r)
                  · exact le_rfl
                  · exact hc r
                have hev : ∀ᶠ q in nhds p, ∀ j, surplus f g q j < 0 :=
                  Filter.eventually_all.mpr (fun j => (hcont j).continuousAt.eventually_lt continuousAt_const (hneg j))
                filter_upwards [hev] with q hq
                exact fun j => (hq j).le
              | some r =>
                have hstrict : ∀ j, j ≠ r → surplus f g p j < surplus f g p r := by
                  intro j hj
                  refine lt_of_le_of_ne (hc.2 j) ?_
                  intro he
                  apply hnt
                  refine ⟨some r, some j, by simpa using (Ne.symm hj), he.symm, ?_⟩
                  rintro (_ | j')
                  · exact hc.1.le
                  · exact hc.2 j'
                have hpos : ∀ᶠ q in nhds p, 0 < surplus f g q r :=
                  continuousAt_const.eventually_lt (hcont r).continuousAt hc.1
                have hmax : ∀ᶠ q in nhds p, ∀ j, j ≠ r → surplus f g q j < surplus f g q r := by
                  apply Filter.eventually_all.mpr
                  intro j
                  by_cases hj : j = r
                  · exact Filter.Eventually.of_forall (fun q hne => False.elim (hne hj))
                  · filter_upwards [(hcont j).continuousAt.eventually_lt (hcont r).continuousAt (hstrict j hj)] with q hq
                    exact fun _ => hq
                filter_upwards [hpos, hmax] with q hpos hmax
                refine ⟨hpos, ?_⟩
                intro j
                by_cases hj : j = r
                · simp [hj]
                · exact (hmax j hj).le
            have hscoreVec : ∀ {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ)
                (p : Fin m → ℝ) (c : Option (Fin k)),
                score f g p c = ∑ j, surplus f g p j * choiceVec c j := by
              intro m k f g p c
              cases c <;> simp [score, choiceVec, eq_comm]
            have hshiftScore : ∀ {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ)
                (p : Fin m → ℝ) (c : Option (Fin k)) (i : Fin m) (z : ℝ),
                score f g (fun u => p u + if u = i then z else 0) c =
                  score f g p c - z * c.elim 0 (g i) := by
              intro m k f g p c i z
              cases c with
              | none => simp [score]
              | some r =>
                simp only [score, surplus, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
                  Finset.sum_ite_eq', Finset.mem_univ, if_true, Option.elim_some]
                ring
            have hresourceBand : ∀ {m n k : ℕ} (I : MultiInstance m n k) (S : Finset (Fin n))
                (d p : Fin m → ℝ) (c : Fin n → Option (Fin k)),
                I.GeneralPosition → IsBlockOptimalPrice S I.f I.g d p →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c t)) →
                ∀ i, (∑ t ∈ S, (c t).elim 0 (I.g t i)) ≤ d i + 2 * m ∧
                  (0 < p i → d i - 2 * m ≤ ∑ t ∈ S, (c t).elim 0 (I.g t i)) := by
              intro m n k I S d p c hgp hp hc i
              obtain ⟨y, hy, hmin⟩ := hp
              let shift : ℝ → Fin m → ℝ := fun z u => p u + if u = i then z else 0
              let v : Fin n → ℝ := fun t => score (I.f t) (I.g t) p (c t)
              let U : ℝ := ∑ t ∈ S, (c t).elim 0 (I.g t i)
              have hv : ∀ t, 0 ≤ v t ∧ ∀ j, surplus (I.f t) (I.g t) p j ≤ v t := by
                intro t
                rw [show v t = ∑ j, surplus (I.f t) (I.g t) p j * choiceVec (c t) j from hscoreVec _ _ _ _]
                exact hchoiceSurplus _ _ _ _ (hc t)
              have hG : ∀ t, 0 ≤ (c t).elim 0 (I.g t i) ∧ (c t).elim 0 (I.g t i) ≤ 1 := by
                intro t
                cases c t <;> simp [I.g_nonneg, I.g_le_one]
              have hJ : ((S.filter (fun t => IsTied (I.f t) (I.g t) p)).card : ℝ) ≤ m := by
                exact_mod_cast le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))) (hgp p)
              have hstable : ∀ᶠ z in nhds (0 : ℝ), ∀ t,
                  ¬ IsTied (I.f t) (I.g t) p → IsSurplusChoice (I.f t) (I.g t) (shift z) (c t) := by
                apply Filter.eventually_all.mpr
                intro t
                by_cases ht : IsTied (I.f t) (I.g t) p
                · exact Filter.Eventually.of_forall (fun z hnt => False.elim (hnt ht))
                · have hpath : Continuous shift := by
                    apply continuous_pi
                    intro u
                    dsimp [shift]
                    split <;> fun_prop
                  have hzero : shift 0 = p := by ext u; simp [shift]
                  have hlim : Filter.Tendsto shift (nhds 0) (nhds p) := hzero ▸ hpath.continuousAt.tendsto
                  filter_upwards [hlim.eventually (hsurplusStable _ _ _ _ (hc t) ht)] with z hz
                  exact fun _ => hz
              obtain ⟨η, hη, hηstable⟩ := Metric.eventually_nhds_iff.mp hstable
              have hcompare : ∀ z : ℝ, (∀ u, 0 ≤ shift z u) →
                  (∀ t, ¬ IsTied (I.f t) (I.g t) p → IsSurplusChoice (I.f t) (I.g t) (shift z) (c t)) →
                  z * (U - d i) ≤ 2 * |z| * m := by
                intro z hz hstable
                let Y : Fin n → ℝ := fun t => if IsTied (I.f t) (I.g t) p then v t + |z|
                  else score (I.f t) (I.g t) (shift z) (c t)
                have hY : IsBlockDualFeasible S I.f I.g (shift z) Y := by
                  refine ⟨hz, ?_⟩
                  intro t ht
                  by_cases htp : IsTied (I.f t) (I.g t) p
                  · simp only [Y, if_pos htp]
                    refine ⟨add_nonneg (hv t).1 (abs_nonneg _), ?_⟩
                    intro j
                    have hshift := hshiftScore (I.f t) (I.g t) p (some j) i z
                    change surplus (I.f t) (I.g t) (shift z) j =
                      surplus (I.f t) (I.g t) p j - z * I.g t i j at hshift
                    have hmul : -z * I.g t i j ≤ |z| := le_trans
                      (mul_le_mul_of_nonneg_right (neg_le_abs z) (I.g_nonneg t i j))
                      (mul_le_of_le_one_right (abs_nonneg _) (I.g_le_one t i j))
                    have hvj := (hv t).2 j
                    dsimp only [surplus] at hshift hvj
                    linarith only [hshift, hvj, hmul]
                  · simp only [Y, if_neg htp]
                    have hallowed := hchoiceSurplus _ _ _ _ (hstable t htp)
                    rw [← hscoreVec] at hallowed
                    refine ⟨hallowed.1, ?_⟩
                    intro j
                    have := hallowed.2 j
                    unfold surplus at this
                    linarith only [this]
                have hlower : ∑ u, d u * p u + ∑ t ∈ S, v t ≤ blockDualObj S d p y := by
                  unfold blockDualObj
                  apply add_le_add_right
                  apply Finset.sum_le_sum
                  intro t ht
                  cases hct : c t with
                  | none => simpa [v, hct, score] using (hy.2 t ht).1
                  | some r =>
                    have := (hy.2 t ht).2 r
                    change I.f t r ≤ (∑ u, p u * I.g t u r) + y t at this
                    dsimp only [v]
                    rw [hct]
                    change I.f t r - (∑ u, p u * I.g t u r) ≤ y t
                    linarith only [this]
                have hYbound : ∀ t, Y t ≤ v t - z * (c t).elim 0 (I.g t i) +
                    if IsTied (I.f t) (I.g t) p then 2 * |z| else 0 := by
                  intro t
                  by_cases ht : IsTied (I.f t) (I.g t) p
                  · simp only [Y, if_pos ht]
                    have hmul : z * (c t).elim 0 (I.g t i) ≤ |z| := le_trans
                      (mul_le_mul_of_nonneg_right (le_abs_self z) (hG t).1)
                      (mul_le_of_le_one_right (abs_nonneg _) (hG t).2)
                    linarith only [hmul]
                  · simp only [Y, if_neg ht, add_zero]
                    rw [hshiftScore]
                have hsumY : ∑ t ∈ S, Y t ≤ (∑ t ∈ S, v t) - z * U +
                    2 * |z| * ((S.filter (fun t => IsTied (I.f t) (I.g t) p)).card : ℝ) := by
                  have h := Finset.sum_le_sum (fun t (_ : t ∈ S) => hYbound t)
                  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
                    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, U, mul_comm, mul_assoc] using h
                have hprice : ∑ u, d u * shift z u = (∑ u, d u * p u) + z * d i := by
                  simp only [shift, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
                    Finset.sum_ite_eq', Finset.mem_univ, if_true]
                  ring
                have hval := le_trans hlower (hmin (shift z) Y hY)
                unfold blockDualObj at hval
                rw [hprice] at hval
                have hJ' := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ 2 * |z|)
                nlinarith only [hval, hsumY, hJ']
              constructor
              · let z : ℝ := η / 2
                have hz : 0 < z := by dsimp [z]; positivity
                have hzne : dist z 0 < η := by
                  rw [Real.dist_eq, sub_zero, abs_of_pos hz]
                  exact half_lt_self hη
                have hqnonneg : ∀ u, 0 ≤ shift z u := by
                  intro u
                  by_cases hui : u = i
                  · simp only [shift, if_pos hui]
                    exact add_nonneg (hy.1 u) hz.le
                  · simp only [shift, if_neg hui, add_zero]
                    exact hy.1 u
                have hcomp := hcompare z hqnonneg (hηstable hzne)
                rw [abs_of_pos hz] at hcomp
                change U ≤ d i + 2 * m
                nlinarith only [hcomp, hz]
              · intro hpi
                let z : ℝ := min (η / 2) (p i / 2)
                have hz : 0 < z := lt_min (by positivity) (by positivity)
                have hzne : dist (-z) 0 < η := by
                  rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hz]
                  exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
                have hqnonneg : ∀ u, 0 ≤ shift (-z) u := by
                  intro u
                  dsimp [shift]
                  by_cases hui : u = i
                  · subst u
                    rw [if_pos rfl]
                    have := min_le_right (η / 2) (p i / 2)
                    dsimp only [z] at *
                    linarith only [this, hpi]
                  · simp only [if_neg hui, add_zero]
                    exact hy.1 u
                have hcomp := hcompare (-z) hqnonneg (hηstable hzne)
                rw [abs_neg, abs_of_pos hz] at hcomp
                change d i - 2 * m ≤ U
                nlinarith only [hcomp, hz]
            have htotalProposalFits : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (rule : MultiDualRule m n k) (tie : TieRule m n k) (ε : ℝ) (σ : Equiv.Perm (Fin n)),
                (∀ i, (∑ t, ∑ j, I.arrG σ t i j * multiProposal I rule tie ε σ t j) ≤ I.b i) →
                ∀ t, multiX I rule tie ε σ t = multiProposal I rule tie ε σ t := by
              intro m n k I rule tie ε σ hfit
              let use : Fin n → Fin m → ℝ := fun t i => ∑ j, I.arrG σ t i j * multiProposal I rule tie ε σ t j
              let U : ℕ → Fin m → ℝ := fun τ i => ∑ t ∈ Finset.univ.filter (fun t : Fin n => t.val < τ), use t i
              have huse : ∀ t i, 0 ≤ use t i := fun t i =>
                Finset.sum_nonneg fun j _ => mul_nonneg (I.g_nonneg _ _ _) (hproposal I rule tie ε σ t j)
              have hmono : ∀ τ s, τ ≤ s → ∀ i, U τ i ≤ U s i := by
                intro τ s hτs i
                exact Finset.sum_le_sum_of_subset_of_nonneg
                  (by intro t ht; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp ht).2 hτs⟩)
                  (fun t ht htn => huse t i)
              have hrec : ∀ τ (hτ : τ < n) i, U (τ + 1) i = U τ i + use ⟨τ, hτ⟩ i := by
                intro τ hτ i
                have heq : Finset.univ.filter (fun t : Fin n => t.val < τ + 1) =
                    insert ⟨τ, hτ⟩ (Finset.univ.filter (fun t : Fin n => t.val < τ)) := by
                  ext t
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.mk.injEq]
                  constructor
                  · intro ht
                    by_cases he : t.val = τ
                    · exact Or.inl (Fin.ext he)
                    · exact Or.inr (by omega)
                  · rintro (rfl | h)
                    · simp
                    · omega
                dsimp only [U]
                rw [heq, Finset.sum_insert (by simp)]
                ring
              have hdec : ∀ used t j, multiDecision I rule tie ε σ used t j ≤ multiProposal I rule tie ε σ t j := by
                intro used t j
                unfold multiDecision
                split
                · exact le_rfl
                · exact hproposal I rule tie ε σ t j
              have hactual : ∀ τ i, multiUsed I rule tie ε σ τ i ≤ U τ i := by
                intro τ
                induction τ with
                | zero => simp [multiUsed, U]
                | succ τ ih =>
                  intro i
                  simp only [multiUsed]
                  split
                  · rename_i hτ
                    rw [hrec τ hτ i]
                    apply add_le_add (ih i)
                    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hdec _ _ j) (I.g_nonneg _ _ _)
                  · exact le_trans (ih i) (hmono τ (τ + 1) (by omega) i)
              have hUn : ∀ i, U n i ≤ I.b i := by
                intro i
                simpa [U, use] using hfit i
              intro t
              unfold multiX multiDecision
              rw [if_pos]
              intro i
              have hstep := hrec t.val t.isLt i
              have hsum := hmono (t.val + 1) n t.isLt i
              have ha := hactual t.val i
              have hb := hUn i
              change use t i ≤ I.b i - multiUsed I rule tie ε σ t.val i
              linarith only [hstep, hsum, ha, hb]
            have hchoiceResourceDiff : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (p : Fin m → ℝ) (c c' : Fin n → Option (Fin k)) (S : Finset (Fin n)),
                I.GeneralPosition →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c t)) →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c' t)) →
                ∀ i, |(∑ t ∈ S, (c t).elim 0 (I.g t i)) - (∑ t ∈ S, (c' t).elim 0 (I.g t i))| ≤ m := by
              intro m n k I p c c' S hgp hc hc' i
              have hcard : (S.filter (fun t => c t ≠ c' t)).card ≤ m :=
                le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S)))
                  (hchoicesDiffer I p c c' hgp hc hc')
              have hG : ∀ t, 0 ≤ (c t).elim 0 (I.g t i) ∧ (c t).elim 0 (I.g t i) ≤ 1 := by
                intro t
                cases c t <;> simp [I.g_nonneg, I.g_le_one]
              have hG' : ∀ t, 0 ≤ (c' t).elim 0 (I.g t i) ∧ (c' t).elim 0 (I.g t i) ≤ 1 := by
                intro t
                cases c' t <;> simp [I.g_nonneg, I.g_le_one]
              rw [← Finset.sum_sub_distrib]
              apply le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
              have hbound : ∑ t ∈ S, |(c t).elim 0 (I.g t i) - (c' t).elim 0 (I.g t i)| ≤
                  ((S.filter (fun t => c t ≠ c' t)).card : ℝ) := by
                calc
                  (∑ t ∈ S, |(c t).elim 0 (I.g t i) - (c' t).elim 0 (I.g t i)|) ≤
                      ∑ t ∈ S, if c t ≠ c' t then (1 : ℝ) else 0 := by
                    apply Finset.sum_le_sum
                    intro t ht
                    by_cases he : c t = c' t
                    · simp [he]
                    · simp only [if_pos he]
                      apply abs_le.mpr
                      constructor <;> linarith [(hG t).1, (hG t).2, (hG' t).1, (hG' t).2]
                  _ = _ := by rw [← Finset.sum_filter]; simp
              exact le_trans hbound (by exact_mod_cast hcard)
            have hchoiceScoreMax : ∀ {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ)
                (p : Fin m → ℝ) (c : Option (Fin k)), IsSurplusChoice f g p c →
                ∀ c', score f g p c' ≤ score f g p c := by
              intro m k f g p c hc c'
              cases c with
              | none =>
                cases c' with
                | none => exact le_rfl
                | some j => exact hc j
              | some r =>
                cases c' with
                | none => exact hc.1.le
                | some j => exact hc.2 j
            have hchoiceRewardDiff : ∀ {m n k : ℕ} (I : MultiInstance m n k)
                (p : Fin m → ℝ) (c c' : Fin n → Option (Fin k)) (S : Finset (Fin n)),
                I.GeneralPosition → (∀ i, 0 ≤ p i) →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c t)) →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c' t)) →
                (∑ t ∈ S, (c t).elim 0 (I.f t)) ≤
                  (∑ t ∈ S, (c' t).elim 0 (I.f t)) + (m : ℝ) * ∑ i, p i := by
              intro m n k I p c c' S hgp hp hc hc'
              have heq : ∀ t, (c t).elim 0 (I.f t) - (c' t).elim 0 (I.f t) =
                  ∑ i, p i * ((c t).elim 0 (I.g t i) - (c' t).elim 0 (I.g t i)) := by
                intro t
                have hsc : score (I.f t) (I.g t) p (c t) = score (I.f t) (I.g t) p (c' t) :=
                  le_antisymm (hchoiceScoreMax _ _ _ _ (hc' t) _) (hchoiceScoreMax _ _ _ _ (hc t) _)
                rw [hscoreLinear, hscoreLinear] at hsc
                simp only [mul_sub, Finset.sum_sub_distrib]
                linarith only [hsc]
              have hsum : (∑ t ∈ S, (c t).elim 0 (I.f t)) - (∑ t ∈ S, (c' t).elim 0 (I.f t)) =
                  ∑ i, p i * ((∑ t ∈ S, (c t).elim 0 (I.g t i)) - (∑ t ∈ S, (c' t).elim 0 (I.g t i))) := by
                rw [← Finset.sum_sub_distrib]
                simp_rw [heq]
                rw [Finset.sum_comm]
                simp only [Finset.sum_sub_distrib, Finset.mul_sum, mul_sub]
              have hle : ∑ i, p i * ((∑ t ∈ S, (c t).elim 0 (I.g t i)) - (∑ t ∈ S, (c' t).elim 0 (I.g t i))) ≤
                  (m : ℝ) * ∑ i, p i := by
                rw [Finset.mul_sum]
                apply Finset.sum_le_sum
                intro i hi
                have hdiff := (abs_le.mp (hchoiceResourceDiff I p c c' S hgp hc hc' i)).2
                simpa only [mul_comm] using mul_le_mul_of_nonneg_left hdiff (hp i)
              linarith only [hsum, hle]
            have havgMono : ∀ {n : ℕ} (f g : Equiv.Perm (Fin n) → ℝ),
                (∀ σ, f σ ≤ g σ) → avgPerm f ≤ avgPerm g := by
              intro n f g h
              exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _ => h σ)) (Nat.cast_nonneg _)
            have havgAdd : ∀ {n : ℕ} (f g : Equiv.Perm (Fin n) → ℝ),
                avgPerm (fun σ => f σ + g σ) = avgPerm f + avgPerm g := by
              intros; simp [avgPerm, Finset.sum_add_distrib, add_div]
            have havgSub : ∀ {n : ℕ} (f g : Equiv.Perm (Fin n) → ℝ),
                avgPerm (fun σ => f σ - g σ) = avgPerm f - avgPerm g := by
              intros; simp [avgPerm, Finset.sum_sub_distrib, sub_div]
            have havgMul : ∀ {n : ℕ} (c : ℝ) (f : Equiv.Perm (Fin n) → ℝ),
                avgPerm (fun σ => c * f σ) = c * avgPerm f := by
              intros; simp only [avgPerm, ← Finset.mul_sum, mul_div_assoc]
            have havgConst : ∀ {n : ℕ} (c : ℝ), avgPerm (fun _ : Equiv.Perm (Fin n) => c) = c := by
              intro n c
              simp [avgPerm, Fintype.card_ne_zero]
            have havgError : ∀ {n : ℕ} (f g : Equiv.Perm (Fin n) → ℝ) (K : ℝ)
                (P : Equiv.Perm (Fin n) → Prop),
                (∀ σ, f σ ≤ g σ + if P σ then K else 0) →
                avgPerm f ≤ avgPerm g + K * probPerm P := by
              intro n f g K P h
              apply le_trans (havgMono f _ h)
              rw [havgAdd]
              apply le_of_eq
              congr 1
              simp only [avgPerm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, probPerm]
              ring
            have hsumChoice : ∀ {k : ℕ} (c : Option (Fin k)) (a : Fin k → ℝ),
                (∑ j, a j * choiceVec c j) = c.elim 0 a := by
              intro k c a
              cases c <;> simp [choiceVec, eq_comm]
            have hpermGP : ∀ {m n k : ℕ} (I : MultiInstance m n k) (σ : Equiv.Perm (Fin n)),
                I.GeneralPosition → BlockGeneralPositionOn Finset.univ (I.arrF σ) (I.arrG σ) := by
              intro m n k I σ h p
              have he : (Finset.univ.filter (fun t => IsTied (I.arrF σ t) (I.arrG σ t) p)).image σ =
                  Finset.univ.filter (fun t => IsTied (I.f t) (I.g t) p) := by
                ext t
                simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · rintro ⟨u, hu, rfl⟩; exact hu
                · intro ht; exact ⟨σ.symm t, by simpa [MultiInstance.arrF, MultiInstance.arrG] using ht, by simp⟩
              have hc := Finset.card_image_of_injective
                (Finset.univ.filter (fun t => IsTied (I.arrF σ t) (I.arrG σ t) p)) σ.injective
              rw [he] at hc
              rw [← hc]
              exact h p
            have hbandArr : ∀ {m n k : ℕ} (I : MultiInstance m n k) (σ : Equiv.Perm (Fin n))
                (S : Finset (Fin n)) (d p : Fin m → ℝ) (c : Fin n → Option (Fin k)),
                I.GeneralPosition → IsBlockOptimalPrice S (I.arrF σ) (I.arrG σ) d p →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c t)) →
                ∀ i, (∑ t ∈ S, (c (σ t)).elim 0 (I.g (σ t) i)) ≤ d i + 2 * m ∧
                  (0 < p i → d i - 2 * m ≤ ∑ t ∈ S, (c (σ t)).elim 0 (I.g (σ t) i)) := by
              intro m n k I σ S d p c hgp hp hc
              let J : MultiInstance m n k :=
                { f := I.arrF σ, g := I.arrG σ, b := I.b,
                  f_nonneg := fun t j => I.f_nonneg (σ t) j,
                  g_nonneg := fun t i j => I.g_nonneg (σ t) i j,
                  g_le_one := fun t i j => I.g_le_one (σ t) i j }
              exact hresourceBand J S d p (fun t => c (σ t)) (hpermGP I σ hgp) hp (fun t => hc (σ t))
            have hscalarBand : ∀ (b G s h e : ℝ), 0 ≤ b → 0 ≤ G → 0 < h → h ≤ 1 / 2 →
                e ≤ h * b / 16 → s ≤ (1 - h) * b + e →
                |s - G| ≤ h / 16 * max b G →
                G ≤ (1 - h / 2) * b ∧ ((1 - h) * b - e ≤ s → (1 - 2 * h) * b ≤ G) := by
              intro b G s h e hb hG hh hh1 he hs hd
              have hGb : G ≤ b := by
                by_contra hn
                have hbG : b ≤ G := (lt_of_not_ge hn).le
                rw [max_eq_right hbG] at hd
                have hd' := (abs_le.mp hd).1
                have hprod : 0 ≤ (1 - h / 16) * (G - b) := mul_nonneg (by linarith) (by linarith)
                nlinarith
              rw [max_eq_left hGb] at hd
              obtain ⟨hd1, hd2⟩ := abs_le.mp hd
              constructor
              · nlinarith
              · intro hl; nlinarith
            have hfirstCard : ∀ (n ℓ : ℕ), ℓ ≤ n → (firstTimes n ℓ).card = ℓ := by
              intro n ℓ h
              simp [firstTimes, Fin.card_filter_val_lt, min_eq_right h]
            have hfirstAvg : ∀ {n : ℕ} (ℓ : ℕ) (a : Fin n → ℝ), ℓ ≤ n → 0 < n →
                avgPerm (fun σ => ∑ t ∈ firstTimes n ℓ, a (σ t)) = (ℓ : ℝ) / n * ∑ t, a t := by
              intro n ℓ a hℓ hn
              have he := hpermSubsetAverage (firstTimes n ℓ) (fun S => ∑ t ∈ S, a t)
              have hc := hfirstCard n ℓ hℓ
              have hav : ∀ t : Fin n, avgPerm (fun σ => a (σ t)) = (∑ u, a u) / n := by
                intro t
                have hi : ∀ t u : Fin n, avgPerm (fun σ => a (σ t)) = avgPerm (fun σ => a (σ u)) := by
                  intro t u
                  exact hswapAverage 0 (fun _ : Equiv.Perm (Fin n) => ()) (fun _ t => a t)
                    (fun _ _ _ _ _ => rfl) t u (Nat.zero_le _) (Nat.zero_le _)
                have hs : ∑ u : Fin n, avgPerm (fun σ => a (σ u)) = ∑ u, a u := by
                  rw [← havgSum]
                  have heq : (fun σ : Equiv.Perm (Fin n) => ∑ u, a (σ u)) = fun _ => ∑ u, a u := by
                    funext σ; exact Equiv.sum_comp σ a
                  rw [heq, havgConst]
                have hs' : (n : ℝ) * avgPerm (fun σ => a (σ t)) = ∑ u, a u := by
                  calc
                    (n : ℝ) * avgPerm (fun σ => a (σ t)) = ∑ u : Fin n, avgPerm (fun σ => a (σ t)) := by simp
                    _ = ∑ u : Fin n, avgPerm (fun σ => a (σ u)) :=
                      Finset.sum_congr rfl (fun u _ => hi t u)
                    _ = ∑ u, a u := hs
                exact (eq_div_iff (by exact_mod_cast hn.ne')).mpr (by linarith only [hs'])
              rw [havgSum]
              simp only [hav, Finset.sum_const, hc, nsmul_eq_mul]
              ring
            have hlearnLast : ∀ (n E : ℕ), learnTime n E E = n := by
              intro n E
              have heq : (2 : ℝ) ^ E * eps E * (n : ℝ) = (n : ℝ) := by simp [eps]
              rw [learnTime, heq, Nat.ceil_natCast]
            have hlearnMono : ∀ (n E r s : ℕ), r ≤ s → learnTime n E r ≤ learnTime n E s := by
              intro n E r s hrs
              apply Nat.ceil_mono
              have hp : (2 : ℝ) ^ r ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hrs
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by unfold eps; positivity)) (Nat.cast_nonneg n)
            have hlearnDouble : ∀ (n E r : ℕ), learnTime n E (r + 1) ≤ 2 * learnTime n E r := by
              intro n E r
              apply Nat.ceil_le.mpr
              have h := Nat.le_ceil ((2 : ℝ) ^ r * eps E * (n : ℝ))
              push_cast
              rw [pow_succ]
              change 2 ^ r * 2 * eps E * n ≤ 2 * (learnTime n E r : ℝ)
              change 2 ^ r * eps E * n ≤ (learnTime n E r : ℝ) at h
              linarith only [h]
            have hlearnBounds : ∀ (n E r : ℕ), 1 ≤ eps E * (n : ℝ) →
                0 < learnTime n E r ∧ eps E * (n : ℝ) ≤ learnTime n E r := by
              intro n E r hwindow
              have hp : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
              have hlow : eps E * (n : ℝ) ≤ (2 : ℝ) ^ r * eps E * (n : ℝ) := by
                have hmul := mul_le_mul_of_nonneg_right hp (by unfold eps; positivity : 0 ≤ eps E * (n : ℝ))
                simpa only [one_mul, mul_assoc] using hmul
              have hceil := Nat.le_ceil ((2 : ℝ) ^ r * eps E * (n : ℝ))
              have hle : eps E * (n : ℝ) ≤ (learnTime n E r : ℝ) := le_trans hlow hceil
              exact ⟨by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hwindow hle)), hle⟩
            have hslackSmall : ∀ (n E ℓ : ℕ), 0 < ℓ → eps E * (n : ℝ) ≤ (ℓ : ℝ) → slack n E ℓ ≤ 1 := by
              intro n E ℓ hℓ hlow
              have hδ : 0 ≤ eps E := by unfold eps; positivity
              have hδ1 : eps E ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
              have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
              have hbound : eps E ^ 2 * (n : ℝ) ≤ (ℓ : ℝ) := by
                have hmul := mul_le_mul_of_nonneg_left hlow hδ
                have hmul' := mul_le_of_le_one_left hℓ'.le hδ1
                nlinarith only [hmul, hmul']
              have hs : (slack n E ℓ) ^ 2 ≤ 1 := by
                rw [slack, mul_pow, Real.sq_sqrt (by positivity), ← mul_div_assoc]
                apply (div_le_iff₀ hℓ').mpr
                simpa only [one_mul] using hbound
              have hs0 : 0 ≤ slack n E ℓ := by unfold slack; positivity
              nlinarith only [hs, hs0]
            have hphaseInterval : ∀ (n E τ : ℕ), 1 ≤ E → τ < n → learnTime n E 0 ≤ τ →
                phaseIndex n E τ < E ∧ learnTime n E (phaseIndex n E τ) ≤ τ ∧
                  τ < learnTime n E (phaseIndex n E τ + 1) := by
              intro n E τ hE hτ hlearn
              let F := (Finset.range E).filter (fun r => learnTime n E r ≤ τ)
              have hF : F.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hlearn⟩⟩
              have hmem : phaseIndex n E τ ∈ F := by
                obtain ⟨r, hr, heq⟩ := Finset.exists_mem_eq_sup F hF id
                change F.sup id ∈ F
                rw [heq]
                exact hr
              obtain ⟨hr, hstart⟩ := Finset.mem_filter.mp hmem
              have hr' : phaseIndex n E τ < E := Finset.mem_range.mp hr
              refine ⟨hr', hstart, ?_⟩
              by_contra hnot
              have hend : learnTime n E (phaseIndex n E τ + 1) ≤ τ := le_of_not_gt hnot
              by_cases hnext : phaseIndex n E τ + 1 < E
              · have hm : phaseIndex n E τ + 1 ∈ F := Finset.mem_filter.mpr
                  ⟨Finset.mem_range.mpr hnext, hend⟩
                have hs := Finset.le_sup (f := id) hm
                change phaseIndex n E τ + 1 ≤ phaseIndex n E τ at hs
                omega
              · have heq : phaseIndex n E τ + 1 = E := by omega
                rw [heq, hlearnLast] at hend
                omega
            have hphaseIndexEq : ∀ (n E τ r : ℕ), r < E →
                learnTime n E r ≤ τ → τ < learnTime n E (r + 1) → phaseIndex n E τ = r := by
              intro n E τ r hr hstart hend
              apply le_antisymm
              · apply Finset.sup_le
                intro s hs
                have hstart' := (Finset.mem_filter.mp hs).2
                change learnTime n E s ≤ τ at hstart'
                by_contra hnot
                change ¬ s ≤ r at hnot
                have hmono := hlearnMono n E (r + 1) s (by omega)
                omega
              · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hstart⟩)
            have hdyadic : ∀ ε : ℝ, 0 < ε → ε < 1 →
                ε / 2 < eps (accuracyExp ε) ∧ eps (accuracyExp ε) ≤ ε := by
              intro ε hε hsmall
              have hlog : 0 < Real.logb 2 (1 / ε) :=
                Real.logb_pos (by norm_num) ((lt_div_iff₀ hε).2 (by linarith))
              have hEle : Real.logb 2 (1 / ε) ≤ (accuracyExp ε : ℝ) :=
                le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
              have hElt : (accuracyExp ε : ℝ) < Real.logb 2 (1 / ε) + 1 := by
                unfold accuracyExp
                rw [Nat.cast_max]
                exact max_lt (by simpa only [Nat.cast_one] using (by linarith : (1 : ℝ) < Real.logb 2 (1 / ε) + 1)) (Nat.ceil_lt_add_one hlog.le)
              have hp := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hElt
              rw [Real.rpow_natCast, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_one] at hp
              constructor
              · rw [eps, div_pow, one_pow]
                apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ accuracyExp ε)).2
                have hp' : (2 : ℝ) ^ accuracyExp ε * ε < 2 :=
                  (lt_div_iff₀ hε).mp (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hp)
                nlinarith
              · rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast] at hEle
                rw [eps, div_pow, one_pow, div_le_iff₀ (by positivity)]
                rw [div_le_iff₀ hε] at hEle
                linarith
            refine ⟨1073741824, 4096, by norm_num, by norm_num, ?_⟩
            intro m n k ε I rule tie hm hn hk hε hgp hr ht hb hB
            by_cases heasy : 1 ≤ 4096 * ε
            · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hopt I hb))
                (havg I rule tie ε)
            have hsmall : ε < 1 / 4096 := by linarith
            have hlog : 1 ≤ Real.log ((n : ℝ) * (k : ℝ) / ε) := by
              have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
              have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
              have harg : (4 : ℝ) ≤ (n : ℝ) * (k : ℝ) / ε := by
                rw [le_div_iff₀ hε]
                nlinarith
              have hlog4 : 1 ≤ Real.log 4 := by
                have := Real.log_two_gt_d9
                have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
                  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
                linarith
              exact le_trans hlog4 (Real.log_le_log (by norm_num) harg)
            by_cases hwindow : eps (accuracyExp ε) * (n : ℝ) < 1
            · have hbudget : ∀ i, (n : ℝ) ≤ I.b i := by
                intro i
                have hδ := (hdyadic ε hε (by linarith)).1
                have hn' : (0 : ℝ) < n := by exact_mod_cast hn
                have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
                have hne : (n : ℝ) * ε < 2 := by
                  have hdn := mul_lt_mul_of_pos_right hδ hn'
                  nlinarith only [hdn, hwindow]
                have hB' := (div_le_iff₀ (sq_pos_of_pos hε)).1 (hB i)
                have hmLog : (1 : ℝ) ≤ (m : ℝ) * Real.log ((n : ℝ) * (k : ℝ) / ε) :=
                  le_trans hm' (le_mul_of_one_le_right (by positivity) hlog)
                have hne2 : (n : ℝ) * ε ^ 2 < 1 := by
                  calc
                    (n : ℝ) * ε ^ 2 = ((n : ℝ) * ε) * ε := by ring
                    _ < 2 * ε := mul_lt_mul_of_pos_right hne hε
                    _ < 1 := by linarith only [hsmall]
                have hb' : 1073741824 ≤ I.b i * ε ^ 2 := le_trans (by linarith only [hmLog]) hB'
                exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hε)).mp
                  (le_trans hne2.le (by linarith only [hb']))
              have hpoint : ∀ σ : Equiv.Perm (Fin n), I.OPT ≤ multiValue I rule tie ε σ :=
                hshort I rule tie ε hbudget ht hwindow
              have hmean : I.OPT ≤ avgPerm (fun σ => multiValue I rule tie ε σ) := by
                unfold avgPerm
                rw [le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]
                simpa [mul_comm] using Finset.sum_le_sum
                  (s := Finset.univ) (fun σ _ => hpoint σ)
              exact le_trans (by nlinarith [hopt I hb]) hmean
            have hwindow' : 1 ≤ eps (accuracyExp ε) * (n : ℝ) := le_of_not_gt hwindow
            let pstar : Fin m → ℝ := rule n I.f I.g I.b
            obtain ⟨ystar, hstar⟩ := hr.2 n I.f I.g I.b le_rfl hb
            have hfirstAll : firstTimes n n = Finset.univ := by
              ext t
              simp only [firstTimes, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
              exact t.isLt
            rw [hfirstAll] at hstar
            let V : ℝ := blockDualObj Finset.univ I.b pstar ystar
            have hVnonneg : 0 ≤ V := by
              exact add_nonneg
                (Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (hstar.1.1 i))
                (Finset.sum_nonneg fun t ht => (hstar.1.2 t ht).1)
            have hVopt : I.OPT ≤ V := hoptDual I pstar ystar hb hstar.1
            have hVdual : ∀ p y, IsBlockDualFeasible Finset.univ I.f I.g p y →
                V ≤ blockDualObj Finset.univ I.b p y := hstar.2
            have hpriceBound : ∀ B : ℝ, (∀ i, B ≤ I.b i) → B * ∑ i, pstar i ≤ V := by
              intro B hBmin
              have hresource : B * ∑ i, pstar i ≤ ∑ i, I.b i * pstar i := by
                rw [Finset.mul_sum]
                exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hBmin i) (hstar.1.1 i)
              have hy0 : 0 ≤ ∑ t, ystar t := Finset.sum_nonneg fun t ht => (hstar.1.2 t ht).1
              exact le_trans hresource (by dsimp [V, blockDualObj]; linarith only [hy0])
            have hphasePrice : ∀ (r : ℕ) (σ : Equiv.Perm (Fin n)), r < accuracyExp ε →
                IsBlockOptimalPrice (firstTimes n (learnTime n (accuracyExp ε) r))
                  (I.arrF σ) (I.arrG σ)
                  (fun i => (1 - slack n (accuracyExp ε) (learnTime n (accuracyExp ε) r)) *
                    ((learnTime n (accuracyExp ε) r : ℝ) / n) * I.b i)
                  (multiLearnedPrice I rule (accuracyExp ε) σ (learnTime n (accuracyExp ε) r)) := by
              intro r σ hr'
              apply hr.2
              · exact le_trans (hlearnMono n (accuracyExp ε) r (accuracyExp ε) hr'.le)
                  (by rw [hlearnLast])
              · intro i
                have hL := hlearnBounds n (accuracyExp ε) r hwindow'
                have hslack := hslackSmall n (accuracyExp ε) _ hL.1 hL.2
                exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hslack) (by positivity)) (hb i)
            obtain ⟨A, hAcard, hAcover⟩ := hpriceCover I
            have hAcost : ∀ c ∈ A, ∀ (t : Fin n) (i : Fin m),
                0 ≤ (c t).elim 0 (I.g t i) ∧ (c t).elim 0 (I.g t i) ≤ 1 := by
              intro c hc t i
              cases c t <;> simp [I.g_nonneg, I.g_le_one]
            have hAconcentration : ∀ (S : Finset (Fin n)) (h B : ℝ) (i : Fin m),
                0 < S.card → S.card < n → 0 < h → h ≤ 1 → 0 ≤ B →
                probPerm (fun σ => ∃ c ∈ A, h * ((S.card : ℝ) / n) *
                  max B (∑ t, (c t).elim 0 (I.g t i)) ≤
                  |(∑ t ∈ S, (c (σ t)).elim 0 (I.g (σ t) i)) -
                    (S.card : ℝ) / n * ∑ t, (c t).elim 0 (I.g t i)|) ≤
                  (A.card : ℝ) * (2 * (n + 1 : ℝ) * Real.exp (-h ^ 2 * ((S.card : ℝ) / n) * B / 4)) := by
              intro S h B i hS hSn hh hh1 hB'
              exact huniformConcentration A S (fun c t => (c t).elim 0 (I.g t i)) h B
                hS hSn (fun c hc t => hAcost c hc t i) hh hh1 hB'
            have hglobalPerformance : ∀ (p : Fin m → ℝ) (c : Fin n → Option (Fin k)) (ρ : ℝ),
                (∀ i, 0 ≤ p i) → 0 ≤ ρ → ρ ≤ 1 →
                (∀ t, IsSurplusChoice (I.f t) (I.g t) p (c t)) →
                (∀ i, 0 < p i → ρ * I.b i ≤ ∑ t, ∑ j, I.g t i j * choiceVec (c t) j) →
                ρ * V ≤ ∑ t, ∑ j, I.f t j * choiceVec (c t) j := by
              intro p c ρ hp hρ hρ1 hc huse
              exact hpricePerformance I p c ρ V hb hp hρ hρ1 hc huse hVdual
            by_cases hVz : V = 0
            · have hoptz : I.OPT = 0 := le_antisymm (by simpa only [hVz] using hVopt) (hopt I hb)
              rw [hoptz, mul_zero]
              exact havg I rule tie ε
            have hVpos : 0 < V := lt_of_le_of_ne hVnonneg (Ne.symm hVz)
            apply le_trans (mul_le_mul_of_nonneg_left hVopt (by linarith only [heasy]))
            have hRule := hr
            let E := accuracyExp ε
            let δ := eps E
            let L : ℕ → ℕ := learnTime n E
            let H : ℕ → ℝ := fun r => slack n E (L r)
            let q : ℕ → ℝ := fun r => (L r : ℝ) / n
            let T : ℕ → Finset (Fin n) := fun r => firstTimes n (L (r + 1)) \ firstTimes n (L r)
            have hn0 : 0 < n := by omega
            have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
            have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
            have hδ : 0 < δ := by dsimp [δ, E]; unfold eps; positivity
            have hδε : ε / 2 < δ ∧ δ ≤ ε := hdyadic ε hε (by linarith)
            have hδsmall : δ < 1 / 4096 := lt_of_le_of_lt hδε.2 hsmall
            have hδn : 1 ≤ δ * (n : ℝ) := hwindow'
            have hEL : 1 ≤ E := le_max_left _ _
            have hLlast : L E = n := hlearnLast n E
            have hLm : ∀ r s, r ≤ s → L r ≤ L s := hlearnMono n E
            have hLpos : ∀ r, 0 < L r := fun r => (hlearnBounds n E r hwindow').1
            have hLlow : ∀ r, δ * (n : ℝ) ≤ L r := fun r => (hlearnBounds n E r hwindow').2
            have hLle : ∀ r, r ≤ E → L r ≤ n := fun r hr => by
              simpa only [hLlast] using hLm r E hr
            have hnlarge : (4 : ℝ) ≤ n := by nlinarith only [hδsmall, hδn, hnR]
            have hqpos : ∀ r, 0 < q r := fun r => div_pos (by exact_mod_cast hLpos r) hnR
            have hqδ : ∀ r, δ ≤ q r := fun r => (le_div_iff₀ hnR).mpr (hLlow r)
            have hqle : ∀ r, r < E → q r ≤ 3 / 4 := by
              intro r hr
              have hp : (2 : ℝ) ^ (r + 1) ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) (by omega)
              have heq : (2 : ℝ) ^ E * δ = 1 := by dsimp [δ]; simp [eps]
              have hp' := mul_le_mul_of_nonneg_right hp hδ.le
              rw [pow_succ] at hp'
              have hx : (2 : ℝ) ^ r * δ * (n : ℝ) ≤ (n : ℝ) / 2 := by
                nlinarith only [hp', heq, hnR]
              have hc : (L r : ℝ) < (2 : ℝ) ^ r * δ * (n : ℝ) + 1 := by
                exact Nat.ceil_lt_add_one (by positivity)
              apply (div_le_iff₀ hnR).mpr
              nlinarith only [hx, hc, hnlarge]
            have hLlt : ∀ r, r < E → L r < n := by
              intro r hr
              have h := (div_le_iff₀ hnR).mp (hqle r hr)
              have hh : (L r : ℝ) < n := by nlinarith only [h, hnR]
              exact_mod_cast hh
            have hHpos : ∀ r, 0 < H r := by
              intro r
              exact mul_pos hδ (Real.sqrt_pos.2 (div_pos hnR (by exact_mod_cast hLpos r)))
            have hHsq : ∀ r, (H r) ^ 2 * q r = δ ^ 2 := by
              intro r
              dsimp only [H, q]
              rw [slack, mul_pow, Real.sq_sqrt (by positivity)]
              have hln : (L r : ℝ) ≠ 0 := by exact_mod_cast (hLpos r).ne'
              field_simp
              rfl
            have hHsmall : ∀ r, H r ≤ 1 / 16 := by
              intro r
              have he := hHsq r
              have hlo := mul_le_mul_of_nonneg_left (hqδ r) (sq_nonneg (H r))
              have hs : (H r) ^ 2 ≤ δ := by nlinarith only [he, hlo, hδ]
              nlinarith only [hs, hδsmall, hHpos r]
            have hBδ : ∀ i, 262144 * (m : ℝ) ≤ δ ^ 2 * I.b i := by
              intro i
              have hbase := (div_le_iff₀ (sq_pos_of_pos hε)).mp (hB i)
              have hmLog : (m : ℝ) ≤ (m : ℝ) * Real.log ((n : ℝ) * k / ε) :=
                le_mul_of_one_le_right (by positivity) hlog
              have hsq : ε ^ 2 / 4 ≤ δ ^ 2 := by nlinarith only [hδε.1, hε, hδ]
              have hmul := mul_le_mul_of_nonneg_right hsq (hb i)
              nlinarith only [hbase, hmLog, hmul]
            have hb1 : ∀ i, 1 ≤ I.b i := by
              intro i
              have hh := hBδ i
              have hsq : δ ^ 2 ≤ 1 := by nlinarith only [hδsmall, hδ]
              have hp := mul_le_mul_of_nonneg_right hsq (hb i)
              nlinarith only [hh, hp, hmR]
            have hmSlack : ∀ r i, (m : ℝ) ≤ H r * q r * I.b i / 1024 := by
              intro r i
              have hq : 0 < q r := hqpos r
              have hH : 0 < H r := hHpos r
              have heq := hHsq r
              have hlow := hqδ r
              have hH1 : H r ≤ 1 := le_trans (hHsmall r) (by norm_num)
              have hh : δ ^ 2 ≤ H r * q r := by
                have hm := mul_le_of_le_one_left hq.le hH1
                have hmul := mul_le_mul_of_nonneg_left hm hH.le
                nlinarith only [heq, hmul]
              have hmul := mul_le_mul_of_nonneg_right hh (hb i)
              have hbd := hBδ i
              nlinarith only [hmul, hbd]
            have hLdouble : ∀ r, L (r + 1) ≤ 2 * L r := fun r => hlearnDouble n E r
            have hMlow : ∀ r, (L r : ℝ) / 2 ≤ (L (r + 1) - L r : ℕ) := by
              intro r
              let x : ℝ := (2 : ℝ) ^ r * δ * (n : ℝ)
              have hx : 1 ≤ x := by
                have hp : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
                have hm := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ δ * (n : ℝ))
                dsimp [x]; nlinarith only [hm, hδn]
              have hceil : (L r : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
              have hceil' : 2 * x ≤ (L (r + 1) : ℝ) := by
                have := Nat.le_ceil ((2 : ℝ) ^ (r + 1) * δ * (n : ℝ))
                change (2 : ℝ) ^ (r + 1) * δ * (n : ℝ) ≤ (L (r + 1) : ℝ) at this
                rw [pow_succ] at this
                dsimp only [x]
                nlinarith only [this]
              have hmono : L r ≤ L (r + 1) := hLm r (r + 1) (by omega)
              rw [Nat.cast_sub hmono]
              by_cases hl : L r = 1
              · rw [hl]; push_cast
                nlinarith only [hx, hceil']
              · have htwo : 2 ≤ L r := by have := hLpos r; omega
                have hint : 2 * L r ≤ L (r + 1) + 1 := by
                  have hh : ((2 * L r : ℕ) : ℝ) < (L (r + 1) + 2 : ℕ) := by push_cast; linarith only [hceil, hceil']
                  have : 2 * L r < L (r + 1) + 2 := by exact_mod_cast hh
                  omega
                have hint' : (2 : ℝ) * L r ≤ (L (r + 1) : ℝ) + 1 := by exact_mod_cast hint
                have htwo' : (2 : ℝ) ≤ L r := by exact_mod_cast htwo
                linarith only [hint', htwo']
            have hTcard : ∀ r, r < E → (T r).card = L (r + 1) - L r := by
              intro r hr
              have hs : firstTimes n (L r) ⊆ firstTimes n (L (r + 1)) := by
                intro t ht
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp ht).2 (hLm r (r + 1) (by omega))⟩
              dsimp only [T]
              rw [Finset.card_sdiff_of_subset hs, hfirstCard n _ (hLle _ (by omega)), hfirstCard n _ (hLle _ hr.le)]
            have hTpos : ∀ r, r < E → 0 < (T r).card := by
              intro r hr
              rw [hTcard r hr]
              have hl := hMlow r
              have hlp : (0 : ℝ) < L r := by exact_mod_cast hLpos r
              have hm : (0 : ℝ) < (L (r + 1) - L r : ℕ) := by linarith only [hl, hlp]
              exact_mod_cast hm
            have hTlt : ∀ r, r < E → (T r).card < n := by
              intro r hr
              rw [hTcard r hr]
              have h1 := hLle (r + 1) (by omega)
              have h2 := hLpos r
              omega
            have htel : ∀ (F : ℕ → ℝ) (s : ℕ),
                (∑ r ∈ Finset.range s, (F (r + 1) - F r)) = F s - F 0 := by
              intro F s
              induction s with
              | zero => simp
              | succ s ih => rw [Finset.sum_range_succ, ih]; ring
            have hphaseSum : ∀ (a : Fin n → ℝ),
                (∑ r ∈ Finset.range E, ∑ t ∈ T r, a t) = (∑ t, a t) - ∑ t ∈ firstTimes n (L 0), a t := by
              intro a
              have he : ∀ r, r < E → (∑ t ∈ T r, a t) =
                  (∑ t ∈ firstTimes n (L (r + 1)), a t) - ∑ t ∈ firstTimes n (L r), a t := by
                intro r hr
                have hs : firstTimes n (L r) ⊆ firstTimes n (L (r + 1)) := by
                  intro t ht
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp ht).2 (hLm r (r + 1) (by omega))⟩
                exact Finset.sum_sdiff_eq_sub hs
              calc
                (∑ r ∈ Finset.range E, ∑ t ∈ T r, a t) =
                    ∑ r ∈ Finset.range E, ((∑ t ∈ firstTimes n (L (r + 1)), a t) - ∑ t ∈ firstTimes n (L r), a t) :=
                  Finset.sum_congr rfl (fun r hr => he r (Finset.mem_range.mp hr))
                _ = (∑ t, a t) - ∑ t ∈ firstTimes n (L 0), a t := by
                  rw [htel (fun r => ∑ t ∈ firstTimes n (L r), a t) E, hLlast, hfirstAll]
            have hTsum : ∑ r ∈ Finset.range E, ((T r).card : ℝ) / n = 1 - q 0 := by
              have hh := hphaseSum (fun _ => (1 : ℝ))
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
                hfirstCard n _ (hLle 0 (by omega))] at hh
              rw [← Finset.sum_div, hh]
              dsimp [q]
              field_simp
            have hHweighted : ∑ r ∈ Finset.range E, ((T r).card : ℝ) / n * H r ≤ 3 * δ := by
              have hstep : ∀ r < E, ((T r).card : ℝ) / n * H r ≤
                  3 * δ * (Real.sqrt (q (r + 1)) - Real.sqrt (q r)) := by
                intro r hr
                let a := Real.sqrt (q r)
                let b := Real.sqrt (q (r + 1))
                have ha : 0 < a := Real.sqrt_pos.2 (hqpos r)
                have hb : 0 ≤ b := Real.sqrt_nonneg _
                have ha2 : a ^ 2 = q r := Real.sq_sqrt (hqpos r).le
                have hb2 : b ^ 2 = q (r + 1) := Real.sq_sqrt (hqpos (r + 1)).le
                have hab : a ≤ b := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by exact_mod_cast hLm r (r + 1) (by omega)) hnR.le)
                have hqdouble : q (r + 1) ≤ 2 * q r := by
                  dsimp [q]
                  rw [← mul_div_assoc]
                  apply div_le_div_of_nonneg_right _ hnR.le
                  exact_mod_cast hLdouble r
                have hba : b ≤ 2 * a := by nlinarith only [ha2, hb2, hqdouble, ha, hb]
                have hha : H r * a = δ := by
                  have hh := hHsq r
                  have hp : 0 ≤ H r * a := mul_nonneg (hHpos r).le ha.le
                  nlinarith only [ha2, hh, hp, hδ]
                have hhb : H r * (b + a) ≤ 3 * δ := by
                  have h := mul_le_mul_of_nonneg_left hba (hHpos r).le
                  nlinarith only [h, hha]
                have hmul := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hhb)
                rw [hTcard r hr, Nat.cast_sub (hLm r (r + 1) (by omega)), sub_div]
                change (q (r + 1) - q r) * H r ≤ 3 * δ * (b - a)
                rw [← ha2, ← hb2]
                nlinarith only [hmul]
              have hsum := Finset.sum_le_sum (fun r hr => hstep r (Finset.mem_range.mp hr))
              rw [← Finset.mul_sum, htel (fun r => Real.sqrt (q r)) E] at hsum
              have hqE : q E = 1 := by dsimp [q]; rw [hLlast]; exact div_self hnR.ne'
              rw [hqE, Real.sqrt_one] at hsum
              have hroot := Real.sqrt_nonneg (q 0)
              nlinarith only [hsum, hroot, hδ]
            have hEδ : (E : ℝ) * δ ≤ 1 := by
              have he : (E : ℝ) ≤ (2 : ℝ) ^ E := by exact_mod_cast (Nat.lt_two_pow_self (n := E)).le
              have hm := mul_le_mul_of_nonneg_right he hδ.le
              have heq : (2 : ℝ) ^ E * δ = 1 := by dsimp [δ]; simp [eps]
              simpa only [heq] using hm
            have hEn : E ≤ n := by
              have hh : (E : ℝ) ≤ n := (mul_le_mul_iff_left₀ hδ).mp (by nlinarith only [hEδ, hδn])
              exact_mod_cast hh
            let F : Finset (Finset (Fin n)) := ((Finset.range E).image (fun r => firstTimes n (L r))) ∪
              ((Finset.range E).image T)
            have hFcard : F.card ≤ 2 * n := by
              apply le_trans (Finset.card_union_le _ _)
              have h1 := Finset.card_image_le (s := Finset.range E) (f := fun r => firstTimes n (L r))
              have h2 := Finset.card_image_le (s := Finset.range E) (f := T)
              simp only [Finset.card_range] at h1 h2
              omega
            have hFprefix : ∀ r, r < E → firstTimes n (L r) ∈ F := by
              intro r hr
              exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, rfl⟩)
            have hFphase : ∀ r, r < E → T r ∈ F := by
              intro r hr
              exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, rfl⟩)
            have hFbounds : ∀ S ∈ F, 0 < S.card ∧ S.card < n ∧ δ * (n : ℝ) / 2 ≤ S.card := by
              intro S hS
              rcases Finset.mem_union.mp hS with hS | hS
              · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hS
                have hr' := Finset.mem_range.mp hr
                rw [hfirstCard n _ (hLle r hr'.le)]
                exact ⟨hLpos r, hLlt r hr', by linarith only [hLlow r, hδn]⟩
              · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hS
                have hr' := Finset.mem_range.mp hr
                refine ⟨hTpos r hr', hTlt r hr', ?_⟩
                rw [hTcard r hr']
                linarith only [hMlow r, hLlow r]
            let η : Finset (Fin n) → ℝ := fun S => slack n E S.card / 128
            have hηpos : ∀ S ∈ F, 0 < η S := by
              intro S hS
              exact div_pos (mul_pos hδ (Real.sqrt_pos.2 (div_pos hnR (by exact_mod_cast (hFbounds S hS).1)))) (by norm_num)
            have hηsq : ∀ S ∈ F, (η S) ^ 2 * ((S.card : ℝ) / n) = δ ^ 2 / 16384 := by
              intro S hS
              have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (hFbounds S hS).1.ne'
              dsimp only [η, slack]
              rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
              dsimp only [δ]
              field_simp
              <;> ring
            have hηsmall : ∀ S ∈ F, η S ≤ 1 := by
              intro S hS
              have hs := hηsq S hS
              have hlow : δ / 2 ≤ (S.card : ℝ) / n := (le_div_iff₀ hnR).mpr (by linarith only [(hFbounds S hS).2.2])
              have hmul := mul_le_mul_of_nonneg_left hlow (sq_nonneg (η S))
              have hη := hηpos S hS
              have hsquare : (η S) ^ 2 ≤ δ / 8192 := by
                apply (mul_le_mul_iff_left₀ hδ).mp
                nlinarith only [hs, hmul]
              nlinarith only [hsquare, hδsmall, hη]
            let R : ℝ := (n : ℝ) * k / ε
            have hRpos : 0 < R := div_pos (mul_pos hnR (by exact_mod_cast (show 0 < k by omega))) hε
            have hRlarge : 16 * (n : ℝ) ≤ R := by
              have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
              apply (le_div_iff₀ hε).mpr
              nlinarith only [hkR, hnR, hsmall]
            have hRone : 1 ≤ R := by nlinarith only [hRlarge, hnlarge]
            have hRlog : 1 ≤ Real.log R := hlog
            have hmlog : Real.log R ≤ (m : ℝ) * Real.log R := le_mul_of_one_le_left (by linarith only [hRlog]) hmR
            have hAexp : (A.card : ℝ) ≤ Real.exp (8 * (m : ℝ) * Real.log R) := by
              let N : ℕ := n * (k + 1) ^ 2
              have hN : 1 ≤ N := by
                have hh : 0 < N := by dsimp [N]; positivity
                omega
              have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast hN
              have hcount : (A.card : ℝ) ≤ ((m : ℝ) + 2) * ((N : ℝ) + 1) ^ (m + 1) := by
                have hcast : (A.card : ℝ) ≤ ∑ j ∈ Finset.Iic (m + 1), (N.choose j : ℝ) := by exact_mod_cast hAcard
                apply le_trans hcast
                have hs := Finset.sum_le_sum (s := Finset.Iic (m + 1)) (fun j hj => show (N.choose j : ℝ) ≤ ((N : ℝ) + 1) ^ (m + 1) from by
                  have hj' : j ≤ m + 1 := Finset.mem_Iic.mp hj
                  have hchoose : (N.choose j : ℝ) ≤ (N : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow N j
                  exact le_trans hchoose (le_trans (pow_le_pow_left₀ (by positivity) (by linarith) j)
                    (pow_le_pow_right₀ (by linarith) hj')))
                simpa [add_assoc] using hs
              have hm2 : (m : ℝ) + 2 ≤ (2 : ℝ) ^ (m + 1) := by
                have hh : ∀ a : ℕ, a + 2 ≤ 2 ^ (a + 1) := by
                  intro a
                  induction a with
                  | zero => norm_num
                  | succ a ih => rw [Nat.succ_add, pow_succ]; nlinarith [Nat.one_le_two_pow (n := a + 1)]
                exact_mod_cast hh m
              have hbase : 2 * ((N : ℝ) + 1) ≤ R ^ 4 := by
                have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
                have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
                have hε1 : ε ≤ 1 / 16 := by linarith only [hsmall]
                have hRnk : 16 * ((n : ℝ) * k) ≤ R := by
                  apply (le_div_iff₀ hε).mpr
                  have hp : 0 ≤ (n : ℝ) * k := by positivity
                  nlinarith only [hε1, hp]
                have hNcast : (N : ℝ) = (n : ℝ) * ((k : ℝ) + 1) ^ 2 := by dsimp [N]; push_cast; rfl
                have hk2 : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith only [hkR]
                have hnk : 0 ≤ (n : ℝ) * k := by positivity
                have hR2 : 256 * ((n : ℝ) * k) ^ 2 ≤ R ^ 2 := by nlinarith only [hRnk, hnk, hRpos]
                have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hnR1]
                have hNle : (N : ℝ) ≤ 4 * ((n : ℝ) * k) ^ 2 := by
                  have hh := mul_le_mul_of_nonneg_left hk2 hnR.le
                  have hh' := mul_le_mul_of_nonneg_right hn2 (sq_nonneg (k : ℝ))
                  nlinarith only [hNcast, hh, hh']
                have hR2one : 1 ≤ R ^ 2 := one_le_pow₀ hRone
                have hpow : R ^ 2 ≤ R ^ 4 := by
                  have hh := mul_le_mul_of_nonneg_right hR2one (sq_nonneg R)
                  nlinarith only [hh]
                nlinarith only [hNle, hR2, hNpos, hpow]
              have hpow : (A.card : ℝ) ≤ (R ^ 4) ^ (m + 1) := by
                calc
                  (A.card : ℝ) ≤ ((m : ℝ) + 2) * ((N : ℝ) + 1) ^ (m + 1) := hcount
                  _ ≤ (2 : ℝ) ^ (m + 1) * ((N : ℝ) + 1) ^ (m + 1) :=
                    mul_le_mul_of_nonneg_right hm2 (by positivity)
                  _ = (2 * ((N : ℝ) + 1)) ^ (m + 1) := (mul_pow _ _ _).symm
                  _ ≤ (R ^ 4) ^ (m + 1) := pow_le_pow_left₀ (by positivity) hbase _
              have he : (R ^ 4) ^ (m + 1) = Real.exp ((m + 1 : ℕ) * (4 * Real.log R)) := by
                rw [Real.exp_nat_mul]
                congr 1
                rw [show (4 : ℝ) * Real.log R = (4 : ℕ) * Real.log R by norm_num, Real.exp_nat_mul, Real.exp_log hRpos]
              rw [he] at hpow
              exact le_trans hpow (Real.exp_le_exp.mpr (by push_cast; nlinarith only [hmlog, hRlog]))
            have hBδlog : ∀ i, 268435456 * (m : ℝ) * Real.log R ≤ δ ^ 2 * I.b i := by
              intro i
              have hbase := (div_le_iff₀ (sq_pos_of_pos hε)).mp (hB i)
              have hsq : ε ^ 2 / 4 ≤ δ ^ 2 := by nlinarith only [hδε.1, hε, hδ]
              have hmul := mul_le_mul_of_nonneg_right hsq (hb i)
              change 1073741824 * (m : ℝ) * Real.log R ≤ I.b i * ε ^ 2 at hbase
              nlinarith only [hbase, hmul]
            let Bad : Equiv.Perm (Fin n) → Prop := fun σ => ∃ S ∈ F, ∃ i : Fin m, ∃ c ∈ A,
              η S * ((S.card : ℝ) / n) * max (I.b i) (∑ t, (c t).elim 0 (I.g t i)) ≤
                |(∑ t ∈ S, (c (σ t)).elim 0 (I.g (σ t) i)) -
                  (S.card : ℝ) / n * ∑ t, (c t).elim 0 (I.g t i)|
            have hBadBound : probPerm Bad ≤ (F.card : ℝ) * (m : ℝ) * (A.card : ℝ) *
                (2 * (n + 1 : ℝ) * Real.exp (-4096 * (m : ℝ) * Real.log R)) := by
              apply le_trans (hprobUnion F (fun S σ => ∃ i : Fin m, ∃ c ∈ A,
                η S * ((S.card : ℝ) / n) * max (I.b i) (∑ t, (c t).elim 0 (I.g t i)) ≤
                  |(∑ t ∈ S, (c (σ t)).elim 0 (I.g (σ t) i)) -
                    (S.card : ℝ) / n * ∑ t, (c t).elim 0 (I.g t i)|))
              have hS : ∀ S ∈ F, probPerm (fun σ => ∃ i : Fin m, ∃ c ∈ A,
                η S * ((S.card : ℝ) / n) * max (I.b i) (∑ t, (c t).elim 0 (I.g t i)) ≤
                  |(∑ t ∈ S, (c (σ t)).elim 0 (I.g (σ t) i)) -
                    (S.card : ℝ) / n * ∑ t, (c t).elim 0 (I.g t i)|) ≤
                  (m : ℝ) * ((A.card : ℝ) * (2 * (n + 1 : ℝ) * Real.exp (-4096 * (m : ℝ) * Real.log R))) := by
                intro S hS
                have hi : ∀ i : Fin m, probPerm (fun σ => ∃ c ∈ A,
                  η S * ((S.card : ℝ) / n) * max (I.b i) (∑ t, (c t).elim 0 (I.g t i)) ≤
                    |(∑ t ∈ S, (c (σ t)).elim 0 (I.g (σ t) i)) -
                      (S.card : ℝ) / n * ∑ t, (c t).elim 0 (I.g t i)|) ≤
                    (A.card : ℝ) * (2 * (n + 1 : ℝ) * Real.exp (-4096 * (m : ℝ) * Real.log R)) := by
                  intro i
                  have hh := hAconcentration S (η S) (I.b i) i (hFbounds S hS).1 (hFbounds S hS).2.1
                    (hηpos S hS) (hηsmall S hS) (hb i)
                  apply le_trans hh
                  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  apply Real.exp_le_exp.mpr
                  have heq := hηsq S hS
                  have hB' := hBδlog i
                  have heq' := congrArg (fun x : ℝ => x * I.b i) heq
                  nlinarith only [heq', hB']
                have hu := hprobUnion (Finset.univ : Finset (Fin m)) (fun i σ => ∃ c ∈ A,
                  η S * ((S.card : ℝ) / n) * max (I.b i) (∑ t, (c t).elim 0 (I.g t i)) ≤
                    |(∑ t ∈ S, (c (σ t)).elim 0 (I.g (σ t) i)) -
                      (S.card : ℝ) / n * ∑ t, (c t).elim 0 (I.g t i)|)
                simp only [Finset.mem_univ, true_and] at hu
                apply le_trans hu
                simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
                  Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
              have hsum := Finset.sum_le_sum hS
              simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hsum
            have hBadSmall : probPerm Bad ≤ 1 / (16 * (n : ℝ) ^ 2) := by
              have hexp2 : Real.exp (2 * Real.log R) = R ^ 2 := by
                rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hRpos]
              have hFexp : (F.card : ℝ) ≤ Real.exp (2 * (m : ℝ) * Real.log R) := by
                have hc : (F.card : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hFcard
                have h0 : 2 * (n : ℝ) ≤ R ^ 2 := by nlinarith only [hRlarge, hRone, hnR]
                apply le_trans hc (le_trans h0 ?_)
                rw [← hexp2]
                exact Real.exp_le_exp.mpr (by nlinarith only [hmlog, hRlog])
              have hmexp : (m : ℝ) ≤ Real.exp ((m : ℝ) * Real.log R) := by
                have hm2 : (m : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
                rw [Real.exp_nat_mul, Real.exp_log hRpos]
                exact le_trans hm2 (pow_le_pow_left₀ (by norm_num) (by nlinarith only [hRlarge, hnlarge]) _)
              have hnexp : 2 * (n + 1 : ℝ) ≤ Real.exp (2 * (m : ℝ) * Real.log R) := by
                have h0 : 2 * (n + 1 : ℝ) ≤ R ^ 2 := by nlinarith only [hRlarge, hRone, hnlarge]
                apply le_trans h0
                rw [← hexp2]
                exact Real.exp_le_exp.mpr (by nlinarith only [hmlog, hRlog])
              have hprod : (F.card : ℝ) * (m : ℝ) * (A.card : ℝ) *
                  (2 * (n + 1 : ℝ) * Real.exp (-4096 * (m : ℝ) * Real.log R)) ≤
                  Real.exp (-4 * Real.log R) := by
                have hh := mul_le_mul (mul_le_mul (mul_le_mul hFexp hmexp (by positivity) (by positivity))
                  hAexp (by positivity) (by positivity))
                  (mul_le_mul_of_nonneg_right hnexp (Real.exp_pos (-4096 * (m : ℝ) * Real.log R)).le) (by positivity) (by positivity)
                apply le_trans hh
                simp only [← Real.exp_add]
                apply Real.exp_le_exp.mpr
                nlinarith only [hmlog, hRlog]
              apply le_trans hBadBound (le_trans hprod ?_)
              have he : Real.exp (-4 * Real.log R) = 1 / R ^ 4 := by
                rw [show -4 * Real.log R = -(4 * Real.log R) by ring, Real.exp_neg]
                rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hRpos]
                simp [one_div]
              rw [he]
              apply one_div_le_one_div_of_le (by positivity)
              have hR2 : 256 * (n : ℝ) ^ 2 ≤ R ^ 2 := by nlinarith only [hRlarge, hRpos, hnR]
              have hn2 : 1 ≤ (n : ℝ) ^ 2 := by nlinarith only [hnlarge]
              nlinarith only [hR2, hn2]
            have hGood : ∀ σ, ¬ Bad σ → ∀ S ∈ F, ∀ i, ∀ c ∈ A,
                |(∑ t ∈ S, (c (σ t)).elim 0 (I.g (σ t) i)) -
                  (S.card : ℝ) / n * ∑ t, (c t).elim 0 (I.g t i)| ≤
                  η S * ((S.card : ℝ) / n) * max (I.b i) (∑ t, (c t).elim 0 (I.g t i)) := by
              intro σ hgood S hS i c hc
              exact (lt_of_not_ge (fun hh => hgood ⟨S, hS, i, c, hc, hh⟩)).le
            choose C hCA hC using hAcover
            let P : ℕ → Equiv.Perm (Fin n) → Fin m → ℝ := fun r σ =>
              multiLearnedPrice I rule E σ (L r)
            let G : (Fin m → ℝ) → Fin m → ℝ := fun p i => ∑ t, (C p t).elim 0 (I.g t i)
            let W : (Fin m → ℝ) → Finset (Fin n) → Equiv.Perm (Fin n) → ℝ := fun p S σ =>
              ∑ t ∈ S, (C p (σ t)).elim 0 (I.f (σ t))
            let D : ℕ → Equiv.Perm (Fin n) → ℝ := fun r σ =>
              q r * (∑ i, I.b i * pstar i) + ∑ t ∈ firstTimes n (L r), ystar (σ t)
            have hPopt : ∀ r σ, r < E → IsBlockOptimalPrice (firstTimes n (L r))
                (I.arrF σ) (I.arrG σ) (fun i => (1 - H r) * q r * I.b i) (P r σ) := hphasePrice
            have hPnonneg : ∀ r σ, r < E → ∀ i, 0 ≤ P r σ i := by
              intro r σ hr
              obtain ⟨y, hy⟩ := hPopt r σ hr
              exact hy.1.1
            have hband : ∀ r σ, r < E → ∀ i,
                (∑ t ∈ firstTimes n (L r), (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) ≤
                  (1 - H r) * q r * I.b i + 2 * m ∧
                (0 < P r σ i → (1 - H r) * q r * I.b i - 2 * m ≤
                  ∑ t ∈ firstTimes n (L r), (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) := by
              intro r σ hr
              exact hbandArr I σ _ _ _ _ hgp (hPopt r σ hr) (hC (P r σ))
            have hsampleFit : ∀ r σ, r < E → ∀ i,
                (∑ t ∈ firstTimes n (L r), (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) ≤ q r * I.b i := by
              intro r σ hr i
              have hh := (hband r σ hr i).1
              have hm := hmSlack r i
              nlinarith only [hh, hm, hmR]
            have hDavg : ∀ r, r < E → avgPerm (D r) = q r * V := by
              intro r hr
              dsimp only [D]
              rw [havgAdd, havgConst, hfirstAvg (L r) ystar (hLle r hr.le) hn0]
              dsimp only [V, blockDualObj, q]
              ring
            have hDnonneg : ∀ r σ, 0 ≤ D r σ := by
              intro r σ
              exact add_nonneg (mul_nonneg (hqpos r).le
                (Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (hstar.1.1 i)))
                (Finset.sum_nonneg fun t _ => (hstar.1.2 (σ t) (Finset.mem_univ _)).1)
            have hsampleReward : ∀ r σ, r < E → W (P r σ) (firstTimes n (L r)) σ ≤ D r σ := by
              intro r σ hr
              have hx : IsBlockFeasible (firstTimes n (L r)) (I.arrG σ) (fun i => q r * I.b i)
                  (fun t => choiceVec (C (P r σ) (σ t))) := by
                constructor
                · intro i; simpa only [hsumChoice, MultiInstance.arrG] using hsampleFit r σ hr i
                · intro t ht; exact ⟨hchoice _, hchoiceSum _⟩
              have hp : IsBlockDualFeasible (firstTimes n (L r)) (I.arrF σ) (I.arrG σ) pstar (fun t => ystar (σ t)) := by
                refine ⟨hstar.1.1, ?_⟩
                intro t ht
                exact hstar.1.2 (σ t) (Finset.mem_univ _)
              have hh := hweakDual _ _ _ _ _ _ _ hx hp
              simpa only [blockPrimalObj, blockDualObj, hsumChoice, ← Finset.mul_sum, mul_assoc, D, W, MultiInstance.arrF] using hh
            have hpriceSmall : ∀ r σ, r < E → (m : ℝ) * (∑ i, P r σ i) ≤ δ ^ 2 / (131072 * q r) * D r σ := by
              intro r σ hr
              obtain ⟨y, hy⟩ := hPopt r σ hr
              have hdualStar : IsBlockDualFeasible (firstTimes n (L r)) (I.arrF σ) (I.arrG σ)
                  pstar (fun t => ystar (σ t)) := by
                refine ⟨hstar.1.1, ?_⟩
                intro t ht; exact hstar.1.2 (σ t) (Finset.mem_univ _)
              have hminimal := hy.2 pstar (fun t => ystar (σ t)) hdualStar
              have hright : blockDualObj (firstTimes n (L r)) (fun i => (1 - H r) * q r * I.b i)
                  pstar (fun t => ystar (σ t)) ≤ D r σ := by
                dsimp only [blockDualObj, D]
                refine add_le_add ?_ le_rfl
                rw [Finset.mul_sum]
                apply Finset.sum_le_sum
                intro i hi
                have hp := mul_nonneg (hb i) (hstar.1.1 i)
                have hc := mul_nonneg (mul_nonneg (hHpos r).le (hqpos r).le) hp
                nlinarith only [hc]
              have hleft : (131072 * q r / δ ^ 2) * ((m : ℝ) * ∑ i, P r σ i) ≤
                  blockDualObj (firstTimes n (L r)) (fun i => (1 - H r) * q r * I.b i) (P r σ) y := by
                dsimp only [blockDualObj]
                have hy0 : 0 ≤ ∑ t ∈ firstTimes n (L r), y t :=
                  Finset.sum_nonneg fun t ht => (hy.1.2 t ht).1
                have hsum : (131072 * q r / δ ^ 2) * ((m : ℝ) * ∑ i, P r σ i) ≤
                    ∑ i, ((1 - H r) * q r * I.b i) * P r σ i := by
                  rw [Finset.mul_sum, Finset.mul_sum]
                  apply Finset.sum_le_sum
                  intro i hi
                  rw [← mul_assoc]
                  apply mul_le_mul_of_nonneg_right _ (hy.1.1 i)
                  have hbδ := hBδ i
                  have hH := hHsmall r
                  have hq := hqpos r
                  rw [div_mul_eq_mul_div]
                  apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
                  have hm := mul_le_mul_of_nonneg_left hbδ (mul_nonneg (by linarith only [hH] : 0 ≤ 1 - H r) hq.le)
                  have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) / 2 ≤ 1 - H r by linarith only [hH])
                    (mul_nonneg (Nat.cast_nonneg m) hq.le)
                  nlinarith only [hm, hh]
                linarith only [hsum, hy0]
              have hh := le_trans hleft (le_trans hminimal hright)
              have hp := (hqpos r)
              have hd := sq_pos_of_pos hδ
              rw [div_mul_eq_mul_div]
              apply (le_div_iff₀ (by positivity : 0 < 131072 * q r)).mpr
              have hh' := (div_le_iff₀ hd).mp (show (131072 * q r * ((m : ℝ) * ∑ i, P r σ i)) / δ ^ 2 ≤ D r σ by
                simpa only [div_mul_eq_mul_div] using hh)
              nlinarith only [hh']
            have hpriceAvg : ∀ r, r < E → avgPerm (fun σ => (m : ℝ) * ∑ i, P r σ i) ≤ δ ^ 2 / 131072 * V := by
              intro r hr
              have hh := havgMono _ _ (fun σ => hpriceSmall r σ hr)
              rw [havgMul (δ ^ 2 / (131072 * q r)) (D r), hDavg r hr] at hh
              have he : δ ^ 2 / (131072 * q r) * (q r * V) = δ ^ 2 / 131072 * V := by
                field_simp [(hqpos r).ne']
              simpa only [he] using hh
            have hglobalUse : ∀ r σ, r < E → ¬ Bad σ → ∀ i,
                G (P r σ) i ≤ (1 - H r / 2) * I.b i ∧
                  (0 < P r σ i → (1 - 2 * H r) * I.b i ≤ G (P r σ) i) := by
              intro r σ hr hgood i
              let s := (∑ t ∈ firstTimes n (L r), (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) / q r
              let e := 2 * (m : ℝ) / q r
              have hq := hqpos r
              have hband' := hband r σ hr i
              have he : e ≤ H r * I.b i / 16 := by
                apply (div_le_iff₀ hq).mpr
                nlinarith only [hmSlack r i, hmR]
              have hs : s ≤ (1 - H r) * I.b i + e := by
                apply (div_le_iff₀ hq).mpr
                dsimp only [e]
                have heq : (2 * (m : ℝ) / q r) * q r = 2 * m := div_mul_cancel₀ _ hq.ne'
                nlinarith only [hband'.1, heq]
              have hd := hGood σ hgood _ (hFprefix r hr) i _ (hCA (P r σ))
              rw [hfirstCard n _ (hLle r hr.le)] at hd
              have hη : η (firstTimes n (L r)) = H r / 128 := by
                dsimp only [η]
                rw [hfirstCard n _ (hLle r hr.le)]
              rw [hη] at hd
              change |(∑ t ∈ firstTimes n (L r), (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) -
                q r * G (P r σ) i| ≤ H r / 128 * q r * max (I.b i) (G (P r σ) i) at hd
              have hdev : |s - G (P r σ) i| ≤ H r / 16 * max (I.b i) (G (P r σ) i) := by
                dsimp only [s]
                rw [show (∑ t ∈ firstTimes n (L r), (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) / q r - G (P r σ) i =
                  ((∑ t ∈ firstTimes n (L r), (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) - q r * G (P r σ) i) / q r by field_simp,
                  abs_div, abs_of_pos hq]
                apply (div_le_iff₀ hq).mpr
                have hmax : 0 ≤ max (I.b i) (G (P r σ) i) := le_trans (hb i) (le_max_left _ _)
                have hp := mul_nonneg (mul_nonneg (hHpos r).le hq.le) hmax
                nlinarith only [hd, hp]
              have hG0 : 0 ≤ G (P r σ) i := Finset.sum_nonneg fun t _ => (hAcost _ (hCA (P r σ)) t i).1
              have hres := hscalarBand (I.b i) (G (P r σ) i) s (H r) e (hb i) hG0 (hHpos r)
                (le_trans (hHsmall r) (by norm_num)) he hs hdev
              refine ⟨hres.1, fun hpi => hres.2 ?_⟩
              apply (le_div_iff₀ hq).mpr
              have heq : (2 * (m : ℝ) / q r) * q r = 2 * m := div_mul_cancel₀ _ hq.ne'
              nlinarith only [hband'.2 hpi, heq]
            have hglobalReward : ∀ r σ, r < E → ¬ Bad σ →
                (1 - 2 * H r) * V ≤ W (P r σ) Finset.univ σ := by
              intro r σ hr hgood
              have hh := hglobalPerformance (P r σ) (C (P r σ)) (1 - 2 * H r)
                (hPnonneg r σ hr) (by linarith only [hHsmall r]) (by linarith only [hHpos r])
                (hC (P r σ)) (fun i hpi => by simpa only [hsumChoice] using (hglobalUse r σ hr hgood i).2 hpi)
              have heq : W (P r σ) Finset.univ σ = ∑ t, (C (P r σ) t).elim 0 (I.f t) :=
                Equiv.sum_comp σ (fun t => (C (P r σ) t).elim 0 (I.f t))
              rw [heq]
              simpa only [hsumChoice] using hh
            have hηphase : ∀ r, r < E → η (T r) ≤ H r / 16 := by
              intro r hr
              let u : ℝ := ((T r).card : ℝ) / n
              have hu : 0 < u := div_pos (by exact_mod_cast hTpos r hr) hnR
              have hqu : q r ≤ 2 * u := by
                dsimp only [q, u]
                rw [← mul_div_assoc]
                apply div_le_div_of_nonneg_right _ hnR.le
                rw [hTcard r hr]
                linarith only [hMlow r]
              have hs := hηsq (T r) (hFphase r hr)
              have hH := hHsq r
              have hm := mul_le_mul_of_nonneg_left hqu (sq_nonneg (H r))
              have hsq : (η (T r)) ^ 2 ≤ (H r) ^ 2 / 8192 := by
                apply (mul_le_mul_iff_left₀ hu).mp
                change (η (T r)) ^ 2 * u ≤ (H r) ^ 2 / 8192 * u
                change (η (T r)) ^ 2 * u = δ ^ 2 / 16384 at hs
                nlinarith only [hs, hH, hm]
              nlinarith only [hsq, hηpos (T r) (hFphase r hr), hHpos r]
            let J : Equiv.Perm (Fin n) → MultiInstance m n k := fun σ =>
              { f := I.arrF σ, g := I.arrG σ, b := I.b,
                f_nonneg := fun t j => I.f_nonneg (σ t) j,
                g_nonneg := fun t i j => I.g_nonneg (σ t) i j,
                g_le_one := fun t i j => I.g_le_one (σ t) i j }
            have hTie : ∀ r σ t, IsSurplusChoice ((J σ).f t) ((J σ).g t) (P r σ)
                (tie t (I.arrF σ) (I.arrG σ) (P r σ)) := fun r σ t => ht.2 _ _ _ _
            have hproposalPhase : ∀ r σ t, r < E → t ∈ T r → multiProposal I rule tie ε σ t =
                choiceVec (tie t (I.arrF σ) (I.arrG σ) (P r σ)) := by
              intro r σ t hr ht
              have hmem := Finset.mem_sdiff.mp ht
              have hend : t.val < L (r + 1) := (Finset.mem_filter.mp hmem.1).2
              have hstart : L r ≤ t.val := by
                have hh := hmem.2
                simp only [firstTimes, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hh
                exact hh
              have hinitial : ¬ t.val < L 0 := by have := hLm 0 r (Nat.zero_le _); omega
              have heq := hphaseIndexEq n E t.val r hr hstart hend
              change ¬ t.val < learnTime n (accuracyExp ε) 0 at hinitial
              change phaseIndex n (accuracyExp ε) t.val = r at heq
              simp only [multiProposal, if_neg hwindow, if_neg hinitial, heq]
              rfl
            have hphaseFits : ∀ r σ, r < E → ¬ Bad σ → ∀ i,
                (∑ t ∈ T r, ∑ j, I.arrG σ t i j * multiProposal I rule tie ε σ t j) ≤
                  ((T r).card : ℝ) / n * I.b i := by
              intro r σ hr hgood i
              let u : ℝ := ((T r).card : ℝ) / n
              have hu : 0 < u := div_pos (by exact_mod_cast hTpos r hr) hnR
              have hqM : q r ≤ 2 * u := by
                dsimp only [q, u]
                rw [← mul_div_assoc]
                apply div_le_div_of_nonneg_right _ hnR.le
                rw [hTcard r hr]
                linarith only [hMlow r]
              have huse := (hglobalUse r σ hr hgood i).1
              have hGle : G (P r σ) i ≤ I.b i := by
                have hp := mul_nonneg (hHpos r).le (hb i)
                nlinarith only [huse, hp]
              have hd := hGood σ hgood _ (hFphase r hr) i _ (hCA (P r σ))
              rw [max_eq_left hGle] at hd
              have hcan : (∑ t ∈ T r, (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) ≤
                  u * ((1 - H r / 2) * I.b i) + H r / 16 * u * I.b i := by
                have hd' := (abs_le.mp hd).2
                have hg := mul_le_mul_of_nonneg_left huse hu.le
                have he := mul_le_mul_of_nonneg_right (hηphase r hr) (mul_nonneg hu.le (hb i))
                change (∑ t ∈ T r, (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) -
                  u * G (P r σ) i ≤ η (T r) * u * I.b i at hd'
                nlinarith only [hd', hg, he]
              have hdiff := hchoiceResourceDiff (J σ) (P r σ) (fun t => C (P r σ) (σ t))
                (fun t => tie t (I.arrF σ) (I.arrG σ) (P r σ)) (T r)
                (hpermGP I σ hgp) (fun t => hC (P r σ) (σ t)) (hTie r σ) i
              have hm : (m : ℝ) ≤ H r * u * I.b i / 512 := by
                have hh := hmSlack r i
                have hp := mul_le_mul_of_nonneg_left hqM (mul_nonneg (hHpos r).le (hb i))
                nlinarith only [hh, hp]
              have hh := (abs_le.mp hdiff).1
              have hsum : (∑ t ∈ T r, ∑ j, I.arrG σ t i j * multiProposal I rule tie ε σ t j) =
                  ∑ t ∈ T r, (tie t (I.arrF σ) (I.arrG σ) (P r σ)).elim 0 (I.g (σ t) i) := by
                apply Finset.sum_congr rfl
                intro t ht
                rw [hproposalPhase r σ t hr ht, hsumChoice]
                rfl
              rw [hsum]
              change (∑ t ∈ T r, (C (P r σ) (σ t)).elim 0 (I.g (σ t) i)) -
                (∑ t ∈ T r, (tie t (I.arrF σ) (I.arrG σ) (P r σ)).elim 0 (I.g (σ t) i)) ≥ -(m : ℝ) at hh
              have hp := mul_nonneg (mul_nonneg (hHpos r).le hu.le) (hb i)
              change _ ≤ u * I.b i
              nlinarith only [hcan, hm, hh, hp]
            have hgoodFits : ∀ σ, ¬ Bad σ → ∀ t, multiX I rule tie ε σ t = multiProposal I rule tie ε σ t := by
              intro σ hgood
              apply htotalProposalFits
              intro i
              have hzero : (∑ t ∈ firstTimes n (L 0), ∑ j, I.arrG σ t i j * multiProposal I rule tie ε σ t j) = 0 := by
                apply Finset.sum_eq_zero
                intro t ht
                have ht' : t.val < learnTime n (accuracyExp ε) 0 := (Finset.mem_filter.mp ht).2
                simp only [multiProposal, if_neg hwindow, if_pos ht', mul_zero, Finset.sum_const_zero]
              have hh := hphaseSum (fun t => ∑ j, I.arrG σ t i j * multiProposal I rule tie ε σ t j)
              rw [hzero, sub_zero] at hh
              rw [← hh]
              have hsum := Finset.sum_le_sum (fun r hr => hphaseFits r σ (Finset.mem_range.mp hr) hgood i)
              rw [← Finset.sum_mul, hTsum] at hsum
              have hp := mul_nonneg (hqpos 0).le (hb i)
              nlinarith only [hsum, hp]
            let a : ℕ → ℝ := fun r => ((T r).card : ℝ) / n
            let z : ℕ → ℝ := fun r => ((T r).card : ℝ) / (n - L r : ℕ)
            let Q : Equiv.Perm (Fin n) → ℝ := fun σ => ∑ t, ∑ j, I.arrF σ t j * multiProposal I rule tie ε σ t j
            have ha0 : ∀ r, 0 ≤ a r := fun r => div_nonneg (Nat.cast_nonneg _) hnR.le
            have hz0 : ∀ r, 0 ≤ z r := fun r => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
            have hza : ∀ r, r < E → z r * (1 - q r) = a r := by
              intro r hr
              have hden : ((n - L r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt (hLlt r hr)).ne'
              dsimp only [z, a, q]
              rw [Nat.cast_sub (hLle r hr.le)] at hden ⊢
              field_simp
              <;> ring
            have hzle : ∀ r, r < E → z r ≤ 4 * a r := by
              intro r hr
              have hh := hza r hr
              have hq := hqle r hr
              have hp := mul_le_mul_of_nonneg_left hq (hz0 r)
              nlinarith only [hh, hp]
            have hzsum : ∑ r ∈ Finset.range E, z r ≤ 4 := by
              have hh := Finset.sum_le_sum (fun r hr => hzle r (Finset.mem_range.mp hr))
              rw [← Finset.mul_sum] at hh
              change (∑ r ∈ Finset.range E, z r) ≤ 4 * ∑ r ∈ Finset.range E, ((T r).card : ℝ) / n at hh
              rw [hTsum] at hh
              linarith only [hh, hqpos 0]
            have hWnonneg : ∀ p S σ, 0 ≤ W p S σ := by
              intro p S σ
              apply Finset.sum_nonneg
              intro t ht
              cases C p (σ t) <;> simp [I.f_nonneg]
            have hWtotalAvg : ∀ r, r < E →
                (1 - 2 * H r) * V - V * probPerm Bad ≤ avgPerm (fun σ => W (P r σ) Finset.univ σ) := by
              intro r hr
              have hh := havgError (fun _ : Equiv.Perm (Fin n) => (1 - 2 * H r) * V)
                (fun σ => W (P r σ) Finset.univ σ) V Bad (fun σ => by
                  by_cases hbad : Bad σ
                  · rw [if_pos hbad]
                    have hw := hWnonneg (P r σ) Finset.univ σ
                    have hp := mul_nonneg (hHpos r).le hVnonneg
                    nlinarith only [hw, hp]
                  · rw [if_neg hbad, add_zero]
                    exact hglobalReward r σ hr hbad)
              rw [havgConst] at hh
              linarith only [hh]
            have hWprefixAvg : ∀ r, r < E → avgPerm (fun σ => W (P r σ) (firstTimes n (L r)) σ) ≤ q r * V := by
              intro r hr
              exact le_trans (havgMono _ _ (fun σ => hsampleReward r σ hr)) (le_of_eq (hDavg r hr))
            have hWsegment : ∀ r, r < E → avgPerm (fun σ => W (P r σ) (T r) σ) =
                z r * (avgPerm (fun σ => W (P r σ) Finset.univ σ) -
                  avgPerm (fun σ => W (P r σ) (firstTimes n (L r)) σ)) := by
              intro r hr
              have hTmem : ∀ t ∈ T r, L r ≤ t.val := by
                intro t ht
                have hh := (Finset.mem_sdiff.mp ht).2
                simpa only [firstTimes, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hh
              have hs := hsegmentAverage (L r) (T r) (P r) (fun p t => (C p t).elim 0 (I.f t))
                (hLlt r hr) hTmem (hlearnedSwap I rule E (L r) hRule)
              have hcomp : Finset.univ.filter (fun t : Fin n => L r ≤ t.val) = Finset.univ \ firstTimes n (L r) := by
                ext t; simp [firstTimes, not_lt]
              rw [hcomp] at hs
              have he : (fun σ => ∑ t ∈ Finset.univ \ firstTimes n (L r), (C (P r σ) (σ t)).elim 0 (I.f (σ t))) =
                  (fun σ => W (P r σ) Finset.univ σ - W (P r σ) (firstTimes n (L r)) σ) := by
                funext σ
                exact Finset.sum_sdiff_eq_sub (Finset.subset_univ _)
              rw [he, havgSub] at hs
              exact hs
            have hcanonicalPhase : ∀ r, r < E →
                a r * (1 - 8 * H r) * V - z r * V * probPerm Bad ≤ avgPerm (fun σ => W (P r σ) (T r) σ) := by
              intro r hr
              rw [hWsegment r hr]
              have hleft := hWtotalAvg r hr
              have hright := hWprefixAvg r hr
              have hmul := mul_le_mul_of_nonneg_left (sub_le_sub hleft hright) (hz0 r)
              have hzH := mul_le_mul_of_nonneg_right (hzle r hr) (mul_nonneg (hHpos r).le hVnonneg)
              have hzaV := congrArg (fun x : ℝ => x * V) (hza r hr)
              nlinarith only [hmul, hzH, hzaV]
            have hproposalPhaseReward : ∀ r σ, r < E → W (P r σ) (T r) σ ≤
                (∑ t ∈ T r, ∑ j, I.arrF σ t j * multiProposal I rule tie ε σ t j) + (m : ℝ) * ∑ i, P r σ i := by
              intro r σ hr
              have hh := hchoiceRewardDiff (J σ) (P r σ) (fun t => C (P r σ) (σ t))
                (fun t => tie t (I.arrF σ) (I.arrG σ) (P r σ)) (T r)
                (hpermGP I σ hgp) (hPnonneg r σ hr) (fun t => hC (P r σ) (σ t)) (hTie r σ)
              have he : (∑ t ∈ T r, ∑ j, I.arrF σ t j * multiProposal I rule tie ε σ t j) =
                  ∑ t ∈ T r, (tie t (I.arrF σ) (I.arrG σ) (P r σ)).elim 0 (I.f (σ t)) := by
                apply Finset.sum_congr rfl
                intro t ht
                rw [hproposalPhase r σ t hr ht, hsumChoice]
                rfl
              rw [he]
              exact hh
            have hphaseAvg : ∀ r, r < E → a r * (1 - 8 * H r) * V - z r * V * probPerm Bad - δ ^ 2 / 131072 * V ≤
                avgPerm (fun σ => ∑ t ∈ T r, ∑ j, I.arrF σ t j * multiProposal I rule tie ε σ t j) := by
              intro r hr
              have hh := havgMono _ _ (fun σ => hproposalPhaseReward r σ hr)
              rw [havgAdd] at hh
              linarith only [hh, hcanonicalPhase r hr, hpriceAvg r hr]
            have hQavg : (1 - q 0 - 24 * δ - δ / 131072) * V - 4 * V * probPerm Bad ≤ avgPerm Q := by
              have hzero : ∀ σ, (∑ t ∈ firstTimes n (L 0), ∑ j, I.arrF σ t j * multiProposal I rule tie ε σ t j) = 0 := by
                intro σ
                apply Finset.sum_eq_zero
                intro t ht
                have ht' : t.val < learnTime n (accuracyExp ε) 0 := (Finset.mem_filter.mp ht).2
                simp only [multiProposal, if_neg hwindow, if_pos ht', mul_zero, Finset.sum_const_zero]
              have he : Q = fun σ => ∑ r ∈ Finset.range E, ∑ t ∈ T r, ∑ j, I.arrF σ t j * multiProposal I rule tie ε σ t j := by
                funext σ
                have hh := hphaseSum (fun t => ∑ j, I.arrF σ t j * multiProposal I rule tie ε σ t j)
                rw [hzero σ, sub_zero] at hh
                exact hh.symm
              rw [he, havgSum]
              have hh := Finset.sum_le_sum (fun r hr => hphaseAvg r (Finset.mem_range.mp hr))
              have hsum : (∑ r ∈ Finset.range E, (a r * (1 - 8 * H r) * V - z r * V * probPerm Bad - δ ^ 2 / 131072 * V)) =
                  ((∑ r ∈ Finset.range E, a r) - 8 * ∑ r ∈ Finset.range E, a r * H r) * V -
                  (∑ r ∈ Finset.range E, z r) * V * probPerm Bad - (E : ℝ) * δ ^ 2 / 131072 * V := by
                calc
                  _ = ∑ r ∈ Finset.range E, (V * a r - (8 * V) * (a r * H r) - (V * probPerm Bad) * z r - δ ^ 2 / 131072 * V) := by
                    apply Finset.sum_congr rfl
                    intro r hr
                    ring
                  _ = _ := by
                    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                    ring
              rw [hsum] at hh
              have haSum : ∑ r ∈ Finset.range E, a r = 1 - q 0 := hTsum
              rw [haSum] at hh
              have hH := mul_le_mul_of_nonneg_right hHweighted hVnonneg
              have hz := mul_le_mul_of_nonneg_right hzsum (mul_nonneg hVnonneg (by unfold probPerm; positivity : 0 ≤ probPerm Bad))
              have hEd : (E : ℝ) * δ ^ 2 ≤ δ := by
                have hm := mul_le_mul_of_nonneg_right hEδ hδ.le
                nlinarith only [hm]
              have hEdV := mul_le_mul_of_nonneg_right hEd hVnonneg
              nlinarith only [hh, hH, hz, hEdV]
            have hft : ∀ t j, I.f t j ≤ V := by
              intro t j
              have hf := (hstar.1.2 t (Finset.mem_univ _)).2 j
              have hg : ∑ i, pstar i * I.g t i j ≤ ∑ i, I.b i * pstar i := by
                apply Finset.sum_le_sum
                intro i hi
                have hh := mul_le_mul_of_nonneg_right (le_trans (I.g_le_one t i j) (hb1 i)) (hstar.1.1 i)
                simpa only [mul_comm] using hh
              have hy : ystar t ≤ ∑ u, ystar u := Finset.single_le_sum
                (fun u _ => (hstar.1.2 u (Finset.mem_univ _)).1) (Finset.mem_univ t)
              change I.f t j ≤ (∑ i, I.b i * pstar i) + ∑ u, ystar u
              linarith only [hf, hg, hy]
            have hQbound : ∀ σ, Q σ ≤ (n : ℝ) * V := by
              intro σ
              have hh : Q σ ≤ ∑ t : Fin n, V := by
                apply Finset.sum_le_sum
                intro t ht
                calc
                  (∑ j, I.arrF σ t j * multiProposal I rule tie ε σ t j) ≤
                      ∑ j, V * multiProposal I rule tie ε σ t j :=
                    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hft (σ t) j) (hproposal I rule tie ε σ t j)
                  _ = V * ∑ j, multiProposal I rule tie ε σ t j := (Finset.mul_sum _ _ _).symm
                  _ ≤ V := mul_le_of_le_one_right hVnonneg (hproposalSum I rule tie ε σ t)
              simpa using hh
            have hguardAvg : avgPerm Q ≤ avgPerm (fun σ => multiValue I rule tie ε σ) + (n : ℝ) * V * probPerm Bad := by
              exact havgError Q (fun σ => multiValue I rule tie ε σ) ((n : ℝ) * V) Bad (fun σ => by
                by_cases hbad : Bad σ
                · rw [if_pos hbad]
                  linarith only [hQbound σ, hvalue I rule tie ε σ]
                · rw [if_neg hbad, add_zero]
                  have he : Q σ = multiValue I rule tie ε σ := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    rw [hgoodFits σ hbad t]
                  exact he.le)
            have hqzero : q 0 ≤ 2 * δ := by
              have hh : (L 0 : ℝ) ≤ δ * (n : ℝ) + 1 := by
                simpa [L, learnTime, δ] using (Nat.ceil_lt_add_one (by positivity : 0 ≤ δ * (n : ℝ))).le
              apply (div_le_iff₀ hnR).mpr
              nlinarith only [hh, hδn]
            have hp0 : 0 ≤ probPerm Bad := by unfold probPerm; positivity
            have hbadLoss : ((n : ℝ) + 4) * probPerm Bad ≤ δ := by
              have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (n : ℝ) ^ 2)).mp hBadSmall
              have hn4 : (n : ℝ) + 4 ≤ 2 * n := by linarith only [hnlarge]
              have hm := mul_le_mul_of_nonneg_right hn4 hp0
              have h1 : (n : ℝ) * probPerm Bad ≤ 1 / (16 * (n : ℝ)) := by
                apply (le_div_iff₀ (by positivity)).mpr
                nlinarith only [hh]
              have h2 : 1 / (16 * (n : ℝ)) ≤ δ / 16 := by
                apply (div_le_iff₀ (by positivity)).mpr
                nlinarith only [hδn]
              linarith only [hm, h1, h2, hδ]
            have hbadV := mul_le_mul_of_nonneg_right hbadLoss hVnonneg
            have hqV := mul_le_mul_of_nonneg_right hqzero hVnonneg
            have hεV := mul_le_mul_of_nonneg_right hδε.2 hVnonneg
            have hδV := mul_nonneg hδ.le hVnonneg
            nlinarith only [hQavg, hguardAvg, hbadV, hqV, hεV, hδV]
