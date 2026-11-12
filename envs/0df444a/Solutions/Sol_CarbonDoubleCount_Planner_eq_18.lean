-- Prove2me | solution 1 for CarbonDoubleCount.Planner.eq_18
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:23:39.616129+00:00
-- url     : https://prove2.me/submissions/3ddf85f7-b93c-456e-91af-9a84e8709139

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_Setting

variable {ι : Type} {act : ι → Type} {κ : Type}
variable [Fintype ι] [DecidableEq ι]
variable [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
variable [Fintype κ] [DecidableEq κ]

open CarbonDoubleCount.Planner in
theorem solution
    (A pS : ℝ) (hA : 0 < A) (hpS : 0 < pS)
    (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (effortBox A))
    (estar : (n : ι) → act n → ℝ)
    (hebox : estar ∈ effortBox A)
    (hint : ∀ n j, 0 < estar n j ∧ estar n j < A)
    (h : ι → (κ → ℝ) → ℝ)
    (hdiff : ∀ n, Differentiable ℝ (h n))
    (hmono : ∀ n, Monotone (h n))
    (h17 : ∀ i, (∑ n, dFoot (h n) (f estar) i) ≤ pS)
    (h14 : ∀ n j,
      (∑ i, dEff (fun e => f e i) estar n j *
        (dFoot (h n) (f estar) i - pS)) = 0) :
    ∀ i n j,
      dEff (fun e => f e i) estar n j *
        (dFoot (h n) (f estar) i - pS) = 0 := by
  have hbox : ∀ (n : ι) (j : act n) (u : ℝ), 0 ≤ u → u ≤ A →
      Function.update estar n (Function.update (estar n) j u) ∈ effortBox A := by
    intro n j u hu0 huA n' j'
    by_cases hn : n' = n
    · subst hn
      rw [Function.update_self]
      by_cases hj : j' = j
      · subst hj
        rw [Function.update_self]
        exact ⟨hu0, huA⟩
      · rw [Function.update_of_ne hj]
        exact hebox n' j'
    · rw [Function.update_of_ne hn]
      exact hebox n' j'
  have hmu : ∀ (n : ι) (j : act n) (s t : ℝ), s ≤ t →
      Function.update estar n (Function.update (estar n) j s) ≤
        Function.update estar n (Function.update (estar n) j t) := by
    intro n j s t hst n' j'
    by_cases hn : n' = n
    · subst hn
      rw [Function.update_self, Function.update_self]
      by_cases hj : j' = j
      · subst hj
        rw [Function.update_self, Function.update_self]
        exact hst
      · simp only [Function.update_of_ne hj, le_refl]
    · simp only [Function.update_of_ne hn, le_refl]
  have hdEff : ∀ i n j, dEff (fun e => f e i) estar n j ≤ 0 := by
    intro i n j
    obtain ⟨h0, hA'⟩ := hint n j
    unfold dEff
    rw [← derivWithin_of_mem_nhds (Ioo_mem_nhds h0 hA')]
    apply AntitoneOn.derivWithin_nonpos
    intro s hs t ht hst
    exact hfanti i (hbox n j s hs.1.le hs.2.le) (hbox n j t ht.1.le ht.2.le) (hmu n j s t hst)
  have hdF : ∀ n i, 0 ≤ dFoot (h n) (f estar) i := by
    intro n i
    unfold dFoot
    apply Monotone.deriv_nonneg
    intro s t hst
    apply hmono n
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self]
      exact hst
    · simp only [Function.update_of_ne hk, le_refl]
  have hT : ∀ i n j, 0 ≤ dEff (fun e => f e i) estar n j * (dFoot (h n) (f estar) i - pS) := by
    intro i n j
    have hle : dFoot (h n) (f estar) i ≤ ∑ n', dFoot (h n') (f estar) i :=
      Finset.single_le_sum (fun n' _ => hdF n' i) (Finset.mem_univ n)
    exact mul_nonneg_of_nonpos_of_nonpos (hdEff i n j) (by linarith [h17 i])
  intro i n j
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ => hT i' n j)).1 (h14 n j) i
    (Finset.mem_univ _)
