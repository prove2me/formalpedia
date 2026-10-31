-- Prove2me | solution 1 for FairRentFPTAS.Approx.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:29:28.322153+00:00
-- url     : https://prove2.me/submissions/b4a73593-8a15-4871-ad46-c0e81e436f50

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

open FairRentFPTAS.Approx

namespace FRFL5Aux

lemma drop_mono : ∀ (l : List (ℝ × ℝ)), (∀ e ∈ l, 0 ≤ e.2) →
    ∀ x y : ℝ, x ≤ y → PLFun.drop l x ≤ PLFun.drop l y := by
  intro l
  induction l with
  | nil => intro _ x y _; simp [PLFun.drop]
  | cons e t ih =>
    intro hl x y hxy
    have he := hl e (by simp)
    cases t with
    | nil =>
      simp only [PLFun.drop]
      exact mul_le_mul_of_nonneg_left (by gcongr) he
    | cons e' t' =>
      simp only [PLFun.drop]
      have := ih (fun z hz => hl z (List.mem_cons_of_mem _ hz)) x y hxy
      have h2 : e.2 * (min (max x e.1) e'.1 - e.1) ≤ e.2 * (min (max y e.1) e'.1 - e.1) :=
        mul_le_mul_of_nonneg_left (by gcongr) he
      linarith

lemma eval_hat_anti {n : ℕ} (J : Instance n) (hJ : Standing J) (M : ℝ) (a r : Fin n)
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ((hatInst M J).v a r).eval y ≤ ((hatInst M J).v a r).eval x := by
  show (extendQL M (J.v a r)).eval y ≤ (extendQL M (J.v a r)).eval x
  unfold PLFun.eval
  simp only [not_lt.mpr hx, not_lt.mpr (le_trans hx hxy), if_false]
  have : PLFun.drop (extendQL M (J.v a r)).pieces x ≤ PLFun.drop (extendQL M (J.v a r)).pieces y := by
    apply drop_mono _ _ x y hxy
    intro e he
    unfold extendQL at he
    simp only [List.mem_append, List.mem_filter, List.mem_singleton] at he
    rcases he with ⟨he, _⟩ | rfl
    · exact ((hJ a r).2.2.2 e he).le
    · norm_num
  linarith

end FRFL5Aux

open FRFL5Aux in
theorem solution {n : ℕ} (J : Instance n) (M : ℝ) (hJ : Standing J) (hM : IsThreshold J M)
    (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ) (hrun : IsRun J M T π p)
    (i : ℕ) (hi : 1 ≤ i) (hiT : i ≤ T) :
    ∀ r, p i r ≤ p (i - 1) r := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨hpos, hmax, hLP⟩ := hrun.2.2 k (by omega)
  obtain ⟨⟨hL1, hU1, hEF1, hnn1⟩, hopt⟩ := hLP
  set Ĵ := hatInst M J
  set σ := π (k + 1)
  -- `p k` is feasible
  have hLk : ∀ r, domL Ĵ (p k) r ≤ ((p k r : ℝ) : WithBot ℝ) := by
    intro r
    unfold domL
    apply Finset.max_le
    intro b hb
    exact WithBot.coe_le_coe.mpr (Finset.mem_filter.mp hb).2.le
  have hUk : ∀ r, ((p k r : ℝ) : WithTop ℝ) ≤ domU Ĵ (p k) r := by
    intro r
    unfold domU
    apply Finset.le_min
    intro b hb
    exact WithTop.coe_le_coe.mpr (Finset.mem_filter.mp hb).2
  have hEFk : IsEF Ĵ σ (p k) := fun a r => hmax.1 a r
  by_contra hcon
  push_neg at hcon
  obtain ⟨r0, hr0⟩ := hcon
  set q : Fin n → ℝ := fun r => min (p k r) (p (k + 1) r) with hq
  have hqfeas : LPFeasible Ĵ (domL Ĵ (p k)) (domU Ĵ (p k)) σ q := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r
      rcases min_choice (p k r) (p (k + 1) r) with h | h
      · simp only [hq, h]; exact hLk r
      · simp only [hq, h]; exact hL1 r
    · intro r
      refine le_trans ?_ (hU1 r)
      exact WithTop.coe_le_coe.mpr (min_le_right _ _)
    · intro a r
      have hσ0 : 0 ≤ q (σ a) := le_min (hpos _).le (hnn1 _)
      rcases min_choice (p k r) (p (k + 1) r) with h | h
      · have e : q r = p k r := by simp only [hq, h]
        rw [e]
        refine le_trans (hEFk a r) ?_
        exact eval_hat_anti J hJ M a (σ a) _ _ hσ0 (min_le_left _ _)
      · have e : q r = p (k + 1) r := by simp only [hq, h]
        rw [e]
        refine le_trans (hEF1 a r) ?_
        exact eval_hat_anti J hJ M a (σ a) _ _ hσ0 (min_le_right _ _)
    · intro r
      exact le_min (hpos r).le (hnn1 r)
  have h1 := hopt q hqfeas
  have h2 : ∑ r, q r < ∑ r, p (k + 1) r := by
    apply Finset.sum_lt_sum
    · intro r _; exact min_le_right _ _
    · exact ⟨r0, Finset.mem_univ _, by simp only [hq]; exact min_lt_of_left_lt hr0⟩
  linarith
