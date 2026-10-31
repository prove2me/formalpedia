-- Prove2me | solution 1 for DisplayMNL.Rounding.ineq_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:37:06.801993+00:00
-- url     : https://prove2.me/submissions/be159b2e-e727-4c33-b13e-4feefca9b10a

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model
import Theorems.Thm_DisplayMNL_Rounding_lemma_5_2
import Theorems.Thm_DisplayMNL_Rounding_lemma_5_3

open Finset

namespace RRBI16
open DisplayMNL.Rounding

theorem rhoSet_nonneg {n : ℕ} (I : Instance n) (hr : ∀ i, 0 < I.r i) (hw : ∀ i, 0 < I.w i)
    (S : Finset (Fin n)) : 0 ≤ rhoSet I S :=
  Finset.sum_nonneg (fun i _ => (mul_pos (hr i) (hw i)).le)

theorem wt_nonneg {n : ℕ} (I : Instance n) (hw : ∀ i, 0 < I.w i)
    (S : Finset (Fin n)) : 0 ≤ wt I S :=
  Finset.sum_nonneg (fun i _ => (hw i).le)

/-- One endpoint: `(1 - 8ε) α_j ≤ R_{ẽ_j}`. -/
theorem single {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j ≤ s.T) :
    (1 - 8 * ε) * alpha I s j ≤ revAt I A (etil s kmid j) := by
  have h2 := lemma_5_2 I ε kmid s A hst hk1 hk2 hF hR j hj1 hjT
  have h3 := lemma_5_3 I ε kmid s A hst hk1 hk2 hF hR j hj1 hjT
  have hr := hst.2.1
  have hw := hst.2.2.1
  have hρ := rhoSet_nonneg I hr hw (pre A (etil s kmid j))
  have hwU := wt_nonneg I hw (pre A (etil s kmid j))
  unfold revAt rev alpha
  set a := rhoSet I (s.sm j)
  set b := wt I (s.sp j)
  set c := rhoSet I (pre A (etil s kmid j))
  set d := wt I (pre A (etil s kmid j))
  have hb : 0 < 1 + b := by linarith
  have hd : 0 < 1 + d := by linarith
  rw [← mul_div_assoc, div_le_div_iff₀ hb hd]
  calc (1 - 8 * ε) * a * (1 + d) ≤ c * (1 + d) := mul_le_mul_of_nonneg_right h2 hd.le
    _ ≤ c * (1 + b) := mul_le_mul_of_nonneg_left (by linarith) hρ

theorem alpha_nonneg {n : ℕ} (I : Instance n) (hr : ∀ i, 0 < I.r i) (hw : ∀ i, 0 < I.w i)
    (s : DPSeq n) (j : ℕ) : 0 ≤ alpha I s j := by
  unfold alpha
  apply div_nonneg (rhoSet_nonneg I hr hw _)
  have := wt_nonneg I hw (s.sp j); linarith

end RRBI16

open DisplayMNL.Rounding in
theorem solution {n : ℕ} (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (A : Fin n ≃ Fin n)
    (hst : Standing I ε) (hk1 : 1 ≤ kmid) (hk2 : kmid + 1 ≤ n)
    (hF : IsFeasible I ε kmid s) (hR : IsRounded I s kmid A)
    (j : ℕ) (hj1 : 1 ≤ j) (hjT : j + 1 ≤ s.T) :
    (1 - 8 * ε) * min (alpha I s j) (alpha I s (j + 1)) ≤
      min (revAt I A (etil s kmid j)) (revAt I A (etil s kmid (j + 1))) := by
  have h1 := RRBI16.single I ε kmid s A hst hk1 hk2 hF hR j hj1 (by omega)
  have h2 := RRBI16.single I ε kmid s A hst hk1 hk2 hF hR (j + 1) (by omega) hjT
  have ha1 := RRBI16.alpha_nonneg I hst.2.1 hst.2.2.1 s j
  have ha2 := RRBI16.alpha_nonneg I hst.2.1 hst.2.2.1 s (j + 1)
  rcases le_total 0 (1 - 8 * ε) with hc | hc
  · rw [mul_min_of_nonneg _ _ hc]
    exact min_le_min h1 h2
  · have hm : 0 ≤ min (alpha I s j) (alpha I s (j + 1)) := le_min ha1 ha2
    have hneg : (1 - 8 * ε) * min (alpha I s j) (alpha I s (j + 1)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc hm
    refine hneg.trans (le_min ?_ ?_)
    · unfold revAt rev
      apply div_nonneg (RRBI16.rhoSet_nonneg I hst.2.1 hst.2.2.1 _)
      have := RRBI16.wt_nonneg I hst.2.2.1 (pre A (etil s kmid j)); linarith
    · unfold revAt rev
      apply div_nonneg (RRBI16.rhoSet_nonneg I hst.2.1 hst.2.2.1 _)
      have := RRBI16.wt_nonneg I hst.2.2.1 (pre A (etil s kmid (j + 1))); linarith
