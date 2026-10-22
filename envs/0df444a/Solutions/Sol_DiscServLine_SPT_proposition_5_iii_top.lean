-- Prove2me | solution 1 for DiscServLine.SPT.proposition_5_iii_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:49:30.389267+00:00
-- url     : https://prove2.me/submissions/dcaa1486-699a-4d30-83cb-e1dd2d8f24c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model
import Theorems.Thm_DiscServLine_SPT_proposition_5_i_ii
import Theorems.Thm_DiscServLine_SPT_W_quadratic_at_optimum

open DiscServLine.SPT

theorem solution (P : Params) (hP : P.Standing) :
    (∃ d, IsOptimal P d) ∧
      ∀ d, IsOptimal P d →
        ConcaveOn ℝ (Set.Icc d.lo d.hi) (price P d) ∧
        ∃ p < 0, HasDerivWithinAt (price P d) p (Set.Icc d.lo d.hi) d.hi := by
  obtain ⟨hex, h12⟩ := proposition_5_i_ii P hP
  refine ⟨hex, fun d hd => ?_⟩
  obtain ⟨hlohi, -⟩ := h12 d hd
  obtain ⟨α0, α2, hα2, hW, hhi⟩ := W_quadratic_at_optimum P hP d hd
  have hlo0 : 0 ≤ d.lo := hd.1.1.2.1
  obtain ⟨hc, -, hb, -⟩ := hP
  set q : ℝ → ℝ := fun t => (P.θbar * t - P.b * t ^ 2) - P.c * (t + (-α0 + t ^ 2 * α2)) with hq
  have heq : Set.EqOn q (price P d) (Set.Icc d.lo d.hi) := by
    intro t ht; simp only [hq, price, hW t ht]
  have hderiv : ∀ t, HasDerivAt q (P.θbar - 2 * P.b * t - P.c * (1 + 2 * α2 * t)) t := by
    intro t
    have := (((hasDerivAt_id t).const_mul P.θbar).sub ((hasDerivAt_pow 2 t).const_mul P.b)).sub
      (((hasDerivAt_id t).add (((hasDerivAt_pow 2 t).mul_const α2).const_add (-α0))).const_mul P.c)
    exact (this.congr_deriv (by simp; ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp [hq])
  have hK : 0 < P.b + P.c * α2 := by positivity
  refine ⟨?_, ?_⟩
  · refine ConcaveOn.congr ?_ heq
    refine ⟨convex_Icc _ _, fun x _ y _ a b' ha hb' hab => ?_⟩
    have hb'' : b' = 1 - a := by linarith
    subst hb''
    simp only [hq, smul_eq_mul]
    nlinarith [mul_nonneg (mul_nonneg ha hb') (mul_nonneg hK.le (sq_nonneg (x - y)))]
  · refine ⟨P.θbar - 2 * P.b * d.hi - P.c * (1 + 2 * α2 * d.hi), ?_, ?_⟩
    · have hhi0 : 0 < d.hi := by linarith
      have : P.c * (2 * α2 * d.hi) = P.θbar - P.c := by
        rw [hhi]; field_simp
      nlinarith [mul_pos hb hhi0]
    · exact (hderiv d.hi).hasDerivWithinAt.congr_of_mem (fun t ht => (heq ht).symm)
        ⟨hlohi.le, le_refl _⟩
