-- Prove2me | solution 2 for CohnElkies.saddleNegativeFrequencyMajorant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:11.779992+00:00
-- url     : https://prove2.me/submissions/ef84963a-0623-420f-92c7-6aa0a33b2927

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
noncomputable def h47_G (ε : ℝ) (s : ℝ) : ℝ := (1 + s) ^ 3 * Real.exp (-ε * Real.pi * s)

theorem h47_G_integrableOn {ε : ℝ} (hε : 0 < ε) : IntegrableOn (h47_G ε) (Ioi 0) := by
  have hc : 0 < ε * Real.pi / 2 := by have := Real.pi_pos; positivity
  apply integrable_of_isBigO_exp_neg hc (by unfold h47_G; fun_prop : Continuous (h47_G ε)).continuousOn
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 3 hc).bound one_pos
  apply Asymptotics.IsBigO.of_bound 8
  filter_upwards [h1, eventually_ge_atTop 1] with x hx hx1
  simp only [Real.norm_eq_abs] at hx ⊢
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 3), abs_of_pos (Real.exp_pos _), one_mul] at hx
  unfold h47_G
  rw [abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)]
  have hBB : Real.exp (-ε * Real.pi * x) = Real.exp (-(ε * Real.pi / 2) * x) * Real.exp (-(ε * Real.pi / 2) * x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hAB : Real.exp (ε * Real.pi / 2 * x) * Real.exp (-(ε * Real.pi / 2) * x) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]; congr 1; ring
  have hpoly : (1 + x) ^ 3 ≤ 8 * Real.exp (ε * Real.pi / 2 * x) := by nlinarith [sq_nonneg x, mul_nonneg (sub_nonneg.2 hx1) (sq_nonneg x)]
  have hB := Real.exp_pos (-(ε * Real.pi / 2) * x)
  rw [hBB]
  have := mul_le_mul_of_nonneg_right hpoly (mul_pos hB hB).le
  nlinarith

theorem solution
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (saddleNegativeFrequencyMajorant ε) := by
  have hgI : Integrable ((Ici (0:ℝ)).indicator (h47_G ε)) :=
    (integrable_indicator_iff measurableSet_Ici).2 ((integrableOn_Ici_iff_integrableOn_Ioi).2 (h47_G_integrableOn hε))
  have hG0 : ∀ s, 0 ≤ s → 0 ≤ h47_G ε s := fun s hs => by unfold h47_G; positivity
  have hind : ∀ s, 0 ≤ (Ici (0:ℝ)).indicator (h47_G ε) s := fun s => by
    by_cases hs : 0 ≤ s
    · rw [indicator_of_mem (show s ∈ Ici (0:ℝ) from hs)]; exact hG0 s hs
    · rw [indicator_of_notMem (show s ∉ Ici (0:ℝ) from hs)]
  unfold saddleNegativeFrequencyMajorant
  refine Integrable.mono' (hgI.add hgI.comp_neg) (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun s => ?_)
  rw [Real.norm_of_nonneg (by positivity), Pi.add_apply]
  beta_reduce
  rcases le_total 0 s with hs | hs
  · rw [indicator_of_mem (show s ∈ Ici (0:ℝ) from hs), abs_of_nonneg hs]
    have := hind (-s)
    unfold h47_G at this ⊢
    linarith
  · rw [indicator_of_mem (show -s ∈ Ici (0:ℝ) from neg_nonneg.2 hs), abs_of_nonpos hs]
    have := hind s
    unfold h47_G at this ⊢
    linarith

