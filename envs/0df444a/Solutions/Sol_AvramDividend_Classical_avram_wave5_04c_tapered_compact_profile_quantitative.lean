-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_tapered_compact_profile_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:22:20.305753+00:00
-- url     : https://prove2.me/submissions/4fa81f06-e360-4248-9984-8c913f7afa50

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set

/-! Quantitative compact cutoff: the taper is bounded pointwise by the
absolute profile at the clamped argument. -/
theorem solution (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hb : b ≤ 1)
    (hf : ContinuousOn f (Icc a 1)) :
    ∃ G : C(unitInterval.Elem, ℝ),
      (∀ t : unitInterval.Elem, (t : ℝ) ≤ a → G t = 0) ∧
      (∀ t : unitInterval.Elem, b ≤ (t : ℝ) → G t = f (t : ℝ)) ∧
      (∀ t : unitInterval.Elem,
        |G t| ≤ |f (max a (min (t : ℝ) 1))|) := by
  have hden : 0 < b - a := sub_pos.mpr hab
  let cutoff : ℝ → ℝ := fun t => min 1 (max 0 ((t - a) / (b - a)))
  have hcut : Continuous cutoff := by
    dsimp [cutoff]
    fun_prop
  have hc : Continuous (fun t : ℝ => max a (min t 1)) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hmap : ∀ t : ℝ, max a (min t 1) ∈ Icc a 1 := by
    intro t
    exact ⟨le_max_left _ _, max_le (le_trans (le_of_lt hab) hb) (min_le_right _ _)⟩
  have hcomp : ContinuousOn (fun t : ℝ => f (max a (min t 1))) (Icc 0 1) := by
    apply hf.comp hc.continuousOn
    intro t ht
    exact hmap t
  have hprod : ContinuousOn
      (fun t : ℝ => cutoff t * f (max a (min t 1))) (Icc 0 1) :=
    hcut.continuousOn.mul hcomp
  have hsub : Continuous
      (fun t : unitInterval.Elem =>
        cutoff (t : ℝ) * f (max a (min (t : ℝ) 1))) :=
    (continuousOn_iff_continuous_restrict).mp hprod
  let G : C(unitInterval.Elem, ℝ) :=
    ⟨fun t => cutoff (t : ℝ) * f (max a (min (t : ℝ) 1)), hsub⟩
  refine ⟨G, ?_, ?_, ?_⟩
  · intro t ht
    have hr : ((t : ℝ) - a) / (b - a) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hden.le
    have hk : cutoff (t : ℝ) = 0 := by
      simp [cutoff, max_eq_left hr]
    simp [G, hk]
  · intro t ht
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hat : a ≤ (t : ℝ) := le_trans (le_of_lt hab) ht
    have hr : 1 ≤ ((t : ℝ) - a) / (b - a) := by
      apply (one_le_div₀ hden).2
      linarith
    have hmax : max 0 (((t : ℝ) - a) / (b - a)) =
        ((t : ℝ) - a) / (b - a) :=
      max_eq_right (le_trans (by norm_num) hr)
    have hmin : min 1 (((t : ℝ) - a) / (b - a)) = 1 :=
      min_eq_left hr
    have hk : cutoff (t : ℝ) = 1 := by
      change min 1 (max 0 (((t : ℝ) - a) / (b - a))) = 1
      rw [hmax]
      exact hmin
    simp [G, hk, min_eq_left ht1, max_eq_right hat]
  · intro t
    have hk0 : 0 ≤ cutoff (t : ℝ) := by
      dsimp [cutoff]
      exact le_min (by norm_num) (le_max_left _ _)
    have hk1 : cutoff (t : ℝ) ≤ 1 := min_le_left _ _
    change |cutoff (t : ℝ) * f (max a (min (t : ℝ) 1))| ≤
      |f (max a (min (t : ℝ) 1))|
    rw [abs_mul, abs_of_nonneg hk0]
    nlinarith [abs_nonneg (f (max a (min (t : ℝ) 1)))]
