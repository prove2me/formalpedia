-- Prove2me | solution 1 for BesbesZeevi.Nonparametric.JDn_eq_mul_JD
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:26:29.334486+00:00
-- url     : https://prove2.me/submissions/c1e5fb71-4046-4b76-b415-7ba550f26b14

import Mathlib
import Definitions.Def_BesbesZeevi_Nonparametric_Model

open MeasureTheory

namespace BesbesZeevi.Nonparametric

lemma feasiblePath_scale_iff_7ee (P : PriceSet) (lam : ℝ → ℝ) (x T c : ℝ) (hc : 0 < c)
    (p : ℝ → ℝ) :
    FeasiblePath P (fun q => c * lam q) (c * x) T p ↔ FeasiblePath P lam x T p := by
  unfold FeasiblePath
  have hii : IntervalIntegrable (fun s => c * lam (p s)) volume 0 T ↔
      IntervalIntegrable (fun s => lam (p s)) volume 0 T := by
    constructor
    · intro h
      have := h.const_mul c⁻¹
      refine this.congr ?_
      intro s _
      simp [hc.ne']
    · intro h
      exact h.const_mul c
  have hint : (∫ s in (0 : ℝ)..T, c * lam (p s)) = c * ∫ s in (0 : ℝ)..T, lam (p s) :=
    intervalIntegral.integral_const_mul c _
  rw [hii, hint, mul_le_mul_iff_of_pos_left hc]

lemma pathRevenue_scale_7ee (lam : ℝ → ℝ) (T c : ℝ) (p : ℝ → ℝ) :
    pathRevenue (fun q => c * lam q) T p = c * pathRevenue lam T p := by
  unfold pathRevenue
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

end BesbesZeevi.Nonparametric

open BesbesZeevi.Nonparametric MeasureTheory Pointwise in
theorem solution (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    JDn P lam x T n = (n : ℝ) * JD P lam x T := by
  have hc : (0 : ℝ) < n := by exact_mod_cast hn
  unfold JDn JD
  have hset : pathRevenue (fun q => (n : ℝ) * lam q) T ''
      {p | FeasiblePath P (fun q => (n : ℝ) * lam q) ((n : ℝ) * x) T p} =
      (n : ℝ) • (pathRevenue lam T '' {p | FeasiblePath P lam x T p}) := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul,
      feasiblePath_scale_iff_7ee P lam x T _ hc, pathRevenue_scale_7ee]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [hset, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul]
