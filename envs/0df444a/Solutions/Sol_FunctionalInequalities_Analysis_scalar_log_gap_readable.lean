-- Prove2me | solution 1 for FunctionalInequalities.Analysis.scalar_log_gap_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:33.294608+00:00
-- url     : https://prove2.me/submissions/bd5ea1c6-19e1-4b43-a025-7cb3098acca7

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_LogDet

noncomputable section
open Matrix
section LogDetConcavity
 lemma solution {a b K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haK : a ≤ K) (hbK : b ≤ K) :
    Real.log b + (b - a) ^ 2 / (2 * K ^ 2) ≤
      Real.log a + (b - a) / a := by
  let f : ℝ → ℝ := fun x => Real.log x + x ^ 2 / (2 * K ^ 2)
  let d : ℝ → ℝ := fun x => x⁻¹ + x / K ^ 2
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt f (d x) x := by
    intro x hx
    have h := (Real.hasDerivAt_log hx.ne').fun_add
      (((hasDerivAt_id x).fun_pow 2).div_const (2 * K ^ 2))
    have he :
        x⁻¹ + (↑(2 : ℕ) * id x ^ (2 - 1) * 1) / (2 * K ^ 2) = d x := by
      dsimp [d]
      ring
    rw [he] at h
    exact h
  have hdd :
      ∀ x : ℝ, 0 < x → HasDerivAt d (-1 / x ^ 2 + 1 / K ^ 2) x := by
    intro x hx
    simpa [d] using
      ((hasDerivAt_id x).inv hx.ne').fun_add
        ((hasDerivAt_id x).div_const (K ^ 2))
  have hc : ConcaveOn ℝ (Set.Ioc 0 K) f := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos
      (f' := d) (f'' := fun x => -1 / x ^ 2 + 1 / K ^ 2)
      (convex_Ioc 0 K)
      (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx).1).hasDerivWithinAt)
      (fun x hx => (hdd x (interior_subset hx).1).hasDerivWithinAt) ?_
    intro x hx
    have hx' : x ∈ Set.Ioc 0 K := interior_subset hx
    have hsq : x ^ 2 ≤ K ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hx'.2)
        (show 0 ≤ K + x by linarith [hx'.1, hx'.2])
      nlinarith
    have hi := one_div_le_one_div_of_le (sq_pos_of_pos hx'.1) hsq
    change -1 / x ^ 2 + 1 / K ^ 2 ≤ 0
    simp only [neg_div]
    linarith
  have ht : f b - f a ≤ d a * (b - a) := by
    rcases lt_trichotomy a b with hab | hab | hab
    · have hs := hc.slope_le_of_hasDerivAt
        ⟨ha, haK⟩ ⟨hb, hbK⟩ hab (hd a ha)
      rw [slope_def_field] at hs
      exact (div_le_iff₀ (sub_pos.mpr hab)).mp hs
    · subst b
      simp
    · have hs := hc.le_slope_of_hasDerivAt
        ⟨hb, hbK⟩ ⟨ha, haK⟩ hab (hd a ha)
      rw [slope_def_field] at hs
      have hs' := (le_div_iff₀ (sub_pos.mpr hab)).mp hs
      nlinarith
  have he :
      Real.log b + (b - a) ^ 2 / (2 * K ^ 2) -
          (Real.log a + (b - a) / a) =
        f b - f a - d a * (b - a) := by
    dsimp [f, d]
    ring
  linarith
