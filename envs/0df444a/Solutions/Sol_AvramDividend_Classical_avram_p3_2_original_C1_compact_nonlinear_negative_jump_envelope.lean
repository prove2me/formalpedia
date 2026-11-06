-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_C1_compact_nonlinear_negative_jump_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:42:02.315541+00:00
-- url     : https://prove2.me/submissions/87e1110f-2e13-4d9a-80bb-25a2fba67266

import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- The actual C1 dividend candidate has a source-valid nonlinear negative
jump envelope on compact original reserve strips, including ruin crossing. -/
theorem solution
    (w : ℝ → ℝ) (U : Set ℝ)
    (hwC1 : ContDiffOn ℝ 1 w U)
    (hwCont : ContinuousOn w (Set.Ici (0 : ℝ)))
    (hwNeg : ∀ v : ℝ, v < 0 → w v = 0)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hBand : Set.Icc (a / 2) b ⊆ U) :
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      ∀ y ∈ Set.Icc a b, ∀ z : ℝ, z < 0 →
        |w (y + z) - w y| ≤
          if -(a / 2) ≤ z then L * |z| else 2 * R := by
  have hC1Band : ContDiffOn ℝ 1 w (Set.Icc (a / 2) b) :=
    hwC1.mono hBand
  have hLocal : LocallyLipschitzOn (Set.Icc (a / 2) b) w :=
    ContDiffOn.locallyLipschitzOn (convex_Icc (a / 2) b) hC1Band
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      isCompact_Icc hLocal
  have hContBand : ContinuousOn w (Set.Icc (0 : ℝ) b) :=
    hwCont.mono (by
      intro v hv
      exact hv.1)
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) b)).exists_bound_of_continuousOn hContBand
  have hBelow (v : ℝ) (hv : v ≤ b) : |w v| ≤ max B 0 := by
    by_cases hNeg : v < 0
    · rw [hwNeg v hNeg]
      simpa only [abs_zero] using (le_max_right B 0)
    · have h0 : 0 ≤ v := le_of_not_gt hNeg
      have hNorm : |w v| ≤ B := by
        simpa only [Real.norm_eq_abs] using hB v ⟨h0, hv⟩
      exact hNorm.trans (le_max_left B 0)
  refine ⟨(K : ℝ), max B 0, NNReal.coe_nonneg K, le_max_right B 0, ?_⟩
  intro y hy z hz
  by_cases hzSmall : -(a / 2) ≤ z
  · have hyBand : y ∈ Set.Icc (a / 2) b := by
      constructor
      · linarith only [ha, hy.1]
      · exact hy.2
    have hyShift : y + z ∈ Set.Icc (a / 2) b := by
      constructor
      · linarith only [hy.1, hzSmall]
      · linarith only [hy.2, hz]
    have h := hK.dist_le_mul (y + z) hyShift y hyBand
    have hShift : y + z - y = z := by ring
    rw [Real.dist_eq, Real.dist_eq, hShift] at h
    simpa [hzSmall] using h
  · have h1 := hBelow (y + z) (by linarith only [hy.2, hz])
    have h2 := hBelow y hy.2
    have hTriangle : |w (y + z) - w y| ≤
        |w (y + z)| + |w y| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (w (y + z)) (0 : ℝ) (w y))
    have hBound : |w (y + z) - w y| ≤ 2 * max B 0 := by
      calc
        _ ≤ |w (y + z)| + |w y| := hTriangle
        _ ≤ max B 0 + max B 0 := add_le_add h1 h2
        _ = 2 * max B 0 := by ring
    simpa [hzSmall] using hBound
