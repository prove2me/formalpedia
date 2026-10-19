-- Prove2me | solution 1 for CohnElkies.eventually_saddleSource_secondBranch_pointwise_gaussian_plus_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/4f4c3cb3-20a1-4df8-9bf9-976bc315d33c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_positiveShellDamping_lower_bound
import Theorems.Thm_CohnElkies_upperGammaDamping_lower_bound
import Theorems.Thm_CohnElkies_eventually_upperSaddleDamping_gamma_add_shell
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_nonneg
import Theorems.Thm_CohnElkies_saddle_exp_neg_mul_min_le_add
import Theorems.Thm_CohnElkies_eventually_saddleSourceContourDamping_secondBranch_local_coercivity

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            saddleGaussianTailWeight T *
                Real.exp
                  (-saddleSourceContourDamping
                    ε ℓ (1 + δ) T) ≤
              saddleGaussianTailWeight T *
                  Real.exp
                    (-saddleSourceSecondBranchGaussianRate
                      ε ℓ δ * T ^ 2) +
                Real.exp
                    (-saddleSourceSecondBranchOuterBarrier
                      ε ℓ δ) *
                  (saddleGaussianTailWeight T *
                    Real.exp
                      (-saddleSourceSecondBranchGammaGaussianRate
                        ℓ δ * T ^ 2) +
                    saddleGaussianTailWeight T *
                      Real.exp
                        (-saddleSourceSecondBranchGammaLinearRate
                          ℓ * |T|)) := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_saddleSourceContourDamping_secondBranch_local_coercivity,
      eventually_upperSaddleDamping_gamma_add_shell]
    with ε hε hlocal hdom
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T
  let t₀ : ℝ := saddleSourceSecondBranchLocalFrequency ε
  let a : ℝ := ℓ / (8 * Real.exp 1)
  let η : ℝ := 2 + δ
  have hδ0 : 0 ≤ δ := by nlinarith
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hB : 0 ≤ shellLocation ε := by
    unfold shellLocation
    positivity
  have ht₀ : 0 < t₀ := by
    try dsimp [t₀, saddleSourceSecondBranchLocalFrequency]
    positivity
  have ht₀one : t₀ ≤ 1 := by
    try dsimp [t₀, saddleSourceSecondBranchLocalFrequency]
    apply (div_le_iff₀
      (show (0 : ℝ) < 2 * (shellLocation ε + 1) by
        positivity)).2
    nlinarith
  have hw : 0 ≤ saddleGaussianTailWeight T :=
    saddleGaussianTailWeight_nonneg T
  by_cases hinside : |T| ≤ t₀
  · have hquadratic := hlocal ℓ hℓ δ hδ T
      (by simpa [t₀,
        saddleSourceSecondBranchLocalFrequency] using! hinside)
    have hlocalexp :
        Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T) ≤
          Real.exp
            (-saddleSourceSecondBranchGaussianRate
              ε ℓ δ * T ^ 2) := by
      apply Real.exp_le_exp.mpr
      unfold saddleSourceSecondBranchGaussianRate
      linarith
    have hfirst := mul_le_mul_of_nonneg_left hlocalexp hw
    have houter : 0 ≤
        Real.exp
            (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
          (saddleGaussianTailWeight T *
            Real.exp
              (-saddleSourceSecondBranchGammaGaussianRate
                ℓ δ * T ^ 2) +
            saddleGaussianTailWeight T *
              Real.exp
                (-saddleSourceSecondBranchGammaLinearRate
                  ℓ * |T|)) := by
      positivity
    linarith
  · have houtside : t₀ ≤ |T| :=
      le_of_not_ge hinside
    have hsquare : t₀ ^ 2 ≤ T ^ 2 := by
      have h := pow_le_pow_left₀ ht₀.le houtside 2
      simpa [sq_abs] using! h
    have hone : t₀ ^ 2 ≤ (1 : ℝ) := by
      nlinarith [sq_nonneg (1 - t₀)]
    have hminimum : t₀ ^ 2 ≤ min (T ^ 2) 1 :=
      le_min hsquare hone
    have hshell := positiveShellDamping_lower_bound
      (ε := ε) (ℓ := ℓ) (δ := δ) (T := T)
        hε hℓ.le hδ0
    have hbarrier :
        saddleSourceSecondBranchOuterBarrier ε ℓ δ ≤
          (99 / 100 : ℝ) *
            positiveShellDamping ε ℓ δ T := by
      calc
        saddleSourceSecondBranchOuterBarrier ε ℓ δ =
            (99 / 100 : ℝ) *
              ((ℓ / 50) * shellWeight ε *
                Real.exp (δ * shellLocation ε) *
                  t₀ ^ 2) := by
              try dsimp [saddleSourceSecondBranchOuterBarrier, t₀]
              ring
        _ ≤ (99 / 100 : ℝ) *
              ((ℓ / 50) * shellWeight ε *
                Real.exp (δ * shellLocation ε) *
                  min (T ^ 2) 1) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_left hminimum
                (by positivity [shellWeight_pos ε])
        _ ≤ (99 / 100 : ℝ) *
            positiveShellDamping ε ℓ δ T := by
              exact mul_le_mul_of_nonneg_left hshell
                (by norm_num)
    have hgamma := upperGammaDamping_lower_bound
      hℓ hη T
    have hcombined :
        saddleSourceSecondBranchOuterBarrier ε ℓ δ +
            a * min (T ^ 2 / η) |T| ≤
          saddleSourceContourDamping ε ℓ (1 + δ) T := by
      rw [saddleSourceContourDamping_eq_secondBranch]
      have hfull := hdom ℓ hℓ δ hδ T
      try dsimp [a, η] at hgamma ⊢
      linarith
    have hmin := saddle_exp_neg_mul_min_le_add
      (a := a) (x := T ^ 2 / η) (y := |T|) ha.le
    have hexp :
        Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T) ≤
          Real.exp
              (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            (Real.exp
              (-saddleSourceSecondBranchGammaGaussianRate
                ℓ δ * T ^ 2) +
              Real.exp
                (-saddleSourceSecondBranchGammaLinearRate
                  ℓ * |T|)) := by
      calc
        Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T) ≤
          Real.exp
            (-(saddleSourceSecondBranchOuterBarrier ε ℓ δ +
              a * min (T ^ 2 / η) |T|)) := by
            apply Real.exp_le_exp.mpr
            linarith
        _ = Real.exp
              (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            Real.exp
              (-a * min (T ^ 2 / η) |T|) := by
            rw [← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp
              (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            (Real.exp (-a * (T ^ 2 / η)) +
              Real.exp (-a * |T|)) := by
            gcongr
        _ = Real.exp
              (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            (Real.exp
              (-saddleSourceSecondBranchGammaGaussianRate
                ℓ δ * T ^ 2) +
              Real.exp
                (-saddleSourceSecondBranchGammaLinearRate
                  ℓ * |T|)) := by
            congr 2
            unfold saddleSourceSecondBranchGammaGaussianRate
            try dsimp [a, η]
            congr 1
            ring
    have hweighted := mul_le_mul_of_nonneg_left hexp hw
    have hfirst : 0 ≤
        saddleGaussianTailWeight T *
          Real.exp
            (-saddleSourceSecondBranchGaussianRate
              ε ℓ δ * T ^ 2) := by
      positivity
    nlinarith
end CohnElkies
