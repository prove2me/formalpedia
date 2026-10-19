-- Prove2me | solution 1 for CohnElkies.eventually_saddleGaussianOuterPhi_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/d29314c3-e61c-41de-8359-86bd84924e57

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleGaussianOuterPhi_le_endpointBarrier

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {B Q c δ₀ : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hc : 0 < c)
    (hδ₀ : 0 ≤ δ₀) :
    ∀ κ : ℝ, 0 < κ →
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, δ₀ ≤ δ →
          Real.sqrt ℓ *
              Real.exp (saddleGaussianOuterPhi B Q c ℓ δ) < κ := by
  let s : ℝ := c * Q * Real.exp (B * δ₀)
  let A : ℝ := (B + 1) / 2 + 4
  have hs : 0 < s := by
    try dsimp [s]
    positivity
  have htendsto : Tendsto
      (fun ℓ : ℝ =>
        Real.sqrt ℓ *
          Real.exp (A * δ₀ + 4 - s * ℓ))
      atTop (𝓝 (0 : ℝ)) := by
    have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 / 2 : ℝ) s hs
    have hscaled : Tendsto
        (fun ℓ : ℝ =>
          Real.exp (A * δ₀ + 4) *
            (ℓ ^ (1 / 2 : ℝ) * Real.exp (-s * ℓ)))
        atTop (𝓝 (0 : ℝ)) := by
      convert!
        (tendsto_const_nhds
          (x := Real.exp (A * δ₀ + 4))).mul hbase using 1; simp
    apply hscaled.congr'
    filter_upwards [] with ℓ
    symm
    rw [Real.sqrt_eq_rpow]
    have hexp :
        Real.exp (A * δ₀ + 4 - s * ℓ) =
          Real.exp (A * δ₀ + 4) *
            Real.exp (-s * ℓ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  intro κ hκ
  have hsmall := htendsto.eventually
    (Iio_mem_nhds hκ)
  have hthreshold :
      ∀ᶠ ℓ : ℝ in atTop,
        A ≤ c * ℓ * Q * B * Real.exp (B * δ₀) := by
    have hfactor :
        0 < c * Q * B * Real.exp (B * δ₀) := by
      positivity
    filter_upwards
      [eventually_ge_atTop
        (A / (c * Q * B * Real.exp (B * δ₀)))]
      with ℓ hℓ
    apply (div_le_iff₀ hfactor).mp at hℓ
    nlinarith
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    hthreshold, hsmall] with ℓ hℓ hscale hbound
  intro δ hδ
  have hphi := saddleGaussianOuterPhi_le_endpointBarrier
    hB hQ hc hℓ hδ₀ hδ hscale
  have hcompare :
      Real.sqrt ℓ *
          Real.exp (saddleGaussianOuterPhi B Q c ℓ δ) ≤
        Real.sqrt ℓ *
          Real.exp (A * δ₀ + 4 - s * ℓ) := by
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg ℓ)
    apply Real.exp_le_exp.mpr
    try dsimp [A, s]
    nlinarith
  exact hcompare.trans_lt hbound
end CohnElkies
