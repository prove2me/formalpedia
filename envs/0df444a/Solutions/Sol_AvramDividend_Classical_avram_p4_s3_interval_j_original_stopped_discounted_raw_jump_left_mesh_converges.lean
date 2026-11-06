-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_j_original_stopped_discounted_raw_jump_left_mesh_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:58:00.924562+00:00
-- url     : https://prove2.me/submissions/7e95e556-3d0a-4684-bec8-3188560f3522

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original X/D raw stopped-discounted jump difference converges along
physical left time meshes without derivative regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (ω : Ω) (t : ℝ≥0)
    (s : ℕ → ℝ≥0) (hsle : ∀ n, s n ≤ t)
    (hst : Tendsto s atTop (𝓝 t))
    (w : ℝ → ℝ) (q z : ℝ)
    (hwy : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t))
    (hwyz : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t + z)) :
    let K : ℝ≥0 → ℝ := fun u =>
      Real.exp (-(q * (u : ℝ))) *
        ((fun y : ℝ => w (y + z) - w y)
          (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))
    Tendsto
      (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
      atTop
      (𝓝 ((if t ≤ τ ω then (1 : ℝ) else 0) * K t)) := by
  let Y : ℝ≥0 → ℝ := fun u =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v ω - rightLimit D v ω) u
  have hY : Tendsto (fun n => Y (s n)) atTop (𝓝 (Y t)) := by
    simpa only [Y] using
      (avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
        X x D hD ω t s hsle hst)
  have hYz : Tendsto (fun n => Y (s n) + z) atTop
      (𝓝 (Y t + z)) := hY.add tendsto_const_nhds
  have hJ : Tendsto (fun n => w (Y (s n) + z) - w (Y (s n)))
      atTop (𝓝 (w (Y t + z) - w (Y t))) :=
    (hwyz.tendsto.comp hYz).sub (hwy.tendsto.comp hY)
  have hExpC : Continuous (fun u : ℝ≥0 =>
      Real.exp (-(q * (u : ℝ)))) := by fun_prop
  have hExp : Tendsto (fun n => Real.exp (-(q * (s n : ℝ))))
      atTop (𝓝 (Real.exp (-(q * (t : ℝ))))) :=
    hExpC.continuousAt.tendsto.comp hst
  let K : ℝ≥0 → ℝ := fun u =>
    Real.exp (-(q * (u : ℝ))) * (w (Y u + z) - w (Y u))
  have hK : Tendsto (fun n => K (s n)) atTop (𝓝 (K t)) := by
    simpa only [K] using hExp.mul hJ
  have hStop : Tendsto (fun n =>
      if s n ≤ τ ω then (1 : ℝ) else 0) atTop
      (𝓝 (if t ≤ τ ω then (1 : ℝ) else 0)) := by
    by_cases ht : t ≤ τ ω
    · have hAll (n : ℕ) : s n ≤ τ ω := (hsle n).trans ht
      have heq : (fun n : ℕ =>
          if s n ≤ τ ω then (1 : ℝ) else 0) =
          (fun _ => (1 : ℝ)) := by
        funext n
        exact if_pos (hAll n)
      rw [if_pos ht, heq]
      exact tendsto_const_nhds
    · have hlt : τ ω < t := lt_of_not_ge ht
      have hev : ∀ᶠ n in atTop, τ ω < s n :=
        hst.eventually (isOpen_Ioi.mem_nhds hlt)
      have hzero : ∀ᶠ n in atTop,
          (if s n ≤ τ ω then (1 : ℝ) else 0) = 0 :=
        hev.mono (fun n hn => if_neg (not_le.mpr hn))
      have hzeroSymm : ∀ᶠ n in atTop,
          (0 : ℝ) = (if s n ≤ τ ω then (1 : ℝ) else 0) :=
        hzero.mono (fun n hn => hn.symm)
      have hlim : Tendsto (fun n : ℕ =>
          if s n ≤ τ ω then (1 : ℝ) else 0) atTop (𝓝 (0 : ℝ)) :=
        tendsto_const_nhds.congr' hzeroSymm
      simpa only [if_neg ht] using hlim
  simpa only [K, Y] using hStop.mul hK
