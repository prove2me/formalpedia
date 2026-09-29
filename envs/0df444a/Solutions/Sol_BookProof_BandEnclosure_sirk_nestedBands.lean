-- Prove2me | solution 1 for BookProof.BandEnclosure.sirk_nestedBands
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:33:38.382973+00:00
-- url     : https://prove2.me/submissions/c824ee52-39e5-41cf-821c-6eaf3768fc79

import Definitions.Def_ChapterBandEnclosure
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SirkBandAux
open BookProof.ChapterH6 BookProof.BandEnclosure Filter Topology

private theorem sirk_error_decay_exponential (C Dmin h nv : ℝ) (hh : 0 < h) :
    Tendsto (fun m : ℕ => sirkBound C Dmin h nv m) atTop (𝓝 0) := by
  have hlin : Tendsto (fun m : ℕ => -(h * (m : ℝ))) atTop atBot := by
    have : Tendsto (fun m : ℕ => h * (m : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop hh tendsto_natCast_atTop_atTop
    exact tendsto_neg_atTop_atBot.comp this
  have hexp : Tendsto (fun m : ℕ => Real.exp (-(h * (m : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have := ((hexp.const_mul (2 * C)).mul_const Dmin).mul_const nv
  simpa [sirkBound, mul_zero, zero_mul] using this

private theorem sirk_error_bound_antitone (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) :
    Antitone (fun m : ℕ => sirkBound C Dmin h nv m) := by
  intro a b hab
  have hexp : Real.exp (-(h * (b : ℝ))) ≤ Real.exp (-(h * (a : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    nlinarith
  have h2C : 0 ≤ 2 * C := by linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h2C) hD) hnv

end SirkBandAux

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.sirk_nestedBands
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8
open SirkBandAux

theorem solution (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) :
    NestedBands (fun _ => (0 : ℝ)) (fun m => sirkBound C Dmin h nv m) := by
  intro m
  exact Set.Icc_subset_Icc le_rfl (sirk_error_bound_antitone C Dmin h nv hC hD hnv hh (Nat.le_succ m))

#print axioms solution
