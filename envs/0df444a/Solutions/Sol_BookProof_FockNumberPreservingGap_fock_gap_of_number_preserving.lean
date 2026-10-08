-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:26:53.254196+00:00
-- url     : https://prove2.me/submissions/c7693f70-6ce1-4672-b731-caad0ee9140b

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockNumberPreservingGap_dGamma_shiftCol
import Theorems.Thm_BookProof_FockNumberPreservingGap_number_quadForm_ge
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_nonneg
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu)
    (hgap : IsPosCol (shiftCol col mu)) {u : FockAlg} (h0 : u 0 = 0) :
    mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by

  have hsplit : (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ)
      = inner ℂ (toLp u) (toLp (dGamma (shiftCol col mu) u))
        + ((mu : ℝ) : ℂ) * inner ℂ (toLp u) (toLp (dGamma numberCol u)) := by
    have hcol : dGamma col u
        = dGamma (shiftCol col mu) u + ((mu : ℝ) : ℂ) • dGamma numberCol u := by
      rw [dGamma_shiftCol, sub_add_cancel]
    have hadd : ∀ a b : FockAlg, toLp (a + b) = toLp a + toLp b := fun a b =>
      map_add toLpL a b
    have hsmul : ∀ (c : ℂ) (a : FockAlg), toLp (c • a) = c • toLp a := fun c a =>
      map_smul toLpL c a
    rw [hcol, hadd, hsmul, inner_add_right, inner_smul_right]
  rw [hsplit, Complex.add_re, Complex.re_ofReal_mul]
  have h1 : 0 ≤ (inner ℂ (toLp u) (toLp (dGamma (shiftCol col mu) u)) : ℂ).re :=
    inner_dGamma_nonneg hgap u
  have h2 := mul_le_mul_of_nonneg_left (number_quadForm_ge h0) hmu
  linarith
