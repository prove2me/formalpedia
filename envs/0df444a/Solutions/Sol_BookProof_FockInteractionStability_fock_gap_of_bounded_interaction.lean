-- Prove2me | solution 1 for BookProof.FockInteractionStability.fock_gap_of_bounded_interaction
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:55:46.388998+00:00
-- url     : https://prove2.me/submissions/db411294-692f-439c-9e1f-61b5c4d0ce9d

-- Generated from ChapterFockInteractionStability.lean — solution of BookProof.FockInteractionStability.fock_gap_of_bounded_interaction
import Mathlib
import Definitions.Def_ChapterFockInteractionStability
import Theorems.Thm_BookProof_FockInteractionStability_interaction_form_bound
import Theorems.Thm_BookProof_FockNumberPreservingGap_fock_gap_of_number_preserving
open BookProof.FockInteractionStability



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap
open BookProof.FarisLavine BookProof.NavierStokesFlow



variable {E : Type*} [NormedAddCommGroup E]

variable {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution {col : ℕ → (ℕ →₀ ℂ)} {mu delta : ℝ} (hmu : 0 ≤ mu)
    (hgap : IsPosCol (shiftCol col mu)) (V : Fock →L[ℂ] Fock) (hV : ‖V‖ ≤ delta)
    {u : FockAlg} (h0 : u 0 = 0) :
    (mu - delta) * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
        + (inner ℂ (toLp u) (V (toLp u)) : ℂ).re := by

  have hq : mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re :=
    fock_gap_of_number_preserving hmu hgap h0
  have hv : |(inner ℂ (toLp u) (V (toLp u)) : ℂ).re| ≤ delta * ‖toLp u‖ ^ 2 := by
    refine (interaction_form_bound V (toLp u)).trans ?_
    exact mul_le_mul_of_nonneg_right hV (sq_nonneg _)
  have h2 := (abs_le.mp hv).1
  nlinarith
