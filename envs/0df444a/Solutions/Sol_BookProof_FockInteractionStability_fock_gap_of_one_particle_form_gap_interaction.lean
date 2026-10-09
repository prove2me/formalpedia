-- Prove2me | solution 1 for BookProof.FockInteractionStability.fock_gap_of_one_particle_form_gap_interaction
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:55:47.577287+00:00
-- url     : https://prove2.me/submissions/781a2cdd-8896-4cb4-9acb-3798fde37bb5

-- Generated from ChapterFockInteractionStability.lean — solution of BookProof.FockInteractionStability.fock_gap_of_one_particle_form_gap_interaction
import Mathlib
import Definitions.Def_ChapterFockInteractionStability
import Theorems.Thm_BookProof_FockInteractionStability_interaction_form_bound
import Theorems.Thm_BookProof_FockNumberPreservingGap_dGamma_vac
import Theorems.Thm_BookProof_FockNumberPreservingGap_fock_gap_of_one_particle_form_gap
open BookProof.FockInteractionStability



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap
open BookProof.FarisLavine BookProof.NavierStokesFlow



variable {E : Type*} [NormedAddCommGroup E]

variable {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] (b : HilbertBasis ℕ ℂ F)
    (A : BookProof.HermiteGalerkin.finiteModeDomain b →ₗ[ℂ]
      BookProof.HermiteGalerkin.finiteModeDomain b)
    {mu delta : ℝ} (hmu : 0 ≤ mu)
    (hgap : ∀ x : BookProof.HermiteGalerkin.finiteModeDomain b,
      mu * ‖(x : F)‖ ^ 2 ≤
        quadForm ((BookProof.HermiteGalerkin.finiteModeDomain b).subtype.comp A) x)
    (V : Fock →L[ℂ] Fock) (hV : ‖V‖ ≤ delta) :
    dGamma (opCol b A) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        (mu - delta) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re
            + (inner ℂ (toLp u) (V (toLp u)) : ℂ).re := by

  refine ⟨dGamma_vac _, fun u h0 => ?_⟩
  have hq : mu * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re :=
    (fock_gap_of_one_particle_form_gap b A hmu hgap).2 u h0
  have hv : |(inner ℂ (toLp u) (V (toLp u)) : ℂ).re| ≤ delta * ‖toLp u‖ ^ 2 := by
    refine (interaction_form_bound V (toLp u)).trans ?_
    exact mul_le_mul_of_nonneg_right hV (sq_nonneg _)
  have h2 := (abs_le.mp hv).1
  nlinarith
