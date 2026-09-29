-- Prove2me | solution 1 for BookProof.FockSecondQuantization.secondQuantization_hashimoto_selects
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:41:53.38602+00:00
-- url     : https://prove2.me/submissions/07abd49a-10bd-4742-9fe2-c14d86fcca15

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.secondQuantization_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_isHermCol_opCol
import Theorems.Thm_BookProof_FockSecondQuantization_isPosCol_opCol
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_hashimoto_selects
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (ε : ℕ ≃ Conf) (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ Fock) (A' : Dom →ₗ[ℂ] Fock) (R : Fock →L[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOpB ε (opCol b A)) A' ∧ IsShiftInvert A' γ R ∧
        ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : Fock, Tendsto (fun k : ℕ => galerkinCompression R (fockBasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : Fock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (fockBasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ Fock) (A'' : Dom' →ₗ[ℂ] Fock), IsShiftInvert A'' γ R →
          Dom' = Dom ∧ ∀ (x : Fock) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
            A'' ⟨x, hx'⟩ = A' ⟨x, hx⟩) := dGamma_hashimoto_selects ε (isHermCol_opCol hA) (isPosCol_opCol hpos) hγ
