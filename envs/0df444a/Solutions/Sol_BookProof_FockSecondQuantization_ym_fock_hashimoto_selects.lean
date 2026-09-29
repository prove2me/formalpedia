-- Prove2me | solution 1 for BookProof.FockSecondQuantization.ym_fock_hashimoto_selects
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:48:36.558542+00:00
-- url     : https://prove2.me/submissions/ee34416c-24d3-4569-8ffe-ea0e2751b01d

-- Generated from ChapterFockSecondQuantization.lean — solution of BookProof.FockSecondQuantization.ym_fock_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_secondQuantization_hashimoto_selects
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_quadForm_nonneg
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
open BookProof.FockSecondQuantization








open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open Filter Topology
















open BookProof.YangMillsHermite BookProof.HermiteProductCore
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ε : ℕ ≃ Conf) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock) (R : Fock →L[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOpB ε (ymFockCol e fabc)) A ∧
        IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : Fock, Tendsto (fun k : ℕ => galerkinCompression R (fockBasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : Fock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (fockBasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ Fock) (A' : Dom' →ₗ[ℂ] Fock), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : Fock) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) :=
  secondQuantization_hashimoto_selects ε (coreBasis e) (ymOnePart e fabc)
      (ymHamiltonian_symmetricOn (coreRepBasis e) fabc)
      (ymHamiltonian_quadForm_nonneg (coreRepBasis e) fabc) hγ
