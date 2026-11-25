-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.beInt_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:16.145669+00:00
-- url     : https://prove2.me/submissions/318c8783-a894-4a75-8d27-d4663b0bb8ef

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMemMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L1QuotientIntegralBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_piW_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_uw_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_S3dx4_sigma_mul__554a11700393


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r) :
    ‖beInt z c π σ (σ g x) v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ := by
  have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hσ : σ (Matrix.of p.1 * Matrix.of p.2 * g) x = σ (Matrix.of p.1 * Matrix.of p.2) (σ g x) := by
    rw [sigma_mul' hds hhn hg]; rfl
  have hi := (MatrixMultiplicationContinuity.uw_inv hp.1).1
  have hπn : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun w => by rw [MatrixMultiplicationContinuity.piW_unitary hT hπ _ hi w, one_mul])
  have hψ : ‖star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))‖ = 1 := by
    rw [norm_star]; unfold Formalism.QuantumDeterminants.psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  unfold beInt
  rw [norm_smul, norm_mul, hψ, mul_one, hσ]
  exact mul_le_of_le_one_right (norm_nonneg _) hπn
end Formalism.FourierDecayAlt.P.S3dx4
