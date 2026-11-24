-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:21:27.228212+00:00
-- url     : https://prove2.me/submissions/fa155c68-d0fa-42eb-bd6c-8af06c9555d6

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_nz_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {X : Mat k r} (hX : inLie k r X) : unitLie k r (nrm X) := by
  unfold unitLie
  refine ⟨lie_rsmul hX _, fun i j => ?_⟩
  have hp := nz_pos X
  have h1 : ‖X i j‖ ≤ ‖X‖ := Matrix.norm_entry_le_entrywise_sup_norm X
  have h2 : ‖X‖ ≤ nz X := le_max_right _ _
  have h3 : ‖(((nz X)⁻¹ : ℝ) : ℂ)‖ = (nz X)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  calc ‖nrm X i j‖ = ‖(((nz X)⁻¹ : ℝ) : ℂ)‖ * ‖X i j‖ := by
        simp only [nrm, Matrix.smul_apply]; exact norm_smul _ _
    _ ≤ (nz X)⁻¹ * nz X := by rw [h3]; gcongr; linarith
    _ = 1 := inv_mul_cancel₀ hp.ne'
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
