-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.exp_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:30:45.538369+00:00
-- url     : https://prove2.me/submissions/79cfd89a-bd0d-41b1-bec9-7984e548c60d

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_uh_inv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_uh_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (X : Mx k r) (t : ℝ) :
    g * NormedSpace.exp ((t : ℂ) • (g⁻¹ * X * g)) = NormedSpace.exp ((t : ℂ) • X) * g := by
  have h1 := uh_inv_mul hg
  have h2 := uh_mul_inv hg
  have hu : IsUnit g := ⟨⟨g, g⁻¹, h2, h1⟩, rfl⟩
  rw [show (t : ℂ) • (g⁻¹ * X * g) = g⁻¹ * ((t : ℂ) • X) * g by rw [Matrix.mul_smul, Matrix.smul_mul]]
  rw [Matrix.exp_conj' g _ hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
