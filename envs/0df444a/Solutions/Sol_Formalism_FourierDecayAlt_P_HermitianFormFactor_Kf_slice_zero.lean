-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Kf_slice_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:36:40.418336+00:00
-- url     : https://prove2.me/submissions/e889c004-86b0-40a8-ad8d-93b906627e44

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {T : Q → Q → ℂ} (hT : ¬ ((Matrix.of T).PosDef ∧ (Matrix.trace (Matrix.of T)).re ≤ 1)) (σ : ℝ)
    (B : Q → P → ℂ) : Kf P Q σ (T, B) = 0 := by
  unfold Kf
  rw [Set.indicator_apply_eq_zero]
  intro h
  exact absurd ⟨h.1, h.2.1⟩ hT
end Formalism.FourierDecayAlt.P.HermitianFormFactor
