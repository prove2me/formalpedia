-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.sv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:08:00.71732+00:00
-- url     : https://prove2.me/submissions/ae096534-fb96-4f0e-ad0d-c3d3276fbeff

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_smul

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
namespace Formalism.FourierDecayAlt.P.Qb1
theorem _root_.solution (σ : Mx k r → (Vs →L[ℂ] Vs)) : SV σ (0 : Vs) := by
  have := sv_smul (σ := σ) (w := (0 : Vs)) 0 (by
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun g _ _ => by simp⟩)
  simpa using this
end Formalism.FourierDecayAlt.P.Qb1
