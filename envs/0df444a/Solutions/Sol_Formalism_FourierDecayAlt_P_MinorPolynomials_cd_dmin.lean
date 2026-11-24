-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.cd_dmin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:36.927654+00:00
-- url     : https://prove2.me/submissions/b8686b6b-4c3f-4d5e-959b-b2caea10f943

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_cd_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ContDiff ℝ ∞ (fun g : Mat k r => Dmin k r z z' g l) := by
  obtain ⟨q, -, hq⟩ := dminPoly (k := k) z z' l
  have h : (fun g : Mat k r => Dmin k r z z' g l) = fun g => eval (vars g) q := funext hq
  rw [h]
  exact cd_eval q
end Formalism.FourierDecayAlt.P.MinorPolynomials
