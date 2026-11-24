-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.gN_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:57:22.946021+00:00
-- url     : https://prove2.me/submissions/feb20136-f544-404b-a68a-57adc87ede58

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
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {k r : ℕ} (A : Mat k r) : gN A ^ 2 = (Matrix.trace (A * Aᴴ)).re := by
  rw [gN, Real.sq_sqrt]
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
end Formalism.FourierDecayAlt.P.HermitianFormFactor
