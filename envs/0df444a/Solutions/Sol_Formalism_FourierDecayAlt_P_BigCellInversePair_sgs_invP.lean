-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellInversePair.sgs_invP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:15:44.082726+00:00
-- url     : https://prove2.me/submissions/be4adce3-cc10-4a8e-bb80-01408c6530ee

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellInversePair
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BigCellInversePair
theorem _root_.solution (p : SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : Mat k r).det) (hp2 : IsUnit (Matrix.of p.1.2 : Mat k r).det)
    (hp3 : IsUnit (Matrix.of p.2.1 : Mat k r).det) (hp4 : IsUnit (Matrix.of p.2.2 : Mat k r).det) (x : Mat k r) :
    sgs (invP p) (sgs p x) = x := by
  show (Matrix.of p.1.1 : Mat k r)⁻¹⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ *
      Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * x *
      Matrix.of p.2.2 * Matrix.of p.2.1) * ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 : Mat k r)⁻¹ *
      Matrix.of p.2.1) * (Matrix.of p.2.1 : Mat k r)⁻¹ = x
  generalize (Matrix.of p.1.1 : Mat k r) = A at hp1 ⊢
  generalize (Matrix.of p.1.2 : Mat k r) = B at hp2 ⊢
  generalize (Matrix.of p.2.1 : Mat k r) = C at hp3 ⊢
  generalize (Matrix.of p.2.2 : Mat k r) = D at hp4 ⊢
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv A hp1,
    Matrix.nonsing_inv_nonsing_inv B hp2]
  simp only [mul_assoc, Matrix.mul_nonsing_inv_cancel_left, Matrix.nonsing_inv_mul_cancel_left,
    Matrix.mul_nonsing_inv, hp1, hp2, hp3, hp4, mul_one]
end Formalism.FourierDecayAlt.P.BigCellInversePair
