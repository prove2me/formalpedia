-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.row_generator_det_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:01:28.488894+00:00
-- url     : https://prove2.me/submissions/b175fbb9-1d57-4706-8cee-e4dd3ed6a036

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ} (a b : Fin r) (hab : a ≠ b) :
    rowGen R a b (genericDet R r) = Polynomial.C (genericDet R r) := by
  have hM : (rowGen R a b).mapMatrix (genericMatrix' R r) =
      (RingHom.mapMatrix Polynomial.C (genericMatrix' R r)).updateRow b
        (RingHom.mapMatrix Polynomial.C (genericMatrix' R r) b +
          (Polynomial.X : Polynomial (MvPolynomial (Fin r × Fin r) R)) •
            RingHom.mapMatrix Polynomial.C (genericMatrix' R r) a) := by
    ext p q
    by_cases hp : p = b
    · subst hp
      simp [rowGen, genericMatrix', Matrix.updateRow_apply]
    · simp [rowGen, genericMatrix', Matrix.updateRow_apply, hp]
  unfold genericDet
  rw [AlgHom.map_det (rowGen R a b), hM, Matrix.det_updateRow_add_smul_self _ (Ne.symm hab),
    ← RingHom.map_det]
end Formalism.CohomologicalDescent.LA
