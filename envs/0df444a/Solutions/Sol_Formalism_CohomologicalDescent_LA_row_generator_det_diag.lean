-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.row_generator_det_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:00:18.133821+00:00
-- url     : https://prove2.me/submissions/3da3a927-ac76-42a1-ab82-4f7310f6ca21

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
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ} (a : Fin r) :
    rowGen R a a (genericDet R r) = Polynomial.C (genericDet R r) * (1 + Polynomial.X) := by
  have hM : (rowGen R a a).mapMatrix (genericMatrix' R r) =
      (RingHom.mapMatrix Polynomial.C (genericMatrix' R r)).updateRow a
        ((1 + Polynomial.X : Polynomial (MvPolynomial (Fin r × Fin r) R)) •
          RingHom.mapMatrix Polynomial.C (genericMatrix' R r) a) := by
    refine Matrix.ext fun p q => ?_
    by_cases hp : p = a
    · subst hp
      simp [rowGen, genericMatrix', Matrix.updateRow_apply] <;> ring
    · simp [rowGen, genericMatrix', Matrix.updateRow_apply, hp]
  unfold genericDet
  rw [AlgHom.map_det (rowGen R a a), hM, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    ← RingHom.map_det]
  ring
end Formalism.CohomologicalDescent.LA
