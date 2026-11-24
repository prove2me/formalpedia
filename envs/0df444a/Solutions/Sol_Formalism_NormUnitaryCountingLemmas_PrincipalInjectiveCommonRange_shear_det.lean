-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.shear_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:14.973337+00:00
-- url     : https://prove2.me/submissions/da4cbd13-2e2e-44c6-85d8-5cb63173e7dd

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
theorem _root_.solution {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    shear R i j (detPoly R n) = Polynomial.C (detPoly R n) := by
  classical
  set A : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin n × Fin n) R)) :=
    (Polynomial.C (R := MvPolynomial (Fin n × Fin n) R)).mapMatrix
      (Matrix.of fun a b : Fin n => (X (a, b) : MvPolynomial (Fin n × Fin n) R)) with hA
  rw [detPoly, AlgHom.map_det]
  have : (shear R i j).mapMatrix
      (Matrix.of fun a b : Fin n => (X (a, b) : MvPolynomial (Fin n × Fin n) R)) =
      A.updateRow j (A j + (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • A i) := by
    ext a b
    by_cases h : a = j
    · subst h; simp [shear, hA, Matrix.updateRow_apply]
    · simp [shear, hA, Matrix.updateRow_apply, h]
  rw [this, Matrix.det_updateRow_add_smul_self _ hij.symm, hA, ← RingHom.map_det]
end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
