-- Prove2me | solution 1 for FiniteFields.Dwork.coefficientFieldFrobenius_coefficientRing
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:37:39.162601+00:00
-- url     : https://prove2.me/submissions/ed0d7da1-15e6-4a49-ae7e-98d424093486

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Foundations
open scoped WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem solution (x : CoefficientRing k p) :
    coefficientFieldFrobenius k p (coefficientRingAlgebraMap k p x) =
      coefficientRingAlgebraMap k p (frobeniusLiftEquiv k p x) := by
  change coefficientFieldFrobenius k p
      (((WithVal.equiv (coefficientValuation k p)).symm
          (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) x) :
        WithVal (coefficientValuation k p)) : CoefficientField k p) = _
  rw [coefficientFieldFrobenius_coe]
  change UniformSpace.Completion.coeRingHom
      ((WithVal.equiv (coefficientValuation k p)).symm
        (WittVector.FractionRing.frobenius p k
          (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) x))) = _
  have hf : WittVector.FractionRing.frobenius p k
        (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) x) =
      algebraMap (CoefficientRing k p) (CoefficientFractionField k p)
        (frobeniusLiftEquiv k p x) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (K := CoefficientFractionField k p) (L := CoefficientFractionField k p)
      (frobeniusLiftEquiv k p) x
  rw [hf]
  rfl
