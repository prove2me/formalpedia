-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.mem_H_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:13.197146+00:00
-- url     : https://prove2.me/submissions/babc5112-39fd-49b2-8bf9-ae52401ad5c5

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
theorem _root_.solution {N n : ℕ} (ν : Fin N → ℕ) (P : MvPolynomial (Fin N × Fin n) R) :
    P ∈ H R ν ↔ P.IsWeightedHomogeneous (blockWt N n) ν ∧
      ∀ i j : Fin N, i < j → shear R i j P = Polynomial.C P := by
  simp only [H, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule,
    IsScalarTower.toAlgHom_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
end Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
