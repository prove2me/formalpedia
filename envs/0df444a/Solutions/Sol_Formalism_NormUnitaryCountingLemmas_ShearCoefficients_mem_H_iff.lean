-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.mem_H_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:59.72814+00:00
-- url     : https://prove2.me/submissions/801ce465-99b0-4061-af35-7c559a80b0fe

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients

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
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.ShearCoefficients
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.ShearCoefficients
theorem _root_.solution {N n : ℕ} (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) R) :
    F ∈ H R ν ↔ F.IsWeightedHomogeneous (blockWt N n) ν ∧
      ∀ i j : Fin N, i < j → shear R i j F = Polynomial.C F := by
  simp only [H, Submodule.mem_inf, mem_weightedHomogeneousSubmodule, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    IsScalarTower.toAlgHom_apply, sub_eq_zero]
  rfl
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
