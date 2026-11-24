-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:14.282878+00:00
-- url     : https://prove2.me/submissions/f659093c-d4a2-4950-8dad-d43b2a26e4e8

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe

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
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.H1OnPoints
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints
theorem _root_.solution {N n : ℕ} {ν : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν)
    (i j : Fin N) (hij : i < j) : shear R i j F = Polynomial.C F := by
  have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hF).2 i) j) hij
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
  exact h
end Formalism.NormUnitaryCountingLemmas.H1OnPoints
