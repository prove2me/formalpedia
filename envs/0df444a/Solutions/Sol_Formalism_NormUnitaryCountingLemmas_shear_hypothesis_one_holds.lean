-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.shear_hypothesis_one_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:26.920145+00:00
-- url     : https://prove2.me/submissions/8c0de61a-1819-4327-a56c-0733682afd09

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisOneHolds
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_core

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
open Formalism.NormUnitaryCountingLemmas.H1OnPoints
namespace Formalism.NormUnitaryCountingLemmas
theorem _root_.solution : H1 := by
  intro R _ N n ν F hF A _ _ x u c
  let g : Polynomial A →ₐ[R] A := (Polynomial.aeval (0 : A)).restrictScalars R
  have hreg : IsLeftRegular (Polynomial.C (c 0) + Polynomial.X : Polynomial A) := by
    rw [add_comm]
    exact (Polynomial.monic_X_add_C _).isRegular.left
  have hc := core (B := Polynomial A) hF (fun j k => Polynomial.C (x j k))
    (fun k => Polynomial.C (u k)) (fun j => Polynomial.C (c j) + if j = 0 then Polynomial.X else 0)
    (by simpa using hreg)
  refine le_trans (le_of_eq ?_) ((Polynomial.natDegree_map_le (f := (g : Polynomial A →+* A))).trans hc)
  congr 1
  rw [← Polynomial.coe_mapAlgHom, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  congr 1
  funext p
  by_cases h : p.1 = 0 <;> simp [g, h]
end Formalism.NormUnitaryCountingLemmas
