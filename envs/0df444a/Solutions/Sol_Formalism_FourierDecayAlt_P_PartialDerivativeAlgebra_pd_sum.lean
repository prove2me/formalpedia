-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:10:41.238401+00:00
-- url     : https://prove2.me/submissions/d0d5a99a-8e6f-4c78-87d7-0a033f1ef02f

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {N : ℕ}
namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
theorem _root_.solution {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 0 a
  | insert x s hx ih =>
    have h1 := pd_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert hx] using h1
end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
