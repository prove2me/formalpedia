-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:12:00.678096+00:00
-- url     : https://prove2.me/submissions/2dc3130a-3bdb-4299-87af-3bfbafa9425a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution {ι : Type*} (s : Finset ι) (D : ι → ℕ) (P : ι → Mat k r → ℂ)
    (h : ∀ i ∈ s, PolyClass (D i) (P i)) : PolyClass (∑ i ∈ s, D i) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyClass_const (k := k) (r := r) 1
  | insert a s ha ih =>
    have := polyClass_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : (fun g => ∏ i ∈ insert a s, P i g) = fun g => P a g * ∏ i ∈ s, P i g := by
      funext g; rw [Finset.prod_insert ha]
    rw [Finset.sum_insert ha, e]
    exact this
end Formalism.FourierDecayAlt.P.ListSumSplittings
