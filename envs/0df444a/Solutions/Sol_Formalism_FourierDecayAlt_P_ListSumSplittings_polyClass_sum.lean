-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:11.656807+00:00
-- url     : https://prove2.me/submissions/16fc69e1-7c70-407a-b842-3b7a09f71ca8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_add

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (D : ℕ) (P : ι → Mat k r → ℂ)
    (h : ∀ i ∈ s, PolyClass D (P i)) : PolyClass D (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyClass_mono (Nat.zero_le D) (polyClass_const (k := k) (r := r) 0)
  | insert a s ha ih =>
    have := polyClass_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : (fun g => ∑ i ∈ insert a s, P i g) = fun g => P a g + ∑ i ∈ s, P i g := by
      funext g; rw [Finset.sum_insert ha]
    rw [e]
    exact this
end Formalism.FourierDecayAlt.P.ListSumSplittings
