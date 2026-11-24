-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:36:09.521978+00:00
-- url     : https://prove2.me/submissions/2541e035-8fdb-4aac-bfd2-4759b047a489

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {W : Type} [AddCommGroup W] [Module ℂ W]
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
theorem _root_.solution (hPV : PolyVanish) (K : Module.End ℂ W) (A : ℕ → Module.End ℂ W) (d : ℕ) (P : ℂ[X])
    (hP : P.natDegree < d + 1) (x : W)
    (h : ∀ u : ℂ, (∑ s ∈ range d, u ^ s • A s) (u • x - K x) = P.eval u • x) :
    ∀ s ∈ range (d + 1),
      (if s = 0 then 0 else A (s - 1) x) - (if s < d then A s (K x) else 0) = P.coeff s • x := by
  intro s hs
  have key := hPV W (d + 1)
    (fun s => (if s = 0 then 0 else A (s - 1) x) - (if s < d then A s (K x) else 0) - P.coeff s • x) ∅ ?_ s hs
  · exact sub_eq_zero.1 key
  intro u _
  have hu := h u
  simp only [smul_sub, Finset.sum_sub_distrib]
  have e1 : ∑ s ∈ range (d + 1), u ^ s • (if s = 0 then (0 : W) else A (s - 1) x) =
      ∑ s ∈ range d, u ^ s • A s (u • x) := by
    rw [Finset.sum_range_succ']
    simp only [if_true, smul_zero, add_zero, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, map_smul, smul_smul, pow_succ]
  have e2 : ∑ s ∈ range (d + 1), u ^ s • (if s < d then A s (K x) else (0 : W)) =
      ∑ s ∈ range d, u ^ s • A s (K x) := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl d), smul_zero, add_zero]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [if_pos (Finset.mem_range.1 hs)]
  have e3 : ∑ s ∈ range (d + 1), u ^ s • P.coeff s • x = P.eval u • x := by
    rw [Polynomial.eval_eq_sum_range' hP, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [smul_smul, mul_comm]
  rw [e1, e2, e3, ← hu, ← Finset.sum_sub_distrib]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sub]
  rw [Finset.sum_sub_distrib, sub_self]
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
