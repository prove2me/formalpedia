-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.ch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:12:40.091882+00:00
-- url     : https://prove2.me/submissions/c9360c74-4d41-4b2e-9e18-906f282734a5

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_coeffs
import Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_pow_mem

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
theorem _root_.solution (hPV : PolyVanish) (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G)
    (A : ℕ → Module.End ℂ W) (d : ℕ) (P : ℂ[X]) (hP : P.natDegree < d + 1)
    (h : ∀ x ∈ G, ∀ u : ℂ, (∑ s ∈ range d, u ^ s • A s) (u • x - K x) = P.eval u • x) :
    ∀ x ∈ G, aeval K P x = 0 := by
  intro x hx
  rw [Polynomial.aeval_eq_sum_range' hP, LinearMap.sum_apply]
  have h1 : ∀ s ∈ range (d + 1), (P.coeff s • K ^ s) x =
      (if s = 0 then 0 else A (s - 1) ((K ^ s) x)) - (if s < d then A s (K ((K ^ s) x)) else 0) := by
    intro s hs
    rw [LinearMap.smul_apply]
    exact (coeffs hPV K A d P hP _ (h _ (pow_mem G K hK s x hx)) s hs).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.sum_range_succ (fun s => if s < d then _ else _),
    if_neg (lt_irrefl d), if_pos rfl, add_zero, add_zero, sub_eq_zero]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [if_pos (Finset.mem_range.1 hs), if_neg (Nat.succ_ne_zero s), Nat.add_sub_cancel, pow_succ', Module.End.mul_apply]
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
