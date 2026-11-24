-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.basis_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:59:28.278544+00:00
-- url     : https://prove2.me/submissions/5d6b1d4d-4970-4c82-ba6c-477559579b74

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution {N : ℕ} (m : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    ∃ w : ℂ, ((Polynomial.X : ℂ[X]) + C (m i)) * Lagrange.basis Finset.univ (fun j => -m j) i =
      C w * ∏ j, ((Polynomial.X : ℂ[X]) + C (m j)) := by
  refine ⟨∏ j ∈ Finset.univ.erase i, (-m i - -m j)⁻¹, ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (Polynomial.X : ℂ[X]) + C (m j)) (Finset.mem_univ i)]
  have hb : Lagrange.basis Finset.univ (fun j => -m j) i =
      C (∏ j ∈ Finset.univ.erase i, (-m i - -m j)⁻¹) *
        ∏ j ∈ Finset.univ.erase i, ((Polynomial.X : ℂ[X]) + C (m j)) := by
    rw [Lagrange.basis, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [Lagrange.basisDivisor, map_neg, sub_neg_eq_add]
  rw [hb]
  beta_reduce
  ring
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
