-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.normSq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:42.481935+00:00
-- url     : https://prove2.me/submissions/1aaa068b-267e-4ad4-8084-0f93c15e2385

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_blockDeg_of_mem
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_bweight_pos
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_key_c
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_coeff_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.NMul
namespace Formalism.NormUnitaryCountingLemmas.NMul
theorem _root_.solution {N n : ℕ} (ν : Fin N → ℕ) (F G : MvPolynomial (Fin N × Fin n) ℂ)
    (hF : F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν) :
    bnormSq (F * G) ≤ bnormSq F * bnormSq G := by
  classical
  have hF' : ∀ a ∈ F.support, ∀ j, blockDeg a j = ν j := fun a ha j => blockDeg_of_mem hF ha j
  have hnn : ∀ p : (Fin N × Fin n →₀ ℕ) × (Fin N × Fin n →₀ ℕ),
      0 ≤ (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := fun p =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (bweight_pos _).le)
      (mul_nonneg (sq_nonneg _) (bweight_pos _).le)
  calc bnormSq (F * G) = ∑ c ∈ (F * G).support, ‖coeff c (F * G)‖ ^ 2 * bweight c := rfl
    _ ≤ ∑ c ∈ (F * G).support, ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
          (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := by
        refine sum_le_sum fun c _ => ?_
        rw [coeff_mul_eq]
        exact key_c hF' c
    _ = ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 ∈ (F * G).support),
          (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) :=
        sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ F.support ×ˢ G.support,
          (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hnn p)
    _ = bnormSq F * bnormSq G := by
        rw [bnormSq, bnormSq, Finset.sum_mul_sum, Finset.sum_product]
end Formalism.NormUnitaryCountingLemmas.NMul
