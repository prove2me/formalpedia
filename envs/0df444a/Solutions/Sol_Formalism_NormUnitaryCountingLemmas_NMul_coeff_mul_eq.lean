-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.coeff_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:18.162138+00:00
-- url     : https://prove2.me/submissions/b86e0701-1230-4634-a272-55134c6dd804

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul

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
theorem _root_.solution {N n : ℕ} (F G : MvPolynomial (Fin N × Fin n) ℂ)
    (c : Fin N × Fin n →₀ ℕ) :
    coeff c (F * G) = ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      coeff p.1 F * coeff p.2 G := by
  classical
  rw [coeff_mul]
  symm
  refine sum_subset (fun p hp => ?_) (fun p hp hnot => ?_)
  · rw [mem_filter] at hp
    exact mem_antidiagonal.2 hp.2
  · by_cases h1 : coeff p.1 F = 0
    · simp [h1]
    by_cases h2 : coeff p.2 G = 0
    · simp [h2]
    have h3 : p.1 + p.2 = c := mem_antidiagonal.1 hp
    exact (hnot (mem_filter.2 ⟨mem_product.2 ⟨mem_support_iff.2 h1, mem_support_iff.2 h2⟩,
      h3⟩)).elim
end Formalism.NormUnitaryCountingLemmas.NMul
