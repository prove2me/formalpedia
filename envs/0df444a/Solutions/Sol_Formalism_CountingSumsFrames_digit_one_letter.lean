-- Prove2me | solution 1 for Formalism.CountingSumsFrames.digit_one_letter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:39.081909+00:00
-- url     : https://prove2.me/submissions/5508cd2f-c3cb-4f2c-9dbd-0ea4f601aba0

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Theorems.Thm_Formalism_CountingSumsFrames_digit_inner_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (P m t : ℕ) (hP : 0 < P) :
    ((univ : Finset (Fin (m+1) → Fin P)).filter (fun f => (∑ c, (f c : ℕ)) % P = t % P)).card = P ^ m := by
  rw [Finset.card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (m+1) => Fin P)
    (fun p => if (∑ c, ((Fin.cons p.1 p.2 : Fin (m+1) → Fin P) c : ℕ)) % P = t % P then 1 else 0)
    (fun f => if (∑ c, (f c : ℕ)) % P = t % P then 1 else 0) (fun p => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h1 : ∀ g : Fin m → Fin P, ∑ x : Fin P,
      (if (∑ c, ((Fin.cons x g : Fin (m+1) → Fin P) c : ℕ)) % P = t % P then 1 else 0) = 1 := by
    intro g
    obtain ⟨n, rfl⟩ : ∃ n, P = n + 1 := ⟨P - 1, by omega⟩
    rw [← Finset.card_filter]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    exact digit_inner_one n _ t
  simp [h1]
end Formalism.CountingSumsFrames
