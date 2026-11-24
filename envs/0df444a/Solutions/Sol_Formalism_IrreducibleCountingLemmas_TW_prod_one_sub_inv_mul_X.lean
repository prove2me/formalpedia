-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.prod_one_sub_inv_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:05.029495+00:00
-- url     : https://prove2.me/submissions/c99480e2-dc68-43ef-881a-7b1a3365f174

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWHeckeDetFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
namespace Formalism.IrreducibleCountingLemmas.TW
theorem _root_.solution {k : Type} [Field k] (s : Multiset k) (hs : ∀ a ∈ s, a ≠ 0) :
    (s.map (fun a => (1 : k[X]) - C a⁻¹ * X)).prod * C (s.map (fun a => 0 - a)).prod =
      (s.map (fun a => (X : k[X]) - C a)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih', C_mul]
    have h2 : ((1 : k[X]) - C a⁻¹ * X) * C (0 - a) = X - C a := by
      have h1 : (C a⁻¹ : k[X]) * C a = 1 := by rw [← C_mul, inv_mul_cancel₀ ha, C_1]
      rw [zero_sub, C_neg]; linear_combination X * h1
    rw [← h2]; ring
end Formalism.IrreducibleCountingLemmas.TW
