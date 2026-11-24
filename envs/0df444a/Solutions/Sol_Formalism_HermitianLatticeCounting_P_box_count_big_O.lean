-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.box_count_big_O
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:41.433301+00:00
-- url     : https://prove2.me/submissions/883e6a51-2116-48ca-b4c1-dfee793a93a6

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_card_separated_set_le_prod
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finite_of_finset_card_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_lt_one_of_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : BoxCountO := by
  intro ι _ Λ B hB hΛ
  have h12 : {x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.Finite ∧
      ({x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.ncard : ℝ) ≤ ∏ v, (1 + 2 * B v) ^ 2 := by
    apply finite_of_finset_card_bound
    intro S hS
    have := card_separated_set_le_prod S (fun _ => 1 / 2) B (fun _ => by norm_num) (fun v => (hB v).le)
      (fun c hc => (hS hc).2) (by
        intro c hc d hd hcd
        by_contra hcon
        push_neg at hcon
        have hne : c - d ≠ 0 := sub_ne_zero.mpr hcd
        obtain ⟨v₀, -⟩ : ∃ v, c v ≠ d v := Function.ne_iff.mp hcd
        have h1 := hΛ (c - d) (Λ.sub_mem (hS hc).1 (hS hd).1) hne
        have h2 := prod_lt_one_of_lt_one (fun v => ‖(c - d) v‖) (fun v => norm_nonneg _)
          (fun v => by have := hcon v; simp only [Pi.sub_apply]; linarith) v₀
        linarith)
    refine this.trans (le_of_eq ?_)
    rw [Complex.finrank_real_complex]
    refine Finset.prod_congr rfl fun v _ => ?_
    congr 1; field_simp; ring
  refine ⟨h12.1, h12.2, ?_⟩
  rw [Fintype.card, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
  have a1 : (1:ℝ) ≤ max 1 (B v) := le_max_left _ _
  have a2 : B v ≤ max 1 (B v) := le_max_right _ _
  have := hB v
  nlinarith
end Formalism.HermitianLatticeCounting.P
