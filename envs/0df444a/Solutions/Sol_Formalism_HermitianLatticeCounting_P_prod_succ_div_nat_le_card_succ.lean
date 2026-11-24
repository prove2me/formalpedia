-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prod_succ_div_nat_le_card_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:41.562929+00:00
-- url     : https://prove2.me/submissions/61a8be42-57d9-4408-a2b0-cd1f6e739a4a

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (S : Finset ℕ) : (∀ y ∈ S, 1 ≤ y) →
    ∏ y ∈ S, (((y : ℝ) + 1) / (y : ℝ)) ≤ (S.card : ℝ) + 1 := by
  refine Finset.induction_on_max S ?_ ?_
  · intro _
    simp
  · intro a S ha ih hS
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS]
    have hS' : ∀ y ∈ S, 1 ≤ y := fun y hy => hS y (Finset.mem_insert_of_mem hy)
    have ih' := ih hS'
    have ha1 : 1 ≤ a := hS a (Finset.mem_insert_self a S)
    have hcard : S.card + 1 ≤ a := by
      have hsub : insert a S ⊆ Finset.Icc 1 a := by
        intro y hy
        rw [Finset.mem_Icc]
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact ⟨ha1, le_refl _⟩
        · exact ⟨hS y hy, (ha y hy').le⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc, Finset.card_insert_of_notMem haS] at this
      omega
    have ha0 : (0:ℝ) < a := by exact_mod_cast ha1
    have hcardR : (S.card : ℝ) + 1 ≤ a := by exact_mod_cast hcard
    push_cast
    calc ((a:ℝ) + 1) / a * ∏ y ∈ S, (((y : ℝ) + 1) / (y : ℝ)) ≤ ((a:ℝ) + 1) / a * ((S.card : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ (S.card : ℝ) + 1 + 1 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ ha0]
          nlinarith
end Formalism.HermitianLatticeCounting.P
