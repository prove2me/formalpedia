-- Prove2me | solution 1 for BookProof.ChapterIrreversible.exists_mem_Ioo_of_not_pointMass
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:14:50.76527+00:00
-- url     : https://prove2.me/submissions/116c0e68-d4bd-44ac-99ff-8889bb6f5ac2

-- Generated from ChapterIrreversible.lean — solution of BookProof.ChapterIrreversible.exists_mem_Ioo_of_not_pointMass
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hnp : ¬ IsPointMass p) :
    ∃ a, 0 < p a ∧ p a < 1 := by

  contrapose! hnp; simp_all only [IsPointMass, ne_eq] ;
  -- Since $p$ is not a point mass, there exists some $a$ such that $p(a) > 0$.
  obtain ⟨a, ha⟩ : ∃ a, 0 < p a := by
    refine not_forall_not.mp fun h => ?_
    have hp0 : p = fun _ => 0 := by funext a; linarith [ h a, hnn a ]
    norm_num [ hp0 ] at hsum
  exact ⟨ a,
    le_antisymm ( hsum ▸ Finset.single_le_sum ( fun x _ => hnn x ) ( Finset.mem_univ a ) )
      ( hnp a ha ),
    fun b hb => le_antisymm
      ( by
          have := hsum ▸ Finset.sum_eq_add_sum_sdiff_singleton_of_mem
            ( Finset.mem_univ a ) p
          linarith [ hnp a ha, hnn b, Finset.single_le_sum ( fun x _ => hnn x )
            ( Finset.mem_sdiff.mpr ⟨ Finset.mem_univ b, by aesop ⟩ :
              b ∈ Finset.univ \ { a } ) ] )
      ( hnn b ) ⟩
