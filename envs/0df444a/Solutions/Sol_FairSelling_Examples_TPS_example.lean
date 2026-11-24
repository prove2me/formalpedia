-- Prove2me | solution 1 for FairSelling.Examples.TPS_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:23.40481+00:00
-- url     : https://prove2.me/submissions/43deb21f-bcb3-4cba-8588-0eb19d7b2b42

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_Examples
import Theorems.Thm_FairSelling_TPS_eq_bracket_formula
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem


section
open scoped BigOperators
namespace FairSelling
namespace Examples
private lemma truncSum_ex (t : ℝ) (ht0 : 0 ≤ t) :
    truncSum 2 vex pex t = (min 3 t + min 1 t) / 2 := by
  simp only [truncSum, Fin.sum_univ_two, vex, pex, Matrix.cons_val_zero, Matrix.cons_val_one,
    ]
  rw [max_eq_right (le_min (by norm_num) ht0), max_eq_right (le_min (by norm_num) ht0)]
  norm_num
end Examples
end FairSelling
end

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.Examples
namespace FairSelling.Examples
theorem _root_.solution : TPS 2 vex pex = 1 := by
  have hp : ∀ g, 0 ≤ pex g := by
    intro g; fin_cases g <;> norm_num [pex]
  have hf1 : truncSum 2 vex pex 1 = 1 := by
    rw [truncSum_ex 1 (by norm_num)]; norm_num
  have hf3 : truncSum 2 vex pex 3 = 2 := by
    rw [truncSum_ex 3 (by norm_num)]; norm_num
  have hvvals : ∀ g, vex g = 3 ∨ vex g = 1 := by
    intro g; fin_cases g
    · left; norm_num [vex]
    · right; norm_num [vex]
  have hnb : NoBreak vex pex 1 3 := by
    intro g
    refine ⟨?_, Or.inl (by rw [show pex g = 0 from by fin_cases g <;> norm_num [pex]]; norm_num)⟩
    rcases hvvals g with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h])
  obtain ⟨-, hval, -, -⟩ :=
    TPS_eq_bracket_formula (n := 2) vex pex (by norm_num) hp (by norm_num) hnb
      (by rw [hf1]) (by rw [hf3]; norm_num)
      (fun g hg => by
        rcases hvvals g with h | h
        · rw [h, hf3]; norm_num
        · rw [h] at hg; norm_num at hg)
      (fun g hg => by
        rw [show pex g = 0 from by fin_cases g <;> norm_num [pex]] at hg
        norm_num at hg)
  rw [hval]
  have hslope : (slopeGoods vex pex 1 3).card = 1 := by
    have : slopeGoods vex pex 1 3 = {0} := by
      ext g
      rw [slopeGoods, Finset.mem_filter, Finset.mem_singleton]
      fin_cases g <;> simp [vex, pex] <;> norm_num
    rw [this]; rfl
  have hflat : flatConst vex pex 1 3 = 1 := by
    have hset : (Finset.univ.filter (fun g => ¬ ((3:ℝ) ≤ vex g ∧ pex g ≤ 1)))
        = ({1} : Finset (Fin 2)) := by
      ext g
      fin_cases g <;> simp [vex, pex]
    rw [flatConst, hset, Finset.sum_singleton]
    norm_num [vex, pex]
  rw [hslope, hflat]
  norm_num
end FairSelling.Examples
