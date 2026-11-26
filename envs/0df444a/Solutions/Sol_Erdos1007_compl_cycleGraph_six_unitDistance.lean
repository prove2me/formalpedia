-- Prove2me | solution 1 for Erdos1007.compl_cycleGraph_six_unitDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:25.819569+00:00
-- url     : https://prove2.me/submissions/22c6d67a-cfbf-4d3a-bd6c-5726fe0aaf11

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Definitions.Def_Erdos1007_Geometry_Prism
section
namespace Erdos1007
noncomputable section
private lemma dist_sq (u v : Fin 6) :
    dist (pt_prism u) (pt_prism v) ^ 2 = (xCoord_prism u - xCoord_prism v) ^ 2 + (yCoord_prism u - yCoord_prism v) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [pt_prism, Real.dist_eq, sq_abs]
private lemma dist_of_sq {u v : Fin 6}
    (h : (xCoord_prism u - xCoord_prism v) ^ 2 + (yCoord_prism u - yCoord_prism v) ^ 2 = 1) :
    dist (pt_prism u) (pt_prism v) = 1 := by
  have hsq : dist (pt_prism u) (pt_prism v) ^ 2 = 1 := by rw [dist_sq, h]
  rw [← Real.sqrt_sq (dist_nonneg (x := pt_prism u) (y := pt_prism v)), hsq, Real.sqrt_one]
private lemma sq_comm (u v : Fin 6) :
    (xCoord_prism u - xCoord_prism v) ^ 2 + (yCoord_prism u - yCoord_prism v) ^ 2 =
      (xCoord_prism v - xCoord_prism u) ^ 2 + (yCoord_prism v - yCoord_prism u) ^ 2 := by
  ring
private lemma equil : (1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
  rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  norm_num
private lemma sq_02 : (xCoord_prism 0 - xCoord_prism 2) ^ 2 + (yCoord_prism 0 - yCoord_prism 2) ^ 2 = 1 := by
  simp only [xCoord_prism, yCoord_prism]; norm_num
private lemma sq_03 : (xCoord_prism 0 - xCoord_prism 3) ^ 2 + (yCoord_prism 0 - yCoord_prism 3) ^ 2 = 1 := by
  simp only [xCoord_prism, yCoord_prism]; norm_num
private lemma sq_04 : (xCoord_prism 0 - xCoord_prism 4) ^ 2 + (yCoord_prism 0 - yCoord_prism 4) ^ 2 = 1 := by
  simp only [xCoord_prism, yCoord_prism]
  convert equil using 1
  ring
private lemma sq_13 : (xCoord_prism 1 - xCoord_prism 3) ^ 2 + (yCoord_prism 1 - yCoord_prism 3) ^ 2 = 1 := by
  simp only [xCoord_prism, yCoord_prism]
  convert equil using 1
  ring
private lemma sq_14 : (xCoord_prism 1 - xCoord_prism 4) ^ 2 + (yCoord_prism 1 - yCoord_prism 4) ^ 2 = 1 := by
  simp only [xCoord_prism, yCoord_prism]
  ring
private lemma sq_15 : (xCoord_prism 1 - xCoord_prism 5) ^ 2 + (yCoord_prism 1 - yCoord_prism 5) ^ 2 = 1 := by
  simp only [xCoord_prism, yCoord_prism]
  convert equil using 1
  ring
private lemma sq_24 : (xCoord_prism 2 - xCoord_prism 4) ^ 2 + (yCoord_prism 2 - yCoord_prism 4) ^ 2 = 1 := by
  simp only [xCoord_prism, yCoord_prism]
  convert equil using 1
  ring
private lemma sq_25 : (xCoord_prism 2 - xCoord_prism 5) ^ 2 + (yCoord_prism 2 - yCoord_prism 5) ^ 2 = 1 := by
  simp only [xCoord_prism, yCoord_prism]; norm_num
private lemma sq_35 : (xCoord_prism 3 - xCoord_prism 5) ^ 2 + (yCoord_prism 3 - yCoord_prism 5) ^ 2 = 1 := by
  simp only [xCoord_prism, yCoord_prism]; norm_num
private lemma pt_injective : Function.Injective pt_prism := by
  intro u v h
  have hx : xCoord_prism u = xCoord_prism v := by
    simpa [pt_prism] using congr_arg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) h
  have hy : yCoord_prism u = yCoord_prism v := by
    simpa [pt_prism] using congr_arg (fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 1) h
  fin_cases u <;> fin_cases v <;> simp_all [xCoord_prism, yCoord_prism]
@[expose] public section
end
end
end Erdos1007
end

set_option autoImplicit false
@[expose] public section
open Erdos1007
noncomputable section
public section
namespace Erdos1007
theorem _root_.solution :
    ∃ f : Fin 6 → EuclideanSpace ℝ (Fin 2), Function.Injective f ∧
      ∀ u v, (SimpleGraph.cycleGraph 6)ᶜ.Adj u v → dist (f u) (f v) = 1 := by
  refine ⟨pt_prism, pt_injective, ?_⟩
  intro u v huv
  -- `fin_cases` walks pairs `(u, v)` in lexicographic order.
  fin_cases u <;> fin_cases v
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_02
  · exact dist_of_sq sq_03
  · exact dist_of_sq sq_04
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_13
  · exact dist_of_sq sq_14
  · exact dist_of_sq sq_15
  · exact dist_of_sq ((sq_comm 0 2).symm.trans sq_02)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_24
  · exact dist_of_sq sq_25
  · exact dist_of_sq ((sq_comm 0 3).symm.trans sq_03)
  · exact dist_of_sq ((sq_comm 1 3).symm.trans sq_13)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_35
  · exact dist_of_sq ((sq_comm 0 4).symm.trans sq_04)
  · exact dist_of_sq ((sq_comm 1 4).symm.trans sq_14)
  · exact dist_of_sq ((sq_comm 2 4).symm.trans sq_24)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq ((sq_comm 1 5).symm.trans sq_15)
  · exact dist_of_sq ((sq_comm 2 5).symm.trans sq_25)
  · exact dist_of_sq ((sq_comm 3 5).symm.trans sq_35)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
end Erdos1007
