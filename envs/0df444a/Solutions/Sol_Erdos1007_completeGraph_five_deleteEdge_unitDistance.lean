-- Prove2me | solution 1 for Erdos1007.completeGraph_five_deleteEdge_unitDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:33.769863+00:00
-- url     : https://prove2.me/submissions/f83c3be0-711a-4da8-ad28-34ce2ea6421d

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Erdos1007_Geometry_CompleteMinusEdge
section
namespace Erdos1007
noncomputable section
private lemma dist_sq (u v : Fin 5) :
    dist (pt_cme u) (pt_cme v) ^ 2 =
      (xCoord_cme u - xCoord_cme v) ^ 2 + (yCoord_cme u - yCoord_cme v) ^ 2 + (zCoord_cme u - zCoord_cme v) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
  simp [pt_cme, Real.dist_eq, sq_abs]
private lemma dist_of_sq {u v : Fin 5}
    (h : (xCoord_cme u - xCoord_cme v) ^ 2 + (yCoord_cme u - yCoord_cme v) ^ 2 +
      (zCoord_cme u - zCoord_cme v) ^ 2 = 1) :
    dist (pt_cme u) (pt_cme v) = 1 := by
  have hsq : dist (pt_cme u) (pt_cme v) ^ 2 = 1 := by rw [dist_sq, h]
  rw [← Real.sqrt_sq (dist_nonneg (x := pt_cme u) (y := pt_cme v)), hsq, Real.sqrt_one]
private lemma sq_comm (u v : Fin 5) :
    (xCoord_cme u - xCoord_cme v) ^ 2 + (yCoord_cme u - yCoord_cme v) ^ 2 + (zCoord_cme u - zCoord_cme v) ^ 2 =
      (xCoord_cme v - xCoord_cme u) ^ 2 + (yCoord_cme v - yCoord_cme u) ^ 2 + (zCoord_cme v - zCoord_cme u) ^ 2 := by
  ring
private lemma equil : (1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
  rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  norm_num
private lemma apexFromCorner :
    (1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 6) ^ 2 + (Real.sqrt (2 / 3)) ^ 2 = 1 := by
  rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  norm_num
private lemma apexFromTop :
    (Real.sqrt 3 / 2 - Real.sqrt 3 / 6) ^ 2 + (Real.sqrt (2 / 3)) ^ 2 = 1 := by
  have h : Real.sqrt 3 / 2 - Real.sqrt 3 / 6 = Real.sqrt 3 / 3 := by ring
  rw [h, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  norm_num
private lemma sq_01 :
    (xCoord_cme 0 - xCoord_cme 1) ^ 2 + (yCoord_cme 0 - yCoord_cme 1) ^ 2 + (zCoord_cme 0 - zCoord_cme 1) ^ 2 = 1 := by
  simp only [xCoord_cme, yCoord_cme, zCoord_cme]; norm_num
private lemma sq_02 :
    (xCoord_cme 0 - xCoord_cme 2) ^ 2 + (yCoord_cme 0 - yCoord_cme 2) ^ 2 + (zCoord_cme 0 - zCoord_cme 2) ^ 2 = 1 := by
  simp only [xCoord_cme, yCoord_cme, zCoord_cme]
  convert equil using 1
  ring
private lemma sq_12 :
    (xCoord_cme 1 - xCoord_cme 2) ^ 2 + (yCoord_cme 1 - yCoord_cme 2) ^ 2 + (zCoord_cme 1 - zCoord_cme 2) ^ 2 = 1 := by
  simp only [xCoord_cme, yCoord_cme, zCoord_cme]
  convert equil using 1
  ring
private lemma sq_03 :
    (xCoord_cme 0 - xCoord_cme 3) ^ 2 + (yCoord_cme 0 - yCoord_cme 3) ^ 2 + (zCoord_cme 0 - zCoord_cme 3) ^ 2 = 1 := by
  simp only [xCoord_cme, yCoord_cme, zCoord_cme]
  convert apexFromCorner using 1
  ring
private lemma sq_13 :
    (xCoord_cme 1 - xCoord_cme 3) ^ 2 + (yCoord_cme 1 - yCoord_cme 3) ^ 2 + (zCoord_cme 1 - zCoord_cme 3) ^ 2 = 1 := by
  simp only [xCoord_cme, yCoord_cme, zCoord_cme]
  convert apexFromCorner using 1
  ring
private lemma sq_23 :
    (xCoord_cme 2 - xCoord_cme 3) ^ 2 + (yCoord_cme 2 - yCoord_cme 3) ^ 2 + (zCoord_cme 2 - zCoord_cme 3) ^ 2 = 1 := by
  simp only [xCoord_cme, yCoord_cme, zCoord_cme]
  convert apexFromTop using 1
  ring
private lemma sq_04 :
    (xCoord_cme 0 - xCoord_cme 4) ^ 2 + (yCoord_cme 0 - yCoord_cme 4) ^ 2 + (zCoord_cme 0 - zCoord_cme 4) ^ 2 = 1 := by
  simp only [xCoord_cme, yCoord_cme, zCoord_cme]
  convert apexFromCorner using 1
  ring
private lemma sq_14 :
    (xCoord_cme 1 - xCoord_cme 4) ^ 2 + (yCoord_cme 1 - yCoord_cme 4) ^ 2 + (zCoord_cme 1 - zCoord_cme 4) ^ 2 = 1 := by
  simp only [xCoord_cme, yCoord_cme, zCoord_cme]
  convert apexFromCorner using 1
  ring
private lemma sq_24 :
    (xCoord_cme 2 - xCoord_cme 4) ^ 2 + (yCoord_cme 2 - yCoord_cme 4) ^ 2 + (zCoord_cme 2 - zCoord_cme 4) ^ 2 = 1 := by
  simp only [xCoord_cme, yCoord_cme, zCoord_cme]
  convert apexFromTop using 1
  ring
private lemma sqrt23_ne_zero : Real.sqrt (2 / 3) ≠ 0 :=
  ne_of_gt (by positivity)
private lemma neg_sqrt23_ne_zero : -Real.sqrt (2 / 3) ≠ 0 := by
  intro h
  exact sqrt23_ne_zero (neg_eq_zero.mp h)
private lemma sqrt23_ne_neg : Real.sqrt (2 / 3) ≠ -Real.sqrt (2 / 3) := by
  intro h
  have hpos : (0 : ℝ) < Real.sqrt (2 / 3) := by positivity
  nlinarith
private lemma pt_injective : Function.Injective pt_cme := by
  intro u v h
  have hx : xCoord_cme u = xCoord_cme v := by
    simpa [pt_cme] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 0) h
  have hz : zCoord_cme u = zCoord_cme v := by
    simpa [pt_cme] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 2) h
  fin_cases u <;> fin_cases v <;> simp only [xCoord_cme, zCoord_cme] at hx hz
  · rfl
  · exact absurd hx (by norm_num)
  · exact absurd hx (by norm_num)
  · exact absurd hz sqrt23_ne_zero.symm
  · exact absurd hz.symm neg_sqrt23_ne_zero
  · exact absurd hx (by norm_num)
  · rfl
  · exact absurd hx (by norm_num)
  · exact absurd hz sqrt23_ne_zero.symm
  · exact absurd hz.symm neg_sqrt23_ne_zero
  · exact absurd hx (by norm_num)
  · exact absurd hx (by norm_num)
  · rfl
  · exact absurd hz sqrt23_ne_zero.symm
  · exact absurd hz.symm neg_sqrt23_ne_zero
  · exact absurd hz sqrt23_ne_zero
  · exact absurd hz sqrt23_ne_zero
  · exact absurd hz sqrt23_ne_zero
  · rfl
  · exact absurd hz sqrt23_ne_neg
  · exact absurd hz neg_sqrt23_ne_zero
  · exact absurd hz neg_sqrt23_ne_zero
  · exact absurd hz neg_sqrt23_ne_zero
  · exact absurd hz.symm sqrt23_ne_neg
  · rfl
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
    ∃ f : Fin 5 → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ u v, ((⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)}).Adj u v →
        dist (f u) (f v) = 1 := by
  refine ⟨pt_cme, pt_injective, ?_⟩
  intro u v huv
  -- `fin_cases` walks pairs `(u, v)` in lexicographic order. The deleted edge is `(3, 4)`.
  fin_cases u <;> fin_cases v
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_01
  · exact dist_of_sq sq_02
  · exact dist_of_sq sq_03
  · exact dist_of_sq sq_04
  · exact dist_of_sq ((sq_comm 0 1).symm.trans sq_01)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_12
  · exact dist_of_sq sq_13
  · exact dist_of_sq sq_14
  · exact dist_of_sq ((sq_comm 0 2).symm.trans sq_02)
  · exact dist_of_sq ((sq_comm 1 2).symm.trans sq_12)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_23
  · exact dist_of_sq sq_24
  · exact dist_of_sq ((sq_comm 0 3).symm.trans sq_03)
  · exact dist_of_sq ((sq_comm 1 3).symm.trans sq_13)
  · exact dist_of_sq ((sq_comm 2 3).symm.trans sq_23)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq ((sq_comm 0 4).symm.trans sq_04)
  · exact dist_of_sq ((sq_comm 1 4).symm.trans sq_14)
  · exact dist_of_sq ((sq_comm 2 4).symm.trans sq_24)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
end Erdos1007
