-- Prove2me | solution 1 for Erdos1007.completeBipartiteGraph_three_three_unitDistance_with_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:28.967576+00:00
-- url     : https://prove2.me/submissions/826a6def-1a17-42b7-94a7-71228fffd930

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartite
section
namespace Erdos1007
private theorem sq_dist_svec {a b : ℝ} {i j : Fin 4} (h : i ≠ j) :
    ∑ k : Fin 4, dist ((svec i a).ofLp k) ((svec j b).ofLp k) ^ 2 = a ^ 2 + b ^ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [svec, PiLp.single_apply, Fin.sum_univ_four, Real.dist_eq, sq_abs] <;> ring
@[expose] public section
end
end Erdos1007
end

set_option autoImplicit false
@[expose] public section
open Erdos1007
public section
namespace Erdos1007
theorem _root_.solution :
    ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 4), Function.Injective f ∧
      (∀ u v, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v → dist (f u) (f v) = 1) ∧
      dist (f (Sum.inl 0)) (f (Sum.inl 2)) = 1 := by
  obtain ⟨r, hr2, hrpos⟩ : ∃ r : ℝ, r ^ 2 = 1 / 2 ∧ 0 < r :=
    ⟨1 / Real.sqrt 2, by rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)], by positivity⟩
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  -- Two signed axis vectors with a nonzero entry agree only on the same axis with the same entry.
  have hvec_inj : ∀ i j : Fin 4, ∀ a b : ℝ, a ≠ 0 → svec i a = svec j b → i = j ∧ a = b := by
    intro i j a b ha h
    have h1 : a = if i = j then b else 0 := by
      have h2 : (svec i a).ofLp i = (svec j b).ofLp i := by rw [h]
      simp only [svec, PiLp.single_eq_same, PiLp.single_apply] at h2
      exact h2
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl] at h1
      exact ⟨rfl, h1⟩
    · rw [if_neg hij] at h1
      exact absurd h1 ha
  -- Two signed axis vectors on distinct axes, each of squared length `r² = 1/2`, are at distance 1.
  have hvec_dist : ∀ i j : Fin 4, i ≠ j → ∀ a b : ℝ,
      a ^ 2 = r ^ 2 → b ^ 2 = r ^ 2 → dist (svec i a) (svec j b) = 1 := by
    intro i j hij a b ha hb
    rw [EuclideanSpace.dist_eq, sq_dist_svec hij, ha, hb, hr2]
    norm_num
  refine ⟨pt r, ?_, ?_, ?_⟩
  · -- Injectivity: read off the axis and the sign from a placed point.
    intro u v huv
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u <;> fin_cases v <;> simp only [pt] at huv
      · rfl
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).2 (by linarith)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).2 (by linarith)
      · rfl
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · rfl
    · fin_cases u <;> fin_cases v <;> simp only [pt] at huv <;>
        exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
    · fin_cases u <;> fin_cases v <;> simp only [pt] at huv <;>
        exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
    · fin_cases u <;> fin_cases v <;> simp only [pt] at huv
      · rfl
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).2 (by linarith)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).2 (by linarith)
      · rfl
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · exact absurd (hvec_inj _ _ _ _ (by simp [hr0]) huv).1 (by simp)
      · rfl
  · -- Every edge joins the two parts, whose points lie on disjoint axes.
    intro u v huv
    rcases u with u | u <;> rcases v with v | v
    · simp [completeBipartiteGraph] at huv
    · fin_cases u <;> fin_cases v <;> simp only [pt] <;>
        exact hvec_dist _ _ (by simp) _ _ (by ring) (by ring)
    · fin_cases u <;> fin_cases v <;> simp only [pt] <;>
        exact hvec_dist _ _ (by simp) _ _ (by ring) (by ring)
    · simp [completeBipartiteGraph] at huv
  · rw [show pt r (Sum.inl 0) = svec (0 : Fin 4) r from rfl,
        show pt r (Sum.inl 2) = svec (1 : Fin 4) r from rfl]
    exact hvec_dist (0 : Fin 4) 1 (by decide) r r rfl rfl
end Erdos1007
