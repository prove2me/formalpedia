-- Prove2me | solution 1 for Expanders.alon_boppana_of_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:07:20.296387+00:00
-- url     : https://prove2.me/submissions/dacff244-1e95-48c1-9574-c5b6964f5173

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux
public import Definitions.Def_ExpanderLib_NilliBall
public import Definitions.Def_ExpanderLib_Expanders
public import Theorems.Thm_Expanders_adjMatrix_dotProduct_comm
public import Theorems.Thm_Expanders_dist_adj_le
public import Theorems.Thm_Expanders_dist_triangle_of_reachable
public import Theorems.Thm_Expanders_dotProduct_adjMatrix_mulVec_eq_zero
public import Theorems.Thm_Expanders_mem_vertexBall
public import Theorems.Thm_Expanders_nilli_vertexBall


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd2 : 2 ≤ d)
    (hd : G.IsRegularOfDegree d) {k : ℕ} {u w : V} (huw : 2 * k + 4 ≤ G.dist u w) :
    ∃ x : V → ℝ, x ≠ 0 ∧ ∑ v, x v = 0 ∧
      (2 * Real.sqrt (d - 1) - (2 * Real.sqrt (d - 1) - 1) / (k + 1)) * dotProduct x x ≤
        dotProduct x (G.adjMatrix ℝ *ᵥ x) := by
  classical
  set s := Real.sqrt ((d : ℝ) - 1) with hs
  set β := 2 * s - (2 * s - 1) / (k + 1) with hβ
  set A := G.adjMatrix ℝ
  set Bu := vertexBall G u k
  set Bw := vertexBall G w k
  set f := nilliVec s Bu (fun v => G.dist u v - 1) with hf
  set g := nilliVec s Bw (fun v => G.dist w v - 1) with hg
  have hfn : ∀ v, v ∉ Bu → f v = 0 := fun v hv => by simp [hf, nilliVec, hv]
  have hgn : ∀ v, v ∉ Bw → g v = 0 := fun v hv => by simp [hg, nilliVec, hv]
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hfnn : ∀ v, 0 ≤ f v := fun v => by
    simp only [hf, nilliVec]; split_ifs <;> positivity
  have hgnn : ∀ v, 0 ≤ g v := fun v => by
    simp only [hg, nilliVec]; split_ifs <;> positivity
  have huBu : u ∈ Bu := mem_vertexBall.mpr ⟨Reachable.refl u, by simp⟩
  have hwBw : w ∈ Bw := mem_vertexBall.mpr ⟨Reachable.refl w, by simp⟩
  have hfu : f u = 1 := by simp [hf, nilliVec, huBu]
  have hgw : g w = 1 := by simp [hg, nilliVec, hwBw]
  -- the balls are disjoint and non-adjacent
  have hdisj : ∀ v, v ∈ Bu → v ∉ Bw := by
    intro v hvu hvw
    rw [mem_vertexBall] at hvu hvw
    have := dist_triangle_of_reachable hvu.1 hvw.1.symm
    rw [SimpleGraph.dist_comm (u := v)] at this
    omega
  have hnoadj : ∀ a ∈ Bu, ∀ b ∈ Bw, ¬ G.Adj a b := by
    intro a ha b hb hab
    rw [mem_vertexBall] at ha hb
    have h1 := dist_adj_le ha.1 hab
    have h2 := dist_triangle_of_reachable (ha.1.trans hab.reachable) hb.1.symm
    rw [SimpleGraph.dist_comm (u := b)] at h2
    omega
  have hfAg : dotProduct f (A *ᵥ g) = 0 :=
    dotProduct_adjMatrix_mulVec_eq_zero G f g Bu Bw hfn hgn hnoadj
  have hgAf : dotProduct g (A *ᵥ f) = 0 := by
    rw [adjMatrix_dotProduct_comm]; exact hfAg
  have hfg : dotProduct f g = 0 := by
    refine Finset.sum_eq_zero (fun v _ => ?_)
    by_cases hv : v ∈ Bu
    · rw [hgn v (hdisj v hv), mul_zero]
    · rw [hfn v hv, zero_mul]
  have hgf : dotProduct g f = 0 := by rw [dotProduct_comm]; exact hfg
  -- the ball estimates
  have hF : β * dotProduct f f ≤ dotProduct f (A *ᵥ f) := nilli_vertexBall hd2 hd u k
  have hG : β * dotProduct g g ≤ dotProduct g (A *ᵥ g) := nilli_vertexBall hd2 hd w k
  -- combine
  have hgpos : 0 < ∑ v, g v := by
    have := Finset.single_le_sum (fun v _ => hgnn v) (Finset.mem_univ w)
    rw [hgw] at this; linarith
  set c := (∑ v, f v) / ∑ v, g v with hc
  refine ⟨f - c • g, ?_, ?_, ?_⟩
  · intro h0
    have := congrFun h0 u
    simp [hfu, hgn u (hdisj u huBu)] at this
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hc]
    field_simp; ring
  · simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hfAg, hgAf, hfg, hgf]
    nlinarith [sq_nonneg c, mul_le_mul_of_nonneg_left hG (sq_nonneg c)]
end Expanders
