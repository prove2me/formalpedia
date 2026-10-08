-- Prove2me | solution 1 for ConvexRiskFn.Cont.positive_functional_continuous
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T04:02:12.537066+00:00
-- url     : https://prove2.me/submissions/0eb5bbde-62d6-4aa3-81a1-c3e933aba402

import Definitions.Def_ConvexRiskFn_Cont_Setting
set_option autoImplicit false
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    (l : E →ₗ[ℝ] ℝ) (hl : ∀ X : E, 0 ≤ X → 0 ≤ l X) : Continuous l := by
  classical
  have hm : Monotone l := by
    intro x y hxy
    have h := hl (y-x) (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    linarith
  have habs (x : E) : |l x| ≤ l |x| := by
    apply abs_le.mpr
    constructor
    · have h := hm (neg_le_abs x)
      rw [map_neg] at h
      linarith
    · exact hm (le_abs_self x)
  by_contra hc
  have hunbounded (C : ℝ) : ∃ x : E, C * ‖x‖ < ‖l x‖ := by
    by_contra h
    push Not at h
    exact hc (l.mkContinuous C h).continuous
  have hsmall (ε M : ℝ) (hε : 0 < ε) (hM : 0 < M) :
      ∃ u : E, 0 ≤ u ∧ ‖u‖ = ε ∧ M < l u := by
    obtain ⟨x,hx⟩ := hunbounded (M/ε)
    have hn : 0 < ‖x‖ := by
      by_contra h
      have hx0 : x = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt h) (norm_nonneg x))
      simp [hx0] at hx
    refine ⟨|(ε/‖x‖) • x|,abs_nonneg _,?_,?_⟩
    · rw [norm_abs_eq_norm,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hε hn)]
      exact div_mul_cancel₀ ε (ne_of_gt hn)
    · have ha := habs ((ε/‖x‖) • x)
      rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos (div_pos hε hn)] at ha
      rw [Real.norm_eq_abs] at hx
      rw [div_mul_eq_mul_div] at hx
      have hmul : M * ‖x‖ < |l x| * ε := (div_lt_iff₀ hε).mp hx
      have hgoal : M < (ε/‖x‖) * |l x| := by
        rw [div_mul_eq_mul_div]
        apply (lt_div_iff₀ hn).mpr
        simpa [mul_comm] using hmul
      exact hgoal.trans_le ha
  have hex : ∀ n : ℕ, ∃ u : E, 0 ≤ u ∧ ‖u‖ = (1/2:ℝ)^n ∧ (n:ℝ)+1 < l u := by
    intro n
    exact hsmall _ _ (pow_pos (by norm_num) _) (by positivity)
  choose u hu hn hlower using hex
  have hs : Summable u := Summable.of_norm_bounded
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1))
    (fun n => (hn n).le)
  obtain ⟨n,hnat⟩ := exists_nat_gt (l (∑' n, u n))
  have hle : u n ≤ ∑' n, u n := hs.le_tsum n (fun j _ => hu j)
  have h := (hlower n).trans_le (hm hle)
  linarith

#print axioms solution

open ConvexRiskFn.Cont Filter Topology
namespace ConvexRiskFn.Cont

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    (l : E →ₗ[ℝ] ℝ) (hl : ∀ X : E, 0 ≤ X → 0 ≤ l X) :
    Continuous l := by
  exact solution l hl

end ConvexRiskFn.Cont

#print axioms solution
