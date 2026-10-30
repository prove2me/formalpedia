-- Prove2me | solution 1 for DerivativeChainContinuation.cubic_endpoint_parameters
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:27:46.904553+00:00
-- url     : https://prove2.me/submissions/be1d34f1-50e4-4010-9ef5-88cf600abddd

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem solution (x y u v : ℝ) (hx : 0 < x) (hy0 : 0 ≤ y)
    (hu0 : 0 ≤ u) (hv0 : u=0 → v ≤ 0)
    (hrel : u*v=-(3/4)*x*y)
    (hA : 0 ≤ (3/4)*(x^2-y^2)+u^2-v^2)
    (hB : 0 ≤ x^3/4-3*x*y^2/4-x*u^2+x*v^2+2*y*u*v) :
    ∃ k s : ℝ, 0 ≤ k ∧ k ≤ 1 ∧ 0 ≤ s ∧ s^2 ≤ 3 ∧
      y=k*s*x/3 ∧ u=k*x/2 ∧ v= -x*s/2 := by
  by_cases hu : u=0
  · have hy : y=0 := by rw [hu] at hrel; nlinarith
    have hv : v ≤ 0 := hv0 hu
    let s := -2*v/x
    refine ⟨0,s,by norm_num,by norm_num,?_,?_,?_,?_,?_⟩
    · dsimp [s]; exact div_nonneg (by linarith) hx.le
    · have hs : s*x= -2*v := by dsimp [s]; field_simp
      rw [hu,hy] at hA
      have hxs : 0 < x^2 := sq_pos_of_pos hx
      have hb : x^2*s^2 ≤ 3*x^2 := by nlinarith [sq_nonneg (s*x+2*v)]
      exact (mul_le_mul_iff_right₀ hxs).mp (by nlinarith [hb])
    · simp [hy]
    · simp [hu]
    · dsimp [s]; field_simp
  · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    let k := 2*u/x
    let s := 3*y/(2*u)
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hs : 0 ≤ s := by dsimp [s]; positivity
    have hy : y=k*s*x/3 := by dsimp [k,s]; field_simp
    have hur : u=k*x/2 := by dsimp [k]; field_simp
    have hv : v= -x*s/2 := by dsimp [s]; field_simp; nlinarith [hrel]
    have hAi : (3/4)*(x^2-y^2)+u^2-v^2 = x^2*(3+k^2)*(3-s^2)/12 := by
      rw [hy,hur,hv]; ring
    have hBi : x^3/4-3*x*y^2/4-x*u^2+x*v^2+2*y*u*v =
        x^3*(1-k^2)*(1+s^2)/4 := by rw [hy,hur,hv]; ring
    rw [hAi] at hA
    rw [hBi] at hB
    have hsa : 0 ≤ (x^2*(3+k^2))*(3-s^2) := by linarith
    have hsb : 0 ≤ (x^3*(1+s^2))*(1-k^2) := by nlinarith
    have hss := (mul_nonneg_iff_of_pos_left (by positivity : 0 < x^2*(3+k^2))).mp hsa
    have hkk := (mul_nonneg_iff_of_pos_left (by positivity : 0 < x^3*(1+s^2))).mp hsb
    exact ⟨k,s,hk,by nlinarith,hs,by linarith,hy,hur,hv⟩
