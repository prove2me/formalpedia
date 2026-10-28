-- Prove2me | solution 1 for ConvexOn.exists_linear_upper_of_upperSemicontinuousAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:46.637927+00:00
-- url     : https://prove2.me/submissions/dc0bc8f0-ec6d-4f46-90d3-1ac6e656a5e3

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting
import Definitions.Def_WassDDRO_Reduction_Setting

-- carved verbatim out of submission 9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 929-996

section
set_option autoImplicit false
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E → EReal)
    (hne_top : ∀ x, L x ≠ ⊤)
    (hconvex : Convex ℝ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)})
    (x0 : E) (a : ℝ) (ha : L x0=(a : EReal))
    (husc : UpperSemicontinuousAt L x0) :
    ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, L x ≤ ((C+A*‖x-x0‖ : ℝ) : EReal) := by
  have hn : ∀ᶠ x in 𝓝 x0, L x < ((a+1 : ℝ) : EReal) := by
    apply husc
    rw [ha]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨a+1,2/δ,by positivity,?_⟩
  intro x
  cases hx : L x using EReal.rec with
  | bot => exact bot_le
  | top => exact False.elim (hne_top x hx)
  | coe b =>
    by_cases hd : ‖x-x0‖ < δ
    · have hb : b < a+1 := EReal.coe_lt_coe_iff.mp (by
        rw [←hx]
        exact hlocal (by simpa [dist_eq_norm] using hd))
      apply EReal.coe_le_coe_iff.mpr
      have hp : 0 ≤ (2/δ)*‖x-x0‖ := by positivity
      linarith
    · have hd0 : 0 < ‖x-x0‖ := lt_of_lt_of_le hδ (le_of_not_gt hd)
      let t : ℝ := δ/(2*‖x-x0‖)
      have ht : 0 < t := by dsimp [t];positivity
      have ht1 : t ≤ 1 := by
        dsimp [t]
        apply (div_le_iff₀ (by positivity)).mpr
        linarith [le_of_not_gt hd]
      have hp0 : (x0,-a) ∈ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)} := by
        change -L x0 ≤ ((-a : ℝ) : EReal)
        simp [ha, EReal.coe_neg]
      have hpx : (x,-b) ∈ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)} := by
        change -L x ≤ ((-b : ℝ) : EReal)
        simp [hx, EReal.coe_neg]
      have hc := hconvex hp0 hpx (sub_nonneg.mpr ht1) ht.le (by ring : (1-t)+t=1)
      change -L ((1-t) • x0+t • x) ≤ (((1-t)*(-a)+t*(-b) : ℝ) : EReal) at hc
      have hvec : (1-t) • x0+t • x-x0 = t • (x-x0) := by module
      have hnorm : ‖(1-t) • x0+t • x-x0‖ = δ/2 := by
        rw [hvec,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
        dsimp [t]
        field_simp
      have hu := (hlocal (y:=(1-t) • x0+t • x) (by
        rw [dist_eq_norm,hnorm];linarith)).le
      have hlow : (((1-t)*a+t*b : ℝ) : EReal) ≤ L ((1-t) • x0+t • x) := by
        have hc' : -L ((1-t) • x0+t • x) ≤ -(((1-t)*a+t*b : ℝ) : EReal) := by
          convert hc using 1 <;> simp only [←EReal.coe_neg] <;> congr 1 <;> ring
        exact EReal.neg_le_neg_iff.mp hc'
      have hb : (1-t)*a+t*b ≤ a+1 := by
        have hh := hlow.trans hu
        exact EReal.coe_le_coe_iff.mp hh
      have htd : t*((2/δ)*‖x-x0‖)=1 := by dsimp [t];field_simp <;> ring
      apply EReal.coe_le_coe_iff.mpr
      have hbx : b ≤ a+(2/δ)*‖x-x0‖ := by nlinarith
      linarith

end
