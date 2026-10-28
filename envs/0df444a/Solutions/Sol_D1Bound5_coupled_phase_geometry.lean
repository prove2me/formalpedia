-- Prove2me | solution 1 for D1Bound5.coupled_phase_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:34:41.974991+00:00
-- url     : https://prove2.me/submissions/19ae0948-a06e-42f4-a8e9-97b810d1cc37

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_CoupledPhaseGeometry_Definitions

section
namespace D1Bound5







/-- The elementary coupled-phase estimate retains the relation between
the sum and difference of the last two anchors. No independent maximization
of their phases is used. -/
theorem _root_.solution (a b s : ℂ) (q : ℝ)
    (hq : 1 ≤ q) (hB : 0 < ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hsep : q*‖a‖ ≤ ‖b‖) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 2 ∧
      (phaseVandermondeRatio a b s)^2*phasePhi b s ≤ coupledPhasePolynomial q x := by
  let A := ‖a‖; let B := ‖b‖; let S := ‖s‖
  let u := A/B; let v := B/S
  let d := ‖b-s‖/S; let y := ‖b+s‖/S
  let R := phaseVandermondeRatio a b s
  have hS : 0 < S := hB.trans_le hBS
  have hq0 : 0 < q := by linarith only [hq]
  have hBn : B ≠ 0 := ne_of_gt hB
  have hSn : S ≠ 0 := ne_of_gt hS
  have hu0 : 0 ≤ u := div_nonneg (norm_nonneg _) hB.le
  have hv0 : 0 ≤ v := div_nonneg hB.le hS.le
  have hd0 : 0 ≤ d := div_nonneg (norm_nonneg _) hS.le
  have hy0 : 0 ≤ y := div_nonneg (norm_nonneg _) hS.le
  have hi0 : 0 ≤ 1/q := by positivity
  have hi1 : 1/q ≤ 1 := (div_le_one₀ hq0).mpr hq
  have hu : u ≤ 1/q := (div_le_div_iff₀ hB hq0).mpr (by simpa [mul_comm] using hsep)
  have hv1 : v ≤ 1 := (div_le_one₀ hS).mpr hBS
  have hd2 : d ≤ 2 := by
    apply (div_le_iff₀ hS).mpr
    have hh := norm_sub_le b s
    dsimp [S]
    linarith only [hh,hBS]
  have hdsq : d^2 ≤ 4 := by nlinarith only [hd0,hd2]
  have hsum : y^2+d^2 ≤ 4 := by
    have hpara := parallelogram_law_with_norm ℂ b s
    have hbsq : B^2 ≤ S^2 := by nlinarith only [hBS,hB,hS]
    have he : y^2+d^2 = (‖b+s‖^2+‖b-s‖^2)/S^2 := by dsimp [y,d]; ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hS)).mpr
    change ‖b+s‖^2+‖b-s‖^2 ≤ 4*‖s‖^2
    dsimp [B,S] at hbsq
    nlinarith only [hpara,hbsq]
  let x := Real.sqrt (4-d^2)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x^2 = 4-d^2 := Real.sq_sqrt (by linarith only [hdsq])
  have hx2 : x ≤ 2 := by nlinarith only [hxsq,hx0,sq_nonneg d]
  have hyx : y ≤ x := by nlinarith only [hsum,hxsq,hx0,hy0]
  let W := 1+(1/q)^2+x/q
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hW4 : W ≤ 4 := by
    have hsq : (1/q)^2 ≤ 1 := by nlinarith only [hi0,hi1]
    have hmul : x/q ≤ 2 := by
      calc
        x/q = x*(1/q) := by ring
        _ ≤ 2*1 := mul_le_mul hx2 hi1 hi0 (by norm_num)
        _ = 2 := by ring
    dsimp [W]
    nlinarith only [hsq,hmul]
  have hp : ‖a-b‖*‖a-s‖ ≤ A^2+A*‖b+s‖+B*S := by
    have hid : (a-b)*(a-s) = a^2-a*(b+s)+b*s := by ring
    have hh := norm_add_le (a^2-a*(b+s)) (b*s)
    have hh' := norm_sub_le (a^2) (a*(b+s))
    rw [← hid,norm_mul,norm_mul] at hh
    simp only [norm_pow,norm_mul] at hh'
    dsimp [A,B,S]
    linarith only [hh,hh']
  have hR0 : 0 ≤ R := by dsimp [R,phaseVandermondeRatio]; positivity
  have hR : R ≤ d*W := by
    have hnormalized : (A^2+A*‖b+s‖+B*S)/(B*S) = 1+u^2*v+u*y := by
      dsimp [u,v,y]
      field_simp [hBn,hSn]
      <;> ring
    calc
      R = d*((‖a-b‖*‖a-s‖)/(B*S)) := by
        dsimp [R,phaseVandermondeRatio,d,B,S]
        rw [norm_mul,norm_mul]
        field_simp [hBn,hSn]
        <;> ring
      _ ≤ d*((A^2+A*‖b+s‖+B*S)/(B*S)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp (mul_pos hB hS).le) hd0
      _ = d*(1+u^2*v+u*y) := by rw [hnormalized]
      _ ≤ d*(1+(1/q)^2*1+(1/q)*x) := by gcongr
      _ = d*W := by dsimp [W]; ring
  by_cases hdv : v ≤ d
  · refine ⟨x,hx0,hx2,?_⟩
    have hphi : phasePhi b s = d^6 := by
      change max (d^6) (v*d^5) = d^6
      apply max_eq_left
      have hh := mul_le_mul_of_nonneg_right hdv (pow_nonneg hd0 5)
      nlinarith only [hh]
    rw [hphi]
    have hsquare : R^2 ≤ (d*W)^2 := by nlinarith only [hR,hR0,mul_nonneg hd0 hW0]
    calc
      R^2*d^6 ≤ (d*W)^2*d^6 := mul_le_mul_of_nonneg_right hsquare (pow_nonneg hd0 6)
      _ = coupledPhasePolynomial q x := by
        unfold coupledPhasePolynomial
        have he : 4-x^2 = d^2 := by linarith only [hxsq]
        rw [he]
        dsimp [W]
        ring
  · have hd1 : d ≤ 1 := (lt_of_not_ge hdv).le.trans hv1
    have hR4 : R ≤ 4 := by nlinarith only [hR,hd1,hd0,hW0,hW4]
    have hd5 : d^5 ≤ (1 : ℝ)^5 := by gcongr
    have hd6 : d^6 ≤ (1 : ℝ)^6 := by gcongr
    have hphi : phasePhi b s ≤ 1 := by
      change max (d^6) (v*d^5) ≤ 1
      apply max_le
      · simpa using hd6
      · have hh := mul_le_mul hv1 hd5 (pow_nonneg hd0 5) (by norm_num)
        simpa using hh
    have hphi0 : 0 ≤ phasePhi b s := le_trans (by positivity) (le_max_left _ _)
    have hbound : R^2*phasePhi b s ≤ (4 : ℝ)^2*1 := by gcongr
    have hconst : (16 : ℝ) ≤ coupledPhasePolynomial q 0 := by
      unfold coupledPhasePolynomial
      norm_num only [zero_pow,sub_zero,zero_div,add_zero]
      nlinarith only [sq_nonneg (1/q),sq_nonneg ((1/q)^2)]
    exact ⟨0,le_rfl,by norm_num,(by norm_num at hbound; exact hbound.trans hconst)⟩

end D1Bound5
end
