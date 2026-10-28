-- Prove2me | solution 1 for D1Bound5.nearHalf_offDiagonal_cofactor_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:13.983998+00:00
-- url     : https://prove2.me/submissions/8f3fa629-b70e-43c3-a288-1e0fc4a4e809

import Lean.Util.CollectAxioms
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- A precise off-diagonal cofactor estimate for six complex entries near 1/2. -/
theorem _root_.solution (x y z u v w : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hu : ‖u - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hv : ‖v - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hw : ‖w - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖w^2*x - w*z*u - w*y*v + (1/8 : ℂ)‖ < (197/10000 : ℝ) := by
  let ε : ℝ := 128/8649
  let a : ℂ := x - 1/2
  let b : ℂ := z - 1/2
  let c : ℂ := u - 1/2
  let d : ℂ := y - 1/2
  let e : ℂ := v - 1/2
  let f : ℂ := w - 1/2
  have hε : 0 ≤ ε := by norm_num [ε]
  have ha : ‖a‖ ≤ ε := hx.le
  have hb : ‖b‖ ≤ ε := hz.le
  have hc : ‖c‖ ≤ ε := hu.le
  have hd : ‖d‖ ≤ ε := hy.le
  have he : ‖e‖ ≤ ε := hv.le
  have hf : ‖f‖ ≤ ε := hw.le
  have hpair (r s : ℂ) (hr : ‖r‖ ≤ ε) (hs : ‖s‖ ≤ ε) :
      ‖r*s‖ ≤ ε^2 := by
    rw [norm_mul]
    calc
      ‖r‖ * ‖s‖ ≤ ε * ‖s‖ :=
        mul_le_mul_of_nonneg_right hr (norm_nonneg _)
      _ ≤ ε * ε := mul_le_mul_of_nonneg_left hs hε
      _ = ε^2 := by ring
  let B : ℂ := a-b-c-d-e
  let C : ℂ := a-(b+c+d+e)/2
  let D : ℂ := f^2-b*c-d*e
  let T : ℂ := a*f-b*c-d*e
  have hB : ‖B‖ ≤ 5*ε := by
    have h1 := norm_sub_le a b
    have h2 := norm_sub_le (a-b) c
    have h3 := norm_sub_le (a-b-c) d
    have h4 := norm_sub_le (a-b-c-d) e
    dsimp [B]
    linarith only [h1,h2,h3,h4,ha,hb,hc,hd,he]
  have hC : ‖C‖ ≤ 3*ε := by
    have h1 := norm_add_le b c
    have h2 := norm_add_le (b+c) d
    have h3 := norm_add_le (b+c+d) e
    have h4 := norm_sub_le a ((b+c+d+e)/2)
    have h5 : ‖(b+c+d+e)/2‖ = ‖b+c+d+e‖/2 := by
      simp [norm_div]
    have hs : ‖b+c+d+e‖ ≤ 4*ε := by
      linarith only [h1,h2,h3,hb,hc,hd,he]
    have hhalf : ‖(b+c+d+e)/2‖ ≤ 2*ε := by
      rw [h5]
      calc
        ‖b+c+d+e‖/2 ≤ (4*ε)/2 :=
          div_le_div_of_nonneg_right hs (by norm_num)
        _ = 2*ε := by ring
    change ‖a-(b+c+d+e)/2‖ ≤ 3*ε
    calc
      _ ≤ ‖a‖ + ‖(b+c+d+e)/2‖ := norm_sub_le _ _
      _ ≤ ε + 2*ε := add_le_add ha hhalf
      _ = 3*ε := by ring
  have hD : ‖D‖ ≤ 3*ε^2 := by
    have h1 := norm_sub_le (f^2-b*c) (d*e)
    have h2 := norm_sub_le (f^2) (b*c)
    have hf2 : ‖f^2‖ ≤ ε^2 := by
      calc
        ‖f^2‖ = ‖f*f‖ := by ring
        _ ≤ ε^2 := hpair f f hf hf
    have hbc := hpair b c hb hc
    have hde := hpair d e hd he
    dsimp [D]
    linarith only [h1,h2,hf2,hbc,hde]
  have hT : ‖T‖ ≤ 3*ε^2 := by
    have h1 := norm_sub_le (a*f-b*c) (d*e)
    have h2 := norm_sub_le (a*f) (b*c)
    have haf := hpair a f ha hf
    have hbc := hpair b c hb hc
    have hde := hpair d e hd he
    dsimp [T]
    linarith only [h1,h2,haf,hbc,hde]
  have hfC : ‖f*C‖ ≤ 3*ε^2 := by
    rw [norm_mul]
    calc
      ‖f‖*‖C‖ ≤ ε*‖C‖ :=
        mul_le_mul_of_nonneg_right hf (norm_nonneg _)
      _ ≤ ε*(3*ε) := mul_le_mul_of_nonneg_left hC hε
      _ = 3*ε^2 := by ring
  have hfT : ‖f*T‖ ≤ 3*ε^3 := by
    rw [norm_mul]
    calc
      ‖f‖*‖T‖ ≤ ε*‖T‖ :=
        mul_le_mul_of_nonneg_right hf (norm_nonneg _)
      _ ≤ ε*(3*ε^2) := mul_le_mul_of_nonneg_left hT hε
      _ = 3*ε^3 := by ring
  have hid : w^2*x - w*z*u - w*y*v + (1/8 : ℂ) =
      B/4 + f*C + D/2 + f*T := by
    dsimp [B,C,D,T,a,b,c,d,e,f]
    ring
  have htri : ‖B/4 + f*C + D/2 + f*T‖ ≤
      ‖B/4‖ + ‖f*C‖ + ‖D/2‖ + ‖f*T‖ := by
    have h1 := norm_add_le (B/4+f*C+D/2) (f*T)
    have h2 := norm_add_le (B/4+f*C) (D/2)
    have h3 := norm_add_le (B/4) (f*C)
    linarith only [h1,h2,h3]
  have hB4 : ‖B/4‖ = ‖B‖ / 4 := by simp [norm_div]
  have hD2 : ‖D/2‖ = ‖D‖ / 2 := by simp [norm_div]
  have hn : (5*ε/4 + 3*ε^2 + (3*ε^2)/2 + 3*ε^3 : ℝ) <
      197/10000 := by norm_num [ε]
  have hb4 : ‖B‖/4 ≤ (5*ε)/4 :=
    div_le_div_of_nonneg_right hB (by norm_num)
  have hd2 : ‖D‖/2 ≤ (3*ε^2)/2 :=
    div_le_div_of_nonneg_right hD (by norm_num)
  have hupper : ‖B‖/4 + ‖f*C‖ + ‖D‖/2 + ‖f*T‖ ≤
      (5*ε)/4 + 3*ε^2 + (3*ε^2)/2 + 3*ε^3 := by
    calc
      _ = (‖B‖/4 + ‖f*C‖) + (‖D‖/2 + ‖f*T‖) := by ring
      _ ≤ ((5*ε)/4 + 3*ε^2) + ((3*ε^2)/2 + 3*ε^3) :=
        add_le_add (add_le_add hb4 hfC) (add_le_add hd2 hfT)
      _ = (5*ε)/4 + 3*ε^2 + (3*ε^2)/2 + 3*ε^3 := by ring
  rw [hid]
  rw [hB4,hD2] at htri
  exact lt_of_le_of_lt (le_trans htri hupper) hn

end D1Bound5
end
