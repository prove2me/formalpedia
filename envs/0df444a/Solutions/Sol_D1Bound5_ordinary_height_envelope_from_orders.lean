-- Prove2me | solution 1 for D1Bound5.ordinary_height_envelope_from_orders
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:25:49.689179+00:00
-- url     : https://prove2.me/submissions/7d75349c-9b08-4346-a1f0-6f87f46e6345

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_base_pos
import Theorems.Thm_D1Bound5_ordinaryLog10_lt_of_pow_lt
import Theorems.Thm_D1Bound5_ordinaryLog10_mul
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_strictMono
import Theorems.Thm_D1Bound5_ordinary_height_scalar_envelope
import Theorems.Thm_D1Bound5_ordinary_integer_orders_log_bound

section
namespace D1Bound5















theorem ordinaryLog10_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ ordinaryLog10 x :=
  div_nonneg (Real.log_nonneg hx) ordinaryLog10_base_pos.le



theorem ordinaryLog10_two_lt : ordinaryLog10 2 < (2/5 : ℝ) := by
  have h := ordinaryLog10_lt_of_pow_lt 2 2 5 (by norm_num) (by norm_num)
  norm_num at h
  linarith only [h]



end D1Bound5
end

section
namespace D1Bound5

/-- The ordinary height envelope, proved directly from all integer-order
inequalities. Its hypotheses expose precisely the analytic input; the
full-ring wrapper supplies that input from the actual Bennett matrix. -/
theorem _root_.solution
    (B C D Z R h r u : ℝ)
    (hB : 1 ≤ B) (hC : 1 < C) (hD : 0 < D) (hZ : 1 ≤ Z) (hR : 0 < R)
    (hprod : C*D < 2*Z^2)
    (hHlog : ordinaryLog10 (42*B^3*C) < ordinaryLog10 C+h)
    (hRlog : 2*ordinaryLog10 C+r < ordinaryLog10 R)
    (hUlog : ordinaryLog10 (253*B^2) < u)
    (hxt : h-r < ordinaryLog10 C) (hx2 : 0 < 2*ordinaryLog10 C+r)
    (horders : ∀ k : ℕ, 1 ≤ k →
      1 < 3*C*(42*B^3*C)^k/(B*Z)+Z/(2*R^k)) :
    ordinaryLog10 D < 7*ordinaryLog10 C+(4*u+8*h-4*r)+
      (2*u*r+(4*u+8*h-4*r)*(h-r))/(ordinaryLog10 C-(h-r))+(2/5 : ℝ) := by
  let H := 42*B^3*C
  let X := 3*C/B
  let x := ordinaryLog10 C
  let z := ordinaryLog10 Z
  let p := ordinaryLog10 R
  let q := ordinaryLog10 H
  let L := Real.log (10 : ℝ)
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hC0 : 0 < C := lt_trans (by norm_num) hC
  have hZ0 : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hL : 0 < L := ordinaryLog10_base_pos
  have hB3 : (1 : ℝ) ≤ B^3 := by
    calc
      1 = (1 : ℝ)^3 := by norm_num
      _ ≤ B^3 := by gcongr
  have hH : 1 ≤ H := by
    calc
      1 ≤ (42 : ℝ)*1*1 := by norm_num
      _ ≤ H := by dsimp [H]; gcongr
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hX : 0 < X := by dsimp [X]; positivity
  have hp0 : 0 < p := hx2.trans hRlog
  have hlR : 0 < Real.log R := by
    have hh := (lt_div_iff₀ hL).mp hp0
    simpa only [zero_mul] using hh
  have hR1 : 1 < R := (Real.log_pos_iff hR.le).mp hlR
  have hi := ordinary_integer_orders_log_bound H R Z X hH hR1 hZ hX
    (by
      intro k hk
      have heq : X*H^k/Z = 3*C*H^k/(B*Z) := by
        dsimp [X]
        field_simp [hB0.ne',hZ0.ne'] <;> ring
      rw [heq]
      exact horders k hk)
  have hscaled : z*(p-q) < (Real.log (2*X*H)/L)*p := by
    change (Real.log Z / L) * (Real.log R / L - Real.log H / L) <
      (Real.log (2*X*H) / L) * (Real.log R / L)
    calc
      (Real.log Z / L) * (Real.log R / L - Real.log H / L) =
          (Real.log Z * (Real.log R - Real.log H)) / L^2 := by
            rw [← sub_div, div_mul_div_comm, pow_two]
      _ < (Real.log (2*X*H) * Real.log R) / L^2 :=
        div_lt_div_of_pos_right hi (sq_pos_of_pos hL)
      _ = _ := by rw [div_mul_div_comm, pow_two]
  have hnumid : 2*X*H = 252*B^2*C^2 := by
    dsimp [X,H]
    field_simp [hB0.ne'] <;> ring
  have hnumlt : 2*X*H < 253*B^2*C^2 := by
    rw [hnumid]
    have hh := mul_pos (sq_pos_of_pos hB0) (sq_pos_of_pos hC0)
    nlinarith only [hh]
  have hnumlog : Real.log (2*X*H)/L < 2*x+u := by
    have hh := ordinaryLog10_strictMono (by positivity : 0 < 2*X*H) hnumlt
    rw [ordinaryLog10_mul (253*B^2) (C^2) (by positivity) (by positivity),
      ordinaryLog10_pow] at hh
    change ordinaryLog10 (2*X*H) < 2*ordinaryLog10 C+u
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,hUlog]
  have hbound : z*(p-q) < (2*x+u)*p :=
    hscaled.trans (mul_lt_mul_of_pos_right hnumlog hp0)
  have hdlog : ordinaryLog10 D < (2/5 : ℝ)-x+2*z := by
    have hh := ordinaryLog10_strictMono (mul_pos hC0 hD) hprod
    rw [ordinaryLog10_mul C D hC0.ne' hD.ne',
      ordinaryLog10_mul 2 (Z^2) (by norm_num) (by positivity),
      ordinaryLog10_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have htwo := ordinaryLog10_two_lt
    change ordinaryLog10 D < (2/5 : ℝ)-ordinaryLog10 C+2*ordinaryLog10 Z
    linarith only [hh,htwo]
  exact ordinary_height_scalar_envelope x z (ordinaryLog10 D) p q h r u
    (ordinaryLog10_nonneg hZ) (ordinaryLog10_nonneg hH)
    hRlog hx2 hHlog hxt hbound hdlog

end D1Bound5
end
