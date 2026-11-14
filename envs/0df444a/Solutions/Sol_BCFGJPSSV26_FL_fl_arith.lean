-- Prove2me | solution 1 for BCFGJPSSV26.FL.fl_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:51.429557+00:00
-- url     : https://prove2.me/submissions/b9b01f8d-0468-4915-abba-0fd06a040021

module

public import Definitions.Def_BCFGJPSSV26_FL_Select
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_FL_Run
import all Definitions.Def_BCFGJPSSV26_FL_Run

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

/-- **The arithmetic of the guarantee**: from the robust LMP guarantee in the scaled space, with
`cost / t + n` for the costs, `f̂ = λ (1 - δ) f / t` and `n t ≤ d_min / 10⁵ ≤ cost(O) / 10⁵`. -/
theorem fl_arith {t A B cs co s sl o f fh dm n : ℚ} (ht : 0 < t) (hf : 0 ≤ f)
    (hfh : fh = lmpC * (1 - δ0) * f / t) (hA : cs / t + n ≤ A) (hB : B = co / t + n)
    (hsl : sl ≤ s) (hnt : n * t ≤ dm / cS) (hdm0 : 0 < dm) (hdm : dm ≤ co)
    (hlmp : (1 - δ0) * A + s * fh ≤ (ρ + 6 * δ0) * B + o * fh + s * n * 0) :
    cs + lmpC * f * sl ≤ lmpC * (co + f * o) := by
  have hfh0 : 0 ≤ fh := by
    rw [hfh]
    unfold lmpC δ0
    have := ht.le
    positivity
  have h1 : sl * fh ≤ s * fh := mul_le_mul_of_nonneg_right hsl hfh0
  rw [ρ_eq] at hlmp
  have h2 : (1 - δ0) * (cs / t + n) + sl * fh ≤
      (30466 / 15625 + 6 * δ0) * (co / t + n) + o * fh := by
    rw [← hB]
    unfold δ0 at hlmp ⊢
    linarith
  have ht0 := ht.ne'
  have e1 : ((1 - δ0) * (cs / t + n) + sl * fh) * t =
      (1 - δ0) * (cs + n * t) + lmpC * (1 - δ0) * f * sl := by
    rw [hfh]
    field_simp
  have e2 : ((30466 / 15625 + 6 * δ0) * (co / t + n) + o * fh) * t =
      (30466 / 15625 + 6 * δ0) * (co + n * t) + lmpC * (1 - δ0) * f * o := by
    rw [hfh]
    field_simp
  have h3 := mul_le_mul_of_nonneg_right h2 ht.le
  rw [e1, e2] at h3
  have h4 : n * t ≤ co / cS := hnt.trans (div_le_div_of_nonneg_right hdm (by norm_num [cS]))
  unfold lmpC δ0 cS at *
  linarith

end BCFGJPSSV26.FL

end

public section

theorem solution : type_of% @BCFGJPSSV26.FL.fl_arith := @BCFGJPSSV26.FL.fl_arith
