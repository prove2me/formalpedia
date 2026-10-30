-- Prove2me | solution 1 for DerivativeChainContinuation.normalized_sixth_extend_prefix_seven
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:18:55.382443+00:00
-- url     : https://prove2.me/submissions/10c0d34d-c0f6-4b45-9fab-297a7305feb5

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_normalized_sixth_power_actual_rows
import Theorems.Thm_DerivativeChainPrivate_normalized_sixth_octic_step_with_bounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im) (f : Fin 7 → ℂ)
    (hfroot : ∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (f i)=0)
    (hf0 : f 0=0) (hfr : Monotone (fun i => (f i).re)) (hfi : Monotone (fun i => (f i).im))
    (hfim : 0<(f 6).im) (hfX : 4<(f 6).re^2)
    (hfinv : β/f 6=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*(f 6)^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder (f 6)/f 6) :
    ∃ z : Fin 8 → ℂ,
      (∀ i : Fin 7,z i.castSucc=f i) ∧
      (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
      z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0<(z 7).im ∧ 26/5<(z 7).re^2 ∧
      β/z 7=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*(z 7)^2-
        ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder (z 7)/z 7 ∧
      (sixthOcticRemainder (z 7)).re/(z 7).re≤9/1000 ∧
      (sixthOcticRemainder (z 7)).im/(z 7).im≤0 ∧
      (3*((sixthOcticRemainder (z 7)).re/(z 7).re)-(sixthOcticRemainder (z 7)).im/(z 7).im)/2≤73/4000 ∧
      26/5≤(z 7).re^2-3*(z 7).im^2 := by
  have hfn : 0≤(f 6).re := by
    have hh:=hfr (show (0:Fin 7)≤6 by decide)
    simpa only [hf0,Complex.zero_re] using hh
  have hfpos : 0<(f 6).re := by nlinarith
  have hfQ : (1360/13)*β^2*(f 6)-35*β*(f 6)^4+85*β*(f 6)^2-(1445/78)*β+
      (f 6)^7-7*(f 6)^5+(595/48)*(f 6)^3-(1445/312)*(f 6)=0 := by
    have hh:=hfroot 6
    change (derivative^[11] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (f 6)=0 at hh
    rw [(normalized_sixth_power_actual_rows β (f 6)).2.2.2.2.2.1] at hh
    linear_combination (1/1270312243200:ℂ)*hh
  obtain ⟨w₈,hw₈,h₇₈r,h₇₈i,h₈i,h₈loc,h₈graph,h₈A,h₈B,h₈C,h₈W⟩:=
    normalized_sixth_octic_step_with_bounds β (f 6) hR hI hfpos hfim hfX.le hfQ hfinv
  let g : ℕ → ℂ
    | 0 => f 0
    | 1 => f 1
    | 2 => f 2
    | 3 => f 3
    | 4 => f 4
    | 5 => f 5
    | 6 => f 6
    | _ => w₈
  have hre : ∀ i<7,(g i).re≤(g (i+1)).re := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfr (by decide : (0:Fin 7)≤1)
    · exact hfr (by decide : (1:Fin 7)≤2)
    · exact hfr (by decide : (2:Fin 7)≤3)
    · exact hfr (by decide : (3:Fin 7)≤4)
    · exact hfr (by decide : (4:Fin 7)≤5)
    · exact hfr (by decide : (5:Fin 7)≤6)
    · exact h₇₈r
  have him : ∀ i<7,(g i).im≤(g (i+1)).im := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfi (by decide : (0:Fin 7)≤1)
    · exact hfi (by decide : (1:Fin 7)≤2)
    · exact hfi (by decide : (2:Fin 7)≤3)
    · exact hfi (by decide : (3:Fin 7)≤4)
    · exact hfi (by decide : (4:Fin 7)≤5)
    · exact hfi (by decide : (5:Fin 7)≤6)
    · exact h₇₈i
  have hrows (i : ℕ) (hi : i<8) :
      (derivative^[18-(i+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (g i)=0 := by
    interval_cases i
    · simpa [g] using hfroot 0
    · simpa [g] using hfroot 1
    · simpa [g] using hfroot 2
    · simpa [g] using hfroot 3
    · simpa [g] using hfroot 4
    · simpa [g] using hfroot 5
    · simpa [g] using hfroot 6
    · rw [(normalized_sixth_power_actual_rows β (g 7)).2.2.2.2.1]
      simp only [g]
      linear_combination 158789030400*hw₈
  refine ⟨(fun i => g i.val),?_,(fun i => hrows i.val i.isLt),hf0,?_,?_,h₈i,h₈loc,h₈graph,h₈A,h₈B,h₈C,h₈W⟩
  · intro i
    fin_cases i <;> rfl
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
