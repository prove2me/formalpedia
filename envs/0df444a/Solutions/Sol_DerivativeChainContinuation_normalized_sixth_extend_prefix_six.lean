-- Prove2me | solution 1 for DerivativeChainContinuation.normalized_sixth_extend_prefix_six
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:14:10.378721+00:00
-- url     : https://prove2.me/submissions/c88f4d12-641c-4992-8b02-32e78404a70b

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_DerivativeChainContinuation_normalized_sixth_power_actual_rows
import Theorems.Thm_DerivativeChainPrivate_normalized_sixth_selected_septic_step
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ,t∈Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0<u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u=
      TeschlQM.Herglotz.borelTransform μ u)
    (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im) (f : Fin 6 → ℂ)
    (hfroot : ∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (f i)=0)
    (hf0 : f 0=0) (hfr : Monotone (fun i => (f i).re)) (hfi : Monotone (fun i => (f i).im))
    (hfim : 0<(f 5).im) (hfX : 7/2<(f 5).re^2)
    (hfinv : β/f 5=(((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*(f 5)^2-
      (((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
      ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ,((f 5)^2-(t:ℂ))⁻¹ ∂μ)) :
    ∃ z : Fin 7 → ℂ,
      (∀ i : Fin 6,z i.castSucc=f i) ∧
      (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
      z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0<(z 6).im ∧ 4<(z 6).re^2 ∧
      β/z 6=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*(z 6)^2-
        ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder (z 6)/z 6 ∧
      (sixthSepticRemainder (z 6)).re/(z 6).re≤39/2000 ∧
      (sixthSepticRemainder (z 6)).im/(z 6).im≤0 ∧
      (3*((sixthSepticRemainder (z 6)).re/(z 6).re)-(sixthSepticRemainder (z 6)).im/(z 6).im)/2≤39/1000 ∧
      4≤(z 6).re^2-3*(z 6).im^2 := by
  have hfn : 0≤(f 5).re := by
    have hh:=hfr (show (0:Fin 6)≤5 by decide)
    simpa only [hf0,Complex.zero_re] using hh
  have hfpos : 0<(f 5).re := by nlinarith
  have hfQ : (1360/91)*β^2-20*β*(f 5)^3+(170/7)*β*(f 5)+
      (f 5)^6-5*(f 5)^4+(85/16)*(f 5)^2-1445/2184=0 := by
    have hh:=hfroot 5
    change (derivative^[12] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (f 5)=0 at hh
    rw [(normalized_sixth_power_actual_rows β (f 5)).2.2.2.2.2.2.1] at hh
    linear_combination (1/8892185702400:ℂ)*hh
  obtain ⟨w₇,hw₇,h₆₇r,h₆₇i,h₇i,h₇loc,h₇graph,h₇A,h₇B,h₇C,h₇W⟩:=
    normalized_sixth_selected_septic_step μ hsupp hμ β (f 5) hR hI hfpos hfim hfX.le hfQ hfinv
  let g : ℕ → ℂ
    | 0 => f 0
    | 1 => f 1
    | 2 => f 2
    | 3 => f 3
    | 4 => f 4
    | 5 => f 5
    | _ => w₇
  have hre : ∀ i<6,(g i).re≤(g (i+1)).re := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfr (by decide : (0:Fin 6)≤1)
    · exact hfr (by decide : (1:Fin 6)≤2)
    · exact hfr (by decide : (2:Fin 6)≤3)
    · exact hfr (by decide : (3:Fin 6)≤4)
    · exact hfr (by decide : (4:Fin 6)≤5)
    · exact h₆₇r
  have him : ∀ i<6,(g i).im≤(g (i+1)).im := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfi (by decide : (0:Fin 6)≤1)
    · exact hfi (by decide : (1:Fin 6)≤2)
    · exact hfi (by decide : (2:Fin 6)≤3)
    · exact hfi (by decide : (3:Fin 6)≤4)
    · exact hfi (by decide : (4:Fin 6)≤5)
    · exact h₆₇i
  have hrows (i : ℕ) (hi : i<7) :
      (derivative^[18-(i+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (g i)=0 := by
    interval_cases i
    · simpa [g] using hfroot 0
    · simpa [g] using hfroot 1
    · simpa [g] using hfroot 2
    · simpa [g] using hfroot 3
    · simpa [g] using hfroot 4
    · simpa [g] using hfroot 5
    · rw [(normalized_sixth_power_actual_rows β (g 6)).2.2.2.2.2.1]
      simp only [g]
      linear_combination 1270312243200*hw₇
  refine ⟨(fun i => g i.val),?_,(fun i => hrows i.val i.isLt),hf0,?_,?_,h₇i,h₇loc,h₇graph,h₇A,h₇B,h₇C,h₇W⟩
  · intro i
    fin_cases i <;> rfl
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
