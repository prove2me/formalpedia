-- Prove2me | solution 1 for DerivativeChainContinuation.normalized_sixth_extend_prefix_five
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:14:34.492544+00:00
-- url     : https://prove2.me/submissions/cf637392-5f27-444e-8676-6890d172230d

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_DerivativeChainContinuation_normalized_sixth_power_actual_rows
import Theorems.Thm_DerivativeChainPrivate_normalized_sixth_selected_sextic_step
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (f : Fin 5 → ℂ)
    (hfroot : ∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (f i)=0)
    (hf0 : f 0=0) (hfr : Monotone (fun i => (f i).re)) (hfi : Monotone (fun i => (f i).im))
    (hfpos : 0<(f 4).re) (hfX : 5/2≤(f 4).re^2)
    (hfinv : β/f 4=(1/10:ℂ)*(f 4)^2-41/140+(459/7840)/((f 4)^2-17/42)) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      (∀ᵐ t ∂μ,t∈Icc (-1/4:ℝ) (3/2)) ∧
      (∀ u : ℂ, 0 <u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u=
        TeschlQM.Herglotz.borelTransform μ u) ∧
      ∃ z : Fin 6 → ℂ,
        (∀ i : Fin 5,z i.castSucc=f i) ∧
        (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
        z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
        0<(z 5).im ∧ 7/2<(z 5).re^2 ∧
        β/z 5=(((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*(z 5)^2-
          (((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
          ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ,((z 5)^2-(t:ℂ))⁻¹ ∂μ) := by
  have hfim : 0≤(f 4).im := by
    have hh:=hfi (show (0:Fin 5)≤4 by decide)
    simpa only [hf0,Complex.zero_im] using hh
  have hfQ : (f 4)^5-(10/3)*(f 4)^3-10*β*(f 4)^2+(85/48)*(f 4)+(85/21)*β=0 := by
    have hh:=hfroot 4
    change (derivative^[13] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (f 4)=0 at hh
    rw [(normalized_sixth_power_actual_rows β (f 4)).2.2.2.2.2.2.2.1] at hh
    linear_combination (1/53353114214400:ℂ)*hh
  obtain ⟨μ,hfinite,hsupp,hμ,w₆,hw₆,h₅₆r,h₅₆i,h₆i,h₆loc,h₆graph⟩:=
    normalized_sixth_selected_sextic_step β (f 4) hR hI hfpos hfim hfX hfQ hfinv
  let g : ℕ → ℂ
    | 0 => f 0
    | 1 => f 1
    | 2 => f 2
    | 3 => f 3
    | 4 => f 4
    | _ => w₆
  have hre : ∀ i<5,(g i).re≤(g (i+1)).re := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfr (by decide : (0:Fin 5)≤1)
    · exact hfr (by decide : (1:Fin 5)≤2)
    · exact hfr (by decide : (2:Fin 5)≤3)
    · exact hfr (by decide : (3:Fin 5)≤4)
    · exact h₅₆r
  have him : ∀ i<5,(g i).im≤(g (i+1)).im := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfi (by decide : (0:Fin 5)≤1)
    · exact hfi (by decide : (1:Fin 5)≤2)
    · exact hfi (by decide : (2:Fin 5)≤3)
    · exact hfi (by decide : (3:Fin 5)≤4)
    · exact h₅₆i
  have hrows (i : ℕ) (hi : i<6) :
      (derivative^[18-(i+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (g i)=0 := by
    interval_cases i
    · simpa [g] using hfroot 0
    · simpa [g] using hfroot 1
    · simpa [g] using hfroot 2
    · simpa [g] using hfroot 3
    · simpa [g] using hfroot 4
    · rw [(normalized_sixth_power_actual_rows β (g 5)).2.2.2.2.2.2.1]
      simp only [g]
      linear_combination 8892185702400*hw₆
  refine ⟨μ,hfinite,hsupp,hμ,(fun i => g i.val),?_,(fun i => hrows i.val i.isLt),hf0,?_,?_,h₆i,h₆loc,h₆graph⟩
  · intro i
    fin_cases i <;> rfl
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
