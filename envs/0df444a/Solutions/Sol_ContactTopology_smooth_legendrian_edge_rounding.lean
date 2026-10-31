-- Prove2me | solution 1 for ContactTopology.smooth_legendrian_edge_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T01:27:54.807085+00:00
-- url     : https://prove2.me/submissions/c722eca4-8728-45bd-b276-929fbdfd3f35

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order.IntermediateValue



namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
abbrev V := Fin 3 → ℝ

def coeff (freq : ℝ) (y : V) : V := ![Real.sin (freq*y 2),Real.cos (freq*y 2),0]
def α (freq : ℝ) (y v : V) : ℝ := Real.sin (freq*y 2)*v 0+Real.cos (freq*y 2)*v 1
def field (r : ℝ) (y : V) : V := ![y 0-r,y 1-r,0]
def flow (r t : ℝ) (y : V) : V :=
  ![r+Real.exp t*(y 0-r),r+Real.exp t*(y 1-r),y 2]
def rounded (r : ℝ) (p : ℝ × ℝ) : V :=
  ![r*(1-Real.cos p.1),r*(1-Real.sin p.1),p.2]

def curve (freq r : ℝ) (k : ℤ) (θ : ℝ) : V := rounded r (θ,k*Real.pi/freq-θ/freq)

lemma coeff_smooth (freq : ℝ) : ContDiff ℝ ∞ (coeff freq) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coeff] <;> fun_prop
lemma field_smooth (r : ℝ) : ContDiff ℝ ∞ (field r) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [field] <;> fun_prop
lemma flow_smooth (r : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × V => flow r p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [flow] <;> fun_prop
lemma rounded_smooth (r : ℝ) : ContDiff ℝ ∞ (rounded r) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [rounded] <;> fun_prop

lemma coeff_fderiv (freq : ℝ) (y v : V) :
    fderiv ℝ (coeff freq) y v=
      ![freq*Real.cos (freq*y 2)*v 2,-freq*Real.sin (freq*y 2)*v 2,0] := by
  let e : V →L[ℝ] ℝ := ContinuousLinearMap.proj 2
  have hsin := ((e.hasFDerivAt (x := y)).const_mul freq).sin
  have hcos := ((e.hasFDerivAt (x := y)).const_mul freq).cos
  have hD : HasFDerivAt (coeff freq) (ContinuousLinearMap.pi
      ![Real.cos (freq*y 2) • (freq • e),-Real.sin (freq*y 2) • (freq • e),0]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hsin
    · exact hcos
    · exact hasFDerivAt_const (0:ℝ) y
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp [e] <;> ring

lemma field_fderiv (r : ℝ) (y v : V) : fderiv ℝ (field r) y v=![v 0,v 1,0] := by
  have hD : HasFDerivAt (field r) (ContinuousLinearMap.pi
      ![(ContinuousLinearMap.proj (0:Fin 3) : V →L[ℝ] ℝ),ContinuousLinearMap.proj (1:Fin 3),0]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (ContinuousLinearMap.proj (0:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt.sub_const r
    · exact (ContinuousLinearMap.proj (1:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt.sub_const r
    · exact hasFDerivAt_const (0:ℝ) y
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp

lemma flow_fderiv (r t : ℝ) (y v : V) :
    fderiv ℝ (flow r t) y v=![Real.exp t*v 0,Real.exp t*v 1,v 2] := by
  have hD : HasFDerivAt (flow r t) (ContinuousLinearMap.pi
      ![Real.exp t • (ContinuousLinearMap.proj (0:Fin 3) : V →L[ℝ] ℝ),Real.exp t • ContinuousLinearMap.proj (1:Fin 3),
        ContinuousLinearMap.proj (2:Fin 3)]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (((ContinuousLinearMap.proj (0:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt.sub_const r).const_mul
        (Real.exp t)).const_add r
    · exact (((ContinuousLinearMap.proj (1:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt.sub_const r).const_mul
        (Real.exp t)).const_add r
    · exact (ContinuousLinearMap.proj (2:Fin 3) : V →L[ℝ] ℝ).hasFDerivAt
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp

lemma rounded_fderiv (r : ℝ) (p v : ℝ × ℝ) :
    fderiv ℝ (rounded r) p v=![r*Real.sin p.1*v.1,-r*Real.cos p.1*v.1,v.2] := by
  have hD : HasFDerivAt (rounded r) (ContinuousLinearMap.pi
      ![(r*Real.sin p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ,
        (-r*Real.cos p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ,
        ContinuousLinearMap.snd ℝ ℝ ℝ]) p := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · have hh := ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) p).sub
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).cos).const_mul r
      convert! hh using 1 <;> ext w <;> simp <;> ring
    · have hh := ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) p).sub
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).sin).const_mul r
      convert! hh using 1 <;> ext w <;> simp <;> ring
    · exact hasFDerivAt_snd
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp

lemma contact_volume (freq : ℝ) (y : V) :
    coeff freq y 0*(fderiv ℝ (coeff freq) y (Pi.single 1 1) 2-fderiv ℝ (coeff freq) y (Pi.single 2 1) 1)+
      coeff freq y 1*(fderiv ℝ (coeff freq) y (Pi.single 2 1) 0-fderiv ℝ (coeff freq) y (Pi.single 0 1) 2)+
      coeff freq y 2*(fderiv ℝ (coeff freq) y (Pi.single 0 1) 1-fderiv ℝ (coeff freq) y (Pi.single 1 1) 0)=freq := by
  simp [coeff_fderiv,coeff]
  linear_combination freq * Real.sin_sq_add_cos_sq (freq*y 2)

lemma field_contact (freq r : ℝ) (y v : V) :
    (fderiv ℝ (coeff freq) y (field r y)) 0*v 0+
      (fderiv ℝ (coeff freq) y (field r y)) 1*v 1+
      (fderiv ℝ (coeff freq) y (field r y)) 2*v 2+
      α freq y (fderiv ℝ (field r) y v)=α freq y v := by
  simp [coeff_fderiv,field,field_fderiv,α]

lemma flow_contact (freq r t : ℝ) (y v : V) :
    α freq (flow r t y) (fderiv ℝ (flow r t) y v)=Real.exp t*α freq y v := by
  simp [flow,flow_fderiv,α]
  ring

lemma flow_zero (r : ℝ) (y : V) : flow r 0 y=y := by
  ext i
  fin_cases i <;> simp [flow]
lemma flow_inverse (r t : ℝ) (y : V) : flow r (-t) (flow r t y)=y := by
  ext i
  fin_cases i <;> simp [flow,Real.exp_neg]

lemma flow_velocity (r t : ℝ) (y : V) :
    HasDerivAt (fun s => flow r s y) (field r (flow r t y)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert ((Real.hasDerivAt_exp t).mul_const (y 0-r)).const_add r using 1 <;> simp [flow,field]
  · convert ((Real.hasDerivAt_exp t).mul_const (y 1-r)).const_add r using 1 <;> simp [flow,field]
  · exact hasDerivAt_const t (y 2)

lemma rounded_immersion (r : ℝ) (hr : 0 < r) (p : ℝ × ℝ) :
    Injective (fderiv ℝ (rounded r) p) := by
  intro v w h
  rw [rounded_fderiv,rounded_fderiv] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 : v.2=w.2 := congrFun h 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  have he : v.1=w.1 := by
    by_cases hs : Real.sin p.1=0
    · have hc : Real.cos p.1 ≠ 0 := by intro hc; have hi := Real.sin_sq_add_cos_sq p.1; simp [hs,hc] at hi
      exact mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr hr.ne') hc) h1
    · exact mul_left_cancel₀ (mul_ne_zero hr.ne' hs) h0
  exact Prod.ext he h2

lemma rounded_injOn (r : ℝ) (hr : 0 < r) :
    InjOn (rounded r) (Icc (0:ℝ) (Real.pi/2) ×ˢ (univ:Set ℝ)) := by
  rintro ⟨θ,z⟩ ⟨hθ,hz⟩ ⟨η,w⟩ ⟨hη,hw⟩ heq
  have hsin : Real.sin θ=Real.sin η := by
    have hh := congrFun heq 1
    simp [rounded] at hh
    exact hh.resolve_right hr.ne'
  have hθ' : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2) := ⟨(show -(Real.pi/2) ≤ 0 by linarith [Real.pi_pos]).trans hθ.1,hθ.2⟩
  have hη' : η ∈ Icc (-(Real.pi/2)) (Real.pi/2) := ⟨(show -(Real.pi/2) ≤ 0 by linarith [Real.pi_pos]).trans hη.1,hη.2⟩
  exact Prod.ext (Real.strictMonoOn_sin.injOn hθ' hη' hsin) (congrFun heq 2)

lemma rounded_transverse (r : ℝ) (hr : 0 < r) (p v : ℝ × ℝ) :
    field r (rounded r p) ≠ fderiv ℝ (rounded r) p v := by
  intro heq
  rw [rounded_fderiv] at heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  simp only [rounded,field,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  have hs := Real.sin_sq_add_cos_sq p.1
  have hh : r=0 := by
    linear_combination -Real.cos p.1*h0-Real.sin p.1*h1-r*hs
  linarith

lemma rounded_contact_value (freq r : ℝ) (p : ℝ × ℝ) :
    α freq (rounded r p) (field r (rounded r p)) = -r*Real.sin (freq*p.2+p.1) := by
  simp [α,rounded,field,Real.sin_add]
  ring

lemma rounded_dividing_iff (freq r : ℝ) (hfreq : 0 < freq) (hr : 0 < r) (p : ℝ × ℝ) :
    α freq (rounded r p) (field r (rounded r p))=0 ↔
      ∃ k : ℤ, p.2=k*Real.pi/freq-p.1/freq := by
  rw [rounded_contact_value,mul_eq_zero]
  simp only [neg_eq_zero,hr.ne',false_or,Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [← sub_div]
    apply (eq_div_iff hfreq.ne').mpr
    linarith
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [hk]
    field_simp [hfreq.ne']
    ring

end
end ContactTopology.EdgeRounding



namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology Interval
set_option backward.isDefEq.respectTransparency false
noncomputable section

def bendAngle (s : ℝ) : ℝ := Real.pi/2*Real.smoothTransition s
def speed (s : ℝ) : ℝ := Real.sin (bendAngle s)
def bendX (s : ℝ) : ℝ := ∫ t in (0:ℝ)..s, speed t
def bendC : ℝ := bendX 1

lemma bendAngle_smooth : ContDiff ℝ ∞ bendAngle :=
  contDiff_const.mul Real.smoothTransition.contDiff
lemma speed_smooth : ContDiff ℝ ∞ speed := bendAngle_smooth.sin
lemma transition_reflect (s : ℝ) : Real.smoothTransition (1-s)=1-Real.smoothTransition s := by
  unfold Real.smoothTransition
  rw [show 1-(1-s)=s by ring]
  field_simp [(Real.smoothTransition.pos_denom s).ne',
    show expNegInvGlue (1-s)+expNegInvGlue s ≠ 0 by
      simpa only [add_comm] using (Real.smoothTransition.pos_denom s).ne']
  ring
lemma bendAngle_reflect (s : ℝ) : bendAngle (1-s)=Real.pi/2-bendAngle s := by
  simp only [bendAngle,transition_reflect]
  ring
lemma speed_reflect (s : ℝ) : speed (1-s)=Real.cos (bendAngle s) := by
  rw [speed,bendAngle_reflect,Real.sin_pi_div_two_sub]
lemma speed_sq (s : ℝ) : speed s^2+speed (1-s)^2=1 := by
  rw [speed_reflect]
  exact Real.sin_sq_add_cos_sq _
lemma bendAngle_mem (s : ℝ) : bendAngle s ∈ Icc (0:ℝ) (Real.pi/2) := by
  constructor
  · exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg s)
  · exact mul_le_of_le_one_right (by positivity) (Real.smoothTransition.le_one s)
lemma speed_nonneg (s : ℝ) : 0 ≤ speed s :=
  Real.sin_nonneg_of_nonneg_of_le_pi (bendAngle_mem s).1
    ((bendAngle_mem s).2.trans (by linarith [Real.pi_pos]))
lemma speed_pos (s : ℝ) (hs : 0 < s) : 0 < speed s := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (by positivity) (Real.smoothTransition.pos_of_pos hs)
  · exact lt_of_le_of_lt (bendAngle_mem s).2 (by linarith [Real.pi_pos])
lemma speed_zero (s : ℝ) (hs : s ≤ 0) : speed s=0 := by
  simp [speed,bendAngle,Real.smoothTransition.zero_of_nonpos hs]
lemma speed_one (s : ℝ) (hs : 1 ≤ s) : speed s=1 := by
  simp [speed,bendAngle,Real.smoothTransition.one_of_one_le hs]
lemma bendX_deriv (s : ℝ) : HasDerivAt bendX (speed s) s :=
  intervalIntegral.integral_hasDerivAt_right (speed_smooth.continuous.intervalIntegrable 0 s)
    speed_smooth.continuous.stronglyMeasurable.stronglyMeasurableAtFilter speed_smooth.continuous.continuousAt
@[fun_prop] lemma bendX_smooth : ContDiff ℝ ∞ bendX := by
  rw [contDiff_infty]
  intro n
  cases n with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr (fun s => (bendX_deriv s).continuousAt))
  | succ n =>
    have hd : deriv bendX=speed := funext (fun s => (bendX_deriv s).deriv)
    apply (contDiff_succ_iff_deriv (𝕜 := ℝ) (f := bendX) (n := (n:ℕ∞ω))).mpr
    refine ⟨fun s => (bendX_deriv s).differentiableAt,by simp,?_⟩
    rw [hd]
    exact speed_smooth.of_le (by exact_mod_cast le_top)
lemma bendX_zero : bendX 0=0 := by simp [bendX]
lemma bendX_mono : Monotone bendX :=
  monotone_of_deriv_nonneg (fun s => (bendX_deriv s).differentiableAt)
    (fun s => by rw [(bendX_deriv s).deriv]; exact speed_nonneg s)
lemma bendX_strict : StrictMonoOn bendX (Ici (0:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) bendX_smooth.continuous.continuousOn
  intro s hs
  rw [(bendX_deriv s).deriv]
  apply speed_pos
  simpa only [interior_Ici,mem_Ioi] using hs
lemma bendC_pos : 0 < bendC := by
  have hh := bendX_strict (show (0:ℝ) ∈ Ici 0 by simp) (show (1:ℝ) ∈ Ici 0 by norm_num) zero_lt_one
  simpa only [bendX_zero,bendC] using hh
lemma bendX_nonpos (s : ℝ) (hs : s ≤ 0) : bendX s=0 := by
  change (∫ t in (0:ℝ)..s, speed t)=0
  calc
    (∫ t in (0:ℝ)..s, speed t)=(∫ t in (0:ℝ)..s, (0:ℝ)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hs] at ht
      exact speed_zero t ht.2
    _=0 := by simp

lemma bendX_one_le (s : ℝ) (hs : 1 ≤ s) : bendX s=bendC+s-1 := by
  have heq : (∫ t in (1:ℝ)..s, speed t)=s-1 := by
    calc
      (∫ t in (1:ℝ)..s, speed t)=(∫ t in (1:ℝ)..s, (1:ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs] at ht
        exact speed_one t ht.1
      _=s-1 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (speed_smooth.continuous.intervalIntegrable (μ := MeasureTheory.volume) (0:ℝ) 1)
    (speed_smooth.continuous.intervalIntegrable (μ := MeasureTheory.volume) (1:ℝ) s)
  change bendC+(∫ t in (1:ℝ)..s, speed t)=bendX s at hadd
  rw [heq] at hadd
  linarith
lemma bendX_nonneg (s : ℝ) : 0 ≤ bendX s := by
  by_cases hs : s ≤ 0
  · rw [bendX_nonpos s hs]
  · simpa only [bendX_zero] using bendX_mono (le_of_not_ge hs)
lemma bendX_lt (s : ℝ) (hs : s < 1) : bendX s < bendC := by
  by_cases hz : s ≤ 0
  · rw [bendX_nonpos s hz]; exact bendC_pos
  · exact bendX_strict (le_of_not_ge hz) (show (1:ℝ) ∈ Ici 0 by norm_num) hs

def flatRounded (r : ℝ) (p : ℝ × ℝ) : V := ![r*bendX p.1,r*bendX (1-p.1),p.2]
lemma flatRounded_smooth (r : ℝ) : ContDiff ℝ ∞ (flatRounded r) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [flatRounded] <;> fun_prop

end
end ContactTopology.EdgeRounding


namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma flatRounded_fderiv (r : ℝ) (p v : ℝ × ℝ) :
    fderiv ℝ (flatRounded r) p v=![r*speed p.1*v.1,-r*speed (1-p.1)*v.1,v.2] := by
  have hD : HasFDerivAt (flatRounded r) (ContinuousLinearMap.pi
      ![(r*speed p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ,
        (-r*speed (1-p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ,
        ContinuousLinearMap.snd ℝ ℝ ℝ]) p := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! ((bendX_deriv p.1).comp_hasFDerivAt p
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).const_mul r using 1 <;> ext w <;> simp
    · convert! ((bendX_deriv (1-p.1)).comp_hasFDerivAt p
        ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) p).sub hasFDerivAt_fst)).const_mul r using 1 <;>
        ext w <;> simp <;> ring
    · exact hasFDerivAt_snd
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp

lemma flatRounded_immersion (r : ℝ) (hr : 0 < r) (p : ℝ × ℝ) :
    Injective (fderiv ℝ (flatRounded r) p) := by
  intro v w h
  rw [flatRounded_fderiv,flatRounded_fderiv] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 : v.2=w.2 := congrFun h 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  have he : v.1=w.1 := by
    by_cases hs : speed p.1=0
    · have hc : speed (1-p.1) ≠ 0 := by intro hc; have hi := speed_sq p.1; simp [hs,hc] at hi
      exact mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr hr.ne') hc) h1
    · exact mul_left_cancel₀ (mul_ne_zero hr.ne' hs) h0
  exact Prod.ext he h2

lemma bend_difference_deriv (s : ℝ) : HasDerivAt (fun t => bendX t-bendX (1-t))
    (speed s+speed (1-s)) s := by
  convert! (bendX_deriv s).sub ((bendX_deriv (1-s)).comp s
    ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s))) using 1 <;> simp
lemma bend_difference_strict : StrictMono (fun s => bendX s-bendX (1-s)) := by
  apply strictMono_of_deriv_pos
  intro s
  rw [(bend_difference_deriv s).deriv]
  have hs := speed_sq s
  have ha := speed_nonneg s
  have hb := speed_nonneg (1-s)
  nlinarith
lemma flatRounded_injective (r : ℝ) (hr : 0 < r) : Injective (flatRounded r) := by
  rintro ⟨s,z⟩ ⟨t,w⟩ heq
  have h0 : r*bendX s=r*bendX t := congrFun heq 0
  have h1 : r*bendX (1-s)=r*bendX (1-t) := congrFun heq 1
  have h2 : z=w := congrFun heq 2
  have hst : s=t := bend_difference_strict.injective (by
    rw [mul_left_cancel₀ hr.ne' h0,mul_left_cancel₀ hr.ne' h1])
  exact Prod.ext hst h2

lemma flatRounded_left (r s z : ℝ) (hs : s ≤ 0) :
    flatRounded r (s,z)=![0,r*(bendC-s),z] := by
  have h1 : 1 ≤ 1-s := by linarith
  simp only [flatRounded,bendX_nonpos s hs,bendX_one_le (1-s) h1,mul_zero]
  congr 2
  ring
lemma flatRounded_right (r s z : ℝ) (hs : 1 ≤ s) :
    flatRounded r (s,z)=![r*(bendC+s-1),0,z] := by
  have h1 : 1-s ≤ 0 := by linarith
  simp only [flatRounded,bendX_nonpos (1-s) h1,bendX_one_le s hs,mul_zero]

def bendA (s : ℝ) : ℝ := bendC-bendX s
def bendB (s : ℝ) : ℝ := bendC-bendX (1-s)
lemma bendA_pos (s : ℝ) (hs : s < 1) : 0 < bendA s := sub_pos.mpr (bendX_lt s hs)
lemma bendB_pos (s : ℝ) (hs : 0 < s) : 0 < bendB s := bendA_pos (1-s) (by linarith)
lemma bendA_nonneg (s : ℝ) (hs : s ≤ 1) : 0 ≤ bendA s :=
  sub_nonneg.mpr (bendX_mono hs)
lemma bendB_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ bendB s := bendA_nonneg (1-s) (by linarith)
lemma flat_weight_pos (s : ℝ) : 0 < bendA s*speed (1-s)+bendB s*speed s := by
  by_cases hs0 : s ≤ 0
  · have href : 1 ≤ 1-s := by linarith
    simp only [speed_zero s hs0,speed_one (1-s) href,mul_zero,add_zero,mul_one,bendA,bendX_nonpos s hs0,sub_zero]
    exact bendC_pos
  by_cases hs1 : 1 ≤ s
  · have href : 1-s ≤ 0 := by linarith
    simp only [speed_one s hs1,speed_zero (1-s) href,mul_zero,zero_add,mul_one,bendB,bendX_nonpos (1-s) href,sub_zero]
    exact bendC_pos
  have ha : 0 < bendA s*speed (1-s) :=
    mul_pos (bendA_pos s (lt_of_not_ge hs1)) (speed_pos _ (by linarith))
  have hb : 0 ≤ bendB s*speed s :=
    mul_nonneg (bendB_pos s (lt_of_not_ge hs0)).le (speed_nonneg s)
  exact add_pos_of_pos_of_nonneg ha hb

lemma flatRounded_transverse (r : ℝ) (hr : 0 < r) (p v : ℝ × ℝ) :
    field (r*bendC) (flatRounded r p) ≠ fderiv ℝ (flatRounded r) p v := by
  intro heq
  rw [flatRounded_fderiv] at heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  simp only [flatRounded,field,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  have hh : r*(bendA p.1*speed (1-p.1)+bendB p.1*speed p.1)=0 := by
    dsimp only [bendA,bendB]
    linear_combination -speed (1-p.1)*h0-speed p.1*h1
  have hp := mul_pos hr (flat_weight_pos p.1)
  linarith

lemma flatRounded_contact_value (freq r : ℝ) (p : ℝ × ℝ) :
    α freq (flatRounded r p) (field (r*bendC) (flatRounded r p)) =
      -r*(bendA p.1*Real.sin (freq*p.2)+bendB p.1*Real.cos (freq*p.2)) := by
  simp [α,flatRounded,field,bendA,bendB]
  ring

end
end ContactTopology.EdgeRounding


namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[fun_prop] lemma bendA_smooth : ContDiff ℝ ∞ bendA := contDiff_const.sub bendX_smooth
@[fun_prop] lemma bendB_smooth : ContDiff ℝ ∞ bendB :=
  contDiff_const.sub (bendX_smooth.comp (contDiff_const.sub contDiff_id))

def bendPhase (s : ℝ) : ℝ := if s < 1/2 then Real.arctan (bendB s/bendA s)
  else Real.pi/2-Real.arctan (bendA s/bendB s)
lemma arctan_bend_complement (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Real.arctan (bendA s/bendB s)=Real.pi/2-Real.arctan (bendB s/bendA s) := by
  have h := Real.arctan_inv_of_pos (div_pos (bendB_pos s hs0) (bendA_pos s hs1))
  simpa only [inv_div] using h
lemma bendPhase_left (s : ℝ) (hs : s < 1) :
    bendPhase s=Real.arctan (bendB s/bendA s) := by
  unfold bendPhase
  split_ifs with h
  · rfl
  · have hi := arctan_bend_complement s (by linarith) hs
    linarith
lemma bendPhase_right (s : ℝ) (hs : 0 < s) :
    bendPhase s=Real.pi/2-Real.arctan (bendA s/bendB s) := by
  unfold bendPhase
  split_ifs with h
  · have hi := arctan_bend_complement s hs (by linarith)
    linarith
  · rfl
lemma bendPhase_smooth : ContDiff ℝ ∞ bendPhase := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s < 1
  · have hf : ContDiffAt ℝ ∞ (fun t => Real.arctan (bendB t/bendA t)) s :=
      (bendB_smooth.contDiffAt.div bendA_smooth.contDiffAt (bendA_pos s hs).ne').arctan
    apply hf.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hs] with t ht
    exact bendPhase_left t ht
  · have hpos : 0 < s := by linarith
    have hf : ContDiffAt ℝ ∞ (fun t => Real.pi/2-Real.arctan (bendA t/bendB t)) s :=
      contDiffAt_const.sub
        ((bendA_smooth.contDiffAt.div bendB_smooth.contDiffAt (bendB_pos s hpos).ne').arctan)
    apply hf.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hpos] with t ht
    exact bendPhase_right t ht
lemma bendPhase_zero : bendPhase 0=0 := by
  rw [bendPhase_left 0 (by norm_num)]
  simp [bendB,bendC]
lemma bendPhase_one : bendPhase 1=Real.pi/2 := by
  rw [bendPhase_right 1 (by norm_num)]
  simp [bendA,bendC]

lemma bend_combination_zero (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (x : ℝ) :
    bendA s*Real.sin x+bendB s*Real.cos x=0 ↔ Real.sin (x+bendPhase s)=0 := by
  by_cases hs1 : s < 1
  · have hA : bendA s ≠ 0 := (bendA_pos s hs1).ne'
    have hcos : Real.cos (bendPhase s) ≠ 0 := by
      rw [bendPhase_left s hs1]
      exact (Real.cos_arctan_pos _).ne'
    have htan : Real.sin (bendPhase s)=(bendB s/bendA s)*Real.cos (bendPhase s) := by
      rw [bendPhase_left s hs1]
      have ht := Real.tan_arctan (bendB s/bendA s)
      rw [Real.tan_eq_sin_div_cos] at ht
      exact (div_eq_iff (Real.cos_arctan_pos _).ne').mp ht
    have he : bendA s*Real.sin (x+bendPhase s)=
        Real.cos (bendPhase s)*(bendA s*Real.sin x+bendB s*Real.cos x) := by
      rw [Real.sin_add,htan]
      field_simp [hA]
    constructor
    · intro hz
      have hh : bendA s*Real.sin (x+bendPhase s)=0 := by rw [he,hz,mul_zero]
      exact (mul_eq_zero.mp hh).resolve_left hA
    · intro hz
      have hh : Real.cos (bendPhase s)*(bendA s*Real.sin x+bendB s*Real.cos x)=0 := by
        rw [← he,hz,mul_zero]
      exact (mul_eq_zero.mp hh).resolve_left hcos
  · have hs_eq : s=1 := le_antisymm hs.2 (le_of_not_gt hs1)
    subst s
    have hA : bendA 1=0 := by simp [bendA,bendC]
    have hB : bendB 1=bendC := by simp [bendB,bendX_zero]
    simp only [hA,hB,zero_mul,zero_add,bendPhase_one,Real.sin_add_pi_div_two,mul_eq_zero,bendC_pos.ne',false_or]

lemma flatRounded_dividing_iff (freq r : ℝ) (hfreq : 0 < freq) (hr : 0 < r)
    (s z : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    α freq (flatRounded r (s,z)) (field (r*bendC) (flatRounded r (s,z)))=0 ↔
      ∃ k : ℤ, z=k*Real.pi/freq-bendPhase s/freq := by
  rw [flatRounded_contact_value,mul_eq_zero]
  simp only [neg_eq_zero,hr.ne',false_or]
  rw [bend_combination_zero s hs,Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [← sub_div]
    apply (eq_div_iff hfreq.ne').mpr
    linarith
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    rw [hk]
    field_simp [hfreq.ne']
    ring

def flatCurve (freq r : ℝ) (k : ℤ) (s : ℝ) : V :=
  flatRounded r (s,k*Real.pi/freq-bendPhase s/freq)
lemma flatCurve_smooth (freq r : ℝ) (k : ℤ) : ContDiff ℝ ∞ (flatCurve freq r k) :=
  (flatRounded_smooth r).comp (contDiff_id.prodMk (contDiff_const.sub (bendPhase_smooth.div_const freq)))
lemma flatCurve_regular (freq r : ℝ) (hr : 0 < r) (k : ℤ) (s : ℝ) :
    deriv (flatCurve freq r k) s ≠ 0 := by
  let h : ℝ → ℝ × ℝ := fun t => (t,k*Real.pi/freq-bendPhase t/freq)
  have hd : HasDerivAt h (1,-(deriv bendPhase s/freq)) s := by
    convert! (hasDerivAt_id s).prodMk
      ((hasDerivAt_const s (k*Real.pi/freq)).sub
        ((bendPhase_smooth.differentiable (by simp) s).hasDerivAt.div_const freq)) using 1 <;> simp
  have hc := ((flatRounded_smooth r).differentiable (by simp) (h s)).hasFDerivAt.comp_hasDerivAt s hd
  change HasDerivAt (flatCurve freq r k) _ s at hc
  rw [hc.deriv]
  intro hz
  have heq : fderiv ℝ (flatRounded r) (h s) (1,-(deriv bendPhase s/freq))=
      fderiv ℝ (flatRounded r) (h s) (0 : ℝ × ℝ) := by simpa only [map_zero] using hz
  have hh := (flatRounded_immersion r hr (h s)) heq
  have hh0 := congrArg Prod.fst hh
  norm_num at hh0

lemma flatCurve_endpoints (n : ℕ) (hn : 0 < n) (r : ℝ) (k : ℤ) :
    flatCurve (2*Real.pi*n) r k 0=![0,r*bendC,(k:ℝ)/(2*n)] ∧
    flatCurve (2*Real.pi*n) r k 1=![r*bendC,0,(k:ℝ)/(2*n)-1/(4*n)] := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h0 : (k:ℝ)*Real.pi/(2*Real.pi*n)=(k:ℝ)/(2*n) := by field_simp [Real.pi_ne_zero,hn0]
  have h1 : (Real.pi/2)/(2*Real.pi*n)=1/(4*n) := by field_simp [Real.pi_ne_zero,hn0]; ring
  constructor
  · simp only [flatCurve,bendPhase_zero,zero_div,sub_zero,flatRounded_left r 0 _ le_rfl,h0,sub_zero]
  · simp only [flatCurve,bendPhase_one,flatRounded_right r 1 _ le_rfl,h0,h1]
    congr 2
    ring

end
end ContactTopology.EdgeRounding



namespace ContactTopology.EdgeRounding
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma flatRounded_embedding (r : ℝ) (hr : 0 < r) : Topology.IsEmbedding (flatRounded r) := by
  let g : ℝ → ℝ := fun s => bendX s-bendX (1-s)
  have hgc : Continuous g := bendX_smooth.continuous.sub
    (bendX_smooth.continuous.comp (continuous_const.sub continuous_id))
  have hg : Topology.IsEmbedding g := bend_difference_strict.isEmbedding_of_ordConnected
    (isPreconnected_range hgc).ordConnected
  let L : V → ℝ × ℝ := fun y => ((y 0-y 1)/r,y 2)
  have hL : Continuous L := by fun_prop
  have hprod : Topology.IsEmbedding (Prod.map g (id : ℝ → ℝ)) := hg.prodMap Topology.IsEmbedding.id
  have heq : L ∘ flatRounded r=Prod.map g (id : ℝ → ℝ) := by
    funext p
    apply Prod.ext
    · dsimp [L,flatRounded,g]
      field_simp [hr.ne']
    · rfl
  apply Topology.IsEmbedding.of_comp (flatRounded_smooth r).continuous hL
  simpa only [heq] using hprod

lemma contact_periodic (n : ℕ) (y v : V) :
    α (2*Real.pi*n) (![y 0,y 1,y 2+1]) v=α (2*Real.pi*n) y v := by
  have he : (2*Real.pi*n)*(y 2+1)=(2*Real.pi*n)*y 2+n*(2*Real.pi) := by ring
  change Real.sin ((2*Real.pi*n)*(y 2+1))*v 0+Real.cos ((2*Real.pi*n)*(y 2+1))*v 1=
    Real.sin ((2*Real.pi*n)*y 2)*v 0+Real.cos ((2*Real.pi*n)*y 2)*v 1
  rw [he,Real.sin_add_nat_mul_two_pi,Real.cos_add_nat_mul_two_pi]

end
end ContactTopology.EdgeRounding


open Set Function
open scoped ContDiff

theorem solution (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr : 0 < r) :
    let a : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y =>
      ![Real.sin (2*Real.pi*n*y 2),Real.cos (2*Real.pi*n*y 2),0]
    let α : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun y v =>
      Real.sin (2*Real.pi*n*y 2)*v 0+Real.cos (2*Real.pi*n*y 2)*v 1
    ∃ c : ℝ, ∃ S : ℝ × ℝ → (Fin 3 → ℝ), ∃ X : (Fin 3 → ℝ) → (Fin 3 → ℝ),
    ∃ Φ : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ phase : ℝ → ℝ,
    ∃ γ : ℤ → ℝ → (Fin 3 → ℝ),
      0 < c ∧ ContDiff ℝ ∞ S ∧ Topology.IsEmbedding S ∧
      (∀ p, Injective (fderiv ℝ S p)) ∧ ContDiff ℝ ∞ X ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ phase ∧ (∀ k, ContDiff ℝ ∞ (γ k)) ∧
      (∀ y, X y=![y 0-r*c,y 1-r*c,0]) ∧
      (∀ t y, Φ t y=![r*c+Real.exp t*(y 0-r*c),r*c+Real.exp t*(y 1-r*c),y 2]) ∧
      (∀ y, Φ 0 y=y) ∧ (∀ t y, Φ (-t) (Φ t y)=y) ∧
      (∀ t y, HasDerivAt (fun s => Φ s y) (X (Φ t y)) t) ∧
      (∀ t y v, α (Φ t y) (fderiv ℝ (Φ t) y v)=Real.exp t*α y v) ∧
      (∀ y,
        a y 0*(fderiv ℝ a y (Pi.single 1 1) 2-fderiv ℝ a y (Pi.single 2 1) 1)+
        a y 1*(fderiv ℝ a y (Pi.single 2 1) 0-fderiv ℝ a y (Pi.single 0 1) 2)+
        a y 2*(fderiv ℝ a y (Pi.single 0 1) 1-fderiv ℝ a y (Pi.single 1 1) 0)=2*Real.pi*n) ∧
      (∀ y v : Fin 3 → ℝ, α ![y 0,y 1,y 2+1] v=α y v) ∧
      (∀ s z, s ≤ 0 → S (s,z)=![0,r*(c-s),z]) ∧
      (∀ s z, 1 ≤ s → S (s,z)=![r*(c+s-1),0,z]) ∧
      (∀ p v : ℝ × ℝ, X (S p) ≠ fderiv ℝ S p v) ∧
      (∀ p : ℝ × ℝ, α (S p) (fderiv ℝ S p (0,1))=0) ∧
      phase 0=0 ∧ phase 1=Real.pi/2 ∧
      (∀ k s, γ k s=S (s,(k:ℝ)/(2*n)-phase s/(2*Real.pi*n))) ∧
      (∀ k s, deriv (γ k) s ≠ 0) ∧
      (∀ k, γ k 0=![0,r*c,(k:ℝ)/(2*n)] ∧
        γ k 1=![r*c,0,(k:ℝ)/(2*n)-1/(4*n)]) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ z : ℝ,
        (α (S (s,z)) (X (S (s,z)))=0 ↔
          ∃ k : ℤ, z=(k:ℝ)/(2*n)-phase s/(2*Real.pi*n)) := by

  dsimp only
  let freq : ℝ := 2*Real.pi*n
  have hfreq : 0 < freq := mul_pos (by positivity) (by exact_mod_cast hn)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hcancel : ∀ k : ℤ, (k:ℝ)*Real.pi/freq=(k:ℝ)/(2*n) := by
    intro k
    dsimp only [freq]
    field_simp [Real.pi_ne_zero,hn0]
  refine ⟨ContactTopology.EdgeRounding.bendC,ContactTopology.EdgeRounding.flatRounded r,
    ContactTopology.EdgeRounding.field (r*ContactTopology.EdgeRounding.bendC),
    ContactTopology.EdgeRounding.flow (r*ContactTopology.EdgeRounding.bendC),
    ContactTopology.EdgeRounding.bendPhase,ContactTopology.EdgeRounding.flatCurve freq r,
    ContactTopology.EdgeRounding.bendC_pos,ContactTopology.EdgeRounding.flatRounded_smooth r,
    ContactTopology.EdgeRounding.flatRounded_embedding r hr,
    ContactTopology.EdgeRounding.flatRounded_immersion r hr,
    ContactTopology.EdgeRounding.field_smooth _,ContactTopology.EdgeRounding.flow_smooth _,
    ContactTopology.EdgeRounding.bendPhase_smooth,ContactTopology.EdgeRounding.flatCurve_smooth freq r,
    fun _ => rfl,fun _ _ => rfl,ContactTopology.EdgeRounding.flow_zero _,
    ContactTopology.EdgeRounding.flow_inverse _,ContactTopology.EdgeRounding.flow_velocity _,
    ContactTopology.EdgeRounding.flow_contact freq _,ContactTopology.EdgeRounding.contact_volume freq,
    ContactTopology.EdgeRounding.contact_periodic n,ContactTopology.EdgeRounding.flatRounded_left r,
    ContactTopology.EdgeRounding.flatRounded_right r,ContactTopology.EdgeRounding.flatRounded_transverse r hr,
    ?_,ContactTopology.EdgeRounding.bendPhase_zero,ContactTopology.EdgeRounding.bendPhase_one,?_,
    ContactTopology.EdgeRounding.flatCurve_regular freq r hr,
    ContactTopology.EdgeRounding.flatCurve_endpoints n hn r,?_⟩
  · intro p
    rw [ContactTopology.EdgeRounding.flatRounded_fderiv]
    simp [ContactTopology.EdgeRounding.α]
  · intro k s
    simp only [ContactTopology.EdgeRounding.flatCurve,hcancel k,freq]
  · intro s hs z
    simpa only [hcancel,freq,ContactTopology.EdgeRounding.α] using ContactTopology.EdgeRounding.flatRounded_dividing_iff freq r hfreq hr s z hs
