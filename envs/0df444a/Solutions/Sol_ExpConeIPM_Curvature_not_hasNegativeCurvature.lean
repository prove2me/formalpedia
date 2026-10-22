-- Prove2me | solution 1 for ExpConeIPM.Curvature.not_hasNegativeCurvature
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T18:38:06.954999+00:00
-- url     : https://prove2.me/submissions/e45e3e88-615a-4e0c-9448-3e5dfc9dc62e

import Mathlib
import Definitions.Def_ExpConeIPM_Curvature_ExpCone
import Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature

open scoped InnerProductSpace
open Filter Topology

set_option autoImplicit false

namespace D365C243

open ExpConeIPM.Curvature

abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable def pt (a b : ℝ) : E3 := WithLp.toLp 2 ![a, b, -1]

noncomputable def e1 : E3 := EuclideanSpace.single 0 1
noncomputable def e2 : E3 := EuclideanSpace.single 1 1

@[simp] lemma pt0 (a b : ℝ) : pt a b 0 = a := rfl
@[simp] lemma pt1 (a b : ℝ) : pt a b 1 = b := rfl
@[simp] lemma pt2 (a b : ℝ) : pt a b 2 = -1 := rfl

lemma pt_eq_b (a b : ℝ) : pt a b = pt a 0 + b • e2 := by
  ext i; fin_cases i <;> simp [pt, e2, PiLp.single_apply]

lemma pt_eq_a (a b : ℝ) : pt a b = pt 0 b + a • e1 := by
  ext i; fin_cases i <;> simp [pt, e1, PiLp.single_apply]

lemma barrier_pt (a b : ℝ) :
    barrier (pt a b) = -Real.log (b * Real.log (a / b) + 1) - Real.log a - Real.log b := by
  simp [barrier, sub_neg_eq_add]

lemma contDiffAt_barrier (y : E3) (h0 : 0 < y 0) (h1 : 0 < y 1) (hp : 0 < psi y) :
    ContDiffAt ℝ 3 barrier y := by
  have c0 : ContDiff ℝ 3 (fun z : E3 => z 0) := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).contDiff
  have c1 : ContDiff ℝ 3 (fun z : E3 => z 1) := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).contDiff
  have c2 : ContDiff ℝ 3 (fun z : E3 => z 2) := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).contDiff
  have hdiv : ContDiffAt ℝ 3 (fun z : E3 => z 0 / z 1) y :=
    c0.contDiffAt.div c1.contDiffAt h1.ne'
  have hlog : ContDiffAt ℝ 3 (fun z : E3 => Real.log (z 0 / z 1)) y :=
    hdiv.log (div_pos h0 h1).ne'
  have hpsi : ContDiffAt ℝ 3 (fun z : E3 => z 1 * Real.log (z 0 / z 1) - z 2) y :=
    (c1.contDiffAt.mul hlog).sub c2.contDiffAt
  have := ((hpsi.log hp.ne').neg.sub (c0.contDiffAt.log h0.ne')).sub (c1.contDiffAt.log h1.ne')
  exact this

lemma hasDerivAt_pt_b (a b : ℝ) : HasDerivAt (fun s => pt a s) e2 b := by
  have h : (fun s => pt a s) = fun s => pt a 0 + s • e2 := funext (pt_eq_b a)
  rw [h]; simpa using ((hasDerivAt_id b).smul_const e2).const_add (pt a 0)

lemma hasDerivAt_pt_a (a b : ℝ) : HasDerivAt (fun r => pt r b) e1 a := by
  have h : (fun r => pt r b) = fun r => pt 0 b + r • e1 := funext (fun r => pt_eq_a r b)
  rw [h]; simpa using ((hasDerivAt_id a).smul_const e1).const_add (pt 0 b)

lemma contDiffAt_pt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < b * Real.log (a / b) + 1) :
    ContDiffAt ℝ 3 barrier (pt a b) :=
  contDiffAt_barrier _ (by simpa using ha) (by simpa using hb) (by simp [psi]; linarith)

noncomputable def g1 (a s : ℝ) : ℝ :=
  -((Real.log (a / s) - 1) / (s * Real.log (a / s) + 1)) - s⁻¹

lemma hasDerivAt_div_s (a b : ℝ) (hb : 0 < b) :
    HasDerivAt (fun s : ℝ => a / s) (a * -(b ^ 2)⁻¹) b := by
  have := (hasDerivAt_inv hb.ne').const_mul a
  have h : (fun s : ℝ => a / s) = fun y => a * y⁻¹ := funext fun s => div_eq_mul_inv a s
  rw [h]; exact this

lemma hasDerivAt_line_b (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hp : 0 < b * Real.log (a / b) + 1) :
    HasDerivAt (fun s => -Real.log (s * Real.log (a / s) + 1) - Real.log a - Real.log s)
      (g1 a b) b := by
  have h2 := (hasDerivAt_div_s a b hb).log (div_pos ha hb).ne'
  have h3 := ((hasDerivAt_id' b).mul h2).add_const 1
  have h4 := (h3.log hp.ne').neg
  have h5 := (h4.sub_const (Real.log a)).sub (Real.hasDerivAt_log hb.ne')
  refine h5.congr_deriv ?_
  have ha0 := ha.ne'
  have hb0 := hb.ne'
  have hp0 := hp.ne'
  simp only [Pi.mul_apply]
  unfold g1
  field_simp
  ring

lemma inner_gradient (z : E3) : ⟪gradient barrier z, e2⟫_ℝ = fderiv ℝ barrier z e2 := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

lemma fderiv_e2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < b * Real.log (a / b) + 1) :
    fderiv ℝ barrier (pt a b) e2 = g1 a b := by
  have hF : DifferentiableAt ℝ barrier (pt a b) :=
    (contDiffAt_pt a b ha hb hp).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun s => barrier (pt a s)) (fderiv ℝ barrier (pt a b) e2) b :=
    hF.hasFDerivAt.comp_hasDerivAt b (hasDerivAt_pt_b a b)
  have h2 : HasDerivAt (fun s => barrier (pt a s)) (g1 a b) b := by
    have hfun : (fun s => barrier (pt a s)) =
        fun s => -Real.log (s * Real.log (a / s) + 1) - Real.log a - Real.log s :=
      funext (fun s => barrier_pt a s)
    rw [hfun]; exact hasDerivAt_line_b a b ha hb hp
  exact h1.unique h2

noncomputable def q (a : ℝ) : ℝ :=
  1 / (Real.log a + 1) + (Real.log a - 1) ^ 2 / (Real.log a + 1) ^ 2 + 1

lemma hasDerivAt_g1 (a : ℝ) (ha : 0 < a) (hp : 0 < Real.log a + 1) :
    HasDerivAt (fun s => g1 a s) (q a) 1 := by
  have h2 := (hasDerivAt_div_s a 1 one_pos).log (by simp [ha.ne'])
  have hN := h2.sub_const 1
  have hD := ((hasDerivAt_id' (1 : ℝ)).mul h2).add_const 1
  have hD0 : (1 : ℝ) * Real.log (a / 1) + 1 ≠ 0 := by simp; linarith
  have h5 := ((hN.div hD hD0).neg).sub (hasDerivAt_inv (one_ne_zero (α := ℝ)))
  refine h5.congr_deriv ?_
  have ha0 := ha.ne'
  have hp0 := hp.ne'
  unfold q
  simp only [Pi.mul_apply, div_one, one_mul, one_pow, inv_one, mul_one]
  field_simp
  ring

lemma contDiffAt_gradient (a : ℝ) (ha : 0 < a) (hp : 0 < Real.log a + 1) :
    ContDiffAt ℝ 2 (gradient barrier) (pt a 1) := by
  have hC : ContDiffAt ℝ 3 barrier (pt a 1) :=
    contDiffAt_pt a 1 ha one_pos (by simpa using hp)
  have hf : ContDiffAt ℝ 2 (fderiv ℝ barrier) (pt a 1) := hC.fderiv_right (by norm_num)
  have : ContDiffAt ℝ 2 (fun z => (InnerProductSpace.toDual ℝ E3).symm (fderiv ℝ barrier z))
      (pt a 1) :=
    ((InnerProductSpace.toDual ℝ E3).symm.contDiff).contDiffAt.comp _ hf
  exact this

lemma hess_e2 (a : ℝ) (ha : 0 < a) (hp : 0 < Real.log a + 1) :
    ⟪SelfScaledIPM.ShortStep.hess barrier (pt a 1) e2, e2⟫_ℝ = q a := by
  have hGd : DifferentiableAt ℝ (gradient barrier) (pt a 1) :=
    (contDiffAt_gradient a ha hp).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun s => gradient barrier (pt a s))
      (SelfScaledIPM.ShortStep.hess barrier (pt a 1) e2) 1 :=
    hGd.hasFDerivAt.comp_hasDerivAt 1 (hasDerivAt_pt_b a 1)
  have h2 : HasDerivAt (fun s => ⟪gradient barrier (pt a s), e2⟫_ℝ)
      ⟪SelfScaledIPM.ShortStep.hess barrier (pt a 1) e2, e2⟫_ℝ 1 := by
    have := h1.inner ℝ (hasDerivAt_const (1 : ℝ) e2)
    simpa using this
  have hc : ContinuousAt (fun s : ℝ => s * Real.log (a / s) + 1) 1 :=
    (continuousAt_id.mul ((continuousAt_const.div continuousAt_id one_ne_zero).log
      (by simp [ha.ne']))).add continuousAt_const
  have hev1 : ∀ᶠ s in 𝓝 (1 : ℝ), 0 < s * Real.log (a / s) + 1 :=
    continuousAt_const.eventually_lt hc (by simpa using hp)
  have hev2 : ∀ᶠ s in 𝓝 (1 : ℝ), 0 < s :=
    continuousAt_const.eventually_lt continuousAt_id (by norm_num)
  have h3 : (fun s => ⟪gradient barrier (pt a s), e2⟫_ℝ) =ᶠ[𝓝 1] fun s => g1 a s := by
    filter_upwards [hev1, hev2] with s hs1 hs2
    rw [inner_gradient, fderiv_e2 a s ha hs2 hs1]
  have h4 := (hasDerivAt_g1 a ha hp).congr_of_eventuallyEq h3
  exact h2.unique h4

lemma hasDerivAt_q : HasDerivAt q (1 / (27 * Real.exp 2)) (Real.exp 2) := by
  have hL := Real.hasDerivAt_log (Real.exp_pos 2).ne'
  have hL1 := hL.add_const 1
  have hl2 : Real.log (Real.exp 2) + 1 ≠ 0 := by rw [Real.log_exp]; norm_num
  have hA := (hasDerivAt_const (Real.exp 2) (1 : ℝ)).div hL1 hl2
  have hB := ((hL.sub_const 1).pow 2).div (hL1.pow 2) (pow_ne_zero 2 hl2)
  have h := (hA.add hB).add_const 1
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Real.log_exp]
  field_simp
  ring

lemma key : ⟪thirdDeriv barrier (pt (Real.exp 2) 1) e1 e2, e2⟫_ℝ = 1 / (27 * Real.exp 2) := by
  have hp0 : 0 < Real.log (Real.exp 2) + 1 := by rw [Real.log_exp]; norm_num
  have hH : DifferentiableAt ℝ (SelfScaledIPM.ShortStep.hess barrier) (pt (Real.exp 2) 1) := by
    have : ContDiffAt ℝ 1 (fderiv ℝ (gradient barrier)) (pt (Real.exp 2) 1) :=
      (contDiffAt_gradient _ (Real.exp_pos 2) hp0).fderiv_right (by norm_num)
    exact this.differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun r => SelfScaledIPM.ShortStep.hess barrier (pt r 1))
      (fderiv ℝ (SelfScaledIPM.ShortStep.hess barrier) (pt (Real.exp 2) 1) e1) (Real.exp 2) :=
    HasFDerivAt.comp_hasDerivAt (f := fun r => pt r 1) (Real.exp 2) hH.hasFDerivAt
      (hasDerivAt_pt_a (Real.exp 2) 1)
  have h2 := h1.clm_apply (hasDerivAt_const (Real.exp 2) e2)
  have h3 := h2.inner ℝ (hasDerivAt_const (Real.exp 2) e2)
  simp only [map_zero, add_zero, inner_zero_right, zero_add] at h3
  have hc : ContinuousAt (fun r : ℝ => Real.log r + 1) (Real.exp 2) :=
    (Real.continuousAt_log (Real.exp_pos 2).ne').add continuousAt_const
  have hev1 : ∀ᶠ r in 𝓝 (Real.exp 2), 0 < Real.log r + 1 :=
    continuousAt_const.eventually_lt hc hp0
  have hev2 : ∀ᶠ r in 𝓝 (Real.exp 2), 0 < r :=
    continuousAt_const.eventually_lt continuousAt_id (Real.exp_pos 2)
  have h4 : (fun r => ⟪SelfScaledIPM.ShortStep.hess barrier (pt r 1) e2, e2⟫_ℝ)
      =ᶠ[𝓝 (Real.exp 2)] q := by
    filter_upwards [hev1, hev2] with r hr1 hr2
    exact hess_e2 r hr2 hr1
  have h5 := hasDerivAt_q.congr_of_eventuallyEq h4
  unfold thirdDeriv
  exact h3.unique h5

lemma mem_interior : pt (Real.exp 2) 1 ∈ interior Kexp := by
  rw [mem_interior_iff_mem_nhds]
  have hc1 : ContinuousAt (fun y : E3 => y 1) (pt (Real.exp 2) 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).continuous.continuousAt
  have hc2 : ContinuousAt (fun y : E3 => y 2) (pt (Real.exp 2) 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).continuous.continuousAt
  have hc0 : ContinuousAt (fun y : E3 => y 0) (pt (Real.exp 2) 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).continuous.continuousAt
  have hce : ContinuousAt (fun y : E3 => y 1 * Real.exp (y 2 / y 1)) (pt (Real.exp 2) 1) :=
    hc1.mul (Real.continuous_exp.continuousAt.comp (hc2.div hc1 (by simp)))
  have e1' : ∀ᶠ y in 𝓝 (pt (Real.exp 2) 1), (0 : ℝ) < y 1 :=
    continuousAt_const.eventually_lt hc1 (by simp)
  have e2' : ∀ᶠ y in 𝓝 (pt (Real.exp 2) 1), y 1 * Real.exp (y 2 / y 1) < y 0 :=
    hce.eventually_lt hc0 (by simp [Real.exp_lt_exp]; norm_num)
  filter_upwards [e1', e2'] with y hy1 hy2
  exact subset_closure ⟨hy2.le, hy1⟩

lemma e1_mem : e1 ∈ Kexp := by
  have ht : Tendsto (fun t : ℝ => e1 + t • e2) (𝓝[>] 0) (𝓝 e1) := by
    have : Continuous (fun t : ℝ => e1 + t • e2) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h := this.tendsto 0
    simp only [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have h0 : (e1 + t • e2) 0 = 1 := by simp [e1, e2, PiLp.single_apply]
  have h1 : (e1 + t • e2) 1 = t := by simp [e1, e2, PiLp.single_apply]
  have h2 : (e1 + t • e2) 2 = 0 := by simp [e1, e2, PiLp.single_apply]
  refine ⟨?_, ?_⟩
  · rw [h0, h1, h2]; simp; exact ht.2.le
  · rw [h1]; exact ht.1

end D365C243

open ExpConeIPM.Curvature in
theorem solution : ¬ HasNegativeCurvature Kexp barrier := by
  intro h
  have := h _ D365C243.mem_interior _ D365C243.e1_mem D365C243.e2
  rw [D365C243.key] at this
  have hpos : (0 : ℝ) < 1 / (27 * Real.exp 2) := by positivity
  linarith
