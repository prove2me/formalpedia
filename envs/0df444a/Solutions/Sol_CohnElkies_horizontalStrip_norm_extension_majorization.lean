-- Prove2me | solution 1 for CohnElkies.horizontalStrip_norm_extension_majorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/edec6890-a81f-4104-ad8c-e0dca5aa2fe9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_norm_extension_le_of_frontier

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (f : ℂ → ℂ) (N : ℂ → ℝ)
    (hf : DifferentiableOn ℂ f
      (Complex.im ⁻¹' Ioo a b))
    (hN : ContinuousOn N
      (Complex.im ⁻¹' Icc a b))
    (hNnonneg : ∀ w : ℂ,
      w.im ∈ Icc a b → 0 ≤ N w)
    (hinterior : ∀ w : ℂ,
      w.im ∈ Ioo a b → N w = ‖f w‖)
    (hbottom : ∀ w : ℂ, w.im = a → N w ≤ C)
    (htop : ∀ w : ℂ, w.im = b → N w ≤ C)
    (hgrowth :
      ∃ c < Real.pi / (b - a), ∃ B : ℝ,
        Asymptotics.IsBigO
          (Filter.comap (fun w : ℂ => |w.re|)
              Filter.atTop ⊓
            Filter.principal
              (Complex.im ⁻¹' Ioo a b))
          f
          (fun w : ℂ =>
            Real.exp (B * Real.exp (c * |w.re|))))
    {z : ℂ} (hza : a ≤ z.im) (hzb : z.im ≤ b) :
    N z ≤ C := by
  rw [le_iff_eq_or_lt] at hza hzb
  rcases hza with hza | hza
  · exact hbottom z hza.symm
  rcases hzb with hzb | hzb
  · exact htop z hzb
  obtain ⟨m, r, rfl, rfl⟩ :
      ∃ m r : ℝ, a = m - r ∧ b = m + r :=
    ⟨(a + b) / 2, (b - a) / 2, by ring, by ring⟩
  have hr : 0 < r := by linarith
  have hwidth : m - r < m + r := by linarith
  rw [add_sub_sub_cancel, ← two_mul,
    div_mul_eq_div_div] at hgrowth
  have hπr : 0 < Real.pi / 2 / r :=
    div_pos Real.pi_div_two_pos hr
  rcases hgrowth with ⟨c, hc, B, hO⟩
  obtain ⟨q, ⟨hcq, hq⟩, hqr⟩ :
      ∃ q : ℝ,
        (c < q ∧ 0 < q) ∧
          q < Real.pi / 2 / r := by
    simpa only [max_lt_iff] using!
      exists_between (max_lt hc hπr)
  have hqr' : q * r < Real.pi / 2 :=
    (lt_div_iff₀ hr).mp hqr
  let aff : ℂ → ℂ :=
    fun w => q * (w - m * Complex.I)
  let damp : ℝ → ℂ → ℂ :=
    fun ε w =>
      Complex.exp (ε *
        (Complex.exp (aff w) +
          Complex.exp (-aff w)))
  suffices hevent :
      ∀ᶠ ε : ℝ in 𝓝[<] (0 : ℝ),
        ‖damp ε z • f z‖ ≤ C by
    rw [hinterior z ⟨hza, hzb⟩]
    refine le_of_tendsto
      (Filter.Tendsto.mono_left ?_
        nhdsWithin_le_nhds) hevent
    apply
      ((Complex.continuous_ofReal.mul
        continuous_const).cexp.smul
          continuous_const).norm.tendsto'
    simp
  filter_upwards [self_mem_nhdsWithin]
    with ε hε
  change ε < 0 at hε
  obtain ⟨δ, hδ, hδbound⟩ :
      ∃ δ : ℝ,
        δ < 0 ∧
          ∀ ⦃w : ℂ⦄,
            w.im ∈ Icc (m - r) (m + r) →
              ‖damp ε w‖ ≤
                Real.exp
                  (δ * Real.exp (q * |w.re|)) := by
    refine ⟨ε * Real.cos (q * r),
      mul_neg_of_neg_of_pos hε
        (Real.cos_pos_of_mem_Ioo
          (abs_lt.mp
            ((abs_of_pos (mul_pos hq hr)).symm ▸ hqr'))),
      ?_⟩
    intro w hw
    have hwaff : |(aff w).im| ≤ q * r := by
      rw [← Real.closedBall_eq_Icc,
        Metric.mem_closedBall, Real.dist_eq] at hw
      try dsimp [aff]
      rw [Complex.im_ofReal_mul, Complex.sub_im,
        Complex.mul_I_im, Complex.ofReal_re,
        abs_mul, abs_of_pos hq]
      gcongr
    simpa only [aff, Complex.re_ofReal_mul,
      abs_mul, abs_of_pos hq, Complex.sub_re,
      Complex.mul_I_re, Complex.ofReal_im,
      zero_mul, neg_zero, sub_zero, damp] using!
        norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le
          hε.le hwaff hqr'.le
  have hdampedge :
      ∀ w : ℂ,
        w.im = m - r ∨ w.im = m + r →
          ‖damp ε w‖ ≤ 1 := by
    intro w hw
    apply le_trans (hδbound
      (hw.by_cases
        (fun h => h.symm ▸ left_mem_Icc.mpr hwidth.le)
        (fun h => h.symm ▸ right_mem_Icc.mpr hwidth.le)))
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      hδ.le (Real.exp_pos _).le
  obtain ⟨R, hzR, hR⟩ :
      ∃ R : ℝ,
        |z.re| < R ∧
          ∀ w : ℂ, |w.re| = R →
            w.im ∈ Ioo (m - r) (m + r) →
              ‖damp ε w • f w‖ ≤ C := by
    refine ((eventually_gt_atTop |z.re|).and ?_).exists
    rcases hO.exists_pos with ⟨A, hA, hAmajor⟩
    simp only [isBigOWith_iff,
      eventually_inf_principal, eventually_comap,
      Set.mem_Ioo, Set.mem_preimage,
      Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at hAmajor
    suffices hlimit :
        Tendsto
          (fun R : ℝ =>
            Real.exp
              (δ * Real.exp (q * R) +
                B * Real.exp (c * R) + Real.log A))
          Filter.atTop (𝓝 (0 : ℝ)) by
      filter_upwards
        [hlimit.eventually (ge_mem_nhds hC), hAmajor]
        with R hRC hbound w hwre hwim
      calc
        ‖damp ε w • f w‖ ≤
          Real.exp
            (δ * Real.exp (q * R) +
              B * Real.exp (c * R) + Real.log A) := by
          rw [norm_smul, Real.exp_add, ← hwre,
            Real.exp_add, Real.exp_log hA,
            mul_assoc, mul_comm _ A]
          gcongr
          · exact hδbound
              (Set.Ioo_subset_Icc_self hwim)
          · exact hbound w hwre hwim
        _ ≤ C := hRC
    apply Real.tendsto_exp_atBot.comp
    suffices haux :
        Tendsto
          (fun R : ℝ =>
            δ + B * (Real.exp ((q - c) * R))⁻¹)
          Filter.atTop (𝓝 (δ + B * 0)) by
      rw [mul_zero, add_zero] at haux
      refine Filter.Tendsto.atBot_add ?_
        tendsto_const_nhds
      simpa only [id, Function.comp_apply,
        add_mul, mul_assoc,
        ← div_eq_inv_mul, ← Real.exp_sub,
        ← sub_mul, sub_sub_cancel] using! haux.neg_mul_atTop hδ
          (Real.tendsto_exp_atTop.comp
            (tendsto_id.const_mul_atTop hq))
    exact tendsto_const_nhds.add
      (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp
          (Real.tendsto_exp_atTop.comp
            (tendsto_id.const_mul_atTop
              (sub_pos.mpr hcq)))))
  have hRpos : 0 < R :=
    (abs_nonneg z.re).trans_lt hzR
  let U : Set ℂ :=
    Set.Ioo (-R) R ×ℂ Set.Ioo (m - r) (m + r)
  have hUopen : IsOpen U :=
    IsOpen.reProdIm isOpen_Ioo isOpen_Ioo
  have hUbounded : Bornology.IsBounded U :=
    Bornology.IsBounded.reProdIm
      (isBounded_Ioo _ _) (isBounded_Ioo _ _)
  have hUconvex : Convex ℝ U := by
    have hset : U =
        ({w : ℂ | -R < w.re} ∩
          {w : ℂ | w.re < R}) ∩
        ({w : ℂ | m - r < w.im} ∩
          {w : ℂ | w.im < m + r}) := by
      ext w
      simp [U, Complex.mem_reProdIm]
    rw [hset]
    exact
      ((convex_halfSpace_re_gt (-R)).inter
        (convex_halfSpace_re_lt R)).inter
      ((convex_halfSpace_im_gt (m - r)).inter
        (convex_halfSpace_im_lt (m + r)))
  have hdamp : Differentiable ℂ (damp ε) := by
    exact
      ((((differentiable_id.sub_const _).const_mul _).cexp.add
        ((differentiable_id.sub_const _).const_mul _).neg.cexp).const_mul
          _).cexp
  have hweighted :
      DifferentiableOn ℂ
        (fun w : ℂ => damp ε w • f w) U := by
    exact (hdamp.differentiableOn.smul hf).mono
      Set.inter_subset_right
  have hclosure :
      closure U ⊆
        Complex.im ⁻¹' Icc (m - r) (m + r) := by
    intro w hw
    try dsimp [U] at hw
    rw [Complex.closure_reProdIm,
      closure_Ioo (neg_lt_self hRpos).ne,
      closure_Ioo hwidth.ne] at hw
    exact hw.2
  let Next : ℂ → ℝ :=
    fun w => ‖damp ε w‖ * N w
  have hNext : ContinuousOn Next (closure U) := by
    try dsimp [Next]
    exact hdamp.continuous.norm.continuousOn.mul
      (hN.mono hclosure)
  have hNextinterior :
      ∀ w ∈ U,
        Next w = ‖damp ε w • f w‖ := by
    intro w hw
    try dsimp [Next]
    rw [hinterior w hw.2]
    exact (norm_mul _ _).symm
  have hNextfrontier :
      ∀ w ∈ frontier U, Next w ≤ C := by
    intro w hw
    try dsimp [U] at hw
    rw [Complex.frontier_reProdIm,
      closure_Ioo (neg_lt_self hRpos).ne,
      frontier_Ioo hwidth,
      closure_Ioo hwidth.ne,
      frontier_Ioo (neg_lt_self hRpos)] at hw
    by_cases him : w.im = m - r ∨ w.im = m + r
    · dsimp [Next]
      calc
        ‖damp ε w‖ * N w ≤ 1 * N w := by
          apply mul_le_mul_of_nonneg_right
            (hdampedge w him)
          apply hNnonneg w
          exact him.by_cases
            (fun h => h.symm ▸ left_mem_Icc.mpr hwidth.le)
            (fun h => h.symm ▸ right_mem_Icc.mpr hwidth.le)
        _ = N w := one_mul _
        _ ≤ C := him.by_cases
          (hbottom w) (htop w)
    · have hvert :
          w ∈ ({-R, R} : Set ℝ) ×ℂ
            Icc (m - r) (m + r) := by
        exact hw.resolve_left
          (fun h => him h.2)
      have him' :=
        eq_endpoints_or_mem_Ioo_of_mem_Icc hvert.2
      rw [← or_assoc] at him'
      have himinterior := him'.resolve_left him
      try dsimp [Next]
      rw [hinterior w himinterior]
      simpa [smul_eq_mul, norm_mul] using!
        hR w
          ((abs_eq hRpos.le).mpr hvert.1.symm)
          himinterior
  have hzU : z ∈ U := by
    exact ⟨(abs_lt.mp hzR), ⟨hza, hzb⟩⟩
  have hmax := norm_extension_le_of_frontier
    hUopen hUconvex.isPreconnected hUbounded
    hweighted hNext hNextinterior
    hNextfrontier (subset_closure hzU)
  calc
    ‖damp ε z • f z‖ = Next z := by
      symm
      exact hNextinterior z hzU
    _ ≤ C := hmax
end CohnElkies
