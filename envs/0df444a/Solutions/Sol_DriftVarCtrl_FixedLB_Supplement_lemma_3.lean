-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.Supplement.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:18.810358+00:00
-- url     : https://prove2.me/submissions/09b434e2-0740-4898-962b-490d06585de7

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

open DriftVarCtrl
open DriftVarCtrl.FixedLB
open DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB Filter
open scoped Topology

/-- Lemma 3 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 22, (30)–(32); proof p. EC-30). The upper curve (28),
`ĥ₂(h₁) = (μ₂/μ₁) h₁ [1 + ((v₂ − v₁)/v₂) LW(−e^{−1−(−M)μ₁v₁/h₁})]`, satisfies
`ĥ₂(h₁) → 0` and `ĥ₂′(h₁) → μ₂/μ₁` as `h₁ → 0+`, `ĥ₂′(h₁) → σ₂²/σ₁²` as `h₁ → ∞`, and
`ĥ₂″(h₁) < 0` for every `h₁ ∈ (0, ∞)`.

Formalization Note: `ĥ₂` is `upperCurve p`, a function of `h₁` alone (it does not involve the
running costs of `p` or `U`); derivatives are `deriv`. The standing `v₁ < v₂` is `hv`. -/
theorem solution (p : Params) (hv : v p .one < v p .two) :
    Tendsto (upperCurve p) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (deriv (upperCurve p)) (𝓝[>] 0) (𝓝 (p.μ₂ / p.μ₁)) ∧
    Tendsto (deriv (upperCurve p)) atTop (𝓝 (p.σ₂ ^ 2 / p.σ₁ ^ 2)) ∧
    ∀ h₁ : ℝ, 0 < h₁ → deriv (deriv (upperCurve p)) h₁ < 0 := by
      set L := LiquidWelfareFPA.lambertW with hLdef
      have hqd : ∀ y : ℝ, HasDerivAt (fun y => y * Real.exp y) (Real.exp y * (1 + y)) y := by
        intro y
        have h := (hasDerivAt_id' y).mul (Real.hasDerivAt_exp y)
        exact h.congr_deriv (by ring)
      have hq_mono : StrictMonoOn (fun y : ℝ => y * Real.exp y) (Set.Ici (-1)) := by
        apply strictMonoOn_of_deriv_pos (convex_Ici _)
        · exact (continuous_id.mul Real.continuous_exp).continuousOn
        · intro x hx
          rw [interior_Ici] at hx
          rw [(hqd x).deriv]
          have : (-1 : ℝ) < x := hx
          exact mul_pos (Real.exp_pos x) (by linarith)
      have hL_eq : ∀ y : ℝ, -1 ≤ y → L (y * Real.exp y) = y := by
        intro y hy
        have hex : ∃ z : ℝ, -1 ≤ z ∧ z * Real.exp z = y * Real.exp y := ⟨y, hy, rfl⟩
        rw [hLdef, LiquidWelfareFPA.lambertW, dif_pos hex]
        have hs := Classical.choose_spec hex
        exact hq_mono.injOn hs.1 hy hs.2
      have hL_ex : ∀ x : ℝ, -Real.exp (-1) < x → x < 0 →
          -1 < L x ∧ L x < 0 ∧ L x * Real.exp (L x) = x := by
        intro x hx1 hx2
        have hivt := intermediate_value_Icc (show (-1 : ℝ) ≤ 0 by norm_num)
          (f := fun y : ℝ => y * Real.exp y) (continuous_id.mul Real.continuous_exp).continuousOn
        obtain ⟨y, ⟨hy1, hy2⟩, hyx⟩ := hivt ⟨by simp; linarith, by simp; linarith⟩
        simp only at hyx
        have hLy : L x = y := by rw [← hyx]; exact hL_eq y hy1
        rw [hLy]
        refine ⟨?_, ?_, hyx⟩
        · rcases hy1.lt_or_eq with h | h
          · exact h
          · subst h; simp at hyx; linarith
        · rcases hy2.lt_or_eq with h | h
          · exact h
          · subst h; simp at hyx; linarith
      have hL_mono : MonotoneOn L (Set.Ioo (-Real.exp (-1)) 0) := by
        intro x1 hx1 x2 hx2 h12
        by_contra hc
        push Not at hc
        obtain ⟨a1, _, e1⟩ := hL_ex x1 hx1.1 hx1.2
        obtain ⟨a2, _, e2⟩ := hL_ex x2 hx2.1 hx2.2
        have := hq_mono (Set.mem_Ici.2 a2.le) (Set.mem_Ici.2 a1.le) hc
        simp only at this
        linarith
      have hL_deriv : ∀ x : ℝ, -Real.exp (-1) < x → x < 0 →
          HasDerivAt L (Real.exp (L x) * (1 + L x))⁻¹ x := by
        intro x hx1 hx2
        obtain ⟨a1, a2, e1⟩ := hL_ex x hx1 hx2
        have hcont : ContinuousAt L x := by
          apply continuousAt_of_monotoneOn_of_image_mem_nhds hL_mono (Ioo_mem_nhds hx1 hx2)
          apply Filter.mem_of_superset (Ioo_mem_nhds a1 a2)
          intro y hy
          refine ⟨y * Real.exp y, ⟨?_, ?_⟩, hL_eq y hy.1.le⟩
          · have := hq_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.1.le) hy.1
            simpa using this
          · have := Real.exp_pos y
            nlinarith [hy.2]
        apply HasDerivAt.of_local_left_inverse hcont (hqd (L x))
        · have := Real.exp_pos (L x)
          have : 0 < 1 + L x := by linarith
          positivity
        · filter_upwards [Ioo_mem_nhds hx1 hx2] with z hz
          exact (hL_ex z hz.1 hz.2).2.2
      have hv1 : 0 < v p .one := by
        simp only [v, Params.mu, Params.sig]; have := p.hμ₁; have := p.hσ₁; positivity
      have hv2 : 0 < v p .two := lt_trans hv1 hv
      set a : ℝ := (-p.M) * p.μ₁ * v p .one with ha_def
      have ha : 0 < a := by
        have := p.hM; have := p.hμ₁
        have : 0 < -p.M := by linarith
        positivity
      set c : ℝ := p.μ₂ / p.μ₁ with hc_def
      have hc : 0 < c := div_pos p.hμ₂ p.hμ₁
      set k : ℝ := (v p .two - v p .one) / v p .two with hk_def
      have hk0 : 0 < k := div_pos (by linarith) hv2
      have hk1 : k < 1 := by
        rw [hk_def, div_lt_one hv2]; linarith
      set w : ℝ → ℝ := fun h => L (-Real.exp (-1 - a / h)) with hw_def
      have hf_eq : upperCurve p = fun h => c * h * (1 + k * w h) := by
        funext h; simp only [upperCurve, hw_def, hLdef, hc_def, hk_def, ha_def]
      have hw : ∀ h : ℝ, 0 < h →
          -1 < w h ∧ w h < 0 ∧ w h * Real.exp (w h) = -Real.exp (-1 - a / h) := by
        intro h hh
        apply hL_ex
        · have : 0 < a / h := div_pos ha hh
          have : Real.exp (-1 - a / h) < Real.exp (-1) := Real.exp_lt_exp.2 (by linarith)
          linarith
        · have := Real.exp_pos (-1 - a / h); linarith
      have hwlog : ∀ h : ℝ, 0 < h → a / h = -1 - w h - Real.log (-w h) := by
        intro h hh
        obtain ⟨h1, h2, h3⟩ := hw h hh
        have e : (-w h) * Real.exp (w h) = Real.exp (-1 - a / h) := by linarith
        have := congrArg Real.log e
        rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at this
        linarith
      have hwd : ∀ h : ℝ, 0 < h → HasDerivAt w (w h * a / (h ^ 2 * (1 + w h))) h := by
        intro h hh
        obtain ⟨h1, h2, h3⟩ := hw h hh
        have hin : HasDerivAt (fun x : ℝ => -Real.exp (-1 - a / x))
            (-(Real.exp (-1 - a / h) * -((0 * h - a * 1) / h ^ 2))) h :=
          ((((hasDerivAt_const h a).div (hasDerivAt_id' h) hh.ne').const_sub (-1)).exp).neg
        have hx1 : -Real.exp (-1) < -Real.exp (-1 - a / h) := by
          have : 0 < a / h := div_pos ha hh
          have : Real.exp (-1 - a / h) < Real.exp (-1) := Real.exp_lt_exp.2 (by linarith)
          linarith
        have hx2 : -Real.exp (-1 - a / h) < 0 := by have := Real.exp_pos (-1 - a / h); linarith
        have hcomp := (hL_deriv _ hx1 hx2).comp h hin
        refine hcomp.congr_deriv ?_
        have hwh : L (-Real.exp (-1 - a / h)) = w h := rfl
        rw [hwh]
        have e : Real.exp (-1 - a / h) = -(w h * Real.exp (w h)) := by linarith
        rw [e]
        have : 0 < 1 + w h := by linarith
        have := Real.exp_pos (w h)
        field_simp
        ring
      set F1 : ℝ → ℝ := fun h => c * (1 + k * w h) + c * k * (w h * (a / h) / (1 + w h)) with hF1
      have hfd : ∀ h : ℝ, 0 < h → HasDerivAt (upperCurve p) (F1 h) h := by
        intro h hh
        obtain ⟨h1, h2, h3⟩ := hw h hh
        rw [hf_eq]
        have d := ((hasDerivAt_id' h).const_mul c).mul (((hwd h hh).const_mul k).const_add 1)
        refine d.congr_deriv ?_
        have : 0 < 1 + w h := by linarith
        simp only [hF1]
        field_simp
      have hderiv_eq : ∀ h : ℝ, 0 < h → deriv (upperCurve p) h = F1 h :=
        fun h hh => (hfd h hh).deriv
      -- part 4
      have part4 : ∀ h₁ : ℝ, 0 < h₁ → deriv (deriv (upperCurve p)) h₁ < 0 := by
        intro h hh
        obtain ⟨h1, h2, h3⟩ := hw h hh
        have hpos : 0 < 1 + w h := by linarith
        have hev : deriv (upperCurve p) =ᶠ[𝓝 h] F1 := by
          filter_upwards [Ioi_mem_nhds hh] with x hx
          exact hderiv_eq x hx
        rw [hev.deriv_eq]
        have d1 := (((hwd h hh).const_mul k).const_add 1).const_mul c
        have d2 := ((((hwd h hh).mul ((hasDerivAt_const h a).div (hasDerivAt_id' h) hh.ne')).div
          ((hwd h hh).const_add 1) hpos.ne').const_mul (c * k))
        have d := d1.add d2
        have hF1d : HasDerivAt F1 (c * k * w h * a ^ 2 / (h ^ 3 * (1 + w h) ^ 3)) h := by
          refine d.congr_deriv ?_
          simp only [Pi.mul_apply, Pi.div_apply]
          field_simp
          ring
        rw [hF1d.deriv]
        apply div_neg_of_neg_of_pos
        · have : 0 < c * k * a ^ 2 := by positivity
          nlinarith
        · positivity
      -- part 1
      have part1 : Tendsto (upperCurve p) (𝓝[>] 0) (𝓝 0) := by
        rw [hf_eq]
        have hup : Tendsto (fun h : ℝ => c * h) (𝓝[>] 0) (𝓝 0) := by
          apply tendsto_nhdsWithin_of_tendsto_nhds
          have : Tendsto (fun h : ℝ => c * h) (𝓝 0) (𝓝 (c * 0)) := tendsto_id.const_mul c
          rw [mul_zero] at this
          exact this
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        · filter_upwards [self_mem_nhdsWithin] with h hh
          obtain ⟨h1, h2, h3⟩ := hw h hh
          have : 0 ≤ 1 + k * w h := by nlinarith
          have : 0 < h := hh
          positivity
        · filter_upwards [self_mem_nhdsWithin] with h hh
          obtain ⟨h1, h2, h3⟩ := hw h hh
          have : (0:ℝ) < h := hh
          have : 0 ≤ c * h := by positivity
          have : 1 + k * w h ≤ 1 := by nlinarith
          nlinarith
      -- part 2
      have hT0 : Tendsto (fun h : ℝ => a / h) (𝓝[>] 0) atTop := by
        have := tendsto_inv_nhdsGT_zero.const_mul_atTop ha
        simpa [div_eq_mul_inv] using this
      have hb0 : ∀ h : ℝ, 0 < h → -w h ≤ Real.exp (-(a / h)) := by
        intro h hh
        obtain ⟨h1, h2, h3⟩ := hw h hh
        have hl := hwlog h hh
        have : Real.log (-w h) ≤ -(a / h) := by linarith
        calc -w h = Real.exp (Real.log (-w h)) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp (-(a / h)) := Real.exp_le_exp.2 this
      have hwlim0 : Tendsto w (𝓝[>] 0) (𝓝 0) := by
        have hE : Tendsto (fun h : ℝ => -Real.exp (-(a / h))) (𝓝[>] 0) (𝓝 0) := by
          have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hT0).neg
          simpa using this
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hE tendsto_const_nhds
        · filter_upwards [self_mem_nhdsWithin] with h hh
          have := hb0 h hh; linarith
        · filter_upwards [self_mem_nhdsWithin] with h hh
          exact (hw h hh).2.1.le
      have hwt0 : Tendsto (fun h => w h * (a / h)) (𝓝[>] 0) (𝓝 0) := by
        have hE : Tendsto (fun h : ℝ => -((a / h) ^ 1 * Real.exp (-(a / h)))) (𝓝[>] 0) (𝓝 0) := by
          have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hT0).neg
          simpa using this
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hE tendsto_const_nhds
        · filter_upwards [self_mem_nhdsWithin] with h hh
          have := hb0 h hh
          have : 0 < a / h := div_pos ha hh
          simp only [pow_one]
          nlinarith
        · filter_upwards [self_mem_nhdsWithin] with h hh
          have := (hw h hh).2.1
          have : 0 < a / h := div_pos ha hh
          nlinarith
      have part2 : Tendsto (deriv (upperCurve p)) (𝓝[>] 0) (𝓝 (p.μ₂ / p.μ₁)) := by
        have hF : Tendsto F1 (𝓝[>] 0) (𝓝 (c * (1 + k * 0) + c * k * (0 / (1 + 0)))) := by
          apply Tendsto.add
          · exact ((hwlim0.const_mul k).const_add 1).const_mul c
          · exact (hwt0.div ((hwlim0.const_add 1)) (by norm_num)).const_mul (c * k)
        simp only [mul_zero, add_zero, zero_div, mul_one] at hF
        show Tendsto _ _ (𝓝 c)
        apply hF.congr'
        filter_upwards [self_mem_nhdsWithin] with h hh
        exact (hderiv_eq h hh).symm
      -- part 3
      have hTinf : Tendsto (fun h : ℝ => a / h) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hB1 : ∀ h : ℝ, 0 < h → 1 + w h ≤ Real.sqrt (4 * (a / h)) := by
        intro h hh
        obtain ⟨h1, h2, h3⟩ := hw h hh
        have hl := hwlog h hh
        set u := -w h with hu
        have hu0 : 0 < u := by linarith
        have hu1 : u < 1 := by linarith
        set s := Real.sqrt u with hs
        have hs0 : 0 ≤ s := Real.sqrt_nonneg u
        have hss : s ^ 2 = u := Real.sq_sqrt hu0.le
        have hlogs : Real.log u ≤ 2 * (s - 1) := by
          have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hu0)
          rw [Real.log_sqrt hu0.le] at this
          linarith
        have hs1 : s ≤ 1 := by nlinarith
        apply Real.le_sqrt_of_sq_le
        have : (1 + w h) = 1 - u := by rw [hu]; ring
        rw [this, hl]
        nlinarith
      have hB2 : ∀ h : ℝ, 0 < h → -(1 + w h) ≤ w h * (a / h) / (1 + w h) := by
        intro h hh
        obtain ⟨h1, h2, h3⟩ := hw h hh
        have hl := hwlog h hh
        have hpos : 0 < 1 + w h := by linarith
        rw [le_div_iff₀ hpos]
        have hu0 : 0 < -w h := by linarith
        have hlog : -Real.log (-w h) ≤ 1 / (-w h) - 1 := by
          have := Real.log_le_sub_one_of_pos (one_div_pos.2 hu0)
          rw [one_div, Real.log_inv] at this
          rw [one_div]; linarith
        have hlog' : (-w h) * (-Real.log (-w h)) ≤ 1 - (-w h) := by
          have := mul_le_mul_of_nonneg_left hlog hu0.le
          rw [mul_sub, mul_one_div_cancel hu0.ne'] at this
          linarith
        rw [hl]
        nlinarith
      have hsq : Tendsto (fun h : ℝ => Real.sqrt (4 * (a / h))) atTop (𝓝 0) := by
        have := ((hTinf.const_mul 4).sqrt)
        simpa using this
      have h1w : Tendsto (fun h => 1 + w h) atTop (𝓝 0) := by
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
        · filter_upwards [eventually_gt_atTop 0] with h hh
          linarith [(hw h hh).1]
        · filter_upwards [eventually_gt_atTop 0] with h hh
          exact hB1 h hh
      have hwinf : Tendsto w atTop (𝓝 (-1)) := by
        have := h1w.sub_const 1
        simpa using this
      have hginf : Tendsto (fun h => w h * (a / h) / (1 + w h)) atTop (𝓝 0) := by
        have hneg := h1w.neg
        rw [neg_zero] at hneg
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg tendsto_const_nhds
        · filter_upwards [eventually_gt_atTop 0] with h hh
          exact hB2 h hh
        · filter_upwards [eventually_gt_atTop 0] with h hh
          obtain ⟨h1, h2, h3⟩ := hw h hh
          have : 0 < a / h := div_pos ha hh
          apply div_nonpos_of_nonpos_of_nonneg
          · nlinarith
          · linarith
      have part3 : Tendsto (deriv (upperCurve p)) atTop (𝓝 (p.σ₂ ^ 2 / p.σ₁ ^ 2)) := by
        have hF : Tendsto F1 atTop (𝓝 (c * (1 + k * (-1)) + c * k * 0)) := by
          apply Tendsto.add
          · exact ((hwinf.const_mul k).const_add 1).const_mul c
          · exact hginf.const_mul (c * k)
        have hval : c * (1 + k * (-1)) + c * k * 0 = p.σ₂ ^ 2 / p.σ₁ ^ 2 := by
          simp only [hc_def, hk_def, v, Params.mu, Params.sig]
          have := p.hμ₁; have := p.hμ₂; have := p.hσ₁; have := p.hσ₂
          field_simp
          ring
        rw [hval] at hF
        apply hF.congr'
        filter_upwards [eventually_gt_atTop 0] with h hh
        exact (hderiv_eq h hh).symm
      exact ⟨part1, part2, part3, part4⟩
