-- Prove2me | solution 1 for GJNSteadyState.Interchange.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:39:17.651456+00:00
-- url     : https://prove2.me/submissions/c85a1d81-3d29-46fc-8f4a-22397261186e

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Lyapunov
import Theorems.Thm_GJNSteadyState_Interchange_theorem_5
open MeasureTheory ProbabilityTheory

/-- `e^u ≤ 1 + u + (u²/2) e^{u⁺}` for every real `u`. -/
private lemma exp_le_quad (u : ℝ) : Real.exp u ≤ 1 + u + u ^ 2 / 2 * Real.exp (max u 0) := by
  rcases le_total u 0 with hu | hu
  · rw [max_eq_right hu, Real.exp_zero, mul_one]
    -- f t = 1 + t + t^2/2 - exp t is antitone on (-∞, 0]
    let f : ℝ → ℝ := fun t => 1 + t + t ^ 2 / 2 - Real.exp t
    have hderiv : ∀ t, HasDerivAt f (1 + t - Real.exp t) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => 1 + t + t ^ 2 / 2) (1 + t) t := by
        have := ((hasDerivAt_id t).const_add 1).add ((hasDerivAt_pow 2 t).div_const 2)
        exact this.congr_deriv (by norm_num)
      exact h1.sub (Real.hasDerivAt_exp t)
    have hanti : AntitoneOn f (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
      · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
      · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
      · intro t _
        rw [(hderiv t).deriv]
        linarith [Real.add_one_le_exp t]
    have := hanti hu (Set.mem_Iic.2 le_rfl) hu
    simp only [f, Real.exp_zero] at this
    linarith
  · rw [max_eq_left hu]
    let g : ℝ → ℝ := fun t => 1 + t + t ^ 2 / 2 * Real.exp t - Real.exp t
    have hderiv : ∀ t, HasDerivAt g (1 + (t * Real.exp t + t ^ 2 / 2 * Real.exp t)
        - Real.exp t) t := by
      intro t
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * Real.exp t)
          (t * Real.exp t + t ^ 2 / 2 * Real.exp t) t := by
        have := ((hasDerivAt_pow 2 t).div_const 2).mul (Real.hasDerivAt_exp t)
        exact this.congr_deriv (by norm_num)
      exact (((hasDerivAt_id t).const_add 1).add h2).sub (Real.hasDerivAt_exp t)
    have hmono : MonotoneOn g (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
      · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
      · intro t _
        rw [(hderiv t).deriv]
        have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
        have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
        have h3 : Real.exp t * (1 - t) ≤ 1 :=
          calc Real.exp t * (1 - t) ≤ Real.exp t * Real.exp (-t) :=
                mul_le_mul_of_nonneg_left h1 (Real.exp_pos t).le
            _ = 1 := h2
        have h4 : 0 ≤ t ^ 2 / 2 * Real.exp t := by positivity
        nlinarith [Real.exp_pos t]
    have := hmono (Set.mem_Ici.2 le_rfl) hu hu
    simp only [g, Real.exp_zero] at this
    linarith

open GJNSteadyState.Interchange in
theorem solution {X : Type*} [MeasurableSpace X] (κ : Kernel X X) [IsMarkovKernel κ]
    (π : Measure X) [IsProbabilityMeasure π] (hπ : κ.Invariant π)
    (Φ : X → NNReal) (hΦ : Measurable Φ) (γ K : ℝ)
    (hlyap : IsLyapunov (kernelExp κ) Φ γ K) (hne : ∃ x, K < (Φ x : ℝ))
    (θ : ℝ) (hθ : 0 < θ) (h28 : ENNReal.ofReal θ * L2 (kernelExp κ) Φ θ ≤ ENNReal.ofReal γ) :
    IsGeomLyapunov (kernelExp κ) (fun x => Real.toNNReal (Real.exp (θ * Φ x)))
        (1 - γ * θ / 2) (Real.exp (θ * K)) ∧
      ∀ s : ℝ, K < s →
        π {x | s < (Φ x : ℝ)} ≤
          (ENNReal.ofReal (γ * θ / 2))⁻¹ * L1 (kernelExp κ) Φ θ *
            ENNReal.ofReal (Real.exp (-(θ * (s - K)))) := by
  obtain ⟨hγ, hlyap⟩ := hlyap
  have hΦr : Measurable (fun y => (Φ y : ℝ)) := measurable_coe_nnreal_real.comp hΦ
  -- the exponential of the increment
  let e : X → X → ENNReal := fun x y => ENNReal.ofReal (Real.exp (θ * ((Φ y : ℝ) - Φ x)))
  have he_meas : ∀ x, Measurable (e x) := by
    intro x
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hΦr.sub_const _).const_mul θ))
  -- key estimate (*)
  have hstar : ∀ x, K < (Φ x : ℝ) →
      ∫⁻ y, e x y ∂(κ x) + ENNReal.ofReal (θ * γ) ≤ 1 + ENNReal.ofReal (θ * γ / 2) := by
    intro x hx
    let Qf : X → ENNReal := fun y => ENNReal.ofReal
      (((Φ y : ℝ) - Φ x) ^ 2 * Real.exp (θ * max ((Φ y : ℝ) - Φ x) 0))
    have hQm : Measurable Qf := by
      apply ENNReal.measurable_ofReal.comp
      exact ((hΦr.sub_const _).pow_const 2).mul
        (Real.measurable_exp.comp (((hΦr.sub_const _).max measurable_const).const_mul θ))
    have hQL2 : ∫⁻ y, Qf y ∂(κ x) ≤ L2 (kernelExp κ) Φ θ := by
      unfold L2
      exact le_iSup (fun x => kernelExp κ x (fun y => ENNReal.ofReal
        (((Φ y : ℝ) - Φ x) ^ 2 * Real.exp (θ * max ((Φ y : ℝ) - Φ x) 0)))) x
    -- pointwise inequality
    have hpt : ∀ y, e x y + ENNReal.ofReal (θ * Φ x) ≤
        1 + ENNReal.ofReal θ * (Φ y : ENNReal) + ENNReal.ofReal (θ ^ 2 / 2) * Qf y := by
      intro y
      have hq := exp_le_quad (θ * ((Φ y : ℝ) - Φ x))
      have hmax : max (θ * ((Φ y : ℝ) - Φ x)) 0 = θ * max ((Φ y : ℝ) - Φ x) 0 := by
        rw [mul_max_of_nonneg _ _ hθ.le, mul_zero]
      rw [hmax] at hq
      have hΦx : (0 : ℝ) ≤ Φ x := (Φ x).2
      have hΦy : (0 : ℝ) ≤ Φ y := (Φ y).2
      have hQ0 : 0 ≤ ((Φ y : ℝ) - Φ x) ^ 2 * Real.exp (θ * max ((Φ y : ℝ) - Φ x) 0) := by
        positivity
      simp only [e, Qf]
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
      rw [show (Φ y : ENNReal) = ENNReal.ofReal (Φ y : ℝ) by simp,
        ← ENNReal.ofReal_mul hθ.le, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith
    have hint : ∫⁻ y, e x y ∂(κ x) + ENNReal.ofReal (θ * Φ x) ≤
        1 + ENNReal.ofReal θ * ∫⁻ y, (Φ y : ENNReal) ∂(κ x)
          + ENNReal.ofReal (θ ^ 2 / 2) * L2 (kernelExp κ) Φ θ := by
      have hΦm : Measurable (fun y => (Φ y : ENNReal)) := measurable_coe_nnreal_ennreal.comp hΦ
      calc ∫⁻ y, e x y ∂(κ x) + ENNReal.ofReal (θ * Φ x)
          = ∫⁻ y, (e x y + ENNReal.ofReal (θ * Φ x)) ∂(κ x) := by
            rw [lintegral_add_right _ measurable_const]; simp
        _ ≤ ∫⁻ y, (1 + ENNReal.ofReal θ * (Φ y : ENNReal) + ENNReal.ofReal (θ ^ 2 / 2) * Qf y)
              ∂(κ x) := lintegral_mono hpt
        _ = 1 + ENNReal.ofReal θ * ∫⁻ y, (Φ y : ENNReal) ∂(κ x)
              + ENNReal.ofReal (θ ^ 2 / 2) * ∫⁻ y, Qf y ∂(κ x) := by
            rw [lintegral_add_right _ (hQm.const_mul _), lintegral_add_left measurable_const,
              lintegral_const_mul _ hΦm, lintegral_const_mul _ hQm]
            simp
        _ ≤ _ := by gcongr
    have hly := hlyap x hx
    have hE : kernelExp κ x (fun y => (Φ y : ENNReal)) = ∫⁻ y, (Φ y : ENNReal) ∂(κ x) := rfl
    rw [hE] at hly
    -- θ²/2 L2 ≤ θγ/2
    have hL2 : ENNReal.ofReal (θ ^ 2 / 2) * L2 (kernelExp κ) Φ θ ≤ ENNReal.ofReal (θ * γ / 2) := by
      calc ENNReal.ofReal (θ ^ 2 / 2) * L2 (kernelExp κ) Φ θ
          = ENNReal.ofReal (θ / 2) * (ENNReal.ofReal θ * L2 (kernelExp κ) Φ θ) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]; congr 2; ring
        _ ≤ ENNReal.ofReal (θ / 2) * ENNReal.ofReal γ := by gcongr
        _ = ENNReal.ofReal (θ * γ / 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    -- θ E Φ + θγ ≤ θ Φx
    have hθly : ENNReal.ofReal θ * ∫⁻ y, (Φ y : ENNReal) ∂(κ x) + ENNReal.ofReal (θ * γ) ≤
        ENNReal.ofReal (θ * Φ x) := by
      have : ENNReal.ofReal θ * (∫⁻ y, (Φ y : ENNReal) ∂(κ x) + ENNReal.ofReal γ) ≤
          ENNReal.ofReal θ * (Φ x : ENNReal) := by gcongr
      rw [mul_add] at this
      rw [ENNReal.ofReal_mul hθ.le, ENNReal.ofReal_mul hθ.le, ENNReal.ofReal_coe_nnreal]
      exact this
    have hfin : ENNReal.ofReal (θ * Φ x) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h5 : ∫⁻ y, e x y ∂(κ x) + ENNReal.ofReal (θ * γ) + ENNReal.ofReal (θ * Φ x) ≤
        1 + ENNReal.ofReal (θ * γ / 2) + ENNReal.ofReal (θ * Φ x) := by
      calc ∫⁻ y, e x y ∂(κ x) + ENNReal.ofReal (θ * γ) + ENNReal.ofReal (θ * Φ x)
          = (∫⁻ y, e x y ∂(κ x) + ENNReal.ofReal (θ * Φ x)) + ENNReal.ofReal (θ * γ) := by ring
        _ ≤ (1 + ENNReal.ofReal θ * ∫⁻ y, (Φ y : ENNReal) ∂(κ x)
              + ENNReal.ofReal (θ * γ / 2)) + ENNReal.ofReal (θ * γ) := by
            exact add_le_add (le_trans hint (by gcongr)) le_rfl
        _ = 1 + ENNReal.ofReal (θ * γ / 2) +
              (ENNReal.ofReal θ * ∫⁻ y, (Φ y : ENNReal) ∂(κ x) + ENNReal.ofReal (θ * γ)) := by ring
        _ ≤ 1 + ENNReal.ofReal (θ * γ / 2) + ENNReal.ofReal (θ * Φ x) := by gcongr
    exact (ENNReal.add_le_add_iff_right hfin).1 h5
  -- consequence: ∫ e ≤ 1 - θγ/2, and γθ/2 < 1
  have hhalf : ENNReal.ofReal (θ * γ) = ENNReal.ofReal (θ * γ / 2) + ENNReal.ofReal (θ * γ / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hbound : ∀ x, K < (Φ x : ℝ) →
      ∫⁻ y, e x y ∂(κ x) + ENNReal.ofReal (θ * γ / 2) ≤ 1 := by
    intro x hx
    have h1 : (∫⁻ y, e x y ∂(κ x) + ENNReal.ofReal (θ * γ / 2)) + ENNReal.ofReal (θ * γ / 2) ≤
        1 + ENNReal.ofReal (θ * γ / 2) := by
      rw [add_assoc, ← hhalf]; exact hstar x hx
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
  have hlt1 : γ * θ / 2 < 1 := by
    obtain ⟨x0, hx0⟩ := hne
    have hb := hbound x0 hx0
    have hpos : 0 < ∫⁻ y, e x0 y ∂(κ x0) := by
      rw [lt_iff_le_and_ne, ne_comm, Ne, lintegral_eq_zero_iff (he_meas x0)]
      refine ⟨zero_le, fun h => ?_⟩
      have h' : ∀ᵐ y ∂(κ x0), False := by
        filter_upwards [h] with y hy
        simp only [e, Pi.zero_apply, ENNReal.ofReal_eq_zero] at hy
        exact absurd hy (not_le.2 (Real.exp_pos _))
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h'
      exact IsProbabilityMeasure.ne_zero (κ x0) h'
    have : ENNReal.ofReal (θ * γ / 2) < 1 := by
      calc ENNReal.ofReal (θ * γ / 2) < ∫⁻ y, e x0 y ∂(κ x0) + ENNReal.ofReal (θ * γ / 2) := by
            rw [add_comm]; exact ENNReal.lt_add_right ENNReal.ofReal_ne_top hpos.ne'
        _ ≤ 1 := hb
    rw [ENNReal.ofReal_lt_one] at this
    linarith
  have hexpE : ∀ x, kernelExp κ x (fun y => ((Real.toNNReal (Real.exp (θ * Φ y)) : NNReal) : ENNReal))
      = ENNReal.ofReal (Real.exp (θ * Φ x)) * ∫⁻ y, e x y ∂(κ x) := by
    intro x
    unfold kernelExp
    rw [← lintegral_const_mul _ (he_meas x)]
    congr 1; funext y
    simp only [e]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    change ENNReal.ofReal _ = _
    congr 2; ring
  have hgeo : IsGeomLyapunov (kernelExp κ) (fun x => Real.toNNReal (Real.exp (θ * Φ x)))
      (1 - γ * θ / 2) (Real.exp (θ * K)) := by
    refine ⟨by linarith, by nlinarith, fun x hx => ?_⟩
    have hx' : K < (Φ x : ℝ) := by
      simp only [Real.coe_toNNReal _ (Real.exp_pos _).le] at hx
      have := Real.exp_lt_exp.1 hx
      exact lt_of_mul_lt_mul_left this hθ.le
    rw [hexpE x]
    have hb := hbound x hx'
    have hle : ∫⁻ y, e x y ∂(κ x) ≤ ENNReal.ofReal (1 - γ * θ / 2) := by
      rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
      rw [show γ * θ / 2 = θ * γ / 2 by ring]
      exact ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hb
    change ENNReal.ofReal (Real.exp (θ * Φ x)) * ∫⁻ y, e x y ∂(κ x) ≤
      ENNReal.ofReal (1 - γ * θ / 2) * ENNReal.ofReal (Real.exp (θ * Φ x))
    rw [mul_comm]
    gcongr
  refine ⟨hgeo, fun s hs => ?_⟩
  set Ψ : X → NNReal := fun x => Real.toNNReal (Real.exp (θ * Φ x)) with hΨ
  have hΨm : Measurable Ψ :=
    measurable_real_toNNReal.comp (Real.measurable_exp.comp (hΦr.const_mul θ))
  -- phiSup Ψ ≤ L1
  have hphiL1 : phiSup (kernelExp κ) Ψ ≤ L1 (kernelExp κ) Φ θ := by
    unfold phiSup
    refine iSup_le (fun x => ?_)
    rw [hΨ, hexpE x]
    have hne0 : ENNReal.ofReal (Real.exp (θ * Φ x)) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
    have hnt : ENNReal.ofReal (Real.exp (θ * Φ x)) ≠ ⊤ := ENNReal.ofReal_ne_top
    change ((ENNReal.ofReal (Real.exp (θ * Φ x))))⁻¹ * (ENNReal.ofReal (Real.exp (θ * Φ x)) *
      ∫⁻ y, e x y ∂(κ x)) ≤ _
    rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnt, one_mul]
    unfold L1 kernelExp
    exact le_iSup (fun x => ∫⁻ y, ENNReal.ofReal (Real.exp (θ * ((Φ y : ℝ) - Φ x))) ∂(κ x)) x
  have hc0 : ENNReal.ofReal (γ * θ / 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  by_cases hL1 : L1 (kernelExp κ) Φ θ = ⊤
  · rw [hL1, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top), ENNReal.top_mul]
    · exact le_top
    · rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  have hphi : phiSup (kernelExp κ) Ψ < ⊤ := lt_of_le_of_lt hphiL1 (lt_top_iff_ne_top.2 hL1)
  have h5 := GJNSteadyState.Interchange.theorem_5 κ π hπ Ψ hΨm (1 - γ * θ / 2)
    (Real.exp (θ * K)) hgeo hphi
  rw [show 1 - (1 - γ * θ / 2) = γ * θ / 2 by ring] at h5
  -- Markov inequality
  have hmarkov : ENNReal.ofReal (Real.exp (θ * s)) * π {x | s < (Φ x : ℝ)} ≤
      ∫⁻ x, (Ψ x : ENNReal) ∂π := by
    refine le_trans ?_ (mul_meas_ge_le_lintegral₀
      (measurable_coe_nnreal_ennreal.comp hΨm).aemeasurable (ENNReal.ofReal (Real.exp (θ * s))))
    gcongr with x
    intro hx
    change ENNReal.ofReal _ ≤ ENNReal.ofReal _
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_exp.2 (by nlinarith)
  have hes0 : ENNReal.ofReal (Real.exp (θ * s)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  have hsplit : ENNReal.ofReal (Real.exp (θ * K)) =
      ENNReal.ofReal (Real.exp (-(θ * (s - K)))) * ENNReal.ofReal (Real.exp (θ * s)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
  have hfinal : π {x | s < (Φ x : ℝ)} * ENNReal.ofReal (Real.exp (θ * s)) ≤
      ((ENNReal.ofReal (γ * θ / 2))⁻¹ * L1 (kernelExp κ) Φ θ *
        ENNReal.ofReal (Real.exp (-(θ * (s - K))))) * ENNReal.ofReal (Real.exp (θ * s)) := by
    rw [mul_comm]
    refine le_trans hmarkov (le_trans h5 ?_)
    rw [div_eq_mul_inv, hsplit]
    calc phiSup (kernelExp κ) Ψ * (ENNReal.ofReal (Real.exp (-(θ * (s - K)))) *
          ENNReal.ofReal (Real.exp (θ * s))) * (ENNReal.ofReal (γ * θ / 2))⁻¹
        ≤ L1 (kernelExp κ) Φ θ * (ENNReal.ofReal (Real.exp (-(θ * (s - K)))) *
          ENNReal.ofReal (Real.exp (θ * s))) * (ENNReal.ofReal (γ * θ / 2))⁻¹ := by gcongr
      _ = _ := by ring
  exact (ENNReal.mul_le_mul_iff_left hes0 ENNReal.ofReal_ne_top).1 hfinal
