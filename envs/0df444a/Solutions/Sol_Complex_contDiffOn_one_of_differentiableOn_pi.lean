-- Prove2me | solution 1 for Complex.contDiffOn_one_of_differentiableOn_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f9c9d7aa-eadc-5bf9-b7a8-2097df98aad1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_contDiffOn_one_of_differentiableOn_pi

set_option autoImplicit false

open Complex Metric Topology Filter Set

namespace BenchNOsgood

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}

def ev (n : ℕ) (i : Fin n) : Fin n → ℂ := Pi.single i 1

theorem norm_smul_ev (t : ℂ) (i : Fin n) : ‖t • ev n i‖ = ‖t‖ := by
  rw [norm_smul, ev, Pi.norm_single, norm_one, mul_one]

theorem add_smul_ev_mem_ball {z₀ z : Fin n → ℂ} {R r : ℝ} (hrR : 2 * r ≤ R) (hz : z ∈ ball z₀ r)
    {t : ℂ} (ht : ‖t‖ ≤ r) (i : Fin n) : z + t • ev n i ∈ ball z₀ R := by
  rw [mem_ball] at hz ⊢
  calc dist (z + t • ev n i) z₀ ≤ dist (z + t • ev n i) z + dist z z₀ := dist_triangle _ _ _
    _ = ‖t • ev n i‖ + dist z z₀ := by rw [dist_eq_norm, add_sub_cancel_left]
    _ = ‖t‖ + dist z z₀ := by rw [norm_smul_ev]
    _ < R := by linarith

theorem differentiableOn_slice (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {z : Fin n → ℂ} (i : Fin n)
    {s : Set ℂ} (hs : ∀ t ∈ s, z + t • ev n i ∈ U) :
    DifferentiableOn ℂ (fun t : ℂ => f (z + t • ev n i)) s := by
  intro t ht
  have h1 : DifferentiableAt ℂ f (z + t • ev n i) := hf.differentiableAt (hU.mem_nhds (hs t ht))
  have h2 : DifferentiableAt ℂ (fun t : ℂ => z + t • ev n i) t :=
    (differentiableAt_const z).add (differentiableAt_id.smul_const (ev n i))
  exact (h1.comp t h2).differentiableWithinAt

theorem deriv_slice (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {z : Fin n → ℂ} (hz : z ∈ U) (i : Fin n) :
    deriv (fun t : ℂ => f (z + t • ev n i)) 0 = fderiv ℂ f z (ev n i) := by
  have h1 : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • ev n i) := by
    rw [zero_smul, add_zero]
    exact (hf.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℂ => z + t • ev n i) (ev n i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (ev n i)).const_add z
  exact (h1.comp_hasDerivAt (0 : ℂ) h2).deriv

theorem fderiv_apply_ev_eq_circleIntegral (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z₀ z : Fin n → ℂ} {R r : ℝ} (hr0 : 0 < r) (hRU : ball z₀ R ⊆ U) (hrR : 2 * r ≤ R)
    (hz : z ∈ ball z₀ r) (i : Fin n) :
    fderiv ℂ f z (ev n i) =
      (2 * Real.pi * I)⁻¹ • ∮ ζ in C(0, r), (1 / (ζ - 0) ^ 2) • f (z + ζ • ev n i) := by
  have hmaps : ∀ t ∈ closedBall (0 : ℂ) r, z + t • ev n i ∈ U := fun t ht =>
    hRU (add_smul_ev_mem_ball hrR hz (by simpa [mem_closedBall, dist_zero_right] using ht) i)
  have hzU : z ∈ U := by
    have := hmaps 0 (mem_closedBall_self hr0.le)
    rwa [zero_smul, add_zero] at this
  have key := (differentiableOn_slice hU hf i hmaps).deriv_eq_smul_circleIntegral hr0
  rw [deriv_slice hU hf hzU i] at key
  rw [key, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]

theorem continuousOn_fderiv_apply_ev (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (i : Fin n) :
    ContinuousOn (fun z => fderiv ℂ f z (ev n i)) U := by
  intro z₀ hz₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R, hR0, hRU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set r : ℝ := R / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hrR : 2 * r ≤ R := by rw [hr]; linarith

  have hF : Continuous (fun p : ↥(ball z₀ r) × ℝ =>
      deriv (circleMap 0 r) p.2 • ((1 / (circleMap 0 r p.2 - 0) ^ 2) • f ((p.1 : Fin n → ℂ) + circleMap 0 r p.2 • ev n i))) := by
    have h1 : Continuous (fun p : ↥(ball z₀ r) × ℝ => deriv (circleMap 0 r) p.2) := by
      simp_rw [deriv_circleMap]
      exact ((continuous_circleMap 0 r).comp continuous_snd).mul continuous_const
    have h2 : Continuous (fun p : ↥(ball z₀ r) × ℝ => (1 / (circleMap 0 r p.2 - 0) ^ 2)) := by
      refine continuous_const.div ((((continuous_circleMap 0 r).comp continuous_snd).sub continuous_const).pow 2)
        (fun p => ?_)
      exact pow_ne_zero _ (sub_ne_zero.mpr (circleMap_ne_center hr0.ne'))
    have h3 : Continuous (fun p : ↥(ball z₀ r) × ℝ => f ((p.1 : Fin n → ℂ) + circleMap 0 r p.2 • ev n i)) := by
      refine hf.continuousOn.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).add (((continuous_circleMap 0 r).comp continuous_snd).smul
          continuous_const)) (fun p => ?_)
      refine hRU (add_smul_ev_mem_ball hrR p.1.2 ?_ i)
      rw [norm_circleMap_zero]
      exact le_of_eq (abs_of_pos hr0)
    exact h1.smul (h2.smul h3)
  have hI : Continuous (fun x : ↥(ball z₀ r) =>
      (2 * Real.pi * I)⁻¹ • ∮ ζ in C(0, r), (1 / (ζ - 0) ^ 2) • f ((x : Fin n → ℂ) + ζ • ev n i)) := by
    have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun (x : ↥(ball z₀ r)) (θ : ℝ) =>
        deriv (circleMap 0 r) θ • ((1 / (circleMap 0 r θ - 0) ^ 2) • f ((x : Fin n → ℂ) + circleMap 0 r θ • ev n i)))
      hF 0 (2 * Real.pi)
    exact this.const_smul _
  have hcont : ContinuousOn (fun z : Fin n → ℂ =>
      (2 * Real.pi * I)⁻¹ • ∮ ζ in C(0, r), (1 / (ζ - 0) ^ 2) • f (z + ζ • ev n i)) (ball z₀ r) := by
    rw [continuousOn_iff_continuous_restrict]
    exact hI
  have heq : EqOn (fun z => fderiv ℂ f z (ev n i))
      (fun z : Fin n → ℂ => (2 * Real.pi * I)⁻¹ • ∮ ζ in C(0, r), (1 / (ζ - 0) ^ 2) • f (z + ζ • ev n i)) (ball z₀ r) :=
    fun z hz => fderiv_apply_ev_eq_circleIntegral hU hf hr0 hRU hrR hz i
  exact (hcont.congr heq).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr0))

theorem fderiv_eq_sum (z : Fin n → ℂ) :
    fderiv ℂ f z = ∑ i, ContinuousLinearMap.smulRightL ℂ (Fin n → ℂ) E (ContinuousLinearMap.proj i)
      (fderiv ℂ f z (ev n i)) := by
  ext v
  rw [ContinuousLinearMap.sum_apply]
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.smulRight_apply, map_smul, ev]

theorem main (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ 1 f U := by
  have hcont : ContinuousOn (fderiv ℂ f) U := by
    have h : ContinuousOn (fun z => ∑ i, ContinuousLinearMap.smulRightL ℂ (Fin n → ℂ) E
        (ContinuousLinearMap.proj i) (fderiv ℂ f z (ev n i))) U :=
      continuousOn_finsetSum _ fun i _ =>
        (ContinuousLinearMap.smulRightL ℂ (Fin n → ℂ) E (ContinuousLinearMap.proj i)).continuous.comp_continuousOn
          (continuousOn_fderiv_apply_ev hU hf i)
    exact h.congr fun z _ => fderiv_eq_sum z
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨hf, fun h => absurd h (by simp), contDiffOn_zero.mpr hcont⟩

end BenchNOsgood

theorem solution {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ 1 f U :=
  BenchNOsgood.main hU hf

end S_Complex_contDiffOn_one_of_differentiableOn_pi
end P2MW
export P2MW.S_Complex_contDiffOn_one_of_differentiableOn_pi (solution)
