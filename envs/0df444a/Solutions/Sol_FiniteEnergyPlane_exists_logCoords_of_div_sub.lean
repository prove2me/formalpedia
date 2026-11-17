-- Prove2me | solution 1 for FiniteEnergyPlane.exists_logCoords_of_div_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T21:53:18.617958+00:00
-- url     : https://prove2.me/submissions/bfbbe301-afb3-4394-81ad-34417bd45c7b

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_left
import Mathlib



/-!
# B2: decay is preserved by composition with a map asymptotic to `z ↦ κ z`.

The log chart and `cylInf` identities are copied from `Scratch/JWQ_L4` (namespace `QL`).
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Real

noncomputable section

namespace BT

lemma cylInf_eq_exp (s t : ℝ) :
    cylInf s t = Complex.exp (((2 * π : ℝ) : ℂ) * ((s : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold cylInf ccwLoop
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast; ring

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  rw [cylInf_eq_exp]; exact Complex.exp_ne_zero _

lemma cylInf_add (s t s' t' : ℝ) :
    cylInf (s + s') (t + t') = cylInf s t * cylInf s' t' := by
  rw [cylInf_eq_exp, cylInf_eq_exp, cylInf_eq_exp, ← Complex.exp_add]
  congr 1
  push_cast; ring

lemma cylInf_log_arg {z : ℂ} (hz : z ≠ 0) :
    cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
  unfold cylInf ccwLoop
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hπ, Real.exp_log (norm_pos_iff.2 hz), mul_div_cancel₀ _ hπ]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- `log(1 + ζ) / (2π)`. -/
def lchart (ζ : ℂ) : ℂ := Complex.log (1 + ζ) * (((2 * π : ℝ) : ℂ))⁻¹

lemma one_add_mem_slitPlane' {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 + ζ ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.abs_re_le_norm ζ
  rw [Complex.add_re, Complex.one_re]
  linarith [neg_abs_le ζ.re]

lemma lchart_contDiffAt {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ContDiffAt ℝ ∞ lchart ζ := by
  have hlog : ContDiffAt ℝ ∞ Complex.log (1 + ζ) :=
    (Complex.contDiffAt_log (one_add_mem_slitPlane' hζ)).restrict_scalars ℝ
  exact (hlog.comp ζ (contDiffAt_const.add contDiffAt_id)).mul contDiffAt_const

lemma lchart_contDiffOn : ContDiffOn ℝ ∞ lchart (ball (0 : ℂ) 1) := fun ζ hζ =>
  (lchart_contDiffAt (mem_ball_zero_iff.1 hζ)).contDiffWithinAt

lemma lchart_zero : lchart 0 = 0 := by simp [lchart]

lemma cylInf_mul_one_add (s t : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    cylInf s t * (1 + ζ) = cylInf (s + (lchart ζ).re) (t + (lchart ζ).im) := by
  have hne : 1 + ζ ≠ 0 := Complex.slitPlane_ne_zero (one_add_mem_slitPlane' hζ)
  have hre : 2 * π * (lchart ζ).re = (Complex.log (1 + ζ)).re := by
    simp only [lchart, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
  have him : 2 * π * (lchart ζ).im = (Complex.log (1 + ζ)).im := by
    simp only [lchart, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    field_simp
  unfold cylInf ccwLoop
  rw [← Complex.exp_log hne]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul]
    push_cast
    linarith [hre]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_mul, zero_add]
    push_cast
    linarith [him]

/-- `z ↦ (Re z, Im z)` as a continuous linear map. -/
def reIm : ℂ →L[ℝ] ℝ × ℝ := Complex.reCLM.prod Complex.imCLM

@[simp] lemma reIm_apply (z : ℂ) : reIm z = (z.re, z.im) := rfl

/-- Eventual smallness from `C⁰` decay. -/
lemma eventually_norm_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ × ℝ → E} {b : ℝ} (hb : 0 < b) (ha : ExpDecayCInfty a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ t : ℝ, ‖a (s, t)‖ < ε := by
  obtain ⟨C₀, s₁, hC₀⟩ := ha.2 0
  have htend : Tendsto (fun s : ℝ => |C₀| * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.exp (-(b * s))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)
    simpa using h1.const_mul |C₀|
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 (htend.eventually (gt_mem_nhds hε))
  refine ⟨max s₁ s₂, fun s hs t => ?_⟩
  have h0 := hC₀ s ((le_max_left _ _).trans hs) t
  rw [norm_iteratedFDeriv_zero] at h0
  exact (h0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)).trans_lt
    (hs₂ s ((le_max_right _ _).trans hs))

/-- Log coordinates of a map asymptotic to `z ↦ κ z`: `χ(cylInf p) = cylInf (p + c + E p)` far out,
with `E` decaying like `e^{-bs}`. -/
lemma exists_logCoords_aux (χ : ℂ → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => χ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b) :
    ∃ (E : ℝ × ℝ → ℝ × ℝ) (S : ℝ), ExpDecayCInfty E b ∧ ∀ s ≥ S, ∀ t : ℝ,
      χ (cylInf s t) =
        cylInf ((s, t) + (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π)) + E (s, t)).1
          ((s, t) + (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π)) + E (s, t)).2 := by
  set a : ℝ × ℝ → ℂ := fun p => χ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ with ha
  -- `ζ = a / κ`
  have hζ : ExpDecayCInfty (fun p => (fun z : ℂ => z * κ⁻¹) (a p)) b :=
    expDecayCInfty_comp_left (fun z : ℂ => z * κ⁻¹) 1 one_pos
      (contDiff_id.mul contDiff_const).contDiffOn (by simp) a b hb has
  have hlc : ExpDecayCInfty (fun p => lchart (a p * κ⁻¹)) b :=
    expDecayCInfty_comp_left lchart 1 one_pos lchart_contDiffOn lchart_zero _ b hb hζ
  have hE : ExpDecayCInfty (fun p => reIm (lchart (a p * κ⁻¹))) b :=
    expDecayCInfty_comp_left reIm 1 one_pos reIm.contDiff.contDiffOn (map_zero _) _ b hb hlc
  obtain ⟨S, hS⟩ := eventually_norm_lt hb hζ one_pos
  refine ⟨fun p => reIm (lchart (a p * κ⁻¹)), S, hE, fun s hs t => ?_⟩
  have hsm : ‖a (s, t) * κ⁻¹‖ < 1 := hS s hs t
  have hc := cylInf_ne_zero s t
  have h1 : χ (cylInf s t) = cylInf s t * κ * (1 + a (s, t) * κ⁻¹) := by
    simp only [ha]
    field_simp
    ring
  rw [h1, ← cylInf_log_arg hκ, ← cylInf_add, cylInf_log_arg hκ, cylInf_mul_one_add _ _ hsm]
  simp only [reIm_apply, Prod.fst_add, Prod.snd_add]

end BT

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff Real

theorem solution (χ : ℂ → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => χ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b) :
    ∃ (E : ℝ × ℝ → ℝ × ℝ) (S : ℝ), ExpDecayCInfty E b ∧ ∀ s ≥ S, ∀ t : ℝ,
      χ (cylInf s t) =
        cylInf ((s, t) + (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π)) + E (s, t)).1
          ((s, t) + (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π)) + E (s, t)).2 :=
  BT.exists_logCoords_aux χ κ hκ b hb has
