-- Prove2me | solution 1 for DiffractionCore.bd_weighted_logDeriv_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:01:38.024995+00:00
-- url     : https://prove2.me/submissions/23c6ade4-9d4f-4d00-9262-23d20217b65b

import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_DiffractionCore_rect_weighted_residue_sum_generic
import Theorems.Thm_RHInBoxAnalytic_zeta_blaschke_split_ball
/- Task 2 (parameterized RH-in-a-box): generalize the zeta Blaschke split + box argument
   principle from the merged FIXED ball `ball cB 13` / fixed corners to an ARBITRARY box
   `[sigma0, sigma1] x [T0, T1]` with a VARIABLE Blaschke ball `(c, R)`, the geometry entering
   only as hypotheses `hRpos`, `hbox_ball`, `hs1` (and the box-ordering `hsig`, `hT`).

   This file reproduces, over variable corners and a variable ball, the three merged atoms
     - the per-pole interior winding `Bd((z-ρ)^{-1}) = 2*pi*I` (branch-split primitive),
     - the residue-sum linearity `Bd(∑ d/(z-ρ)) = 2*pi*I*∑ d`,
     - the analytic E-arg-principle `Bd(E) = 0` (Mathlib `integral_boundary_rect_eq_zero...`),
   and the KERNEL-DERIVED local Blaschke split of `logDeriv riemannZeta` over the variable ball
   (`MeromorphicOn.extract_zeros_poles`, E-holomorphicity in-kernel), then composes them into
     `RHInBoxAnalytic.zeta_count_eq_winding_generic`:
   the actual divisor of `riemannZeta` over `ball c R` is nonneg, captures every box zero, and its
   total equals the Arb winding integer `N` (derived from `hwind` via the argument principle).

   Divisor-support finiteness is obtained from `IsCompact.inter_riemannZetaZeros_finite`
   (compact `closedBall c R` meets `riemannZetaZeros` finitely), NOT from meromorphy on the closed
   ball -- so no assumption is needed about the pole `1` on the closed-ball boundary; only
   `1 ∉ ball c R` (open) enters, exactly as the brief requires.

   conjecture1_proved = False.  This is a kernel derivation of a parameterized argument-principle
   count; it does NOT prove RH. -/


open Complex Filter MeasureTheory Real
open scoped Topology

namespace RHInBoxAnalytic

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.
    (Verbatim from the merged `BlaschkeBox.lean`; pure Mathlib, function-agnostic.) -/







/-! ## Part B: log-derivative of the factorized-rational product.  (Verbatim.) -/





/-! ## Part C: `riemannZeta` meromorphic-order facts on `{1}ᶜ`.  (Verbatim from merged.) -/



/-! ## Part D: generic per-pole interior winding and residue-sum atoms over variable corners.

    Generalizes `WindingCount.winding_lambda_five_rect_winding` and
    `BoxArgPrinciple.box_residue_sum_lambda` from the fixed corners `2/5,3/5,10,35` to variable
    `sigma0 < ρ.re < sigma1`, `T0 < ρ.im < T1`. -/









/-- **Generic analytic E-arg-principle.**  Four-segment boundary integral of a function holomorphic
    on the closed box vanishes.  Box instance of Mathlib
    `integral_boundary_rect_eq_zero_of_differentiableOn`, with the corner geometry as ordering
    hypotheses. -/
theorem rect_arg_principle_generic
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1) (f : ℂ → ℂ)
    (H : DifferentiableOn ℂ f (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1)) :
    (∫ x : ℝ in sigma0..sigma1, f (↑x + (T0 : ℂ) * I))
        - (∫ x : ℝ in sigma0..sigma1, f (↑x + (T1 : ℂ) * I))
        + I • (∫ y : ℝ in T0..T1, f ((sigma1 : ℂ) + ↑y * I))
        - I • (∫ y : ℝ in T0..T1, f ((sigma0 : ℂ) + ↑y * I)) = 0 := by
  have key := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((sigma0 : ℂ) + (T0 : ℂ) * I) ((sigma1 : ℂ) + (T1 : ℂ) * I)
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at key
  norm_num at key ⊢
  -- `key`'s hypothesis is stated over `[[sigma0, sigma1]] ×ℂ [[T0, T1]]`; convert to `Icc`.
  rw [Set.uIcc_of_le hsig, Set.uIcc_of_le hT] at key
  exact key H

/-! ## Part E: variable-ball local Blaschke split of `logDeriv riemannZeta`.

    Generalizes `BlaschkeBox.zeta_blaschke_split_box` to an arbitrary ball `(c, R)` whose interior
    avoids `1` (`hs1`) and whose box `[σ0,σ1]x[T0,T1] ⊆ ball c R` (`hbox_ball`).  Divisor
    finiteness comes from `IsCompact.inter_riemannZetaZeros_finite`. -/









/-! ## Part F: the parameterized capstone. -/



end RHInBoxAnalytic


/-  DIFFRACTION CORE (Dyson/quasicrystal axis, QC2 brick 1): the WEIGHTED rectangle pole formula.

    The T-ladder counts zeros (`rect_winding_generic`: `Bd((·-ρ)⁻¹) = 2πi`, the `g ≡ 1` case).
    The Dyson/Weil axis needs WEIGHTED sums over zeros — `Σ_ρ g(ρ)` for analytic test weights —
    because the explicit formula IS the diffraction identity: weighted zero-sums on one side,
    Bragg peaks at `k·log p` (prime sums) on the other.  This brick proves the single-pole
    mechanism over a rectangle:

      `Bd(g·(·-ρ)⁻¹) = 2πi·g(ρ)`   (g holomorphic near the closed box, ρ strictly interior).

    Proof: the removable-singularity split `g(z)·(z-ρ)⁻¹ = dslope g ρ z + g(ρ)·(z-ρ)⁻¹` (off ρ);
    `dslope g ρ` is holomorphic ACROSS ρ (Mathlib `has_fpower_series_dslope_fslope`), so its
    boundary integral vanishes by the generic rectangle Goursat (`rect_arg_principle_generic`);
    the remainder is `g(ρ)` times the counting winding (`rect_winding_generic`).

    Downstream (QC ladder): QC2 brick 2 = finite-sum version over a zero Finset (mirrors
    `box_residue_sum_generic`); QC3 = the finite-height Guinand–Weil identity, pushing the
    right edge to `Re > 1` where Mathlib's `LSeries_vonMangoldt_eq` (`L Λ = -ζ'/ζ`) turns the
    contour into PRIME SUMS — the Bragg peaks, kernel-side.  The Archimedean term is already
    built (`ZeroFreeBridge.logDeriv_gammaR`, the θ-bridge).

    conjecture1_proved = False. -/






open Complex MeasureTheory Real
open scoped Topology

section
namespace DiffractionCore
end DiffractionCore
open DiffractionCore








theorem solution
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    {W : Set ℂ} (g : ℂ → ℂ) (hW : IsOpen W) (hg : DifferentiableOn ℂ g W)
    (hsubW : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ W)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    (∫ x in sigma0..sigma1, g (↑x + (T0 : ℂ) * I) * logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
      - (∫ x in sigma0..sigma1, g (↑x + (T1 : ℂ) * I) * logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
      + I • (∫ y in T0..T1, g ((sigma1 : ℂ) + ↑y * I) * logDeriv riemannZeta ((sigma1 : ℂ) + ↑y * I))
      - I • (∫ y in T0..T1, g ((sigma0 : ℂ) + ↑y * I) * logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))
    = 2 * ↑π * I * ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) * g ρ) := by
  obtain ⟨E, hE, hd1, hcap, hker⟩ := RHInBoxAnalytic.zeta_blaschke_split_ball
    sigma0 sigma1 T0 T1 c R (by
      -- positive radius: the (nonempty) box sits inside the ball
      by_contra hR0
      push_neg at hR0
      have := hbox_ball ((sigma0 : ℂ) + (T0 : ℂ) * I)
        (by constructor <;> simp [hsig]) (by constructor <;> simp [hT])
      have hlt := Metric.mem_ball.mp this
      have : (0:ℝ) ≤ dist ((sigma0 : ℂ) + (T0 : ℂ) * I) c := dist_nonneg
      linarith) hbox_ball hs1
  set Z := RHInBoxAnalytic.zeroFinset c R hs1 with hZdef
  set d : ℂ → ℤ := (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) with hddef
  have hbox_sub : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ Metric.ball c R := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    exact hbox_ball z hz.1 hz.2
  -- ζ and deriv ζ are continuous on the box (box ⊆ ball avoids the pole `1`).
  have hballne : Metric.ball c R ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hs1 hz
  have hζana : AnalyticOnNhd ℂ riemannZeta (Metric.ball c R) :=
    analyticOn_riemannZeta.mono hballne
  have hζcont : ContinuousOn riemannZeta (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hζana.differentiableOn.continuousOn).mono hbox_sub
  have hdζcont : ContinuousOn (deriv riemannZeta) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hζana.deriv.differentiableOn.continuousOn).mono hbox_sub
  have hgcont : ContinuousOn g (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) :=
    (hg.mono hsubW).continuousOn
  have hEcont : ContinuousOn E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := hE.continuousOn
  -- Edge path membership (box form), as in brick 2.
  have hmem_h : ∀ (a : ℝ), a ∈ Set.Icc T0 T1 →
      Set.MapsTo (fun t : ℝ => ((t : ℂ) + (a : ℂ) * I))
        (Set.uIcc sigma0 sigma1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro a ha t ht
    rw [Set.uIcc_of_le hsig] at ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using ht, by simpa using ha⟩
  have hmem_v : ∀ (a : ℝ), a ∈ Set.Icc sigma0 sigma1 →
      Set.MapsTo (fun t : ℝ => ((a : ℂ) + (t : ℂ) * I))
        (Set.uIcc T0 T1) (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) := by
    intro a ha t ht
    rw [Set.uIcc_of_le hT] at ht
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using ha, by simpa using ht⟩
  -- The pointwise weighted split on ball points off the zeros.
  have hsplitpt : ∀ z ∈ Metric.ball c R, riemannZeta z ≠ 0 →
      g z * logDeriv riemannZeta z
        = (∑ ρ ∈ Z, (d ρ : ℂ) * (g z * ((z - ρ)⁻¹))) + g z * E z := by
    intro z hz hnz
    rw [hker z hz hnz, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [div_eq_mul_inv]
    ring
  -- Generic edge machinery: continuity ⟹ integrability for the three integrand families.
  have hIlog_h : ∀ (a : ℝ), a ∈ Set.Icc T0 T1 →
      (∀ t ∈ Set.uIcc sigma0 sigma1, riemannZeta ((t : ℂ) + (a : ℂ) * I) ≠ 0) →
      IntervalIntegrable (fun t : ℝ => g ((t : ℂ) + (a : ℂ) * I)
        * logDeriv riemannZeta ((t : ℂ) + (a : ℂ) * I)) volume sigma0 sigma1 := by
    intro a ha hnz
    refine ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha)) ?_)
    have hEqfun : (fun t : ℝ => logDeriv riemannZeta ((t : ℂ) + (a : ℂ) * I))
        = fun t : ℝ => deriv riemannZeta ((t : ℂ) + (a : ℂ) * I)
            / riemannZeta ((t : ℂ) + (a : ℂ) * I) := by
      funext t; rw [logDeriv_apply]
    rw [hEqfun]
    exact ContinuousOn.div
      (hdζcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha))
      (hζcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha))
      hnz
  have hIlog_v : ∀ (a : ℝ), a ∈ Set.Icc sigma0 sigma1 →
      (∀ t ∈ Set.uIcc T0 T1, riemannZeta ((a : ℂ) + (t : ℂ) * I) ≠ 0) →
      IntervalIntegrable (fun t : ℝ => g ((a : ℂ) + (t : ℂ) * I)
        * logDeriv riemannZeta ((a : ℂ) + (t : ℂ) * I)) volume T0 T1 := by
    intro a ha hnz
    refine ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha)) ?_)
    have hEqfun : (fun t : ℝ => logDeriv riemannZeta ((a : ℂ) + (t : ℂ) * I))
        = fun t : ℝ => deriv riemannZeta ((a : ℂ) + (t : ℂ) * I)
            / riemannZeta ((a : ℂ) + (t : ℂ) * I) := by
      funext t; rw [logDeriv_apply]
    rw [hEqfun]
    exact ContinuousOn.div
      (hdζcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha))
      (hζcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha))
      hnz
  have hIsum_h : ∀ (a : ℝ), a ∈ Set.Icc T0 T1 → (∀ ρ ∈ Z, a ≠ ρ.im) →
      IntervalIntegrable (fun t : ℝ => ∑ ρ ∈ Z, (d ρ : ℂ)
        * (g ((t : ℂ) + (a : ℂ) * I) * (((t : ℂ) + (a : ℂ) * I) - ρ)⁻¹)) volume sigma0 sigma1 := by
    intro a ha hane
    refine ContinuousOn.intervalIntegrable (continuousOn_finsetSum Z fun ρ hρ => ?_)
    exact continuousOn_const.mul (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => (hane ρ hρ) (by
          have him := congrArg Complex.im h
          simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
            Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
            zero_add] at him
          exact him)))))
  have hIsum_v : ∀ (a : ℝ), a ∈ Set.Icc sigma0 sigma1 → (∀ ρ ∈ Z, a ≠ ρ.re) →
      IntervalIntegrable (fun t : ℝ => ∑ ρ ∈ Z, (d ρ : ℂ)
        * (g ((a : ℂ) + (t : ℂ) * I) * (((a : ℂ) + (t : ℂ) * I) - ρ)⁻¹)) volume T0 T1 := by
    intro a ha hane
    refine ContinuousOn.intervalIntegrable (continuousOn_finsetSum Z fun ρ hρ => ?_)
    exact continuousOn_const.mul (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha))
      (Continuous.continuousOn (Continuous.inv₀ (by fun_prop)
        (fun t => sub_ne_zero.mpr fun h => (hane ρ hρ) (by
          have hre := congrArg Complex.re h
          simp only [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re,
            Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, zero_mul, add_zero,
            zero_add, sub_zero] at hre
          exact hre)))))
  have hIgE_h : ∀ (a : ℝ), a ∈ Set.Icc T0 T1 → IntervalIntegrable
      (fun t : ℝ => g ((t : ℂ) + (a : ℂ) * I) * E ((t : ℂ) + (a : ℂ) * I)) volume sigma0 sigma1 := by
    intro a ha
    exact ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha))
      (hEcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_h a ha)))
  have hIgE_v : ∀ (a : ℝ), a ∈ Set.Icc sigma0 sigma1 → IntervalIntegrable
      (fun t : ℝ => g ((a : ℂ) + (t : ℂ) * I) * E ((a : ℂ) + (t : ℂ) * I)) volume T0 T1 := by
    intro a ha
    exact ContinuousOn.intervalIntegrable (ContinuousOn.mul
      (hgcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha))
      (hEcont.comp (Continuous.continuousOn (by fun_prop)) (hmem_v a ha)))
  -- Edge-splits of the weighted boundary integrals.
  have hane_b : ∀ ρ ∈ Z, T0 ≠ ρ.im := fun ρ hρ => ne_of_lt (hins ρ hρ).2.2.1
  have hane_t : ∀ ρ ∈ Z, T1 ≠ ρ.im := fun ρ hρ => ne_of_gt (hins ρ hρ).2.2.2
  have hane_r : ∀ ρ ∈ Z, sigma1 ≠ ρ.re := fun ρ hρ => ne_of_gt (hins ρ hρ).2.1
  have hane_l : ∀ ρ ∈ Z, sigma0 ≠ ρ.re := fun ρ hρ => ne_of_lt (hins ρ hρ).1
  have hsplit_h : ∀ (a : ℝ) (ha : a ∈ Set.Icc T0 T1),
      (∀ t ∈ Set.uIcc sigma0 sigma1, riemannZeta ((t : ℂ) + (a : ℂ) * I) ≠ 0) →
      (∀ ρ ∈ Z, a ≠ ρ.im) →
      (∫ t in sigma0..sigma1, g ((t : ℂ) + (a : ℂ) * I) * logDeriv riemannZeta ((t : ℂ) + (a : ℂ) * I))
        = (∫ t in sigma0..sigma1, ∑ ρ ∈ Z, (d ρ : ℂ)
            * (g ((t : ℂ) + (a : ℂ) * I) * (((t : ℂ) + (a : ℂ) * I) - ρ)⁻¹))
          + (∫ t in sigma0..sigma1, g ((t : ℂ) + (a : ℂ) * I) * E ((t : ℂ) + (a : ℂ) * I)) := by
    intro a ha hnz hane
    rw [← intervalIntegral.integral_add (hIsum_h a ha hane) (hIgE_h a ha)]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hsplitpt _ (hbox_sub (hmem_h a ha ht)) (hnz t ht)
  have hsplit_v : ∀ (a : ℝ) (ha : a ∈ Set.Icc sigma0 sigma1),
      (∀ t ∈ Set.uIcc T0 T1, riemannZeta ((a : ℂ) + (t : ℂ) * I) ≠ 0) →
      (∀ ρ ∈ Z, a ≠ ρ.re) →
      (∫ t in T0..T1, g ((a : ℂ) + (t : ℂ) * I) * logDeriv riemannZeta ((a : ℂ) + (t : ℂ) * I))
        = (∫ t in T0..T1, ∑ ρ ∈ Z, (d ρ : ℂ)
            * (g ((a : ℂ) + (t : ℂ) * I) * (((a : ℂ) + (t : ℂ) * I) - ρ)⁻¹))
          + (∫ t in T0..T1, g ((a : ℂ) + (t : ℂ) * I) * E ((a : ℂ) + (t : ℂ) * I)) := by
    intro a ha hnz hane
    rw [← intervalIntegral.integral_add (hIsum_v a ha hane) (hIgE_v a ha)]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hsplitpt _ (hbox_sub (hmem_v a ha ht)) (hnz t ht)
  -- Assemble: brick 2 on the Herglotz part, Goursat on the g·E part.
  have hSum := rect_weighted_residue_sum_generic sigma0 sigma1 T0 T1 hsig hT
    (s := Z) d g hW hg hsubW hins
  have hGE := RHInBoxAnalytic.rect_arg_principle_generic sigma0 sigma1 T0 T1 hsig hT
    (fun z => g z * E z) ((hg.mono hsubW).mul hE)
  rw [hsplit_h T0 ⟨le_refl _, hT⟩ hnzb hane_b,
    hsplit_h T1 ⟨hT, le_refl _⟩ hnzt hane_t,
    hsplit_v sigma1 ⟨hsig, le_refl _⟩ hnzr hane_r,
    hsplit_v sigma0 ⟨le_refl _, hsig⟩ hnzl hane_l]
  simp only [smul_eq_mul] at hSum hGE ⊢
  linear_combination hSum + hGE
