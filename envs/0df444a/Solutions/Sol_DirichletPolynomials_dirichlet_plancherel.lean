-- Prove2me | solution 1 for DirichletPolynomials.dirichlet_plancherel
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T09:25:50.204622+00:00
-- url     : https://prove2.me/submissions/7359ee30-1eed-4117-bf39-51a62999dfe4

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.SW.Kernel =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The SW rung, wave S1 — the smoothed Mellin/Perron kernel identity

The reusable analytic core of the `sw` rung's smoothed Perron machinery
(`docs/blueprints/sw.md`, Riesz amendment).  The Riesz mean `ψ₁(x,χ)` has
Mellin kernel `x^{s+1}/(s(s+1))` with `1/|s|²` decay, so its vertical integral
converges *absolutely* and its target profile `y ↦ (1-1/y)₊` is *continuous* —
exactly what mathlib's `MellinInversion` machinery serves (the discontinuous
sharp-cutoff Perron step is what it cannot do).

## Route (assessed: MellinInversion, option (a) of the blueprint — chosen)

We take `f := (1 - ·)₊` (`kern`), compute `mellin f s = 1/(s(s+1))` for
`Re s > 0` (the Beta-type integral `∫₀¹ t^{s-1}(1-t) dt = 1/s - 1/(s+1)`,
`hasMellin_kern`), verify the three hypotheses of `mellinInv_mellin_eq`
(`MellinConvergent`, `VerticalIntegrable`, `ContinuousAt` — the latter free,
`kern` is continuous), and instantiate the inversion **at `x = 1/y`**: mathlib's
`mellinInv` carries a *negative* exponent `x^{-s}`, and `reflect` turns
`(1/y)^{-s}` into the `y^{+s}` we want.  The direct two-pole contour (option
(b)) was not needed — the convention match with `MellinInversion` is clean.

## Main results

* `kernel_identity` — `(1/2π) ∫_ℝ y^{c+ti}/((c+ti)(c+ti+1)) dt = (1-1/y)₊`,
  for `y > 0`, `c > 0`.  (`•` is the real scalar action on `ℂ`; exponents are
  `Complex.cpow`; the `1/(2πi)∫ds` becomes `1/(2π)∫dt` after `ds = i·dt`.)
* `hasMellin_kern` — the companion `mellin (1-·)₊ s = 1/(s(s+1))` (+ convergence).
* `verticalIntegrable_mellin_kern` — the vertical absolute-convergence lemma
  (integrand dominated by `(c²+t²)⁻¹`, itself scaled `integrable_inv_one_add_sq`).
* `kernel_sum_swap` — the S1b interface: the dominated sum↔integral swap
  `∑ₙ ∫ aₙ(x/n)^{s}/(...) = ∫ (∑ₙ aₙ(x/n)^{s})/(...)`, under the domination
  hypothesis `Summable (fun n => ‖a n‖·(x/n)^c)` (holds in the `c > 1`,
  `‖a n‖ ≲ log n` regime; the `L'/L` connection is deferred to S1b).

All four are axiom-clean (`propext, Classical.choice, Quot.sound`); no
`native_decide`, no new axioms, no `sorry`.  Imports Mathlib only —
independent of `Salt/SW/Defs.lean`.
-/


open MeasureTheory Complex Set

noncomputable section
namespace Salt.SW

/-- The smoothing profile `t ↦ (1 - t)₊`, ℂ-valued. Continuous everywhere;
supported on `(-∞, 1]`; on `Ioi 0` it agrees with `1[Ioc 0 1]·(1 - t)`. -/
def kern : ℝ → ℂ := fun t => ((max 0 (1 - t) : ℝ) : ℂ)

lemma continuous_kern : Continuous kern :=
  Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.sub continuous_id))

lemma kern_eq_indicator_diff {t : ℝ} (ht : 0 < t) :
    kern t = Set.indicator (Ioc 0 1) (fun _ => (1 : ℂ)) t
           - Set.indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ)) t := by
  simp only [kern]
  by_cases h : t ≤ 1
  · have hmem : t ∈ Ioc (0:ℝ) 1 := ⟨ht, h⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
      max_eq_right (by linarith : (0:ℝ) ≤ 1 - t)]
    push_cast; ring
  · rw [not_le] at h
    have hnot : t ∉ Ioc (0:ℝ) 1 := by
      simp only [Set.mem_Ioc, not_and, not_le]; intro _; exact h
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot,
      max_eq_left (by linarith : (1:ℝ) - t ≤ 0)]
    push_cast; ring

/-- Companion identity: `mellin (1-·)₊ s = 1/(s(s+1))` for `Re s > 0`, together
with Mellin-convergence.  Beta-type integral `∫₀¹ t^{s-1}(1-t) = 1/s - 1/(s+1)`. -/
lemma hasMellin_kern {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent kern s ∧ mellin kern s = 1 / (s * (s + 1)) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre : (s + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at hre
    linarith
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (s := s) (1 : ℂ) (by rw [Complex.one_re]; linarith)
  simp only [Complex.cpow_one] at h2
  have hsub := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at hsub
  refine ⟨?_, ?_⟩
  · rw [MellinConvergent]
    refine hsub.1.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [kern_eq_indicator_diff ht]
  · have hmel : mellin kern s = mellin (fun t => Set.indicator (Ioc 0 1) (fun _ => (1:ℂ)) t
        - Set.indicator (Ioc 0 1) (fun u : ℝ => (u:ℂ)) t) s := by
      simp only [mellin]
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      simp only [kern_eq_indicator_diff ht]
    rw [hmel, hsub.2]
    field_simp
    ring

/-! ## Deliverable 2 — vertical absolute convergence -/

lemma s_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : ((c:ℂ) + (t:ℂ) * I) ≠ 0 := by
  have hre : ((c:ℂ) + (t:ℂ) * I).re = c := by simp
  intro h; rw [h] at hre; simp at hre; linarith

lemma s1_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : ((c:ℂ) + (t:ℂ) * I + 1) ≠ 0 := by
  have hre : ((c:ℂ) + (t:ℂ) * I + 1).re = c + 1 := by simp
  intro h; rw [h] at hre; simp at hre; linarith

lemma integrable_inv_c_sq_add_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) := by
  have hg : Integrable (fun u : ℝ => (c ^ 2)⁻¹ * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul ((c ^ 2)⁻¹)
  have hcomp : Integrable (fun t : ℝ => (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹) :=
    (integrable_comp_mul_left_iff (fun u => (c ^ 2)⁻¹ * (1 + u ^ 2)⁻¹)
      (inv_ne_zero hc.ne')).2 hg
  refine hcomp.congr ?_
  filter_upwards with t
  have hcne : c ≠ 0 := hc.ne'
  have hne : c ^ 2 + t ^ 2 ≠ 0 := by positivity
  field_simp

lemma norm_inv_denom_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(((c:ℂ) + (t:ℂ) * I) * ((c:ℂ) + (t:ℂ) * I + 1))⁻¹‖ ≤ (c ^ 2 + t ^ 2)⁻¹ := by
  have hns : ‖(c:ℂ) + (t:ℂ) * I‖ = Real.sqrt (c ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hns1 : ‖(c:ℂ) + (t:ℂ) * I + 1‖ = Real.sqrt ((c + 1) ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hle : c ^ 2 + t ^ 2 ≤ ‖(c:ℂ) + (t:ℂ) * I‖ * ‖(c:ℂ) + (t:ℂ) * I + 1‖ := by
    rw [hns, hns1]
    calc c ^ 2 + t ^ 2
        = Real.sqrt ((c ^ 2 + t ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((c ^ 2 + t ^ 2) * ((c + 1) ^ 2 + t ^ 2)) := by
            apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg t, hc.le, sq_nonneg c]
      _ = Real.sqrt (c ^ 2 + t ^ 2) * Real.sqrt ((c + 1) ^ 2 + t ^ 2) :=
            Real.sqrt_mul (by positivity) _
  rw [norm_inv, norm_mul]
  gcongr

lemma integrable_inv_denom {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (((c:ℂ) + (t:ℂ) * I) * ((c:ℂ) + (t:ℂ) * I + 1))⁻¹) := by
  refine (integrable_inv_c_sq_add_sq hc).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.inv₀
    · fun_prop
    · intro t; exact mul_ne_zero (s_ne_zero hc t) (s1_ne_zero hc t)
  · filter_upwards with t; exact norm_inv_denom_le hc t

lemma verticalIntegrable_mellin_kern {c : ℝ} (hc : 0 < c) :
    Complex.VerticalIntegrable (mellin kern) c := by
  rw [Complex.VerticalIntegrable]
  refine (integrable_inv_denom hc).congr ?_
  filter_upwards with t
  have hsre : 0 < ((c:ℂ) + (t:ℂ) * I).re := by simp; linarith
  rw [(hasMellin_kern hsre).2, one_div]

/-! ## Deliverable 1 — the kernel identity -/

/-- Reflection across the imaginary axis: `(1/y)^{-s} = y^{s}` for `y > 0`.
This is what lets us instantiate mathlib's `mellinInv` (negative exponent) at
`x = 1/y` to recover the positive-exponent `y^{s}` we want. -/
lemma reflect {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((1 / y : ℝ) : ℂ) ^ (-s) = (y : ℂ) ^ s := by
  have h1 : ((1 / y : ℝ) : ℂ) = ((y : ℂ))⁻¹ := by push_cast; ring
  have harg : ((y : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne
  rw [h1, Complex.cpow_neg, Complex.inv_cpow (y : ℂ) s harg, inv_inv]

/-- The truncated Perron value: `kern (1/y) = (1 - 1/y)₊`. -/
lemma kern_value {y : ℝ} (hy : 0 < y) :
    kern (1 / y) = if 1 ≤ y then (1 - 1 / (y : ℂ)) else 0 := by
  simp only [kern]
  by_cases h : 1 ≤ y
  · rw [if_pos h]
    have hle : (1 : ℝ) / y ≤ 1 := by rw [div_le_one hy]; exact h
    rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - 1 / y)]
    push_cast; ring
  · rw [if_neg h]
    rw [not_le] at h
    have hge : (1 : ℝ) ≤ 1 / y := by rw [le_div_iff₀ hy]; linarith
    rw [max_eq_left (by linarith : (1:ℝ) - 1 / y ≤ 0)]
    simp

/-- **The smoothed Mellin/Perron kernel identity.**  For `y > 0` and any vertical
line `Re s = c > 0`,
`(1/2π) ∫_ℝ y^{c+ti} / ((c+ti)(c+ti+1)) dt = (1 - 1/y)₊`.
(The `1/(2πi) ∫ ds` of the blueprint becomes `1/(2π) ∫ dt` after `ds = i dt`;
`•` is the real scalar action on `ℂ`.  Exponents are `Complex.cpow`.) -/
theorem kernel_identity {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) :
    (1 / (2 * Real.pi)) • ∫ t : ℝ,
        (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
          (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))
      = if 1 ≤ y then (1 - 1 / (y : ℂ)) else 0 := by
  have hx : (0 : ℝ) < 1 / y := by positivity
  have hcre : 0 < ((c : ℂ)).re := by simpa using hc
  have hMC : MellinConvergent kern (↑c) := (hasMellin_kern hcre).1
  have hVI : Complex.VerticalIntegrable (mellin kern) c := verticalIntegrable_mellin_kern hc
  have hCont : ContinuousAt kern (1 / y) := continuous_kern.continuousAt
  have key := mellinInv_mellin_eq c kern hx hMC hVI hCont
  rw [kern_value hy] at key
  rw [← key, mellinInv]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs_def
  have hsre : 0 < s.re := by rw [hs_def]; simpa using hc
  rw [(hasMellin_kern hsre).2, reflect hy s, smul_eq_mul, mul_one_div]

/-! ## Deliverable 3 — the sum ↔ integral swap (S1b interface) -/

/-- `‖(b)^{c+ti}‖ = b^c` for `b ≥ 0`, `c > 0` (constant along the vertical line). -/
lemma norm_ofReal_cpow_vert {b : ℝ} (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ = b ^ c := by
  rcases eq_or_lt_of_le hb with h | h
  · rw [← h, Complex.ofReal_zero, Complex.zero_cpow (s_ne_zero hc t), norm_zero,
      Real.zero_rpow hc.ne']
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos h]; simp

/-- Each summand `t ↦ w · b^{c+ti}/((c+ti)(c+ti+1))` is integrable on the line. -/
lemma integrable_Fterm (w : ℂ) {b : ℝ} (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · have : (fun t : ℝ => w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) = fun _ => 0 := by
      funext t
      rw [← hb0, Complex.ofReal_zero, Complex.zero_cpow (s_ne_zero hc t)]; ring
    rw [this]; exact integrable_zero _ _ _
  · refine ((integrable_inv_c_sq_add_sq hc).const_mul (‖w‖ * b ^ c)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      refine Continuous.div (continuous_const.mul (Continuous.const_cpow (by fun_prop)
        (Or.inl (Complex.ofReal_ne_zero.mpr hbpos.ne')))) (by fun_prop) ?_
      intro t; exact mul_ne_zero (s_ne_zero hc t) (s1_ne_zero hc t)
    · filter_upwards with t
      calc ‖w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
              / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))‖
          = (‖w‖ * b ^ c) * ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹‖ := by
            rw [norm_div, norm_mul, norm_ofReal_cpow_vert hbpos.le hc, norm_inv]; ring
        _ ≤ (‖w‖ * b ^ c) * (c ^ 2 + t ^ 2)⁻¹ := by
            gcongr; exact norm_inv_denom_le hc t

/-- **The summed form (S1b interface).**  For `c > 0`, `x > 0`, and a coefficient
sequence `a` whose Dirichlet-weighted tail `∑ ‖a n‖·(x/n)^c` converges (the `c > 1`,
`‖a n‖ ≲ log n` regime — deferred to S1b), the per-term kernel integrals sum to the
single vertical integral of the Dirichlet series against the kernel:
`∑ₙ ∫ aₙ (x/n)^{c+ti}/(...) = ∫ (∑ₙ aₙ (x/n)^{c+ti})/(...)`.
This is the dominated sum↔integral swap; the `L'/L` connection is S1b's job. -/
theorem kernel_sum_swap (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c)
    (hsum : Summable (fun n : ℕ => ‖a n‖ * (x / n) ^ c)) :
    ∑' n : ℕ, (∫ t : ℝ, a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
      = ∫ t : ℝ, (∑' n : ℕ, a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
  have hb : ∀ n : ℕ, (0 : ℝ) ≤ x / n := fun n => by positivity
  have hInt : ∀ n : ℕ, Integrable (fun t : ℝ => a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) :=
    fun n => integrable_Fterm (a n) (hb n) hc
  have hSum : Summable (fun n : ℕ => ∫ t : ℝ, ‖a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))‖) := by
    have heq : (fun n : ℕ => ∫ t : ℝ, ‖a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))‖)
        = fun n : ℕ => (‖a n‖ * (x / n) ^ c)
            * ∫ t : ℝ, ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹‖ := by
      funext n
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      dsimp only
      rw [norm_div, norm_mul, norm_ofReal_cpow_vert (hb n) hc, norm_inv]; ring
    rw [heq]; exact hsum.mul_right _
  rw [integral_tsum_of_summable_integral_norm hInt hSum]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [tsum_div_const]

end Salt.SW

end

end

-- ===== Salt.SW.ContourShift =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The SW rung, wave S5 — the contour shift with residues-lite

Design: `docs/blueprints/sw.md`, wave S5. The classical contour shift moves the
S1b Perron line integral `Re s = c` into the S3 zero-free region and picks up the
poles (the `s = 1` pole of `−L'/L(χ₀)` and the exceptional real zero `β₁`) as
residues. mathlib has **no** residue theorem, so this module builds the
*residues-lite* core from mathlib's rectangle Cauchy–Goursat
(`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`) plus
the principal-part / `dslope` subtraction trick.

## Route (the residues-lite machinery)

Write `rectBI z w f` for the boundary integral of `f` over the rectangle with
opposite corners `z, w` (mathlib's orientation: bottom − top + `I`·right −
`I`·left).

1. **Goursat re-export** (`rectBI_eq_zero_of_differentiableOn`): if `f` is
   analytic on the closed rectangle, `rectBI z w f = 0`.
2. **The `dslope` trick** (`rectBI_dslope_eq_zero`): for `φ` analytic on the
   closed rectangle and an interior point `p`, the difference quotient
   `dslope φ p` is analytic *except possibly at `p`*, but Goursat's
   off-a-countable-set form (exceptional set `{p}`) still gives
   `rectBI z w (dslope φ p) = 0` — no need for `dslope`-differentiability at `p`.
3. **The rectangle CIF** (`rectBI_cif`): since `φ s/(s−p) = dslope φ p s + φ p /(s−p)`
   off `p`, additivity gives `rectBI z w (fun s => φ s/(s−p)) = φ p · W`, where
   `W := rectBI z w (fun s => (s−p)⁻¹)` is the **rectangle winding number**.
4. **The winding number** (`rectBI_inv_eq_two_pi_I`): `W = 2πi` for `p` strictly
   interior — the one piece mathlib lacks.  Built from the complex-log
   antiderivative `log(s−p)` of `(s−p)⁻¹` on each edge
   (`integral_eq_sub_of_hasDerivAt` + `HasDerivAt.clog_real`); the left edge
   crosses the branch cut, so there we use `log(p−s)` instead, and the mismatch
   is exactly the two branch jumps `log w − log(−w) = ±πi` that sum to `2πi`.
5. **The residue extraction** (`rectBI_cif_eq`): `∮ φ(s)/(s−p) = 2πi·φ(p)`; and
   **the kernel residue** (`kernel_residue`): the concrete payload for the S6
   assembly — `rectBI z w (fun s => x^{s+1}/(s(s+1)) / (s−β)) = 2πi·x^{β+1}/(β(β+1))`.

Scope note (PB-floor): this module lands the residues-lite core (steps 1–5 as they
close). The full `psi1_contour_shift` assembly (truncating the S1b line integral,
the four boundary estimates via the S2 partial fractions, and the `∃-T'`/`∃-σ₀'`
well-spacing dodges) consumes this core and is the remaining S5 work.

All results axiom-clean (`propext, Classical.choice, Quot.sound`); no
`native_decide`, no new axioms, no `sorry`.
-/

open Complex Set MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section
namespace Salt.SW

/-- **The rectangle boundary integral.** `rectBI z w f` is the integral of `f`
over the (counterclockwise-from-bottom) boundary of the axis-parallel rectangle
with opposite corners `z, w`, in mathlib's Cauchy–Goursat orientation:
bottom − top + `I`·right − `I`·left.  (For `z` lower-left and `w` upper-right this
is the counterclockwise boundary.) -/
def rectBI (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
    + I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- The closed rectangle with opposite corners `z, w`. -/
def closedRect (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-- The open rectangle with opposite corners `z, w`. -/
def openRect (z w : ℂ) : Set ℂ :=
  Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)

lemma isOpen_openRect (z w : ℂ) : IsOpen (openRect z w) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

lemma openRect_subset_closedRect (z w : ℂ) : openRect z w ⊆ closedRect z w := by
  intro s hs
  obtain ⟨hre, him⟩ := hs
  exact ⟨Set.Ioo_subset_Icc_self hre, Set.Ioo_subset_Icc_self him⟩

/-- The closed rectangle is a neighbourhood of every interior (open-rectangle) point. -/
lemma closedRect_mem_nhds {z w p : ℂ} (hp : p ∈ openRect z w) : closedRect z w ∈ 𝓝 p :=
  Filter.mem_of_superset ((isOpen_openRect z w).mem_nhds hp) (openRect_subset_closedRect z w)

/-! ## 1. Cauchy–Goursat re-exports -/

/-- **Cauchy–Goursat for a rectangle, off a countable set.**  If `f` is continuous on the
closed rectangle and complex-differentiable on the open rectangle except at a countable set `s`,
then its boundary integral vanishes.  (Direct re-export of mathlib's
`integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`; `I •` becomes `I *` on `ℂ`.) -/
lemma rectBI_eq_zero_off_countable {z w : ℂ} {f : ℂ → ℂ} {s : Set ℂ} (hs : s.Countable)
    (Hc : ContinuousOn f (closedRect z w))
    (Hd : ∀ p ∈ openRect z w \ s, DifferentiableAt ℂ f p) :
    rectBI z w f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs
    Hc Hd
  simpa only [rectBI, smul_eq_mul] using h

/-- **Cauchy–Goursat for a rectangle.**  If `f` is analytic on the closed rectangle, its boundary
integral vanishes. -/
lemma rectBI_eq_zero_of_differentiableOn {z w : ℂ} {f : ℂ → ℂ}
    (H : DifferentiableOn ℂ f (closedRect z w)) : rectBI z w f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w H
  simpa only [rectBI, smul_eq_mul] using h

/-! ## 2. The `dslope` principal-part trick -/

/-- **The `dslope` Goursat vanishing.**  For `φ` analytic on the closed rectangle and an interior
point `p`, the difference quotient `dslope φ p` (which equals `(φ ·−φ p)/(·−p)` off `p` and
`deriv φ p` at `p`) is analytic on the open rectangle *except possibly at `p`* — and it is
continuous through `p`.  So Goursat's off-a-countable-set form (exceptional set `{p}`) gives a
vanishing boundary integral without ever needing `dslope`-differentiability at `p`. -/
lemma rectBI_dslope_eq_zero {z w p : ℂ} {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (closedRect z w)) (hp : p ∈ openRect z w) :
    rectBI z w (dslope φ p) = 0 := by
  have hpc : closedRect z w ∈ 𝓝 p := closedRect_mem_nhds hp
  have hφp : DifferentiableAt ℂ φ p := hφ.differentiableAt hpc
  refine rectBI_eq_zero_off_countable (s := {p}) (countable_singleton p) ?_ ?_
  · exact (continuousOn_dslope hpc).mpr ⟨hφ.continuousOn, hφp⟩
  · intro x hx
    have hxp : x ≠ p := fun h => hx.2 (mem_singleton_iff.mpr h)
    exact (differentiableAt_dslope_of_ne hxp).mpr (hφ.differentiableAt (closedRect_mem_nhds hx.1))

/-! ## 3. The rectangle Cauchy integral formula (up to the winding number) -/

/-- **Edge split.**  Along one edge (parametrised by `t ↦ γ t` for `t ∈ [a,b]`), the integrand
`φ(γ t)/(γ t − p)` splits as `dslope φ p (γ t) + φ p·(γ t − p)⁻¹`.  Given interval-integrability of
the two pieces and the pointwise identity on the edge, the edge integral splits additively. -/
private lemma edge_split {a b : ℝ} {F g h : ℝ → ℂ} (φp : ℂ)
    (hg : IntervalIntegrable g volume a b) (hh : IntervalIntegrable h volume a b)
    (hpt : Set.EqOn F (fun t => g t + φp * h t) (Set.uIcc a b)) :
    (∫ t in a..b, F t) = (∫ t in a..b, g t) + φp * ∫ t in a..b, h t := by
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_add hg (hh.const_mul φp), intervalIntegral.integral_const_mul]

/-- **One rectangle edge.**  For an edge `γ` (globally continuous) mapping the parameter interval
into the closed rectangle and avoiding the pole `p`, the edge integral of `φ(·)/(·−p)` splits as
`∫ dslope φ p (γ) + φ p · ∫ (γ−p)⁻¹`. -/
private lemma rect_edge {z w p : ℂ} {φ : ℂ → ℂ} {a b : ℝ}
    (hds : ContinuousOn (dslope φ p) (closedRect z w))
    (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hmaps : Set.MapsTo γ (Set.uIcc a b) (closedRect z w))
    (hne : ∀ t ∈ Set.uIcc a b, γ t ≠ p) :
    (∫ t in a..b, φ (γ t) / (γ t - p))
      = (∫ t in a..b, dslope φ p (γ t)) + φ p * ∫ t in a..b, (γ t - p)⁻¹ := by
  refine edge_split (φ p) ((hds.comp hγ.continuousOn hmaps).intervalIntegrable)
    (((hγ.continuousOn.sub continuousOn_const).inv₀
      (fun t ht => sub_ne_zero.mpr (hne t ht))).intervalIntegrable) ?_
  intro t ht
  have hd : γ t - p ≠ 0 := sub_ne_zero.mpr (hne t ht)
  change φ (γ t) / (γ t - p) = dslope φ p (γ t) + φ p * (γ t - p)⁻¹
  rw [dslope_of_ne φ (hne t ht), slope_def_field]
  field_simp
  ring

/-- **The rectangle Cauchy integral formula, up to the winding number.**  For `φ` analytic on the
closed rectangle with opposite corners `z` (lower-left) and `w` (upper-right), and `p` strictly
interior, the boundary integral of `φ(s)/(s−p)` equals `φ p` times the rectangle winding number
`W := rectBI z w (·−p)⁻¹`.  (Combined with `rectBI_inv_eq_two_pi_I` this is the residue extraction
`= 2πi·φ p`.)  Proof: `φ(s)/(s−p) = dslope φ p s + φ p·(s−p)⁻¹` off `p`, so additivity plus the
`dslope` Goursat vanishing (`rectBI_dslope_eq_zero`) collapse the boundary integral. -/
theorem rectBI_cif {z w p : ℂ} {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (closedRect z w))
    (hzw_re : z.re < w.re) (hzw_im : z.im < w.im)
    (hp_re : z.re < p.re ∧ p.re < w.re) (hp_im : z.im < p.im ∧ p.im < w.im) :
    rectBI z w (fun s => φ s / (s - p)) = φ p * rectBI z w (fun s => (s - p)⁻¹) := by
  -- interior membership
  have hp : p ∈ openRect z w := by
    rw [openRect, mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo,
      min_eq_left hzw_re.le, max_eq_right hzw_re.le,
      min_eq_left hzw_im.le, max_eq_right hzw_im.le]
    exact ⟨hp_re, hp_im⟩
  have hpc : closedRect z w ∈ 𝓝 p := closedRect_mem_nhds hp
  have hφc : ContinuousOn φ (closedRect z w) := hφ.continuousOn
  have hds : ContinuousOn (dslope φ p) (closedRect z w) :=
    (continuousOn_dslope hpc).mpr ⟨hφc, hφ.differentiableAt hpc⟩
  -- membership of an edge point in the closed rectangle
  have hmem : ∀ {x y : ℝ}, x ∈ Set.uIcc z.re w.re → y ∈ Set.uIcc z.im w.im →
      (↑x + ↑y * I) ∈ closedRect z w := by
    intro x y hx hy
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · simpa using hx
    · simpa using hy
  -- the ≠-p facts on each edge (interior point differs from every edge in one coordinate)
  have hbot : ∀ t ∈ Set.uIcc z.re w.re, (↑t + ↑z.im * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.im he; simp at h2; linarith [hp_im.1]
  have htop : ∀ t ∈ Set.uIcc z.re w.re, (↑t + ↑w.im * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.im he; simp at h2; linarith [hp_im.2]
  have hrgt : ∀ t ∈ Set.uIcc z.im w.im, (↑w.re + ↑t * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.re he; simp at h2; linarith [hp_re.2]
  have hlft : ∀ t ∈ Set.uIcc z.im w.im, (↑z.re + ↑t * I : ℂ) ≠ p := fun t _ he => by
    have h2 := congrArg Complex.re he; simp at h2; linarith [hp_re.1]
  -- the four edge splits
  have Ebot := rect_edge hds (fun x => ↑x + ↑z.im * I) (by fun_prop)
    (fun x hx => hmem hx left_mem_uIcc) hbot
  have Etop := rect_edge hds (fun x => ↑x + ↑w.im * I) (by fun_prop)
    (fun x hx => hmem hx right_mem_uIcc) htop
  have Ergt := rect_edge hds (fun y => ↑w.re + ↑y * I) (by fun_prop)
    (fun y hy => hmem right_mem_uIcc hy) hrgt
  have Elft := rect_edge hds (fun y => ↑z.re + ↑y * I) (by fun_prop)
    (fun y hy => hmem left_mem_uIcc hy) hlft
  -- the `dslope` Goursat vanishing, unfolded to the edge integrals
  have h0 := rectBI_dslope_eq_zero hφ hp
  simp only [rectBI] at h0 ⊢
  rw [Ebot, Etop, Ergt, Elft]
  linear_combination h0

/-! ## 4. The rectangle winding number `∮_{∂R} (s−p)⁻¹ = 2πi` -/

/-- Branch-cut jump (upper): for `Im w > 0`, `log w − log (−w) = π i` (both moduli equal, and
`arg(−w) = arg w − π`). -/
private lemma log_sub_log_neg_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log w - Complex.log (-w) = ↑Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw]

/-- Branch-cut jump (lower): for `Im w < 0`, `log w − log (−w) = −(π i)`. -/
private lemma log_sub_log_neg_im_neg {w : ℂ} (hw : w.im < 0) :
    Complex.log w - Complex.log (-w) = -(↑Real.pi * I) := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]

/-- Horizontal edge of the winding integral (fixed imaginary part `yc`): the complex-log
antiderivative `log(s−p)` is valid since the edge stays off the branch cut. -/
private lemma winding_horiz (yc : ℝ) (p : ℂ) {a b : ℝ}
    (hs : ∀ t ∈ Set.uIcc a b, ((↑t + ↑yc * I) - p) ∈ slitPlane) :
    (∫ t in a..b, ((↑t + ↑yc * I) - p)⁻¹)
      = Complex.log ((↑b + ↑yc * I) - p) - Complex.log ((↑a + ↑yc * I) - p) := by
  have hcont : ContinuousOn (fun t : ℝ => ((↑t + ↑yc * I) - p)⁻¹) (Set.uIcc a b) :=
    ContinuousOn.inv₀
      ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).continuousOn
      (fun t ht => slitPlane_ne_zero (hs t ht))
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log ((↑t + ↑yc * I) - p)) (((↑t + ↑yc * I) - p)⁻¹) t := by
    intro t ht
    have e : HasDerivAt (fun v : ℂ => (v + ↑yc * I) - p) 1 (↑t : ℂ) := by
      simpa using ((hasDerivAt_id (↑t : ℂ)).add_const (↑yc * I)).sub_const p
    have h := (e.comp_ofReal).clog_real (hs t ht)
    rwa [one_div] at h
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- Right vertical edge (fixed real part `xc`), non-crossing branch `log(s−p)`. -/
private lemma winding_vert (xc : ℝ) (p : ℂ) {a b : ℝ}
    (hs : ∀ t ∈ Set.uIcc a b, ((↑xc + ↑t * I) - p) ∈ slitPlane) :
    (∫ t in a..b, ((↑xc + ↑t * I) - p)⁻¹) * I
      = Complex.log ((↑xc + ↑b * I) - p) - Complex.log ((↑xc + ↑a * I) - p) := by
  have hcont : ContinuousOn (fun t : ℝ => ((↑xc + ↑t * I) - p)⁻¹ * I) (Set.uIcc a b) :=
    (ContinuousOn.inv₀
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).continuousOn
      (fun t ht => slitPlane_ne_zero (hs t ht))).mul continuousOn_const
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log ((↑xc + ↑t * I) - p))
        (((↑xc + ↑t * I) - p)⁻¹ * I) t := by
    intro t ht
    have e : HasDerivAt (fun v : ℂ => (↑xc + v * I) - p) I (↑t : ℂ) := by
      simpa using (((hasDerivAt_id (↑t : ℂ)).mul_const I).const_add (↑xc : ℂ)).sub_const p
    have h := (e.comp_ofReal).clog_real (hs t ht)
    rwa [div_eq_inv_mul] at h
  rw [← intervalIntegral.integral_mul_const]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- Left vertical edge (fixed real part `xc`): the edge crosses the branch cut of `log(s−p)`, so
we use the branch `log(p−s)` (valid there), whose derivative coincides with `(s−p)⁻¹·I`. -/
private lemma winding_vert_left (xc : ℝ) (p : ℂ) {a b : ℝ}
    (hs : ∀ t ∈ Set.uIcc a b, (p - (↑xc + ↑t * I)) ∈ slitPlane) :
    (∫ t in a..b, ((↑xc + ↑t * I) - p)⁻¹) * I
      = Complex.log (p - (↑xc + ↑b * I)) - Complex.log (p - (↑xc + ↑a * I)) := by
  have hne : ∀ t ∈ Set.uIcc a b, ((↑xc + ↑t * I) - p) ≠ 0 := fun t ht h =>
    slitPlane_ne_zero (hs t ht)
      (by rw [show p - (↑xc + ↑t * I) = -(((↑xc + ↑t * I) - p)) by ring, h, neg_zero])
  have hcont : ContinuousOn (fun t : ℝ => ((↑xc + ↑t * I) - p)⁻¹ * I) (Set.uIcc a b) :=
    (ContinuousOn.inv₀
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).continuousOn hne).mul continuousOn_const
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log (p - (↑xc + ↑t * I)))
        (((↑xc + ↑t * I) - p)⁻¹ * I) t := by
    intro t ht
    have e : HasDerivAt (fun v : ℂ => p - (↑xc + v * I)) (-I) (↑t : ℂ) := by
      simpa using (((hasDerivAt_id (↑t : ℂ)).mul_const I).const_add (↑xc : ℂ)).const_sub p
    have h := (e.comp_ofReal).clog_real (hs t ht)
    have hEq : (p - (↑xc + ↑t * I))⁻¹ * (-I) = ((↑xc + ↑t * I) - p)⁻¹ * I := by
      rw [show p - (↑xc + ↑t * I) = -(((↑xc + ↑t * I) - p)) by ring, inv_neg]; ring
    rw [div_eq_inv_mul, hEq] at h
    exact h
  rw [← intervalIntegral.integral_mul_const]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- **The rectangle winding number.**  For a strictly interior point `p`, the boundary integral of
`(s−p)⁻¹` around the rectangle is `2πi`.  Built from the complex-log antiderivative on each edge
(`winding_horiz`/`winding_vert`) — with the branch-cut-crossing left edge handled via `log(p−s)`
(`winding_vert_left`) — and the two branch jumps `log w − log(−w) = ±πi`.  mathlib has no residue
theorem, so this is the one piece the residues-lite core supplies by hand. -/
theorem rectBI_inv_eq_two_pi_I {z w p : ℂ}
    (hp_re : z.re < p.re ∧ p.re < w.re) (hp_im : z.im < p.im ∧ p.im < w.im) :
    rectBI z w (fun s => (s - p)⁻¹) = 2 * ↑Real.pi * I := by
  -- imaginary/real parts of the edge points (minus `p`)
  have him : ∀ (t yc : ℝ), ((↑t + ↑yc * I) - p).im = yc - p.im := fun t yc => by simp
  have hre : ∀ (xc t : ℝ), ((↑xc + ↑t * I) - p).re = xc - p.re := fun xc t => by simp
  have hreL : ∀ (xc t : ℝ), (p - (↑xc + ↑t * I)).re = p.re - xc := fun xc t => by simp
  -- slit-plane membership on each edge
  have hs_bot : ∀ t ∈ Set.uIcc z.re w.re, ((↑t + ↑z.im * I) - p) ∈ slitPlane := fun t _ =>
    mem_slitPlane_iff.mpr (Or.inr (by rw [him]; intro h; linarith [hp_im.1]))
  have hs_top : ∀ t ∈ Set.uIcc z.re w.re, ((↑t + ↑w.im * I) - p) ∈ slitPlane := fun t _ =>
    mem_slitPlane_iff.mpr (Or.inr (by rw [him]; intro h; linarith [hp_im.2]))
  have hs_rgt : ∀ t ∈ Set.uIcc z.im w.im, ((↑w.re + ↑t * I) - p) ∈ slitPlane := fun t _ =>
    mem_slitPlane_iff.mpr (Or.inl (by rw [hre]; linarith [hp_re.2]))
  have hs_lft : ∀ t ∈ Set.uIcc z.im w.im, (p - (↑z.re + ↑t * I)) ∈ slitPlane := fun t _ =>
    mem_slitPlane_iff.mpr (Or.inl (by rw [hreL]; linarith [hp_re.1]))
  -- the four edge evaluations
  have Ebot := winding_horiz z.im p hs_bot
  have Etop := winding_horiz w.im p hs_top
  have Ergt := winding_vert w.re p hs_rgt
  have Elft := winding_vert_left z.re p hs_lft
  -- branch jumps at the two left corners
  have hbTL : Complex.log ((↑z.re + ↑w.im * I) - p) - Complex.log (-((↑z.re + ↑w.im * I) - p))
      = ↑Real.pi * I := log_sub_log_neg_im_pos (by rw [him]; linarith [hp_im.2])
  have hbBL : Complex.log ((↑z.re + ↑z.im * I) - p) - Complex.log (-((↑z.re + ↑z.im * I) - p))
      = -(↑Real.pi * I) := log_sub_log_neg_im_neg (by rw [him]; linarith [hp_im.1])
  -- rewrite `p − s` corners in `Elft` to `−(s − p)` to match the branch jumps
  rw [show p - (↑z.re + ↑w.im * I) = -(((↑z.re + ↑w.im * I) - p)) by ring,
      show p - (↑z.re + ↑z.im * I) = -(((↑z.re + ↑z.im * I) - p)) by ring] at Elft
  -- assemble
  simp only [rectBI]
  rw [Ebot, Etop, mul_comm I _, mul_comm I _, Ergt, Elft]
  linear_combination hbTL - hbBL

/-! ## 5. The residue extraction and the kernel residue -/

/-- **The rectangle residue extraction.**  Combining the CIF (`rectBI_cif`) with the winding number
(`rectBI_inv_eq_two_pi_I`): for `φ` analytic on the closed rectangle and `p` strictly interior,
`∮_{∂R} φ(s)/(s−p) ds = 2πi·φ(p)`.  This is the residue theorem for a simple pole with residue
`φ(p)` — exactly the object the S5 contour shift needs to extract the exceptional-zero term. -/
theorem rectBI_cif_eq {z w p : ℂ} {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (closedRect z w))
    (hzw_re : z.re < w.re) (hzw_im : z.im < w.im)
    (hp_re : z.re < p.re ∧ p.re < w.re) (hp_im : z.im < p.im ∧ p.im < w.im) :
    rectBI z w (fun s => φ s / (s - p)) = 2 * ↑Real.pi * I * φ p := by
  rw [rectBI_cif hφ hzw_re hzw_im hp_re hp_im, rectBI_inv_eq_two_pi_I hp_re hp_im]
  ring

/-- **The kernel residue** (the S5/S6 payload).  For `x > 0` and a rectangle strictly to the right
of the imaginary axis (`0 < z.re`, so `s`, `s+1 ≠ 0` throughout), the boundary integral of the
smoothed Perron kernel `x^{s+1}/(s(s+1))` against `1/(s−β)` picks up the residue at an interior
`β`:
`∮_{∂R} x^{s+1}/(s(s+1)) · 1/(s−β) ds = 2πi · x^{β+1}/(β(β+1))`.
This is the exceptional-zero main term the contour shift extracts (the S1b kernel is
`x^{s+1}/(s(s+1))`; near a simple zero `β` the factor `−L'/L` contributes the `1/(s−β)`). -/
theorem kernel_residue {z w : ℂ} {x : ℝ} (hx : 0 < x) {β : ℂ}
    (hz0 : 0 < z.re) (hzw_re : z.re < w.re) (hzw_im : z.im < w.im)
    (hβ_re : z.re < β.re ∧ β.re < w.re) (hβ_im : z.im < β.im ∧ β.im < w.im) :
    rectBI z w (fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - β))
      = 2 * ↑Real.pi * I * ((x : ℂ) ^ (β + 1) / (β * (β + 1))) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hφ : DifferentiableOn ℂ (fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1))) (closedRect z w) := by
    intro s hs
    have hsre : 0 < s.re := by
      have hmem : s.re ∈ Set.Icc z.re w.re := by
        rw [← Set.uIcc_of_le hzw_re.le]; exact hs.1
      exact lt_of_lt_of_le hz0 hmem.1
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
    have hs1 : s + 1 ≠ 0 := fun h => by
      have : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith
    have hd : DifferentiableAt ℂ (fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1))) s := by
      apply DifferentiableAt.div
      · exact (differentiableAt_id.add_const 1).const_cpow (Or.inl hxC)
      · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
      · exact mul_ne_zero hs0 hs1
    exact hd.differentiableWithinAt
  exact rectBI_cif_eq hφ hzw_re hzw_im hβ_re hβ_im

end Salt.SW
end

end

-- ===== Salt.MR.HalaszKernel =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# HALASZ-INFRA wave I-1, FILE A — the hat-kernel Perron infrastructure

The reusable analytic core of the minimal-seam Halász route
(`docs/exploration/halasz-infra-freeze.md`, FILE A, rungs K1'–K4').  We replace
the sharp truncated Perron step by an *exact* representation against a trapezoid
("hat") kernel `hatK X h`, built from two instances of the landed smoothed
Mellin identity `Salt.SW.kernel_identity` (`Salt/SW/Kernel.lean`).

`s` abbreviates `(c : ℂ) + (t : ℂ) * I` throughout (matching the `SW.Kernel`
convention so the landed identities unify).

## Rungs

* `hatK` (K1') — the trapezoid kernel `(max (X+h-n) 0 − max (X-n) 0)/h`, an
  exact indicator of `[1, X]` off the ramp `(X, X+h]`.
* `hat_desmooth` (K1') — the desmoothing bound `‖∑_{1≤n≤⌊X⌋} aₙ − ∑ₙ aₙ hatK‖ ≤ h+1`.
* `hat_contour_rep` (K2') — the EXACT full-line vertical representation of
  `∑ₙ aₙ hatK X h n` (no truncation), via two `kernel_identity` instances.
* `hat_mellin_bound` / `hat_tail` (K3') — the kernel modulus bound and its tail,
  with the `Tsplit := (log X)^4` split ledger.
* K4' (`cos_int_pair` / `dirichlet_plancherel`) — the Poisson-kernel cosine
  integral and the Dirichlet Plancherel bilinear form — is the NAMED RESIDUAL of
  this wave (HAL-I1a NOTES): `cos_int_pair` (`∫ cos(θt)/(c²+t²) = (π/c)e^{-c|θ|}`)
  is mathlib-absent and requires the full contour/arc-limit apparatus (rectangle
  CIF `SW.ContourShift.rectBI_cif_eq` + pole at `t = ci` + edge bounds + `R→∞`);
  `dirichlet_plancherel` is its Finset-bilinear consumer (norm-sq expansion +
  finite Fubini + per-pair `Re`-linear split via `cos_int_pair` and sin-oddness).
  Both are deferred, not built here; see the wave report.
-/

open MeasureTheory Complex Set
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## K1' — the hat (trapezoid) kernel -/

/-- **The hat / trapezoid kernel** (K1').  `hatK X h n` smooths the sharp
indicator of the interval `[1, X]`: it equals `1` for `n ≤ X`, ramps down
linearly on `(X, X+h]`, and vanishes for `n > X+h`. -/
noncomputable def hatK (X h : ℝ) (n : ℕ) : ℝ :=
  (max (X + h - n) 0 - max (X - n) 0) / h

/-! ### Pointwise facts about `hatK`. -/

/-- `hatK` is nonnegative (the numerator is a difference of `max`'s in the right order). -/
lemma hatK_nonneg {X h : ℝ} (hh : 0 < h) (n : ℕ) : 0 ≤ hatK X h n := by
  refine div_nonneg ?_ hh.le
  have : max (X - n) 0 ≤ max (X + h - n) 0 := by apply max_le_max _ le_rfl; linarith
  linarith

/-- `hatK ≤ 1` (the numerator is at most `h`). -/
lemma hatK_le_one {X h : ℝ} (hh : 0 < h) (n : ℕ) : hatK X h n ≤ 1 := by
  rw [hatK, div_le_one hh]
  by_cases hc : X - (n : ℝ) ≤ 0
  · rw [max_eq_right hc]
    by_cases hd : X + h - (n : ℝ) ≤ 0
    · rw [max_eq_right hd]; linarith
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ X + h - n)]; linarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ X - n),
        max_eq_left (by linarith : (0 : ℝ) ≤ X + h - n)]; linarith

/-- On `[0, X]` the hat kernel is exactly `1` (`n ≤ X`). -/
lemma hatK_eq_one {X h : ℝ} (hh : 0 < h) {n : ℕ} (hn : (n : ℝ) ≤ X) : hatK X h n = 1 := by
  rw [hatK, max_eq_left (by linarith : (0 : ℝ) ≤ X + h - n),
    max_eq_left (by linarith : (0 : ℝ) ≤ X - n),
    show X + h - (n : ℝ) - (X - n) = h by ring, div_self hh.ne']

/-- Past the ramp the hat kernel vanishes (`X + h < n`). -/
lemma hatK_eq_zero {X h : ℝ} (hh : 0 < h) {n : ℕ} (hn : X + h < n) : hatK X h n = 0 := by
  rw [hatK, max_eq_right (by linarith : X + h - (n : ℝ) ≤ 0),
    max_eq_right (by linarith : X - (n : ℝ) ≤ 0)]; simp

/-! ### K1' — the desmoothing bound `hat_desmooth`.

CATCH (HAL-I1a, house ratification requested): the frozen statement in
`halasz-infra-freeze.md` line 13 omits the hypothesis `a 0 = 0` and is FALSE as
literally written — e.g. `X = 1.9, h = 0.5, a 0 = a 2 = 1` gives error `1.8 >
h + 1 = 1.5`.  The freeze's own COVER/DEGEN section (line 35) lists "n = 0 (ha0)"
and the downstream consumer K2' (`hat_contour_rep`) carries `ha0` explicitly, so
`ha0` is restored here. -/

/-- **The desmoothing bound** (K1').  Replacing the sharp partial sum
`∑_{1 ≤ n ≤ ⌊X⌋} aₙ` by the hat-smoothed sum `∑ₙ aₙ · hatK X h n` costs at most
`h + 1`: the difference is exactly the ramp contribution `∑_{X < n ≤ X+h}`, whose
`⌊X+h⌋ − ⌊X⌋ ≤ h + 1` terms each have modulus `≤ 1`.  (Requires `a 0 = 0`; see
the CATCH above.) -/
theorem hat_desmooth (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (ha0 : a 0 = 0)
    {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hhX : h ≤ X) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, a n) - ∑' n, a n * (hatK X h n : ℂ)‖ ≤ h + 1 := by
  have _ := hhX  -- `h ≤ X` is a frozen hypothesis; the bound holds without it
  set M := ⌊X⌋₊ with hM
  set N := ⌊X + h⌋₊ with hN
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hXh0 : (0 : ℝ) ≤ X + h := by linarith
  have hMN : M ≤ N := Nat.floor_mono (by linarith)
  -- the tsum collapses to a finite sum over `range (N+1)`
  have htsum : ∑' n, a n * (hatK X h n : ℂ)
      = ∑ n ∈ Finset.range (N + 1), a n * (hatK X h n : ℂ) := by
    apply tsum_eq_sum
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hgt : X + h < n := by
      have h1 := Nat.lt_floor_add_one (X + h)
      have hle : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [hatK_eq_zero hh hgt]; simp
  -- the sharp sum equals `∑_{Icc 1 M} aₙ · hatK` (kernel is `1` there)
  have hS : (∑ n ∈ Finset.Icc 1 M, a n)
      = ∑ n ∈ Finset.Icc 1 M, a n * (hatK X h n : ℂ) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    have hnX : (n : ℝ) ≤ X := by
      have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn.2
      have hMX : (M : ℝ) ≤ X := Nat.floor_le hX0
      linarith
    rw [hatK_eq_one hh hnX, Complex.ofReal_one, mul_one]
  have hsub : Finset.Icc 1 M ⊆ Finset.range (N + 1) := by
    intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
  rw [hS, htsum]
  -- the difference is (minus) the sum over the complement `D := range(N+1) \ Icc 1 M`
  have hdiff : (∑ n ∈ Finset.Icc 1 M, a n * (hatK X h n : ℂ))
        - (∑ n ∈ Finset.range (N + 1), a n * (hatK X h n : ℂ))
      = -(∑ n ∈ Finset.range (N + 1) \ Finset.Icc 1 M, a n * (hatK X h n : ℂ)) := by
    rw [Finset.sum_sdiff_eq_sub hsub]; ring
  rw [hdiff, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  -- `0 ∈ D`; its term vanishes by `ha0`, the rest are each `≤ 1`
  have h0D : (0 : ℕ) ∈ Finset.range (N + 1) \ Finset.Icc 1 M := by
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]; omega
  rw [← Finset.insert_erase h0D, Finset.sum_insert (by simp),
    ha0, zero_mul, norm_zero, zero_add]
  refine (Finset.sum_le_card_nsmul _ _ 1 (fun n _ => ?_)).trans ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hatK_nonneg hh n)]
    exact (mul_le_mul (ha n) (hatK_le_one hh n) (hatK_nonneg hh n) (by norm_num)).trans_eq
      (by ring)
  · rw [nsmul_eq_mul, mul_one]
    have hcardD : (Finset.range (N + 1) \ Finset.Icc 1 M).card = N + 1 - M := by
      rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hsub, Nat.card_Icc]
      omega
    have hcarderase : ((Finset.range (N + 1) \ Finset.Icc 1 M).erase 0).card = N - M := by
      rw [Finset.card_erase_of_mem h0D, hcardD]; omega
    rw [hcarderase, Nat.cast_sub hMN]
    have hNle : (N : ℝ) ≤ X + h := Nat.floor_le hXh0
    have hMgt : X - 1 < (M : ℝ) := by have h1 := Nat.lt_floor_add_one X; linarith
    linarith

/-! ## K2' — the exact vertical (contour) representation `hat_contour_rep`.

Two cpow helpers first. -/

/-- `((x/n)^s = x^s / n^s)` for a real `x ≥ 0` and `n ≥ 1` (positive real bases,
so no branch subtlety). -/
lemma ofReal_div_cpow {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ((x / (n : ℝ) : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (n : ℂ) ^ s := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have harg : (((n : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hnn]; exact Real.pi_pos.ne
  rw [show (x / (n : ℝ) : ℝ) = x * (n : ℝ)⁻¹ by rw [div_eq_mul_inv], Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hx (by positivity), Complex.ofReal_inv,
    Complex.inv_cpow _ _ harg, Complex.ofReal_natCast, div_eq_mul_inv]

/-- The value of `kernel_identity` at `y = x/n`, scaled by `x`, is exactly `max (x-n) 0`:
`x·(1 - n/x)₊ = (x-n)₊`.  (For `n ≥ 1`, so `x/n` is a genuine positive real.) -/
lemma kival_max {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    (x : ℂ) * (if 1 ≤ x / (n : ℝ) then (1 - 1 / ((x / (n : ℝ) : ℝ) : ℂ)) else 0)
      = ((max (x - n) 0 : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hnC : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn0.ne'
  split_ifs with hcond
  · have hxn : (n : ℝ) ≤ x := by rwa [le_div_iff₀ hn0, one_mul] at hcond
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ x - n), Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_natCast]
    field_simp
  · rw [not_le, div_lt_one hn0] at hcond
    rw [max_eq_right (by linarith : x - (n : ℝ) ≤ 0)]; simp

/-- Closed form for the integral of the norm of a single kernel term. -/
private lemma kterm_norm_integral (w : ℂ) {b : ℝ} (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, ‖w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))‖
      = (‖w‖ * b ^ c) * ∫ t : ℝ,
          ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹‖ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [norm_div, norm_mul, Salt.SW.norm_ofReal_cpow_vert hb hc, norm_inv]; ring

theorem hat_contour_rep (a : ℕ → ℂ) (ha0 : a 0 = 0) {X h c : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c)
    (hsum : Summable fun n => ‖a n‖ * ((X + h) / n) ^ c) :
    ∑' n, a n * (hatK X h n : ℂ)
      = (1 / (2 * Real.pi)) •
          ∫ t : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * ((((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
                - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1))
              / ((h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1)))) := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hXh : (0 : ℝ) < X + h := by linarith
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  -- second real summability (base X ≤ X+h)
  have hsum2 : Summable (fun n => ‖a n‖ * (X / (n : ℝ)) ^ c) := by
    refine hsum.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    apply Real.rpow_le_rpow (by positivity) _ hc.le
    gcongr; linarith
  -- the shared denominator-norm integral (a finite nonnegative constant)
  set Cden : ℝ := ∫ t : ℝ, ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹‖
    with hCden
  -- per-n integrals (a included)
  set M1 : ℕ → ℂ := fun n => ∫ t : ℝ, a n * (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) with hM1
  set M2 : ℕ → ℂ := fun n => ∫ t : ℝ, a n * ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) with hM2
  -- summability of the per-n integrals
  have hM1sum : Summable M1 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hsum.mul_right Cden))
    rw [hM1]
    exact (norm_integral_le_integral_norm _).trans_eq (kterm_norm_integral (a n) (by positivity) hc)
  have hM2sum : Summable M2 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hsum2.mul_right Cden))
    rw [hM2]
    exact (norm_integral_le_integral_norm _).trans_eq (kterm_norm_integral (a n) (by positivity) hc)
  -- the frozen per-n summand `W n`
  set W : ℕ → ℝ → ℂ := fun n t => a n
      * ((((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
          - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)))
        / (((n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * (h : ℂ)
            * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1))) with hW
  set rc : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) with hrc
  -- Part A per-n bridges via `kernel_identity`.
  have hM1n : ∀ n : ℕ, 1 ≤ n → a n * ((max (X + h - (n : ℝ)) 0 : ℝ) : ℂ)
      = ((X + h : ℝ) : ℂ) * (rc * M1 n) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hy : (0 : ℝ) < (X + h) / (n : ℝ) := by positivity
    have hki := Salt.SW.kernel_identity hy hc
    rw [Complex.real_smul, ← hrc] at hki
    have hMJ : M1 n = a n * ∫ t : ℝ, (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
      rw [hM1, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun t => by dsimp only; rw [mul_div_assoc]))
    rw [hMJ, ← kival_max (show (0 : ℝ) < X + h by linarith) hn, ← hki]; ring
  have hM2n : ∀ n : ℕ, 1 ≤ n → a n * ((max (X - (n : ℝ)) 0 : ℝ) : ℂ)
      = ((X : ℝ) : ℂ) * (rc * M2 n) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hy : (0 : ℝ) < X / (n : ℝ) := by positivity
    have hki := Salt.SW.kernel_identity hy hc
    rw [Complex.real_smul, ← hrc] at hki
    have hMJ : M2 n = a n * ∫ t : ℝ, ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
      rw [hM2, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun t => by dsimp only; rw [mul_div_assoc]))
    rw [hMJ, ← kival_max hXpos hn, ← hki]; ring
  -- Part A: the LHS equals the common value.
  have key : ∑' n, a n * (hatK X h n : ℂ)
      = (h : ℂ)⁻¹ * (((X + h : ℝ) : ℂ) * (rc * ∑' n, M1 n)
          - ((X : ℝ) : ℂ) * (rc * ∑' n, M2 n)) := by
    have hAn : ∀ n, a n * (hatK X h n : ℂ)
        = (h : ℂ)⁻¹ * (((X + h : ℝ) : ℂ) * (rc * M1 n) - ((X : ℝ) : ℂ) * (rc * M2 n)) := by
      intro n
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have hM10 : M1 0 = 0 := by
          rw [hM1]; simp only [ha0, zero_mul, zero_div]; exact integral_zero _ _
        have hM20 : M2 0 = 0 := by
          rw [hM2]; simp only [ha0, zero_mul, zero_div]; exact integral_zero _ _
        rw [ha0, hM10, hM20]; simp
      · rw [hatK, Complex.ofReal_div, Complex.ofReal_sub, ← mul_div_assoc, mul_sub,
          hM1n n hpos, hM2n n hpos, div_eq_inv_mul]
    rw [tsum_congr hAn, tsum_mul_left,
      Summable.tsum_sub ((hM1sum.mul_left _).mul_left _) ((hM2sum.mul_left _).mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
  -- Part B: the frozen summand `W n` and the integral swap.
  set c1 : ℂ := ((X + h : ℝ) : ℂ) / (h : ℂ) with hc1
  set c2 : ℂ := ((X : ℝ) : ℂ) / (h : ℂ) with hc2
  have hWeq : ∀ n, W n = fun (t : ℝ) =>
      c1 * (a n * (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
      - c2 * (a n * ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) := by
    intro n; funext t; rw [hW]; dsimp only
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [ha0]
    · have hns : ((n : ℂ)) ^ ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨hc0, _⟩
        exact (Nat.cast_ne_zero.mpr (by omega)) hc0
      have hs0 := Salt.SW.s_ne_zero hc t
      have hs1 := Salt.SW.s1_ne_zero hc t
      rw [hc1, hc2, ofReal_div_cpow (by linarith) hpos ((c : ℂ) + (t : ℂ) * I),
        ofReal_div_cpow (by linarith) hpos ((c : ℂ) + (t : ℂ) * I),
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hXh.ne'),
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hXpos.ne'),
        Complex.cpow_one, Complex.cpow_one]
      field_simp
  have hWint : ∀ n, Integrable (W n) := by
    intro n; rw [hWeq n]
    exact ((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c1).sub
      ((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c2)
  have hI1 : ∀ n, (∫ t : ℝ, ‖c1 * (a n * (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))‖)
      = ‖c1‖ * (‖a n‖ * ((X + h) / (n : ℝ)) ^ c * Cden) := by
    intro n; simp_rw [norm_mul]
    rw [integral_const_mul, kterm_norm_integral (a n) (b := (X + h) / (n : ℝ)) (by positivity) hc]
  have hI2 : ∀ n, (∫ t : ℝ, ‖c2 * (a n * ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))‖)
      = ‖c2‖ * (‖a n‖ * (X / (n : ℝ)) ^ c * Cden) := by
    intro n; simp_rw [norm_mul]
    rw [integral_const_mul, kterm_norm_integral (a n) (b := X / (n : ℝ)) (by positivity) hc]
  have hWsum : Summable (fun n => ∫ t : ℝ, ‖W n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (fun n => ?_)
      (((hsum.mul_right Cden).mul_left ‖c1‖).add ((hsum2.mul_right Cden).mul_left ‖c2‖))
    calc (∫ t, ‖W n t‖)
        ≤ ∫ (t : ℝ), (‖c1 * (a n * (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
            / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))‖
          + ‖c2 * (a n * ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
            / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))‖) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            ((((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c1).norm).add
              (((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c2).norm))
            (Filter.Eventually.of_forall fun t => ?_)
          rw [hWeq n]; exact norm_sub_le _ _
      _ = ‖c1‖ * (‖a n‖ * ((X + h) / (n : ℝ)) ^ c * Cden)
            + ‖c2‖ * (‖a n‖ * (X / (n : ℝ)) ^ c * Cden) := by
          rw [integral_add (((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c1).norm)
            (((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c2).norm), hI1, hI2]
  have hWval : ∀ n, (∫ t, W n t)
      = (h : ℂ)⁻¹ * (((X + h : ℝ) : ℂ) * M1 n - ((X : ℝ) : ℂ) * M2 n) := by
    intro n
    rw [hWeq n, integral_sub ((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c1)
      ((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c2),
      integral_const_mul, integral_const_mul]
    simp only [hM1, hM2]
    rw [hc1, hc2]; ring
  have hSGsum : ∀ t : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * ((((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
            - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1))
          / ((h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1))))
      = ∑' n, W n t := by
    intro t; rw [← tsum_mul_right]; refine tsum_congr (fun n => ?_)
    rw [hW]; dsimp only; rw [div_mul_div_comm]; ring
  rw [key]
  rw [Complex.real_smul, ← hrc,
    show (fun t : ℝ => (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * ((((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
            - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1))
          / ((h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1)))))
      = (fun t => ∑' n, W n t) from funext hSGsum,
    (integral_tsum_of_summable_integral_norm hWint hWsum).symm,
    tsum_congr hWval, tsum_mul_left,
    Summable.tsum_sub (hM1sum.mul_left _) (hM2sum.mul_left _), tsum_mul_left, tsum_mul_left]
  ring

/-- The per-`t` kernel factor of the contour representation (`K3'`). -/
def hatKernel (X h c t : ℝ) : ℂ :=
  (((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
      - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1))
    / ((h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1)))


-- segment (MVT) bound on the numerator
lemma cpow_seg_bound {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (t : ℝ) :
    ‖((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
        - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)‖
      ≤ ‖((c : ℂ) + (t : ℂ) * I) + 1‖ * (X + h) ^ c * h := by
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
  have hr : s + 1 ≠ 0 := by
    rw [hs]; intro he
    have := congrArg Complex.re he; simp at this; linarith
  have hderiv : ∀ u ∈ Icc X (X + h),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (s + 1)) ((s + 1) * (u : ℂ) ^ s)
        (Icc X (X + h)) u := by
    intro u hu
    have hu0 : u ≠ 0 := by rw [mem_Icc] at hu; nlinarith [hu.1]
    have h1 := (hasDerivAt_ofReal_cpow_const hu0 hr).hasDerivWithinAt (s := Icc X (X + h))
    have hpow : (s + 1) * (u : ℂ) ^ (s + 1 - 1) = (s + 1) * (u : ℂ) ^ s := by ring_nf
    rwa [hpow] at h1
  have hbound : ∀ u ∈ Icc X (X + h), ‖(s + 1) * (u : ℂ) ^ s‖ ≤ ‖s + 1‖ * (X + h) ^ c := by
    intro u hu
    rw [mem_Icc] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : s.re = c := by rw [hs]; simp
    rw [hre]
    gcongr
    exact hu.2
  have hmvt := (convex_Icc X (X + h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
  calc ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖
      ≤ ‖s + 1‖ * (X + h) ^ c * ‖(X + h) - X‖ := hmvt
    _ = ‖s + 1‖ * (X + h) ^ c * h := by rw [show (X + h) - X = h by ring, Real.norm_of_nonneg hh.le]

theorem hat_mellin_bound {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (t : ℝ) :
    ‖hatKernel X h c t‖
      ≤ (X + h) ^ c * min (2 / ‖(c : ℂ) + (t : ℂ) * I‖)
          (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) := by
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
  have hXh : (0 : ℝ) < X + h := by linarith
  have hsn : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr (by rw [hs]; exact Salt.SW.s_ne_zero hc t)
  have hs1n : (0 : ℝ) < ‖s + 1‖ := norm_pos_iff.mpr (by rw [hs]; exact Salt.SW.s1_ne_zero hc t)
  have hss1 : ‖s‖ ≤ ‖s + 1‖ := by
    rw [hs, Complex.norm_add_mul_I,
      show (c : ℂ) + (t : ℂ) * I + 1 = ((c + 1 : ℝ) : ℂ) + (t : ℂ) * I by push_cast; ring,
      Complex.norm_add_mul_I]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hseg := cpow_seg_bound hX hh hc t
  rw [← hs] at hseg
  have htri : ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖ ≤ 2 * (X + h) ^ (c + 1) := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXh,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < X),
      show (s + 1).re = c + 1 by rw [hs]; simp]
    have : X ^ (c + 1) ≤ (X + h) ^ (c + 1) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    linarith
  have hHK : ‖hatKernel X h c t‖
      = ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖ / (h * ‖s‖ * ‖s + 1‖) := by
    rw [hatKernel, ← hs, norm_div, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hh.le]; ring_nf
  rw [hHK]
  have hbranch1 : ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖ / (h * ‖s‖ * ‖s + 1‖)
      ≤ (X + h) ^ c * (2 / ‖s‖) := by
    rw [div_le_iff₀ (by positivity)]
    refine hseg.trans ?_
    rw [show (X + h) ^ c * (2 / ‖s‖) * (h * ‖s‖ * ‖s + 1‖) = 2 * (‖s + 1‖ * (X + h) ^ c * h) by
      field_simp]
    have hp : (0 : ℝ) ≤ ‖s + 1‖ * (X + h) ^ c * h := by positivity
    linarith
  have hbranch2 : ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖ / (h * ‖s‖ * ‖s + 1‖)
      ≤ (X + h) ^ c * (2 * (X + h) / (h * ‖s‖ ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    refine htri.trans ?_
    rw [show (X + h) ^ c * (2 * (X + h) / (h * ‖s‖ ^ 2)) * (h * ‖s‖ * ‖s + 1‖)
      = 2 * ((X + h) ^ c * (X + h)) * (‖s + 1‖ / ‖s‖) by field_simp,
      show (X + h) ^ (c + 1) = (X + h) ^ c * (X + h) by rw [Real.rpow_add hXh, Real.rpow_one]]
    have hratio : 1 ≤ ‖s + 1‖ / ‖s‖ := by rw [le_div_iff₀ hsn]; linarith
    have hp : (0 : ℝ) ≤ 2 * ((X + h) ^ c * (X + h)) := by positivity
    nlinarith [hratio, hp]
  exact (le_min hbranch1 hbranch2).trans_eq (mul_min_of_nonneg _ _ (by positivity)).symm

/-- **The branch-2 tail bound** (`hat_tail`).  Beyond height `T`, the (dominant,
`1/‖s‖²`-decaying) branch of the kernel has one-sided tail mass `≤ 2(X+h)^{c+1}/(hT)`;
by evenness the full `|t| ≥ T` mass is `≤ 4(X+h)^{c+1}/(hT)`. -/
theorem hat_tail {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) {T : ℝ} (hT : 0 < T) :
    ∫ t in Set.Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2))
      ≤ 2 * (X + h) ^ (c + 1) / (h * T) := by
  have hAnn : (0 : ℝ) ≤ 2 * (X + h) ^ (c + 1) / h := by positivity
  have hInt1 : IntegrableOn (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) (Set.Ioi T) :=
    (Salt.SW.integrable_inv_c_sq_add_sq hc).integrableOn
  have hInt2 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  calc ∫ t in Set.Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2))
      = (2 * (X + h) ^ (c + 1) / h) * ∫ t in Set.Ioi T, (c ^ 2 + t ^ 2)⁻¹ := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        have hne : c ^ 2 + t ^ 2 ≠ 0 := by positivity
        field_simp
    _ ≤ (2 * (X + h) ^ (c + 1) / h) * ∫ t in Set.Ioi T, t ^ (-2 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hAnn
        refine setIntegral_mono_on hInt1 hInt2 measurableSet_Ioi (fun t ht => ?_)
        rw [Set.mem_Ioi] at ht
        have ht0 : (0 : ℝ) < t := by linarith
        rw [Real.rpow_neg ht0.le, Real.rpow_two]
        exact inv_anti₀ (pow_pos ht0 2) (by nlinarith [sq_nonneg c])
    _ = 2 * (X + h) ^ (c + 1) / (h * T) := by
        rw [integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hT,
          show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp

/-! ### The `Tsplit` split ledger (K3', REF-B R1 — binding).

The Perron integral is split at the kernel height `Tsplit := (log X)^4`.  Ledger
(numbers from `halasz-infra-freeze.md`, `L := log X`):

* **main part** `|t| ≤ Tsplit`: the sup of the integrand is `≤ C·L^3`
  (`S_𝒥·L ≤ C·L` times the `Λ`-window double-sum `≤ (log (x/y))^2`);
* **tail part** `|t| > Tsplit`: by `hat_tail`, the branch-2 tail mass is
  `≤ 4(X+h)^{c+1}/(h·Tsplit)`, which — with the frozen `h = X·L^{-1/2}` (#253)
  and `c₀ = 1 + 1/L` — lands `X·L^{-1/2}`, **at grade, zero ε borrowing**.

The REF-B R1 repair: the parent height `T0 = L^2` overruns the grade by a full
`L` (net log-power `L^{+1}`); raising it to `Tsplit = L^4` turns the net log-power
into `L^{-1}` (a genuine gain).  This is `tsplit_ledger` below.  `Tsplit` is the
**kernel-split height** — DISTINCT from the parent freeze's ball radius
`T0 = (log X)^{1/46}`; never conflate the two. -/

/-- The `Tsplit = (log X)^4` kernel-split height (K3'). -/
def Tsplit (X : ℝ) : ℝ := (Real.log X) ^ 4

/-- **The split ledger arithmetic** (REF-B R1, verified).  With sup-integrand
budget `C·L^3` and a branch-2 tail decaying as `1/T`, the net log-power of the tail
contribution is `L^3/Tsplit = L^{-1}` at `Tsplit = L^4` (a genuine gain, at grade),
whereas at the parent height `T0 = L^2` it is `L^3/T0 = L^{+1} > 1` (the overrun
REF-B R1 caught). -/
lemma tsplit_ledger {L : ℝ} (hL : 1 < L) :
    L ^ 3 * (L ^ 4)⁻¹ ≤ L⁻¹ ∧ 1 < L ^ 3 * (L ^ 2)⁻¹ := by
  have hL0 : (0 : ℝ) < L := by linarith
  refine ⟨le_of_eq ?_, ?_⟩
  · field_simp
  · rw [show L ^ 3 * (L ^ 2)⁻¹ = L by field_simp]; exact hL

end Salt.MR

end

-- ===== Salt.MR.HalaszContour =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# HALASZ-INFRA wave I-1, K4' residual — the Poisson-kernel cosine integral

The named residual of the minimal-seam Halász route
(`docs/exploration/halasz-infra-freeze.md`, FILE A, rung K4').  Two stones:

* `cos_int_pair` — the Fourier cosine transform of the Poisson/Cauchy kernel,
  `∫ cos(θt)/(c²+t²) dt = (π/c)·e^{-c|θ|}` for `0 < c`.  mathlib-absent
  (Cauchy characteristic function is not formalised); proved here by the
  rectangle-CIF contour route on a growing square `[-R,R]×[0,R]`, using the
  landed residue apparatus `Salt.SW.ContourShift.rectBI_cif_eq`.  The pole at
  `s = ci` in the upper half-plane contributes the constant residue
  `(π/c)e^{-cθ}` for every `R`; the top and two side edges vanish as `R→∞`
  (`squeeze_zero'` against `2R/(R²−c²) → 0`); the bottom edge converges to the
  full-line integral (`intervalIntegral_tendsto_integral`).

* `dirichlet_plancherel` — the Finset-bilinear consumer:
  `∫ ‖∑_{n∈F} bₙ n^{-s}‖²/(c²+t²) dt = (π/c)·∑_{m,n} Re(bₘ b̄ₙ)/(mn)^c·e^{-c|log m−log n|}`.
  Norm-square expansion → `n^{-s} = n^{-c}e^{-it log n}` → finite Fubini →
  per-pair `Re`-linear split consuming `cos_int_pair` and the sin-oddness of
  `∫ sin(θt)/(c²+t²) = 0`.  Does NOT consume `MVHilbert` (freeze law).

The K4' statements are FROZEN (iron rule 1); the routes are the executor's.
-/

open MeasureTheory Complex Set Filter Topology
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## The integrand and its algebraic skeleton -/

/-- The residue factor `φ(s) = e^{iθs}/(s + ci)`; analytic on the upper closed
square (its only zero of the denominator is at `s = −ci`, below the real axis). -/
private noncomputable def poisφ (θ c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((θ : ℂ) * s * I) / (s + (c : ℂ) * I)

/-- The full integrand `F(s) = e^{iθs}/((s+ci)(s−ci)) = e^{iθs}/(c²+s²)`. -/
private noncomputable def poisF (θ c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((θ : ℂ) * s * I) / ((s + (c : ℂ) * I) * (s - (c : ℂ) * I))

/-- `F(s) = φ(s)/(s − ci)`: the exact `rectBI_cif_eq` shape. -/
private lemma poisF_eq (θ c : ℝ) (s : ℂ) : poisF θ c s = poisφ θ c s / (s - (c : ℂ) * I) := by
  rw [poisF, poisφ, div_div]

/-- On the real axis `F(x) = e^{iθx}/(c²+x²)` — the target integrand. -/
private lemma poisF_ofReal (θ c : ℝ) (x : ℝ) :
    poisF θ c (x : ℂ) = Complex.exp (((θ * x : ℝ) : ℂ) * I) / (((c ^ 2 + x ^ 2 : ℝ)) : ℂ) := by
  rw [poisF]
  congr 1
  · push_cast; ring
  · rw [show ((x : ℂ) + (c : ℂ) * I) * ((x : ℂ) - (c : ℂ) * I)
        = (x : ℂ) ^ 2 - (c : ℂ) ^ 2 * I ^ 2 by ring, Complex.I_sq]
    push_cast; ring

/-- `‖F(s)‖ = e^{−θ·Im s}/‖(s+ci)(s−ci)‖`. -/
private lemma norm_poisF (θ c : ℝ) (s : ℂ) :
    ‖poisF θ c s‖ = Real.exp (-(θ * s.im)) / ‖(s + (c : ℂ) * I) * (s - (c : ℂ) * I)‖ := by
  rw [poisF, norm_div, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]

/-! ## The `R/(R²−c²) → 0` decay used for the three vanishing edges. -/

/-- The edge-bound ratio tends to `0`. -/
private lemma ratio_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => R / (R ^ 2 - c ^ 2)) atTop (𝓝 0) := by
  have h2R : Tendsto (fun R : ℝ => 2 / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2 : ℝ)
  refine squeeze_zero' ?_ ?_ h2R
  · filter_upwards [eventually_gt_atTop c] with R hR
    have hR0 : 0 < R := lt_trans hc hR
    have : 0 < R ^ 2 - c ^ 2 := by
      nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
    positivity
  · filter_upwards [eventually_gt_atTop c, eventually_ge_atTop (Real.sqrt 2 * c)] with R hR hR1
    have hR0 : 0 < R := lt_trans hc hR
    have hden : 0 < R ^ 2 - c ^ 2 := by
      nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hexp : (Real.sqrt 2 * c) ^ 2 = 2 * c ^ 2 := by rw [mul_pow, hs2]
    have hle : 2 * c ^ 2 ≤ R ^ 2 := by
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ Real.sqrt 2 * c by positivity) hR1 2
      rwa [hexp] at h
    rw [div_le_div_iff₀ hden hR0]
    nlinarith [hle]

/-! ## The residue: the boundary integral is the constant `(π/c)e^{-cθ}`. -/

open Salt.SW in
/-- The rectangle boundary integral of `F` over the growing square `[-R,R]×[0,R]`
picks up the residue at the interior pole `s = ci` — the constant `2πi·φ(ci)` for
every `R > c`. -/
private lemma poisF_residue {θ c : ℝ} (hc : 0 < c) {R : ℝ} (hR : c < R) :
    rectBI ((-R : ℝ) : ℂ) ((R : ℝ) + (R : ℝ) * I) (poisF θ c)
      = 2 * (Real.pi : ℂ) * I * poisφ θ c ((c : ℂ) * I) := by
  have hR0 : 0 < R := lt_trans hc hR
  set z : ℂ := ((-R : ℝ) : ℂ) with hz
  set w : ℂ := ((R : ℝ) + (R : ℝ) * I) with hw
  set p : ℂ := ((c : ℂ) * I) with hp
  have hzre : z.re = -R := by simp [hz]
  have hzim : z.im = 0 := by simp [hz]
  have hwre : w.re = R := by simp [hw]
  have hwim : w.im = R := by simp [hw]
  have hpre : p.re = 0 := by simp [hp]
  have hpim : p.im = c := by simp [hp]
  have hcongr : (poisF θ c) = (fun s => poisφ θ c s / (s - p)) := by
    funext s; rw [poisF_eq, hp]
  rw [hcongr]
  refine rectBI_cif_eq ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [closedRect, mem_reProdIm] at hs
    have hsim : 0 ≤ s.im := by
      have h2 := hs.2
      rw [hzim, hwim, Set.uIcc_of_le hR0.le] at h2
      exact h2.1
    have hden : s + (c : ℂ) * I ≠ 0 := by
      intro h
      have h2 : (s + (c : ℂ) * I).im = 0 := by rw [h]; simp
      simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero] at h2
      linarith
    have hnum : DifferentiableAt ℂ (fun s : ℂ => Complex.exp ((θ : ℂ) * s * I)) s := by
      fun_prop
    have hden' : DifferentiableAt ℂ (fun s : ℂ => s + (c : ℂ) * I) s := by fun_prop
    have hd : DifferentiableAt ℂ (poisφ θ c) s := by
      unfold poisφ; exact hnum.div hden' hden
    exact hd.differentiableWithinAt
  · rw [hzre, hwre]; linarith
  · rw [hzim, hwim]; exact hR0
  · rw [hzre, hwre, hpre]; exact ⟨by linarith, hR0⟩
  · rw [hzim, hwim, hpim]; exact ⟨hc, hR⟩

/-- The residue value: `2πi·φ(ci) = (π/c)·e^{-cθ}` (a real number). -/
private lemma poisφ_at_pole {θ c : ℝ} (hc : 0 < c) :
    2 * (Real.pi : ℂ) * I * poisφ θ c ((c : ℂ) * I)
      = ((Real.pi / c * Real.exp (-(c * θ)) : ℝ) : ℂ) := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have harg : (θ : ℂ) * ((c : ℂ) * I) * I = ((-(c * θ) : ℝ) : ℂ) := by
    rw [show (θ : ℂ) * ((c : ℂ) * I) * I = (θ : ℂ) * (c : ℂ) * (I * I) from by ring,
      Complex.I_mul_I]
    push_cast; ring
  rw [poisφ, harg, ← Complex.ofReal_exp,
    show ((c : ℂ) * I + (c : ℂ) * I) = 2 * (c : ℂ) * I from by ring]
  push_cast
  field_simp

/-! ## The uniform edge bound `‖F(s)‖ ≤ (R²−c²)⁻¹`. -/

/-- On the upper half-plane (`0 ≤ Im s`) and outside the disc of radius `R > c`,
the integrand is bounded by `(R²−c²)⁻¹`. -/
private lemma norm_poisF_le {θ c : ℝ} (hθ : 0 ≤ θ) {s : ℂ} (hsim : 0 ≤ s.im)
    {R : ℝ} (hRc : 0 < R ^ 2 - c ^ 2) (hsR : R ^ 2 ≤ ‖s‖ ^ 2) :
    ‖poisF θ c s‖ ≤ (R ^ 2 - c ^ 2)⁻¹ := by
  have heq : (s + (c : ℂ) * I) * (s - (c : ℂ) * I) = s ^ 2 + ((c ^ 2 : ℝ) : ℂ) := by
    rw [show (s + (c : ℂ) * I) * (s - (c : ℂ) * I) = s ^ 2 - (c : ℂ) ^ 2 * I ^ 2 from by ring,
      Complex.I_sq]
    push_cast; ring
  have hncsq : ‖((c ^ 2 : ℝ) : ℂ)‖ = c ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)]
  have hlow : R ^ 2 - c ^ 2 ≤ ‖s ^ 2 + ((c ^ 2 : ℝ) : ℂ)‖ := by
    have htri : ‖s ^ 2‖ - ‖((c ^ 2 : ℝ) : ℂ)‖ ≤ ‖s ^ 2 + ((c ^ 2 : ℝ) : ℂ)‖ := by
      have := norm_sub_norm_le (s ^ 2) (-(((c ^ 2 : ℝ) : ℂ)))
      simpa using this
    rw [hncsq, norm_pow] at htri
    nlinarith [htri, hsR]
  have hDpos : 0 < ‖s ^ 2 + ((c ^ 2 : ℝ) : ℂ)‖ := lt_of_lt_of_le hRc hlow
  rw [norm_poisF, heq, div_le_iff₀ hDpos]
  have hexp1 : Real.exp (-(θ * s.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hθ hsim))
  have h1 : (R ^ 2 - c ^ 2)⁻¹ * (R ^ 2 - c ^ 2) = 1 := inv_mul_cancel₀ hRc.ne'
  have h2 : (R ^ 2 - c ^ 2)⁻¹ * (R ^ 2 - c ^ 2)
      ≤ (R ^ 2 - c ^ 2)⁻¹ * ‖s ^ 2 + ((c ^ 2 : ℝ) : ℂ)‖ :=
    mul_le_mul_of_nonneg_left hlow (by positivity)
  linarith

/-! ## The three non-bottom edges vanish as `R → ∞`. -/

/-- Any edge whose norm is eventually `≤ M·R/(R²−c²)` tends to `0`. -/
private lemma edge_tendsto {c : ℝ} (hc : 0 < c) {J : ℝ → ℂ} {M : ℝ}
    (hb : ∀ᶠ R in atTop, ‖J R‖ ≤ M * (R / (R ^ 2 - c ^ 2))) :
    Tendsto J atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hb ?_
  simpa using (ratio_tendsto hc).const_mul M

/-- The top edge (`Im = R`) vanishes. -/
private lemma top_tendsto {θ c : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I)) atTop (𝓝 0) := by
  refine edge_tendsto hc (M := 2) ?_
  filter_upwards [eventually_gt_atTop c] with R hR
  have hR0 : 0 < R := lt_trans hc hR
  have hRc : 0 < R ^ 2 - c ^ 2 := by
    nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
  have hbd : ∀ x ∈ Set.uIoc (-R) R, ‖poisF θ c ((x : ℂ) + (R : ℂ) * I)‖ ≤ (R ^ 2 - c ^ 2)⁻¹ := by
    intro x _
    refine norm_poisF_le hθ ?_ hRc ?_
    · have : ((x : ℂ) + (R : ℂ) * I).im = R := by simp
      rw [this]; exact hR0.le
    · rw [Complex.norm_add_mul_I, Real.sq_sqrt (show (0:ℝ) ≤ x ^ 2 + R ^ 2 by positivity)]
      nlinarith [sq_nonneg x]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [show |R - -R| = 2 * R by rw [show R - -R = 2 * R by ring, abs_of_pos (by linarith)]] at hnorm
  calc ‖∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I)‖
      ≤ (R ^ 2 - c ^ 2)⁻¹ * (2 * R) := hnorm
    _ = 2 * (R / (R ^ 2 - c ^ 2)) := by rw [div_eq_mul_inv]; ring

/-- The right edge (`Re = R`) vanishes. -/
private lemma right_tendsto {θ c : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    Tendsto (fun R : ℝ => ∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
  refine edge_tendsto hc (M := 1) ?_
  filter_upwards [eventually_gt_atTop c] with R hR
  have hR0 : 0 < R := lt_trans hc hR
  have hRc : 0 < R ^ 2 - c ^ 2 := by
    nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
  have hbd : ∀ y ∈ Set.uIoc (0:ℝ) R, ‖poisF θ c ((R : ℂ) + (y : ℂ) * I)‖ ≤ (R ^ 2 - c ^ 2)⁻¹ := by
    intro y hy
    rw [Set.uIoc_of_le hR0.le] at hy
    refine norm_poisF_le hθ ?_ hRc ?_
    · have : ((R : ℂ) + (y : ℂ) * I).im = y := by simp
      rw [this]; exact hy.1.le
    · rw [Complex.norm_add_mul_I, Real.sq_sqrt (show (0:ℝ) ≤ _ by positivity)]
      nlinarith [sq_nonneg y]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [show |R - 0| = R by rw [sub_zero, abs_of_pos hR0]] at hnorm
  calc ‖∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I)‖
      ≤ (R ^ 2 - c ^ 2)⁻¹ * R := hnorm
    _ = 1 * (R / (R ^ 2 - c ^ 2)) := by rw [div_eq_mul_inv]; ring

/-- The left edge (`Re = −R`) vanishes. -/
private lemma left_tendsto {θ c : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    Tendsto (fun R : ℝ => ∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)) atTop
      (𝓝 0) := by
  refine edge_tendsto hc (M := 1) ?_
  filter_upwards [eventually_gt_atTop c] with R hR
  have hR0 : 0 < R := lt_trans hc hR
  have hRc : 0 < R ^ 2 - c ^ 2 := by
    nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
  have hbd : ∀ y ∈ Set.uIoc (0:ℝ) R,
      ‖poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ (R ^ 2 - c ^ 2)⁻¹ := by
    intro y hy
    rw [Set.uIoc_of_le hR0.le] at hy
    refine norm_poisF_le hθ ?_ hRc ?_
    · have : (((-R : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
      rw [this]; exact hy.1.le
    · rw [Complex.norm_add_mul_I, Real.sq_sqrt (show (0:ℝ) ≤ _ by positivity)]
      nlinarith [sq_nonneg y]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [show |R - 0| = R by rw [sub_zero, abs_of_pos hR0]] at hnorm
  calc ‖∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ (R ^ 2 - c ^ 2)⁻¹ * R := hnorm
    _ = 1 * (R / (R ^ 2 - c ^ 2)) := by rw [div_eq_mul_inv]; ring

/-! ## Assembly of the complex Poisson integral. -/

/-- `‖F(x)‖ = (c²+x²)⁻¹` on the real axis, hence `F(↑·)` is integrable. -/
private lemma norm_poisF_ofReal {θ c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖poisF θ c (t : ℂ)‖ = (c ^ 2 + t ^ 2)⁻¹ := by
  rw [poisF_ofReal, norm_div, Complex.norm_exp]
  have h1 : (((θ * t : ℝ) : ℂ) * I).re = 0 := by simp
  rw [h1, Real.exp_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < c ^ 2 + t ^ 2), one_div]

private lemma integrable_poisF_ofReal {θ c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => poisF θ c (t : ℂ)) := by
  refine (Salt.SW.integrable_inv_c_sq_add_sq hc).mono' ?_
    (Filter.Eventually.of_forall (fun t => le_of_eq (norm_poisF_ofReal hc t)))
  have he : (fun t : ℝ => poisF θ c (t : ℂ))
      = fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ) :=
    funext (fun t => poisF_ofReal θ c t)
  rw [he]
  refine (Continuous.div ?_ ?_ ?_).aestronglyMeasurable
  · fun_prop
  · fun_prop
  · exact fun t => Complex.ofReal_ne_zero.mpr (by positivity)

open Salt.SW in
/-- **The complex Poisson integral** (`θ ≥ 0`): `∫ e^{iθt}/(c²+t²) dt = (π/c)e^{-cθ}`. -/
private lemma cexp_pois_integral {c θ : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    ∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)
      = ((Real.pi / c * Real.exp (-(c * θ)) : ℝ) : ℂ) := by
  set V : ℂ := ((Real.pi / c * Real.exp (-(c * θ)) : ℝ) : ℂ) with hV
  have hInt := integrable_poisF_ofReal (θ := θ) hc
  -- bottom edge converges to the full-line integral
  have hbot : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poisF θ c (x : ℂ)) atTop
      (𝓝 (∫ t : ℝ, poisF θ c (t : ℂ))) :=
    intervalIntegral_tendsto_integral hInt tendsto_neg_atTop_atBot tendsto_id
  -- the eventual identity: bottom = residue + top − I·right + I·left
  have hrel : ∀ᶠ R : ℝ in atTop, (∫ x in (-R)..R, poisF θ c (x : ℂ))
      = V + (∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I))
        - I * (∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I))
        + I * (∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)) := by
    filter_upwards [eventually_gt_atTop c] with R hR
    have hres : rectBI ((-R : ℝ) : ℂ) ((R : ℝ) + (R : ℝ) * I) (poisF θ c) = V := by
      rw [poisF_residue hc hR, poisφ_at_pole hc]
    have hunf : rectBI ((-R : ℝ) : ℂ) ((R : ℝ) + (R : ℝ) * I) (poisF θ c)
        = (∫ x in (-R)..R, poisF θ c (x : ℂ))
          - (∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I))
          + I * (∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I))
          - I * (∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)) := by
      rw [rectBI]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_zero,
        mul_zero, zero_mul, add_zero, mul_one, sub_zero, zero_add]
    rw [hunf] at hres
    linear_combination hres
  -- the top/right/left edges vanish
  have hsum : Tendsto (fun R : ℝ => V + (∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I))
      - I * (∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I))
      + I * (∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I))) atTop (𝓝 V) := by
    have h := (((tendsto_const_nhds (x := V)).add (top_tendsto hc hθ)).sub
      ((right_tendsto hc hθ).const_mul I)).add ((left_tendsto hc hθ).const_mul I)
    simpa using h
  have hbot2 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poisF θ c (x : ℂ)) atTop (𝓝 V) :=
    hsum.congr' (hrel.mono fun R h => h.symm)
  have key : (∫ t : ℝ, poisF θ c (t : ℂ)) = V := tendsto_nhds_unique hbot hbot2
  rw [← key]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun t => (poisF_ofReal θ c t).symm))

/-! ## K4' stone 1 — `cos_int_pair`. -/

/-- The `θ ≥ 0` case: `∫ cos(θt)/(c²+t²) = (π/c)e^{-cθ}` (real part of the complex integral). -/
private lemma cos_int_pair_nonneg {c θ : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    ∫ t : ℝ, Real.cos (θ * t) / (c ^ 2 + t ^ 2) = Real.pi / c * Real.exp (-(c * θ)) := by
  have hInt : Integrable
      (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
    have he : (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
        = fun t : ℝ => poisF θ c (t : ℂ) := funext (fun t => (poisF_ofReal θ c t).symm)
    rw [he]; exact integrable_poisF_ofReal hc
  have hre : ∀ t : ℝ,
      (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
        = Real.cos (θ * t) / (c ^ 2 + t ^ 2) := by
    intro t; rw [Complex.div_ofReal_re, Complex.exp_ofReal_mul_I_re]
  calc ∫ t : ℝ, Real.cos (θ * t) / (c ^ 2 + t ^ 2)
      = ∫ t : ℝ, (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
        integral_congr_ae (Filter.Eventually.of_forall (fun t => (hre t).symm))
    _ = (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
        integral_re hInt
    _ = ((Real.pi / c * Real.exp (-(c * θ)) : ℝ) : ℂ).re := by rw [cexp_pois_integral hc hθ]
    _ = Real.pi / c * Real.exp (-(c * θ)) := Complex.ofReal_re _

/-- **K4' stone 1** (`cos_int_pair`, FROZEN).  The Fourier cosine transform of the
Poisson kernel: `∫ cos(θt)/(c²+t²) dt = (π/c)·e^{-c|θ|}`. -/
theorem cos_int_pair {c th : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, Real.cos (th * t) / (c ^ 2 + t ^ 2) = Real.pi / c * Real.exp (-(c * |th|)) := by
  rw [← cos_int_pair_nonneg hc (abs_nonneg th)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  have hcos : Real.cos (th * t) = Real.cos (|th| * t) := by
    rcases abs_choice th with h1 | h1
    · rw [h1]
    · rw [h1, show (-th) * t = -(th * t) from by ring, Real.cos_neg]
  simp only [hcos]

/-! ## K4' stone 2 — `dirichlet_plancherel`. -/

/-- The sin transform of the Poisson kernel vanishes (odd integrand). -/
private lemma sin_int_zero {c θ : ℝ} (_hc : 0 < c) :
    ∫ t : ℝ, Real.sin (θ * t) / (c ^ 2 + t ^ 2) = 0 := by
  set f : ℝ → ℝ := fun t => Real.sin (θ * t) / (c ^ 2 + t ^ 2) with hf
  have hodd : (fun t : ℝ => f (-t)) = fun t : ℝ => -f t := by
    funext t
    simp only [hf]
    rw [show θ * -t = -(θ * t) by ring, Real.sin_neg, show (-t) ^ 2 = t ^ 2 by ring]
    ring
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
  have h1 : ∫ t : ℝ, f (-t) = ∫ t : ℝ, f t := hmp.integral_comp hemb f
  have h3 : ∫ t : ℝ, f (-t) = -∫ t : ℝ, f t := by rw [hodd, integral_neg]
  have : ∫ t : ℝ, f t = -∫ t : ℝ, f t := h1.symm.trans h3
  linarith

/-- **The full complex Poisson integral** (all real `θ`):
`∫ e^{iθt}/(c²+t²) dt = (π/c)e^{-c|θ|}` — real part is `cos_int_pair`, imaginary
part vanishes by `sin_int_zero`. -/
private lemma cexp_pois_full {c θ : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)
      = ((Real.pi / c * Real.exp (-(c * |θ|)) : ℝ) : ℂ) := by
  have hInt : Integrable
      (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
    have he : (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
        = fun t : ℝ => poisF θ c (t : ℂ) := funext (fun t => (poisF_ofReal θ c t).symm)
    rw [he]; exact integrable_poisF_ofReal hc
  have hre : (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
      = Real.pi / c * Real.exp (-(c * |θ|)) := by
    have hcos : ∀ t : ℝ,
        (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
          = Real.cos (θ * t) / (c ^ 2 + t ^ 2) :=
      fun t => by rw [Complex.div_ofReal_re, Complex.exp_ofReal_mul_I_re]
    calc (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
        = ∫ t : ℝ, (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
          (integral_re hInt).symm
      _ = ∫ t : ℝ, Real.cos (θ * t) / (c ^ 2 + t ^ 2) :=
          integral_congr_ae (Filter.Eventually.of_forall hcos)
      _ = Real.pi / c * Real.exp (-(c * |θ|)) := cos_int_pair hc
  have him : (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).im
      = 0 := by
    have hsin : ∀ t : ℝ,
        (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).im
          = Real.sin (θ * t) / (c ^ 2 + t ^ 2) :=
      fun t => by rw [Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_im]
    calc (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).im
        = ∫ t : ℝ, (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).im :=
          (integral_im hInt).symm
      _ = ∫ t : ℝ, Real.sin (θ * t) / (c ^ 2 + t ^ 2) :=
          integral_congr_ae (Filter.Eventually.of_forall hsin)
      _ = 0 := sin_int_zero hc
  rw [← Complex.re_add_im
    (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)), hre, him]
  push_cast; ring

/-- The per-pair `cpow` decomposition: `(bₘ/mˢ)·conj(bₙ/nˢ)` factors into the
constant amplitude `bₘ b̄ₙ (mn)^{-c}` times the unit `e^{i(log n − log m)t}`. -/
private lemma pair_cpow {c t : ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (bm bn : ℂ) :
    (bm / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (bn / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
      = (bm * starRingEnd ℂ bn) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ)
        * Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have em : (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      = Complex.exp ((Real.log m : ℂ) * ((c : ℂ) + (t : ℂ) * I)) := by
    rw [Complex.cpow_def_of_ne_zero hmC, ← Complex.natCast_log]
  have en : (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      = Complex.exp ((Real.log n : ℂ) * ((c : ℂ) + (t : ℂ) * I)) := by
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  have hrpow : (((m : ℝ) * (n : ℝ)) ^ c)⁻¹
      = Real.exp (-(c * (Real.log m + Real.log n))) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul hm0.ne' hn0.ne', ← Real.exp_neg]
    ring_nf
  have hexp : Complex.exp (-((Real.log m : ℂ) * ((c : ℂ) + (t : ℂ) * I)
        + starRingEnd ℂ ((Real.log n : ℂ) * ((c : ℂ) + (t : ℂ) * I))))
      = (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ)
        * Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I) := by
    rw [show ((((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ)) : ℂ)
        = Complex.exp ((-(c * (Real.log m + Real.log n)) : ℝ) : ℂ) by
      rw [hrpow, Complex.ofReal_exp], ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [em, en, map_div₀, ← Complex.exp_conj, div_mul_div_comm, div_eq_mul_inv,
    ← Complex.exp_add, ← Complex.exp_neg, hexp]
  ring

/-- **K4' stone 2** (`dirichlet_plancherel`, FROZEN).  The Dirichlet-polynomial
Plancherel bilinear form against the Poisson kernel: consumes `cos_int_pair` (via
`cexp_pois_full`) pair-by-pair.  Does NOT consume `MVHilbert`. -/
theorem dirichlet_plancherel (F : Finset ℕ) (b : ℕ → ℂ) {c : ℝ} (hc : 0 < c)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (c ^ 2 + t ^ 2)
      = Real.pi / c * ∑ m ∈ F, ∑ n ∈ F,
          (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(c * |Real.log m - Real.log n|)) := by
  -- integrability of each unit Poisson integrand
  have hg_int : ∀ θ : ℝ,
      Integrable (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) :=
    fun θ => by
      have he : (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
          = fun t : ℝ => poisF θ c (t : ℂ) := funext (fun t => (poisF_ofReal θ c t).symm)
      rw [he]; exact integrable_poisF_ofReal hc
  -- per-pair integrand as constant × unit Poisson integrand
  have hpint : ∀ m ∈ F, ∀ n ∈ F, Integrable (fun t : ℝ =>
      (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
    intro m hm n hn
    have hrw : (fun t : ℝ => (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
      = fun t : ℝ => (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * (Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I)
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
      funext t; rw [pair_cpow (hF m hm) (hF n hn)]; ring
    rw [hrw]; exact (hg_int _).const_mul _
  -- per-pair integral value
  have hpval : ∀ m ∈ F, ∀ n ∈ F,
      ∫ t : ℝ, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)
        = (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * ((Real.pi / c * Real.exp (-(c * |Real.log n - Real.log m|)) : ℝ) : ℂ) := by
    intro m hm n hn
    have hrw : (fun t : ℝ => (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
      = fun t : ℝ => (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * (Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I)
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
      funext t; rw [pair_cpow (hF m hm) (hF n hn)]; ring
    rw [hrw, integral_const_mul, cexp_pois_full hc]
  -- expand the squared norm as a double sum over F × F
  have hsum_expand : ∀ t : ℝ,
      ((‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) := by
    intro t
    rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  -- reduce the real integral to the real part of the complex double-sum integral
  have hcplx : ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (c ^ 2 + t ^ 2)
      = (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * ((Real.pi / c * Real.exp (-(c * |Real.log n - Real.log m|)) : ℝ) : ℂ)).re := by
    have hpt : ∀ t : ℝ,
        ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (c ^ 2 + t ^ 2)
        = (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re := by
      intro t
      have h1 : (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
          = (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun m _ => by rw [Finset.sum_div])
      rw [h1, ← hsum_expand t, Complex.div_ofReal_re, Complex.ofReal_re]
    calc ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (c ^ 2 + t ^ 2)
        = ∫ t : ℝ, (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ t : ℝ, ∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
          integral_re (MeasureTheory.integrable_finsetSum _ (fun m hm =>
            MeasureTheory.integrable_finsetSum _ (fun n hn => hpint m hm n hn)))
      _ = (∑ m ∈ F, ∑ n ∈ F, ∫ t : ℝ, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re := by
          rw [MeasureTheory.integral_finsetSum _ (fun m hm =>
            MeasureTheory.integrable_finsetSum _ (fun n hn => hpint m hm n hn))]
          refine congrArg _ (Finset.sum_congr rfl (fun m hm => ?_))
          rw [MeasureTheory.integral_finsetSum _ (fun n hn => hpint m hm n hn)]
      _ = _ := by rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl
            (fun n hn => hpval m hm n hn))]
  rw [hcplx, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Complex.re_mul_ofReal, Complex.re_mul_ofReal,
    abs_sub_comm (Real.log n) (Real.log m), Nat.cast_mul, div_eq_mul_inv]
  ring

end Salt.MR

end




theorem solution (F : Finset ℕ) (b : ℕ → ℂ) {c : ℝ} (hc : 0 < c)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 / (c ^ 2 + t ^ 2)
      = Real.pi / c * ∑ m ∈ F, ∑ n ∈ F,
          (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(c * |Real.log m - Real.log n|)) :=
  Salt.MR.dirichlet_plancherel F b hc hF

