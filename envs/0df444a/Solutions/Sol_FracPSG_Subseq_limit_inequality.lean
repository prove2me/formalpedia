-- Prove2me | solution 1 for FracPSG.Subseq.limit_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T08:13:07.527558+00:00
-- url     : https://prove2.me/submissions/2c509bdc-9a5e-4feb-93a1-52e26152a455

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_FracPSG_Subseq_Basic
import Definitions.Def_FracPSG_Subseq_EPSG

open Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

namespace P3483

open NonconvexSplitting.Shared FracPSG.Subseq

theorem line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫_ℝ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫_ℝ - ⟪G x, w⟫_ℝ
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫_ℝ) ⟪G x, w⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪G (x + c • w), w⟫_ℝ - ⟪G x, w⟫_ℝ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪G (x + c • w), w⟫_ℝ - ⟪G x, w⟫_ℝ = ⟪G (x + c • w) - G x, w⟫_ℝ := by
      rw [inner_sub_left]
    have e2 := real_inner_le_norm (G (x + c • w) - G x) w
    have e3 := hG (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖G (x + c • w) - G x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

theorem convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : E) : F x + ⟪G x, y - x⟫_ℝ ≤ F y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => F (x + t • w)) := by
    have := hc.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => F (x + t • w)) = F ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using line_deriv hF x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  linarith

/-- A regular subgradient of `g` at `z` satisfies the weak-convexity subgradient inequality. -/
theorem reg_wc_ineq {N : ℕ} {D : Set (EuclideanSpace ℝ (Fin N))}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {β : ℝ}
    (hwc : IsWeaklyConvexOn D g β)
    {z v y : EuclideanSpace ℝ (Fin N)} (hz : z ∈ D) (hy : y ∈ D)
    (hv : IsRegularSubgrad (fun w => (g w : EReal)) z v) :
    g z + ⟪v, y - z⟫_ℝ - β / 2 * ‖y - z‖ ^ 2 ≤ g y := by
  obtain ⟨hβ, hconv⟩ := hwc
  obtain ⟨d, hd⟩ : ∃ d, y - z = d := ⟨_, rfl⟩
  have hyd : y = z + d := by rw [← hd]; abel
  subst hyd
  rw [hd]
  apply le_of_forall_pos_le_add
  intro η hη
  set ε : ℝ := η / (‖d‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hεd : ε * ‖d‖ ≤ η := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg d]
  have hline : Tendsto (fun s : ℝ => z + s • d) (𝓝[>] (0:ℝ)) (𝓝 z) := by
    have : Continuous (fun s : ℝ => z + s • d) := by fun_prop
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 := hline.eventually (hv.2 ε hε0)
  have h2 : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Set.Ioc (0:ℝ) 1 := Ioc_mem_nhdsGT zero_lt_one
  obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
  obtain ⟨hs0, hs1'⟩ := hs2
  have hreg : g z + (s * ⟪v, d⟫_ℝ - ε * (s * ‖d‖)) ≤ g (z + s • d) := by
    have h := hs1
    simp only [add_sub_cancel_left] at h
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at h
    exact_mod_cast h
  have hmem : (1 - s) • z + s • (z + d) = z + s • d := by module
  have hc := hconv.2 hz hy (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring : (1 - s) + s = 1)
  rw [hmem] at hc
  simp only [smul_eq_mul] at hc
  have hn1 : ‖z + s • d‖ ^ 2 = ‖z‖ ^ 2 + 2 * (s * ⟪z, d⟫_ℝ) + s ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]; ring
  have hn2 : ‖z + d‖ ^ 2 = ‖z‖ ^ 2 + 2 * ⟪z, d⟫_ℝ + ‖d‖ ^ 2 := by
    rw [norm_add_sq_real]
  rw [hn1, hn2] at hc
  have key : s * (⟪v, d⟫_ℝ - ε * ‖d‖ - (g (z + d) - g z) - β / 2 * (1 - s) * ‖d‖ ^ 2) ≤ 0 := by
    nlinarith
  have key2 : ⟪v, d⟫_ℝ - ε * ‖d‖ - (g (z + d) - g z) - β / 2 * (1 - s) * ‖d‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_pos hs0 hcon
    linarith
  have hb : β / 2 * (1 - s) * ‖d‖ ^ 2 ≤ β / 2 * ‖d‖ ^ 2 := by
    have : 0 ≤ β / 2 * s * ‖d‖ ^ 2 := by positivity
    nlinarith
  linarith

theorem lim_wc_ineq {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {β : ℝ}
    (hA2 : Assumption2 S g β)
    {x v y : EuclideanSpace ℝ (Fin N)} (hx : x ∈ S) (hy : y ∈ S)
    (hv : v ∈ LimitingSubdiff (fun w => (g w : EReal)) x) :
    g x + ⟪v, y - x⟫_ℝ - β / 2 * ‖y - x‖ ^ 2 ≤ g y := by
  rcases hA2.weakly_convex with ⟨C, hCo, hCc, hSC, hwc⟩ | ⟨hreg, hwc⟩
  · obtain ⟨-, xs, vs, hxs, -, hvs, hreg⟩ := hv
    obtain ⟨O, hO, hSO, hcont⟩ := hA2.continuous_near
    have hgc : ContinuousAt g x := hcont.continuousAt (hO.mem_nhds (hSO hx))
    have hev : ∀ᶠ t in atTop, xs t ∈ C := hxs.eventually (hCo.mem_nhds (hSC hx))
    have hlim : Tendsto (fun t => g (xs t) + ⟪vs t, y - xs t⟫_ℝ - β / 2 * ‖y - xs t‖ ^ 2)
        atTop (𝓝 (g x + ⟪v, y - x⟫_ℝ - β / 2 * ‖y - x‖ ^ 2)) := by
      have h1 : Tendsto (fun t => g (xs t)) atTop (𝓝 (g x)) := hgc.tendsto.comp hxs
      have h2 : Tendsto (fun t => ⟪vs t, y - xs t⟫_ℝ) atTop (𝓝 ⟪v, y - x⟫_ℝ) :=
        Filter.Tendsto.inner (𝕜 := ℝ) hvs (tendsto_const_nhds.sub hxs)
      have h3 : Tendsto (fun t => ‖y - xs t‖) atTop (𝓝 ‖y - x‖) :=
        (tendsto_const_nhds.sub hxs).norm
      exact (h1.add h2).sub ((h3.pow 2).const_mul (β / 2))
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with t ht
    exact reg_wc_ineq hwc ht (hSC hy) (hreg t)
  · have hv' : v ∈ {v | IsRegularSubgrad (fun w => (g w : EReal)) x v} := by
      rw [(hreg x hx).2.2]; exact hv
    exact reg_wc_ineq hwc hx hy hv'

theorem fn_real {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))} {fs : EuclideanSpace ℝ (Fin N) → ℝ}
    {fn : EuclideanSpace ℝ (Fin N) → EReal} {ℓ : ℝ} (hA1 : Assumption1 S fs fn ℓ)
    {y : EuclideanSpace ℝ (Fin N)} (hy : objF fs fn y ≠ ⊤) :
    ∃ r : ℝ, fn y = r ∧ objF fs fn y = ((fs y + r : ℝ) : EReal) ∧
      (objF fs fn y).toReal = fs y + r := by
  have h1 : fn y ≠ ⊥ := hA1.fn_proper.1 y
  have h2 : fn y ≠ ⊤ := by
    intro h; apply hy; simp [objF, h]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, fn y = r := ⟨_, (EReal.coe_toReal h2 h1).symm⟩
  have h3 : objF fs fn y = ((fs y + r : ℝ) : EReal) := by
    unfold objF; rw [hr, EReal.coe_add]
  exact ⟨r, hr, h3, by rw [h3, EReal.toReal_coe]⟩

theorem step_upper {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ) (n : ℕ)
    {xbar : EuclideanSpace ℝ (Fin N)} (hxbS : xbar ∈ S)
    (hxbf : objF fs fn xbar ≠ ⊤)
    (hyf : objF fs fn (x (n + 1)) ≠ ⊤) :
    (objF fs fn (x (n + 1))).toReal ≤ (objF fs fn xbar).toReal
      + (fs (x (n + 1)) - fs xbar)
      + ⟪gradient fs (extrap x κ n), xbar - x (n + 1)⟫_ℝ
      + 1 / (2 * τ n) *
          (‖xbar - extrap x μ n - (τ n * ratio (objF fs fn) g (x n)) • gs n‖ ^ 2
            - ‖x (n + 1) - extrap x μ n - (τ n * ratio (objF fs fn) g (x n)) • gs n‖ ^ 2)
      + ℓ / 2 * (‖xbar - extrap x κ n‖ ^ 2 - ‖x (n + 1) - extrap x κ n‖ ^ 2) := by
  have h := hrun.next_argmin n xbar hxbS
  obtain ⟨r1, hr1, -, ha⟩ := fn_real hA1 hyf
  obtain ⟨r2, hr2, -, hb⟩ := fn_real hA1 hxbf
  unfold subObj at h
  rw [hr1, hr2, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [ha, hb]
  have e : ⟪gradient fs (extrap x κ n), xbar - x (n + 1)⟫_ℝ =
      ⟪gradient fs (extrap x κ n), xbar - extrap x κ n⟫_ℝ -
      ⟪gradient fs (extrap x κ n), x (n + 1) - extrap x κ n⟫_ℝ := by
    rw [← inner_sub_right]; congr 1; abel
  rw [e]
  have e2 : ∀ (a b : ℝ), 1 / (2 * τ n) * (a - b) = 1 / (2 * τ n) * a - 1 / (2 * τ n) * b := by
    intro a b; ring
  rw [e2]
  linarith

theorem T_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (xn x1 e gn : E) (μ τ θ : ℝ) :
    ‖xn - (xn + μ • e) - (τ * θ) • gn‖ ^ 2 - ‖x1 - (xn + μ • e) - (τ * θ) • gn‖ ^ 2
      = -‖x1 - xn‖ ^ 2 + 2 * μ * ⟪x1 - xn, e⟫_ℝ + 2 * (τ * θ) * ⟪x1 - xn, gn⟫_ℝ := by
  have h1 : xn - (xn + μ • e) - (τ * θ) • gn = -(μ • e + (τ * θ) • gn) := by module
  have h2 : x1 - (xn + μ • e) - (τ * θ) • gn = (x1 - xn) - (μ • e + (τ * θ) • gn) := by module
  rw [h1, h2, norm_neg, norm_sub_sq_real, inner_add_right, inner_smul_right, inner_smul_right]
  ring

theorem dom_next {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ) (n : ℕ)
    (hxS : x n ∈ S) (hxf : objF fs fn (x n) ≠ ⊤) :
    objF fs fn (x (n + 1)) ≠ ⊤ := by
  have h := hrun.next_argmin n (x n) hxS
  obtain ⟨r, hr, -, -⟩ := fn_real hA1 hxf
  intro hcon
  have hfn : fn (x (n + 1)) = ⊤ := by
    by_contra hne
    have hbot := hA1.fn_proper.1 (x (n + 1))
    obtain ⟨r', hr'⟩ : ∃ r' : ℝ, fn (x (n + 1)) = r' := ⟨_, (EReal.coe_toReal hne hbot).symm⟩
    unfold objF at hcon; rw [hr', ← EReal.coe_add] at hcon; exact EReal.coe_ne_top _ hcon
  unfold subObj at h
  rw [hfn, hr, EReal.top_add_coe, ← EReal.coe_add] at h
  exact EReal.coe_ne_top _ (top_le_iff.mp h)

theorem star {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2 S g β)
    (hδ : 0 < δ) (hζ : 0 < ζ) (hβζ : 0 < 1 - Real.sqrt β * ζ)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ) (n : ℕ)
    (hxS : x n ∈ S) (hxf : objF fs fn (x n) ≠ ⊤) :
    g (x (n + 1)) * (ratio (objF fs fn) g (x (n + 1)) - ratio (objF fs fn) g (x n)) ≤
      -(δ * (1 - Real.sqrt β * ζ) / 2) * ‖x (n + 1) - x n‖ ^ 2
        + ℓ * κbar ^ 2 / 2 * ‖x n - xPrev x n‖ ^ 2
        + μbar * (‖x (n + 1) - x n‖ * ‖x n - xPrev x n‖) := by
  have hx1f := dom_next hA1 hrun n hxS hxf
  have hx1S := hrun.next_mem n
  have hβ0 : 0 ≤ β := by
    rcases hA2.weakly_convex with ⟨C, -, -, -, hwc⟩ | ⟨-, hwc⟩ <;> exact hwc.1
  obtain ⟨hμ0, hμ1⟩ := hrun.mu_mem n
  obtain ⟨hκ0, hκ1⟩ := hrun.kappa_mem n
  have hτ := hrun.step_pos n
  have hg0 : 0 < g (x n) := hA2.pos _ hxS
  have hg1 : 0 < g (x (n + 1)) := hA2.pos _ hx1S
  obtain ⟨r0, hr0, hF0, hF0r⟩ := fn_real hA1 hxf
  obtain ⟨r1, hr1, hF1, hF1r⟩ := fn_real hA1 hx1f
  have hFnn : 0 ≤ (objF fs fn (x n)).toReal :=
    EReal.toReal_nonneg (hA1.nonneg _ hxS hxf)
  set θ := ratio (objF fs fn) g (x n) with hθ
  set θ1 := ratio (objF fs fn) g (x (n + 1)) with hθ1
  have hθ0 : 0 ≤ θ := div_nonneg hFnn hg0.le
  have hFθ : (objF fs fn (x n)).toReal = θ * g (x n) := by
    rw [hθ]; unfold ratio; field_simp
  have hF1θ : (objF fs fn (x (n + 1))).toReal = θ1 * g (x (n + 1)) := by
    rw [hθ1]; unfold ratio; field_simp
  have hF : ∀ y, HasGradientAt fs (gradient fs y) y := fun y =>
    ((hA1.fs_contDiff.differentiable one_ne_zero) y).hasGradientAt
  have hsu := step_upper hA1 hrun n hxS hxf hx1f
  have hdesc := descent hF hA1.grad_lipschitz (extrap x κ n) (x (n + 1))
  have hcvx := convex_fo hF hA1.fs_convex (extrap x κ n) (x n)
  have hinner : ⟪gradient fs (extrap x κ n), x n - x (n + 1)⟫_ℝ =
      ⟪gradient fs (extrap x κ n), x n - (extrap x κ n)⟫_ℝ - ⟪gradient fs (extrap x κ n), x (n + 1) - (extrap x κ n)⟫_ℝ := by
    rw [← inner_sub_right]; congr 1; abel
  have hT := T_identity (x n) (x (n + 1)) (x n - xPrev x n) (gs n) (μ n) (τ n) θ
  have hextμ : extrap x μ n = x n + μ n • (x n - xPrev x n) := rfl
  have hxu : x n - (extrap x κ n) = -(κ n • (x n - xPrev x n)) := by
    show x n - (x n + κ n • (x n - xPrev x n)) = _; abel
  have hxu2 : ‖x n - (extrap x κ n)‖ ^ 2 = κ n ^ 2 * ‖(x n - xPrev x n)‖ ^ 2 := by
    rw [hxu, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hextμ, hT] at hsu
  -- weak convexity of g
  have hw := lim_wc_ineq hA2 hxS hx1S (hrun.subgrad n)
  -- step size bound
  have hMx : 0 < max (Real.sqrt β * θ / ζ) δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hstep := hrun.step_le n
  have hu0 : 0 < 1 / τ n := by positivity
  have hmaxle : max (Real.sqrt β * θ / ζ) δ ≤ 1 / τ n := by
    rw [le_div_iff₀ hτ]
    have := (le_div_iff₀ hMx).mp hstep
    linarith
  have hu1 : Real.sqrt β * θ ≤ (1 / τ n) * ζ := by
    have := le_trans (le_max_left _ _) hmaxle
    rwa [div_le_iff₀ hζ] at this
  have hu2 : δ ≤ 1 / τ n := le_trans (le_max_right _ _) hmaxle
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0
  have hA : β * θ / 2 - 1 / (2 * τ n) ≤ -(δ * (1 - Real.sqrt β * ζ) / 2) := by
    have h1 : β * θ ≤ Real.sqrt β * ((1 / τ n) * ζ) := by
      calc β * θ = Real.sqrt β * (Real.sqrt β * θ) := by rw [← mul_assoc, hsq]
        _ ≤ Real.sqrt β * ((1 / τ n) * ζ) :=
          mul_le_mul_of_nonneg_left hu1 (Real.sqrt_nonneg _)
    have h2 : 1 / (2 * τ n) = (1 / τ n) / 2 := by field_simp
    have h3 : δ * (1 - Real.sqrt β * ζ) ≤ (1 / τ n) * (1 - Real.sqrt β * ζ) :=
      mul_le_mul_of_nonneg_right hu2 hβζ.le
    rw [h2]
    nlinarith
  -- inner product bounds
  have hμτ : μ n / τ n ≤ μbar := by
    rw [div_le_iff₀ hτ]; linarith
  have hμτ0 : 0 ≤ μ n / τ n := by positivity
  have hnD := norm_nonneg (x (n + 1) - x n)
  have hne := norm_nonneg (x n - xPrev x n)
  have hin : ⟪(x (n + 1) - x n), (x n - xPrev x n)⟫_ℝ ≤ ‖(x (n + 1) - x n)‖ * ‖(x n - xPrev x n)‖ := real_inner_le_norm (x (n + 1) - x n) (x n - xPrev x n)
  have hB : μ n / τ n * ⟪(x (n + 1) - x n), (x n - xPrev x n)⟫_ℝ ≤ μbar * (‖(x (n + 1) - x n)‖ * ‖(x n - xPrev x n)‖) := by
    calc μ n / τ n * ⟪(x (n + 1) - x n), (x n - xPrev x n)⟫_ℝ ≤ μ n / τ n * (‖(x (n + 1) - x n)‖ * ‖(x n - xPrev x n)‖) :=
          mul_le_mul_of_nonneg_left hin hμτ0
      _ ≤ μbar * (‖(x (n + 1) - x n)‖ * ‖(x n - xPrev x n)‖) := mul_le_mul_of_nonneg_right hμτ (by positivity)
  have hℓ : 0 ≤ ℓ := hA1.ell_nonneg
  have hC : ℓ / 2 * (κ n ^ 2 * ‖(x n - xPrev x n)‖ ^ 2) ≤ ℓ * κbar ^ 2 / 2 * ‖(x n - xPrev x n)‖ ^ 2 := by
    have h0 : κ n ^ 2 ≤ κbar ^ 2 := pow_le_pow_left₀ hκ0 hκ1 2
    have h' : ℓ / 2 * κ n ^ 2 ≤ ℓ / 2 * κbar ^ 2 := mul_le_mul_of_nonneg_left h0 (by positivity)
    calc ℓ / 2 * (κ n ^ 2 * ‖(x n - xPrev x n)‖ ^ 2) = (ℓ / 2 * κ n ^ 2) * ‖(x n - xPrev x n)‖ ^ 2 := by ring
      _ ≤ (ℓ / 2 * κbar ^ 2) * ‖(x n - xPrev x n)‖ ^ 2 := mul_le_mul_of_nonneg_right h' (sq_nonneg _)
      _ = ℓ * κbar ^ 2 / 2 * ‖(x n - xPrev x n)‖ ^ 2 := by ring
  have hgD : θ * ⟪gs n, (x (n + 1) - x n)⟫_ℝ ≤ θ * (g (x (n + 1)) - g (x n) + β / 2 * ‖(x (n + 1) - x n)‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hθ0
    linarith
  -- assemble
  have hTexp : 1 / (2 * τ n) * (-‖(x (n + 1) - x n)‖ ^ 2 + 2 * μ n * ⟪(x (n + 1) - x n), (x n - xPrev x n)⟫_ℝ + 2 * (τ n * θ) * ⟪(x (n + 1) - x n), gs n⟫_ℝ)
      = -(1 / (2 * τ n) * ‖(x (n + 1) - x n)‖ ^ 2) + μ n / τ n * ⟪(x (n + 1) - x n), (x n - xPrev x n)⟫_ℝ + θ * ⟪(x (n + 1) - x n), gs n⟫_ℝ := by
    field_simp
  have hgs : ⟪(x (n + 1) - x n), gs n⟫_ℝ = ⟪gs n, (x (n + 1) - x n)⟫_ℝ := real_inner_comm _ _
  rw [hTexp, hgs] at hsu
  have hF1r' : (objF fs fn (x (n + 1))).toReal = fs (x (n + 1)) + r1 := hF1r
  have hF0r' : (objF fs fn (x n)).toReal = fs (x n) + r0 := hF0r
  have hxu3 : ℓ / 2 * ‖x n - extrap x κ n‖ ^ 2 = ℓ / 2 * (κ n ^ 2 * ‖x n - xPrev x n‖ ^ 2) := by
    rw [hxu2]
  have hAa := mul_le_mul_of_nonneg_left hA (sq_nonneg ‖(x (n + 1) - x n)‖)
  have hrew : g (x (n + 1)) * (θ1 - θ) = θ1 * g (x (n + 1)) - θ * g (x (n + 1)) := by ring
  rw [hrew, ← hF1θ]
  linarith

theorem dom_all {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ) :
    ∀ n, x n ∈ S ∧ objF fs fn (x n) ≠ ⊤ := by
  intro n
  induction n with
  | zero => exact ⟨hrun.start_mem, hrun.start_dom⟩
  | succ k ih => exact ⟨hrun.next_mem k, dom_next hA1 hrun k ih.1 ih.2⟩

theorem amgm (a b l : ℝ) (hl : 0 < l) : 2 * (a * b) ≤ l * a ^ 2 + b ^ 2 / l := by
  rw [← sub_nonneg]
  have : l * a ^ 2 + b ^ 2 / l - 2 * (a * b) = (l * a - b) ^ 2 / l := by
    field_simp; ring
  rw [this]; positivity

theorem lyap_bc {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2 S g β)
    (hδ : 0 < δ) (hζ : 0 < ζ) (hβζ : 0 < 1 - Real.sqrt β * ζ) {m M : ℝ}
    (hpar : ParamsBC S (objF fs fn) g ℓ β δ ζ μbar κbar m M)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ) :
    0 ≤ cBC ℓ μbar κbar m M ∧ 0 < αBC ℓ β δ ζ μbar κbar m M ∧ ∀ n,
      ratio (objF fs fn) g (x (n + 1)) + cBC ℓ μbar κbar m M * ‖x (n + 1) - x n‖ ^ 2
        + αBC ℓ β δ ζ μbar κbar m M * ‖x (n + 1) - x n‖ ^ 2 ≤
      ratio (objF fs fn) g (x n) + cBC ℓ μbar κbar m M * ‖x n - xPrev x n‖ ^ 2 := by
  obtain ⟨⟨hm, hM, hbd⟩, hμ0, hμlt, hκ0, hκlt⟩ := hpar
  have hℓ : 0 ≤ ℓ := hA1.ell_nonneg
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ m = r ^ 2 :=
    ⟨Real.sqrt m, Real.sqrt_pos.2 hm, (Real.sq_sqrt hm.le).symm⟩
  obtain ⟨R, hR, rfl⟩ : ∃ R, 0 < R ∧ M = R ^ 2 :=
    ⟨Real.sqrt M, Real.sqrt_pos.2 hM, (Real.sq_sqrt hM.le).symm⟩
  have hs : Real.sqrt (r ^ 2 * R ^ 2) = r * R := by
    rw [show r ^ 2 * R ^ 2 = (r * R) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs] at hμlt hκlt
  unfold cBC αBC
  rw [hs]
  set η := 1 - Real.sqrt β * ζ with hη
  have hc : 0 ≤ ℓ * κbar ^ 2 / (2 * r ^ 2) + μbar / (2 * (r * R)) := by positivity
  refine ⟨hc, ?_, ?_⟩
  · have h1 : ℓ * κbar ^ 2 / (2 * r ^ 2) < δ * η / (2 * R ^ 2) - μbar / (r * R) := by
      rw [div_lt_iff₀ (by positivity)]
      have : (δ * η / (2 * R ^ 2) - μbar / (r * R)) * (2 * r ^ 2) =
          r ^ 2 * δ * η / R ^ 2 - 2 * r ^ 2 * μbar / (r * R) := by
        field_simp
      rw [this]; exact hκlt
    linarith
  · intro n
    obtain ⟨hxS, hxf⟩ := dom_all hA1 hrun n
    have hst := star hA1 hA2 hδ hζ hβζ hrun n hxS hxf
    have hx1f := dom_next hA1 hrun n hxS hxf
    have hx1S := hrun.next_mem n
    obtain ⟨hgm, hgM⟩ := hbd _ hx1S hx1f
    set a := ‖x (n + 1) - x n‖ with ha
    set b := ‖x n - xPrev x n‖ with hb
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    set G := g (x (n + 1)) with hG
    set Δθ := ratio (objF fs fn) g (x (n + 1)) - ratio (objF fs fn) g (x n) with hΔθ
    have hl : 0 < R / r := by positivity
    have hag := amgm a b (R / r) hl
    have hP1 : 0 ≤ δ * η / 2 - μbar * (R / r) / 2 := by
      have h1 : μbar < δ * η * (r * R) / (2 * R ^ 2) := hμlt
      have h2 : μbar * (R / r) < δ * η / 2 := by
        have : δ * η * (r * R) / (2 * R ^ 2) = δ * η / 2 * (r / R) := by field_simp
        rw [this] at h1
        have h3 : μbar * (R / r) < δ * η / 2 * (r / R) * (R / r) :=
          mul_lt_mul_of_pos_right h1 hl
        have : δ * η / 2 * (r / R) * (R / r) = δ * η / 2 := by field_simp
        linarith
      have : 0 < δ * η := by positivity
      linarith
    have hQ1 : 0 ≤ ℓ * κbar ^ 2 / 2 + μbar / (2 * (R / r)) := by positivity
    have hmain : G * Δθ ≤ -(δ * η / 2 - μbar * (R / r) / 2) * a ^ 2
        + (ℓ * κbar ^ 2 / 2 + μbar / (2 * (R / r))) * b ^ 2 := by
      have h2 : μbar * (a * b) ≤ μbar / 2 * ((R / r) * a ^ 2 + b ^ 2 / (R / r)) := by
        have := mul_le_mul_of_nonneg_left hag (show 0 ≤ μbar / 2 by positivity)
        nlinarith
      have e1 : μbar / 2 * ((R / r) * a ^ 2 + b ^ 2 / (R / r)) =
          μbar * (R / r) / 2 * a ^ 2 + μbar / (2 * (R / r)) * b ^ 2 := by
        field_simp
      nlinarith
    have hGpos : 0 < G := lt_of_lt_of_le (by positivity) hgm
    have hdiv : Δθ ≤ -(δ * η / 2 - μbar * (R / r) / 2) * a ^ 2 / G
        + (ℓ * κbar ^ 2 / 2 + μbar / (2 * (R / r))) * b ^ 2 / G := by
      rw [← add_div, le_div_iff₀ hGpos]; linarith
    have h3 : (δ * η / 2 - μbar * (R / r) / 2) * a ^ 2 / R ^ 2 ≤
        (δ * η / 2 - μbar * (R / r) / 2) * a ^ 2 / G :=
      div_le_div_of_nonneg_left (by positivity) hGpos hgM
    have h4 : (ℓ * κbar ^ 2 / 2 + μbar / (2 * (R / r))) * b ^ 2 / G ≤
        (ℓ * κbar ^ 2 / 2 + μbar / (2 * (R / r))) * b ^ 2 / r ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hgm
    have e2 : (δ * η / 2 - μbar * (R / r) / 2) * a ^ 2 / R ^ 2 =
        (δ * η / (2 * R ^ 2) - μbar / (2 * (r * R)) ) * a ^ 2 := by
      field_simp
    have e3 : (ℓ * κbar ^ 2 / 2 + μbar / (2 * (R / r))) * b ^ 2 / r ^ 2 =
        (ℓ * κbar ^ 2 / (2 * r ^ 2) + μbar / (2 * (r * R))) * b ^ 2 := by
      field_simp
    have e4 : -(δ * η / 2 - μbar * (R / r) / 2) * a ^ 2 / G =
        -((δ * η / 2 - μbar * (R / r) / 2) * a ^ 2 / G) := by ring
    have e5 : δ * η / (2 * R ^ 2) - μbar / (2 * (r * R)) =
        (ℓ * κbar ^ 2 / (2 * r ^ 2) + μbar / (2 * (r * R))) +
        (δ * η / (2 * R ^ 2) - μbar / (r * R) - ℓ * κbar ^ 2 / (2 * r ^ 2)) := by
      field_simp; ring
    rw [e4] at hdiv
    rw [e2] at h3
    rw [e3] at h4
    rw [e5] at h3
    show _ + _ * a ^ 2 + _ * a ^ 2 ≤ _ + _ * b ^ 2
    linarith

theorem lyap_nobc {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hS : IsClosed S)
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2 S g β)
    (hδ : 0 < δ) (hζ : 0 < ζ) (hβζ : 0 < 1 - Real.sqrt β * ζ)
    (hpar : ParamsNoBC μbar κbar)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ)
    (hS0 : Bornology.IsBounded (S0 S (objF fs fn) g (x 0))) :
    ∃ α : ℝ, 0 < α ∧ ∀ n,
      ratio (objF fs fn) g (x (n + 1)) + α * ‖x (n + 1) - x n‖ ^ 2 ≤
      ratio (objF fs fn) g (x n) := by
  obtain ⟨rfl, rfl⟩ := hpar
  have hη := hβζ
  set η := 1 - Real.sqrt β * ζ with hηdef
  have hmono : ∀ n, g (x (n + 1)) * (ratio (objF fs fn) g (x (n + 1)) - ratio (objF fs fn) g (x n))
      ≤ -(δ * η / 2) * ‖x (n + 1) - x n‖ ^ 2 := by
    intro n
    obtain ⟨hxS, hxf⟩ := dom_all hA1 hrun n
    have := star hA1 hA2 hδ hζ hβζ hrun n hxS hxf
    simpa using this
  have hGpos : ∀ n, 0 < g (x (n + 1)) := fun n => hA2.pos _ (hrun.next_mem n)
  have hanti : ∀ n, ratio (objF fs fn) g (x (n + 1)) ≤ ratio (objF fs fn) g (x n) := by
    intro n
    by_contra hcon
    push Not at hcon
    have h1 := mul_pos (hGpos n) (sub_pos.2 hcon)
    have h2 := hmono n
    have h3 : 0 ≤ δ * η / 2 * ‖x (n + 1) - x n‖ ^ 2 := by positivity
    linarith
  have hle0 : ∀ n, ratio (objF fs fn) g (x n) ≤ ratio (objF fs fn) g (x 0) :=
    fun n => (antitone_nat_of_succ_le (f := fun n => ratio (objF fs fn) g (x n)) hanti) (Nat.zero_le n)
  have hmem : ∀ n, x n ∈ S0 S (objF fs fn) g (x 0) := fun n =>
    ⟨(dom_all hA1 hrun n).1, (dom_all hA1 hrun n).2, hle0 n⟩
  -- g is bounded above on S0
  obtain ⟨O, hO, hSO, hcont⟩ := hA2.continuous_near
  have hcl : IsCompact (closure (S0 S (objF fs fn) g (x 0))) := hS0.isCompact_closure
  have hclS : closure (S0 S (objF fs fn) g (x 0)) ⊆ S :=
    closure_minimal (fun y hy => hy.1) hS
  have hcon : ContinuousOn g (closure (S0 S (objF fs fn) g (x 0))) :=
    hcont.mono (hclS.trans hSO)
  obtain ⟨Mb', hMb'⟩ := (hcl.image_of_continuousOn hcon).bddAbove
  have hMb : ∀ y ∈ S0 S (objF fs fn) g (x 0), g y ≤ max Mb' 1 := by
    intro y hy
    exact le_trans (hMb' ⟨y, subset_closure hy, rfl⟩) (le_max_left _ _)
  have hMbpos : 0 < max Mb' 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨δ * η / 2 / max Mb' 1, by positivity, fun n => ?_⟩
  have h1 := hmono n
  have hGM : g (x (n + 1)) ≤ max Mb' 1 := hMb _ (hmem (n + 1))
  set Δθ := ratio (objF fs fn) g (x (n + 1)) - ratio (objF fs fn) g (x n) with hΔθ
  have hdiv : Δθ ≤ -(δ * η / 2 * ‖x (n + 1) - x n‖ ^ 2) / g (x (n + 1)) := by
    rw [le_div_iff₀ (hGpos n)]; linarith
  have h3 : δ * η / 2 * ‖x (n + 1) - x n‖ ^ 2 / max Mb' 1 ≤
      δ * η / 2 * ‖x (n + 1) - x n‖ ^ 2 / g (x (n + 1)) :=
    div_le_div_of_nonneg_left (by positivity) (hGpos n) hGM
  have e1 : -(δ * η / 2 * ‖x (n + 1) - x n‖ ^ 2) / g (x (n + 1)) =
      -(δ * η / 2 * ‖x (n + 1) - x n‖ ^ 2 / g (x (n + 1))) := by ring
  have e2 : δ * η / 2 / max Mb' 1 * ‖x (n + 1) - x n‖ ^ 2 =
      δ * η / 2 * ‖x (n + 1) - x n‖ ^ 2 / max Mb' 1 := by ring
  rw [e1] at hdiv
  rw [e2]
  linarith

theorem lyap_all {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hS : IsClosed S)
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2 S g β)
    (hδ : 0 < δ) (hζ : 0 < ζ) (hβζ : 0 < 1 - Real.sqrt β * ζ) {m M : ℝ}
    (hpar : ParamsBC S (objF fs fn) g ℓ β δ ζ μbar κbar m M ∨ ParamsNoBC μbar κbar)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ)
    (hS0 : Bornology.IsBounded (S0 S (objF fs fn) g (x 0))) :
    ∃ c α : ℝ, 0 ≤ c ∧ 0 < α ∧ ∀ n,
      ratio (objF fs fn) g (x (n + 1)) + c * ‖x (n + 1) - x n‖ ^ 2
        + α * ‖x (n + 1) - x n‖ ^ 2 ≤
      ratio (objF fs fn) g (x n) + c * ‖x n - xPrev x n‖ ^ 2 := by
  rcases hpar with h | h
  · obtain ⟨hc, hα, hstep⟩ := lyap_bc hA1 hA2 hδ hζ hβζ h hrun
    exact ⟨_, _, hc, hα, hstep⟩
  · obtain ⟨α, hα, hstep⟩ := lyap_nobc hS hA1 hA2 hδ hζ hβζ h hrun hS0
    refine ⟨0, α, le_rfl, hα, fun n => ?_⟩
    have := hstep n
    simpa using this

end P3483

namespace P6afa

open NonconvexSplitting.Shared FracPSG.Subseq


/-- A regular subgradient of a function that is `K`-Lipschitz near `z` has norm at most `K`. -/
theorem regSubgrad_norm_le {N : ℕ} {g : EuclideanSpace ℝ (Fin N) → ℝ}
    {z v : EuclideanSpace ℝ (Fin N)} {K : NNReal} {U : Set (EuclideanSpace ℝ (Fin N))}
    (hU : U ∈ 𝓝 z) (hK : LipschitzOnWith K g U)
    (hv : IsRegularSubgrad (fun y => (g y : EReal)) z v) : ‖v‖ ≤ K := by
  by_contra hcon
  push Not at hcon
  have hKnn : (0 : ℝ) ≤ K := K.2
  have hvpos : 0 < ‖v‖ := lt_of_le_of_lt hKnn hcon
  set ε : ℝ := (‖v‖ - K) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hline : Tendsto (fun s : ℝ => z + s • v) (𝓝[>] (0:ℝ)) (𝓝 z) := by
    have : Continuous (fun s : ℝ => z + s • v) := by fun_prop
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 := hline.eventually (hv.2 ε hε)
  have h2 := hline.eventually hU
  obtain ⟨s, hs1, hs2, hs3⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
  have hs0 : 0 < s := hs3
  simp only [add_sub_cancel_left] at hs1
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hs1
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, real_inner_self_eq_norm_sq]
    at hs1
  have hlip : dist (g (z + s • v)) (g z) ≤ K * dist (z + s • v) z :=
    hK.dist_le_mul _ hs2 _ (mem_of_mem_nhds hU)
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hs0] at hlip
  have hup : g (z + s • v) - g z ≤ K * (s * ‖v‖) := (le_abs_self _).trans hlip
  -- s‖v‖² - ε s‖v‖ ≤ K s ‖v‖
  have h3 : s * ‖v‖ ^ 2 - ε * (s * ‖v‖) ≤ K * (s * ‖v‖) := by linarith
  have h4 : 0 < s * ‖v‖ := mul_pos hs0 hvpos
  have h5 : ‖v‖ - ε ≤ K := by
    have : (‖v‖ - ε) * (s * ‖v‖) ≤ K * (s * ‖v‖) := by nlinarith
    exact le_of_mul_le_mul_right this h4
  rw [hεdef] at h5
  linarith

/-- A limiting subgradient of a function that is `K`-Lipschitz near `z` has norm at most `K`. -/
theorem limSubgrad_norm_le {N : ℕ} {g : EuclideanSpace ℝ (Fin N) → ℝ}
    {z v : EuclideanSpace ℝ (Fin N)} {K : NNReal} {U : Set (EuclideanSpace ℝ (Fin N))}
    (hU : U ∈ 𝓝 z) (hK : LipschitzOnWith K g U)
    (hv : v ∈ LimitingSubdiff (fun y => (g y : EReal)) z) : ‖v‖ ≤ K := by
  obtain ⟨-, xs, vs, hxs, -, hvs, hreg⟩ := hv
  have hev : ∀ᶠ y in 𝓝 z, U ∈ 𝓝 y := Filter.Eventually.eventually_nhds (p := fun y => y ∈ U) hU
  have hev2 : ∀ᶠ t in atTop, ‖vs t‖ ≤ K := by
    filter_upwards [hxs.eventually hev] with t ht
    exact regSubgrad_norm_le ht hK (hreg t)
  exact le_of_tendsto hvs.norm hev2

theorem T2_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (xb y v gr : E)
    (τ θ T0 δ Θ Γ : ℝ) (hT0 : 0 < T0) (hτ0 : T0 ≤ τ) (hτδ : τ ≤ 1 / δ) (hδ : 0 < δ)
    (hθ : |θ| ≤ Θ) (hgr : ‖gr‖ ≤ Γ) (h1 : ‖xb - v‖ ≤ 1) (h2 : ‖y - v‖ ≤ 1) :
    |1 / (2 * τ) * (‖xb - v - (τ * θ) • gr‖ ^ 2 - ‖y - v - (τ * θ) • gr‖ ^ 2)| ≤
      1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)) * ‖xb - y‖ := by
  have hτ : 0 < τ := lt_of_lt_of_le hT0 hτ0
  set c := (τ * θ) • gr with hcdef
  have hΘ : 0 ≤ Θ := le_trans (abs_nonneg _) hθ
  have hΓ : 0 ≤ Γ := le_trans (norm_nonneg _) hgr
  have hc : ‖c‖ ≤ 1 / δ * Θ * Γ := by
    rw [hcdef, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hτ]
    have := mul_le_mul hτδ hθ (abs_nonneg _) (by positivity)
    exact mul_le_mul this hgr (norm_nonneg _) (by positivity)
  set K := 1 / δ * Θ * Γ
  have ha : ‖xb - v - c‖ ≤ 1 + K := (norm_sub_le _ _).trans (add_le_add h1 hc)
  have hb : ‖y - v - c‖ ≤ 1 + K := (norm_sub_le _ _).trans (add_le_add h2 hc)
  have hab : |‖xb - v - c‖ - ‖y - v - c‖| ≤ ‖xb - y‖ := by
    have := abs_norm_sub_norm_le (xb - v - c) (y - v - c)
    have e : xb - v - c - (y - v - c) = xb - y := by abel
    rwa [e] at this
  have hsq : |‖xb - v - c‖ ^ 2 - ‖y - v - c‖ ^ 2| ≤ ‖xb - y‖ * (2 + 2 * K) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖xb - v - c‖ + ‖y - v - c‖),
      mul_comm]
    exact mul_le_mul hab (by linarith) (by positivity) (norm_nonneg _)
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * τ))]
  have hinv : 1 / (2 * τ) ≤ 1 / (2 * T0) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  calc 1 / (2 * τ) * |‖xb - v - c‖ ^ 2 - ‖y - v - c‖ ^ 2|
      ≤ 1 / (2 * T0) * (‖xb - y‖ * (2 + 2 * K)) :=
        mul_le_mul hinv hsq (abs_nonneg _) (by positivity)
    _ = 1 / (2 * T0) * (2 + 2 * K) * ‖xb - y‖ := by ring

theorem objF_lsc {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))} {fs : EuclideanSpace ℝ (Fin N) → ℝ}
    {fn : EuclideanSpace ℝ (Fin N) → EReal} {ℓ : ℝ} (hA1 : Assumption1 S fs fn ℓ) :
    LowerSemicontinuous (objF fs fn) := by
  have h1 : LowerSemicontinuous (fun y => ((fs y : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hA1.fs_contDiff.continuous).lowerSemicontinuous
  show LowerSemicontinuous (fun y => ((fs y : ℝ) : EReal) + fn y)
  exact LowerSemicontinuous.add' h1 hA1.fn_lsc (fun y =>
    EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))

/-- Subsequence along which `x (n+1)`, `x n` and both extrapolated points converge to a cluster point. -/
theorem sub_setup {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hδ : 0 < δ) (hμbar : 0 ≤ μbar)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ)
    (hstep : Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0))
    {xbar : EuclideanSpace ℝ (Fin N)} (hcl : MapClusterPt xbar atTop x) :
    ∃ nn : ℕ → ℕ, Tendsto nn atTop atTop ∧
      Tendsto (fun k => x (nn k + 1)) atTop (𝓝 xbar) ∧
      Tendsto (fun k => x (nn k)) atTop (𝓝 xbar) ∧
      Tendsto (fun k => extrap x κ (nn k)) atTop (𝓝 xbar) ∧
      Tendsto (fun k => extrap x μ (nn k)) atTop (𝓝 xbar) := by
  have hτle : ∀ n, τ n ≤ 1 / δ := fun n =>
    (hrun.step_le n).trans (one_div_le_one_div_of_le hδ (le_max_right _ _))

  obtain ⟨ψ, hψm, hψt⟩ := hcl.tendsto_subseq
  obtain ⟨nn, hnn1, hnnk⟩ : ∃ nn : ℕ → ℕ, (∀ k, nn k + 1 = ψ (k + 1)) ∧ ∀ k, k ≤ nn k := by
    refine ⟨fun k => ψ (k + 1) - 1, fun k => ?_, fun k => ?_⟩
    · have hle : k + 1 ≤ ψ (k + 1) := hψm.id_le (k + 1)
      show ψ (k + 1) - 1 + 1 = ψ (k + 1)
      omega
    · have hle : k + 1 ≤ ψ (k + 1) := hψm.id_le (k + 1)
      show k ≤ ψ (k + 1) - 1
      omega
  have hnnt : Tendsto nn atTop atTop := tendsto_atTop_mono hnnk tendsto_id
  have hnnt1 : Tendsto (fun k => nn k + 1) atTop atTop := tendsto_add_atTop_nat 1 |>.comp hnnt
  have hy : Tendsto (fun k => x (nn k + 1)) atTop (𝓝 xbar) := by
    have := hψt.comp (tendsto_add_atTop_nat 1)
    refine this.congr (fun k => ?_)
    simp [Function.comp, hnn1]
  have hsteps : Tendsto (fun k => x (nn k + 1) - x (nn k)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]; exact hstep.comp hnnt
  have hx0 : Tendsto (fun k => x (nn k)) atTop (𝓝 xbar) := by
    have := hy.sub hsteps; simpa using this
  have hprevd : Tendsto (fun n => x n - xPrev x n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 := hstep.comp (tendsto_sub_atTop_nat 1)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp, xPrev, if_neg (by omega : n ≠ 0),
      Nat.sub_add_cancel hn]
  have hprevk := hprevd.comp hnnt
  have hu : Tendsto (fun k => extrap x κ (nn k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => κ (nn k) • (x (nn k) - xPrev x (nn k))) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k => κbar * ‖x (nn k) - xPrev x (nn k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.kappa_mem (nn k)).1]
        exact mul_le_mul_of_nonneg_right (hrun.kappa_mem (nn k)).2 (norm_nonneg _)
      · simpa using (hprevk.norm).const_mul κbar
    have := hx0.add hz
    simpa [extrap] using this
  have hv : Tendsto (fun k => extrap x μ (nn k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => μ (nn k) • (x (nn k) - xPrev x (nn k))) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm
        (a := fun k => (μbar * (1 / δ)) * ‖x (nn k) - xPrev x (nn k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.mu_mem (nn k)).1]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (hrun.mu_mem (nn k)).2.trans
          (mul_le_mul_of_nonneg_left (hτle _) hμbar)
      · simpa using (hprevk.norm).const_mul (μbar * (1 / δ))
    have := hx0.add hz
    simpa [extrap] using this
  exact ⟨nn, hnnt, hy, hx0, hu, hv⟩

/-- The limit of the ratios equals the ratio at any cluster point. -/
theorem ratio_limit_eq {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2 S g β)
    (hδ : 0 < δ) (hμbar : 0 ≤ μbar)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ)
    (hgLip : ∀ y ∈ S, ∃ K : NNReal, ∃ U ∈ 𝓝 y, LipschitzOnWith K g U)
    {τbar : ℝ} (hτbar : 0 < τbar) (hτ : ∀ᶠ n in atTop, τbar ≤ τ n)
    (hxn : ∀ n, x n ∈ S ∧ objF fs fn (x n) ≠ ⊤)
    {L : ℝ} (hL : Tendsto (fun n => ratio (objF fs fn) g (x n)) atTop (𝓝 L))
    (hstep : Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0))
    {xbar : EuclideanSpace ℝ (Fin N)} (hcl : MapClusterPt xbar atTop x) (hxbS : xbar ∈ S) :
    objF fs fn xbar ≠ ⊤ ∧ L = ratio (objF fs fn) g xbar := by
  have hlsc := objF_lsc hA1
  set f := objF fs fn with hf
  obtain ⟨O, hO, hSO, hgO⟩ := hA2.continuous_near
  have hgcont : ContinuousAt g xbar := hgO.continuousAt (hO.mem_nhds (hSO hxbS))
  have hgpos : 0 < g xbar := hA2.pos xbar hxbS
  have hτle : ∀ n, τ n ≤ 1 / δ := fun n =>
    (hrun.step_le n).trans (one_div_le_one_div_of_le hδ (le_max_right _ _))
  obtain ⟨K, U, hU, hKU⟩ := hgLip xbar hxbS
  obtain ⟨nn, hnnt, hy, hx0, hu, hv⟩ := sub_setup hδ hμbar hrun hstep hcl
  have hnnt1 : Tendsto (fun k => nn k + 1) atTop atTop := tendsto_add_atTop_nat 1 |>.comp hnnt
  obtain ⟨K, U, hU, hKU⟩ := hgLip xbar hxbS
  -- a_k
  set a : ℕ → ℝ := fun k => (f (x (nn k + 1))).toReal with ha
  have ha_eq : ∀ k, a k = ratio f g (x (nn k + 1)) * g (x (nn k + 1)) := by
    intro k
    have hp : 0 < g (x (nn k + 1)) := hA2.pos _ (hxn _).1
    simp only [ha, ratio]
    field_simp
  have hA : Tendsto a atTop (𝓝 (L * g xbar)) := by
    have := (hL.comp hnnt1).mul (hgcont.tendsto.comp hy)
    refine this.congr (fun k => ?_)
    rw [ha_eq k]; rfl
  have hfin : ∀ k, f (x (nn k + 1)) = ((a k : ℝ) : EReal) := by
    intro k
    obtain ⟨r, -, h1, h2⟩ := P3483.fn_real hA1 (hxn (nn k + 1)).2
    simp only [ha]; rw [← hf] at h1 h2; rw [h2, h1]
  have hxbf : f xbar ≠ ⊤ := by
    intro htop
    have hlt : (((L * g xbar + 1 : ℝ)) : EReal) < f xbar := by
      rw [htop]; exact EReal.coe_lt_top _
    have hev : ∀ᶠ k in atTop, (((L * g xbar + 1 : ℝ)) : EReal) < ((a k : ℝ) : EReal) := by
      have := hy.eventually (hlsc xbar _ hlt)
      filter_upwards [this] with k hk
      rwa [hfin k] at hk
    have hev2 : ∀ᶠ k in atTop, a k < L * g xbar + 1 :=
      hA.eventually (gt_mem_nhds (by linarith))
    obtain ⟨k, hk1, hk2⟩ := (hev.and hev2).exists
    have := EReal.coe_lt_coe_iff.1 hk1
    linarith
  obtain ⟨F0, -, hF0, hF⟩ := P3483.fn_real hA1 hxbf
  set F := (f xbar).toReal with hFdef
  -- lower bound by lower semicontinuity
  have hlow : F ≤ L * g xbar := by
    have hfin : ∀ k, f (x (nn k + 1)) = ((a k : ℝ) : EReal) := by
      intro k
      obtain ⟨r, -, h1, h2⟩ := P3483.fn_real hA1 (hxn (nn k + 1)).2
      simp only [ha]; rw [← hf] at h1 h2; rw [h2, h1]
    have hfx : f xbar = ((F : ℝ) : EReal) := by
      rw [hFdef, ← hf] at *; rw [hF0, EReal.toReal_coe]
    by_contra hcon
    push Not at hcon
    have hlt : (((L * g xbar : ℝ)) : EReal) < f xbar := by
      rw [hfx]; exact EReal.coe_lt_coe_iff.2 hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hev : ∀ᶠ k in atTop, c < ((a k : ℝ) : EReal) := by
      have := hy.eventually (hlsc xbar c hc2)
      filter_upwards [this] with k hk
      rwa [hfin k] at hk
    have hAE : Tendsto (fun k => ((a k : ℝ) : EReal)) atTop (𝓝 ((L * g xbar : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp hA
    have : c ≤ ((L * g xbar : ℝ) : EReal) := ge_of_tendsto hAE (hev.mono fun k hk => hk.le)
    exact absurd hc1 (not_lt.2 this)
  -- upper bound
  set E : ℕ → ℝ := fun k =>
      (fs (x (nn k + 1)) - fs xbar)
      + ⟪gradient fs (extrap x κ (nn k)), xbar - x (nn k + 1)⟫_ℝ
      + 1 / (2 * τ (nn k)) *
          (‖xbar - extrap x μ (nn k) - (τ (nn k) * ratio f g (x (nn k))) • gs (nn k)‖ ^ 2
            - ‖x (nn k + 1) - extrap x μ (nn k) - (τ (nn k) * ratio f g (x (nn k))) •
              gs (nn k)‖ ^ 2)
      + ℓ / 2 * (‖xbar - extrap x κ (nn k)‖ ^ 2
          - ‖x (nn k + 1) - extrap x κ (nn k)‖ ^ 2) with hE
  have hupk : ∀ k, a k ≤ F + E k := by
    intro k
    have := P3483.step_upper hA1 hrun (nn k) hxbS hxbf (hxn (nn k + 1)).2
    simp only [ha, hE, hFdef]
    linarith
  have hfsc : Continuous fs := hA1.fs_contDiff.continuous
  have hgfs : Continuous (fun z => gradient fs z) := by
    have h1 := hA1.fs_contDiff.continuous_fderiv one_ne_zero
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.continuous.comp h1
  have hdy : Tendsto (fun k => xbar - x (nn k + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := xbar)).sub hy; simpa using this
  have hE1 : Tendsto (fun k => fs (x (nn k + 1)) - fs xbar) atTop (𝓝 0) := by
    have := ((hfsc.tendsto xbar).comp hy).sub (tendsto_const_nhds (x := fs xbar))
    simpa using this
  have hE2 : Tendsto (fun k => ⟪gradient fs (extrap x κ (nn k)),
      xbar - x (nn k + 1)⟫_ℝ) atTop (𝓝 0) := by
    have := Filter.Tendsto.inner (𝕜 := ℝ) ((hgfs.tendsto xbar).comp hu) hdy
    simpa using this
  have hE4 : Tendsto (fun k => ℓ / 2 * (‖xbar - extrap x κ (nn k)‖ ^ 2
          - ‖x (nn k + 1) - extrap x κ (nn k)‖ ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => xbar - extrap x κ (nn k)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := xbar)).sub hu; simpa using this
    have h2 : Tendsto (fun k => x (nn k + 1) - extrap x κ (nn k)) atTop (𝓝 0) := by
      have := hy.sub hu; simpa using this
    have := ((h1.norm.pow 2).sub (h2.norm.pow 2)).const_mul (ℓ / 2)
    simpa using this
  -- the quadratic term, by a squeeze
  set T0 := τbar with hT0
  have hT0pos : 0 < T0 := hτbar
  set Θ := |L| + 1
  set Γ : ℝ := (K : ℝ)
  have ev1 : ∀ᶠ k in atTop, T0 ≤ τ (nn k) := hnnt.eventually hτ
  have ev2 : ∀ᶠ k in atTop, |ratio f g (x (nn k))| ≤ Θ := by
    have := (hL.comp hnnt).eventually (Metric.ball_mem_nhds L one_pos)
    filter_upwards [this] with k hk
    have hk' : |ratio f g (x (nn k)) - L| < 1 := by
      simpa [Real.dist_eq] using hk
    have := abs_sub_abs_le_abs_sub (ratio f g (x (nn k))) L
    linarith
  have ev3 : ∀ᶠ k in atTop, ‖gs (nn k)‖ ≤ Γ := by
    have hev : ∀ᶠ y in 𝓝 xbar, U ∈ 𝓝 y :=
      Filter.Eventually.eventually_nhds (p := fun y => y ∈ U) hU
    filter_upwards [hx0.eventually hev] with k hk
    exact limSubgrad_norm_le hk hKU (hrun.subgrad (nn k))
  have ev4 : ∀ᶠ k in atTop, ‖xbar - extrap x μ (nn k)‖ ≤ 1 := by
    have h1 : Tendsto (fun k => ‖xbar - extrap x μ (nn k)‖) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := xbar)).sub hv).norm; simpa using this
    exact (h1.eventually (gt_mem_nhds one_pos)).mono fun k hk => hk.le
  have ev5 : ∀ᶠ k in atTop, ‖x (nn k + 1) - extrap x μ (nn k)‖ ≤ 1 := by
    have h1 : Tendsto (fun k => ‖x (nn k + 1) - extrap x μ (nn k)‖) atTop
        (𝓝 0) := by
      have := (hy.sub hv).norm; simpa using this
    exact (h1.eventually (gt_mem_nhds one_pos)).mono fun k hk => hk.le
  have hE3 : Tendsto (fun k => 1 / (2 * τ (nn k)) *
          (‖xbar - extrap x μ (nn k) - (τ (nn k) * ratio f g (x (nn k))) • gs (nn k)‖ ^ 2
            - ‖x (nn k + 1) - extrap x μ (nn k) - (τ (nn k) * ratio f g (x (nn k))) •
              gs (nn k)‖ ^ 2)) atTop (𝓝 0) := by
    have hb : Tendsto (fun k => 1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)) *
        ‖xbar - x (nn k + 1)‖) atTop (𝓝 0) := by
      have := (hdy.norm).const_mul (1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)))
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [ev1, ev2, ev3, ev4, ev5] with k h1 h2 h3 h4 h5
    rw [Real.norm_eq_abs]
    exact T2_bound _ _ _ _ _ _ T0 δ Θ Γ hT0pos h1 (hτle _) hδ h2 h3 h4 h5
  have hEt : Tendsto E atTop (𝓝 0) := by
    have := ((hE1.add hE2).add hE3).add hE4
    simpa [hE] using this
  have hup : L * g xbar ≤ F := by
    have := le_of_tendsto_of_tendsto hA ((tendsto_const_nhds (x := F)).add hEt)
      (Eventually.of_forall hupk)
    simpa using this
  have heq : L * g xbar = F := le_antisymm hup hlow
  refine ⟨hxbf, ?_⟩
  simp only [ratio]
  rw [← hFdef, ← heq]
  field_simp

/-- Closedness of the limiting subdifferential graph for a function continuous at the limit point. -/
theorem limSub_closed {N : ℕ} {g : EuclideanSpace ℝ (Fin N) → ℝ}
    {xbar v : EuclideanSpace ℝ (Fin N)} (hg : ContinuousAt g xbar)
    {xs vs : ℕ → EuclideanSpace ℝ (Fin N)}
    (hxs : Tendsto xs atTop (𝓝 xbar)) (hvs : Tendsto vs atTop (𝓝 v))
    (hmem : ∀ k, vs k ∈ LimitingSubdiff (fun y => (g y : EReal)) (xs k)) :
    v ∈ LimitingSubdiff (fun y => (g y : EReal)) xbar := by
  refine ⟨EReal.coe_ne_top _, ?_⟩
  have key : ∀ k : ℕ, ∃ p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N),
      IsRegularSubgrad (fun y => (g y : EReal)) p.1 p.2 ∧
        dist p.1 (xs k) < 1 / ((k : ℝ) + 1) ∧ dist p.2 (vs k) < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨-, ys, ws, hys, -, hws, hreg⟩ := hmem k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have e1 := hys.eventually (Metric.ball_mem_nhds (xs k) hpos)
    have e2 := hws.eventually (Metric.ball_mem_nhds (vs k) hpos)
    obtain ⟨t, h1, h2⟩ := (e1.and e2).exists
    exact ⟨(ys t, ws t), hreg t, h1, h2⟩
  choose p hp1 hp2 hp3 using key
  have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hx1 : Tendsto (fun k => (p k).1) atTop (𝓝 xbar) := by
    have hd : Tendsto (fun k => (p k).1 - xs k) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) h0
      rw [← dist_eq_norm]; exact (hp2 k).le
    have := hd.add hxs
    simpa using this
  have hv1 : Tendsto (fun k => (p k).2) atTop (𝓝 v) := by
    have hd : Tendsto (fun k => (p k).2 - vs k) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) h0
      rw [← dist_eq_norm]; exact (hp3 k).le
    have := hd.add hvs
    simpa using this
  refine ⟨fun k => (p k).1, fun k => (p k).2, hx1, ?_, hv1, fun k => hp1 k⟩
  exact (continuous_coe_real_ereal.tendsto _).comp (hg.tendsto.comp hx1)

theorem base {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hS : IsClosed S)
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2 S g β)
    (hδ : 0 < δ) (hζ : 0 < ζ) (hβζ : 0 < 1 - Real.sqrt β * ζ) {m M : ℝ}
    (hpar : ParamsBC S (objF fs fn) g ℓ β δ ζ μbar κbar m M ∨ ParamsNoBC μbar κbar)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ)
    (hS0 : Bornology.IsBounded (S0 S (objF fs fn) g (x 0))) :
    (∀ n, x n ∈ S ∧ objF fs fn (x n) ≠ ⊤) ∧
    (∃ L : ℝ, Tendsto (fun n => ratio (objF fs fn) g (x n)) atTop (𝓝 L)) ∧
    Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0) := by
  obtain ⟨c, α, hc, hα, hstep⟩ := P3483.lyap_all hS hA1 hA2 hδ hζ hβζ hpar hrun hS0
  have hdom := P3483.dom_all hA1 hrun
  set θ : ℕ → ℝ := fun n => ratio (objF fs fn) g (x n) with hθdef
  set a : ℕ → ℝ := fun n => ‖x (n + 1) - x n‖ with hadef
  set Φ : ℕ → ℝ := fun n => θ n + c * ‖x n - xPrev x n‖ ^ 2 with hΦdef
  have hθnn : ∀ n, 0 ≤ θ n := by
    intro n
    obtain ⟨hxS, hxf⟩ := hdom n
    exact div_nonneg (EReal.toReal_nonneg (hA1.nonneg _ hxS hxf)) (hA2.pos _ hxS).le
  have hΦnn : ∀ n, 0 ≤ Φ n := fun n => add_nonneg (hθnn n) (by positivity)
  have hprev : ∀ n, ‖x (n + 1) - xPrev x (n + 1)‖ = a n := by
    intro n
    simp [xPrev, hadef]
  have hΦ : ∀ n, Φ (n + 1) + α * a n ^ 2 ≤ Φ n := by
    intro n
    have := hstep n
    simp only [hΦdef, hθdef, hprev, hadef]
    simp only [hadef] at *
    linarith
  have hΦanti : Antitone Φ := antitone_nat_of_succ_le (fun k =>
    le_trans (le_add_of_nonneg_right (mul_nonneg hα.le (sq_nonneg _))) (hΦ k))
  have hsum : ∀ N', ∑ i ∈ Finset.range N', α * a i ^ 2 ≤ Φ 0 := by
    have key : ∀ N', ∑ i ∈ Finset.range N', α * a i ^ 2 ≤ Φ 0 - Φ N' := by
      intro N'
      induction N' with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ]
        have := hΦ k
        linarith
    intro N'
    have h1 := key N'
    have h2 := hΦnn N'
    linarith
  have hsumm : Summable (fun n => a n ^ 2) := by
    refine summable_of_sum_range_le (c := Φ 0 / α) (fun n => sq_nonneg _) (fun N' => ?_)
    rw [le_div_iff₀ hα]
    have h := hsum N'
    rw [← Finset.mul_sum] at h
    linarith
  have h0 := hsumm.tendsto_atTop_zero
  refine ⟨hdom, ?_, ?_⟩
  · obtain ⟨L, hL⟩ : ∃ L, Tendsto Φ atTop (𝓝 L) :=
      ⟨_, tendsto_atTop_ciInf hΦanti ⟨0, by rintro _ ⟨n, rfl⟩; exact hΦnn n⟩⟩
    have hb : Tendsto (fun n => ‖x n - xPrev x n‖ ^ 2) atTop (𝓝 0) := by
      rw [← tendsto_add_atTop_iff_nat 1]
      refine h0.congr (fun n => ?_)
      rw [hprev]
    refine ⟨L - c * 0, ?_⟩
    have := hL.sub (hb.const_mul c)
    refine this.congr (fun n => ?_)
    simp [hΦdef]
  · have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at h1
    exact h1.congr (fun n => Real.sqrt_sq (norm_nonneg _))

end P6afa


open Filter Topology FracPSG.Subseq NonconvexSplitting.Shared InnerProductSpace in
theorem solution
    {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ μbar κbar : ℝ}
    {x gs : ℕ → EuclideanSpace ℝ (Fin N)} {τ κ μ : ℕ → ℝ}
    (hS : IsClosed S) (hSconv : Convex ℝ S)
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2 S g β)
    (hδ : 0 < δ) (hζ : 0 < ζ) (hβζ : 0 < 1 - Real.sqrt β * ζ) {m M : ℝ}
    (hpar : ParamsBC S (objF fs fn) g ℓ β δ ζ μbar κbar m M ∨ ParamsNoBC μbar κbar)
    (hrun : IsEPSGRun S fs fn g ℓ β δ ζ μbar κbar x gs τ κ μ)
    (hS0 : Bornology.IsBounded (S0 S (objF fs fn) g (x 0)))
    (hgLip : ∀ y ∈ S, ∃ K : NNReal, ∃ U ∈ 𝓝 y, LipschitzOnWith K g U)
    (τbar : ℝ) (hτbar : 0 < τbar) (hτ : ∀ ε > 0, ∀ᶠ n in atTop, τbar - ε ≤ τ n)
    (xbar : EuclideanSpace ℝ (Fin N)) (hxbar : MapClusterPt xbar atTop x) :
    ∃ gbar ∈ LimitingSubdiff (fun y => (g y : EReal)) xbar, ∀ y ∈ S,
      objF fs fn xbar +
          ((-(1 / (2 * τbar)) * ‖y - xbar‖ ^ 2
            - ratio (objF fs fn) g xbar * ⟪gbar, xbar - y⟫_ℝ
            - ℓ / 2 * ‖y - xbar‖ ^ 2 : ℝ) : EReal) ≤
        objF fs fn y := by
  have hcl := hxbar
  obtain ⟨hxn, ⟨L, hL⟩, hstep⟩ := P6afa.base hS hA1 hA2 hδ hζ hβζ hpar hrun hS0
  have hτ2 : ∀ᶠ n in atTop, τbar / 2 ≤ τ n :=
    (hτ (τbar / 2) (by positivity)).mono fun n hn => by linarith
  have hxbS : xbar ∈ S := by
    obtain ⟨ψ, -, hψt⟩ := hcl.tendsto_subseq
    exact hS.mem_of_tendsto hψt (Eventually.of_forall fun k => (hxn _).1)
  have hμbar : 0 ≤ μbar := by
    rcases hpar with h | h
    · exact h.2.1
    · exact le_of_eq h.1.symm
  obtain ⟨hxbf, hLeq⟩ := P6afa.ratio_limit_eq hA1 hA2 hδ hμbar hrun hgLip (by positivity) hτ2
    hxn hL hstep hcl hxbS
  have hgpos : 0 < g xbar := hA2.pos xbar hxbS
  obtain ⟨O, hO, hSO, hgO⟩ := hA2.continuous_near
  have hgcont : ContinuousAt g xbar := hgO.continuousAt (hO.mem_nhds (hSO hxbS))
  obtain ⟨K, U, hU, hKU⟩ := hgLip xbar hxbS
  have hτle : ∀ n, τ n ≤ 1 / δ := fun n =>
    (hrun.step_le n).trans (one_div_le_one_div_of_le hδ (le_max_right _ _))
  obtain ⟨nn, hnnt, hy, hx0, hu, hv⟩ := P6afa.sub_setup hδ hμbar hrun hstep hcl
  have ev3 : ∀ᶠ k in atTop, ‖gs (nn k)‖ ≤ K := by
    have hev : ∀ᶠ y in 𝓝 xbar, U ∈ 𝓝 y :=
      Filter.Eventually.eventually_nhds (p := fun y => y ∈ U) hU
    filter_upwards [hx0.eventually hev] with k hk
    exact P6afa.limSubgrad_norm_le hk hKU (hrun.subgrad (nn k))
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 ev3
  have hs0 : Tendsto (fun k : ℕ => k + k0) atTop atTop := tendsto_add_atTop_nat k0
  set nn1 : ℕ → ℕ := fun k => nn (k + k0) with hnn1
  have hn1t : Tendsto nn1 atTop atTop := hnnt.comp hs0
  have hy1 : Tendsto (fun k => x (nn1 k + 1)) atTop (𝓝 xbar) := hy.comp hs0
  have hx1 : Tendsto (fun k => x (nn1 k)) atTop (𝓝 xbar) := hx0.comp hs0
  have hu1 : Tendsto (fun k => extrap x κ (nn1 k)) atTop (𝓝 xbar) := hu.comp hs0
  have hv1 : Tendsto (fun k => extrap x μ (nn1 k)) atTop (𝓝 xbar) := hv.comp hs0
  have hmem : ∀ k, (gs (nn1 k), τ (nn1 k)) ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) (K : ℝ) ×ˢ Set.Icc (0 : ℝ) (1 / δ) := by
    intro k
    refine ⟨?_, (hrun.step_pos _).le, hτle _⟩
    rw [mem_closedBall_zero_iff]
    exact hk0 (k + k0) (by omega)
  obtain ⟨p, -, φ, hφ, hlim⟩ :=
    ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N)) (K : ℝ)).prod
      isCompact_Icc).tendsto_subseq hmem
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  set mm : ℕ → ℕ := fun k => nn1 (φ k) with hmm
  have hmt : Tendsto mm atTop atTop := hn1t.comp hφt
  have hym : Tendsto (fun k => x (mm k + 1)) atTop (𝓝 xbar) := hy1.comp hφt
  have hxm : Tendsto (fun k => x (mm k)) atTop (𝓝 xbar) := hx1.comp hφt
  have hum : Tendsto (fun k => extrap x κ (mm k)) atTop (𝓝 xbar) := hu1.comp hφt
  have hvm : Tendsto (fun k => extrap x μ (mm k)) atTop (𝓝 xbar) := hv1.comp hφt
  have hgm : Tendsto (fun k => gs (mm k)) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hlim
  have htm : Tendsto (fun k => τ (mm k)) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hlim
  have hθm : Tendsto (fun k => ratio (objF fs fn) g (x (mm k))) atTop (𝓝 L) := hL.comp hmt
  -- τ* ≥ τbar
  have hτs : τbar ≤ p.2 := by
    by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ k in atTop, τbar - (τbar - p.2) / 2 ≤ τ (mm k) :=
      hmt.eventually (hτ ((τbar - p.2) / 2) (by linarith))
    have := ge_of_tendsto htm hev
    linarith
  have hτspos : 0 < p.2 := lt_of_lt_of_le hτbar hτs
  have hgbar : p.1 ∈ LimitingSubdiff (fun y => (g y : EReal)) xbar :=
    P6afa.limSub_closed hgcont hxm hgm (fun k => hrun.subgrad (mm k))
  refine ⟨p.1, hgbar, fun y hyS => ?_⟩
  by_cases hyf : objF fs fn y = ⊤
  · rw [hyf]; exact le_top
  obtain ⟨F0, -, hF0, hF⟩ := P3483.fn_real hA1 hxbf
  obtain ⟨Fy0, -, hFy0, hFy⟩ := P3483.fn_real hA1 hyf
  set f := objF fs fn with hf
  set gb := p.1 with hgb
  set τs := p.2 with hτsdef
  set θ := ratio f g xbar with hθdef
  rw [hF0, hFy0, ← EReal.coe_add, EReal.coe_le_coe_iff]
  -- real-valued sequences
  set a : ℕ → ℝ := fun k => (f (x (mm k + 1))).toReal with ha
  have ha_eq : ∀ k, a k = ratio f g (x (mm k + 1)) * g (x (mm k + 1)) := by
    intro k
    have hp : 0 < g (x (mm k + 1)) := hA2.pos _ (hxn _).1
    simp only [ha, ratio]
    field_simp
  have hmt1 : Tendsto (fun k => mm k + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hmt
  have hA : Tendsto a atTop (𝓝 (L * g xbar)) := by
    have := (hL.comp hmt1).mul (hgcont.tendsto.comp hym)
    refine this.congr (fun k => ?_)
    rw [ha_eq k]; rfl
  have hLF : L * g xbar = (f xbar).toReal := by
    rw [hLeq]
    show (f xbar).toReal / g xbar * g xbar = (f xbar).toReal
    exact div_mul_cancel₀ _ hgpos.ne'
  have hupk : ∀ k, a k ≤ (f y).toReal + ((fs (x (mm k + 1)) - fs y)
      + ⟪gradient fs (extrap x κ (mm k)), y - x (mm k + 1)⟫_ℝ
      + 1 / (2 * τ (mm k)) *
          (‖y - extrap x μ (mm k) - (τ (mm k) * ratio f g (x (mm k))) • gs (mm k)‖ ^ 2
            - ‖x (mm k + 1) - extrap x μ (mm k) - (τ (mm k) * ratio f g (x (mm k))) •
              gs (mm k)‖ ^ 2)
      + ℓ / 2 * (‖y - extrap x κ (mm k)‖ ^ 2 - ‖x (mm k + 1) - extrap x κ (mm k)‖ ^ 2)) := by
    intro k
    have := P3483.step_upper hA1 hrun (mm k) hyS hyf (hxn (mm k + 1)).2
    simp only [ha]
    linarith
  have hfsc : Continuous fs := hA1.fs_contDiff.continuous
  have hgfs : Continuous (fun z => gradient fs z) := by
    have h1 := hA1.fs_contDiff.continuous_fderiv one_ne_zero
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.continuous.comp h1
  have hE1 : Tendsto (fun k => fs (x (mm k + 1)) - fs y) atTop (𝓝 (fs xbar - fs y)) :=
    ((hfsc.tendsto xbar).comp hym).sub tendsto_const_nhds
  have hdy : Tendsto (fun k => y - x (mm k + 1)) atTop (𝓝 (y - xbar)) :=
    tendsto_const_nhds.sub hym
  have hE2 : Tendsto (fun k => ⟪gradient fs (extrap x κ (mm k)), y - x (mm k + 1)⟫_ℝ)
      atTop (𝓝 ⟪gradient fs xbar, y - xbar⟫_ℝ) :=
    Filter.Tendsto.inner (𝕜 := ℝ) ((hgfs.tendsto xbar).comp hum) hdy
  have hE4 : Tendsto (fun k => ℓ / 2 * (‖y - extrap x κ (mm k)‖ ^ 2
      - ‖x (mm k + 1) - extrap x κ (mm k)‖ ^ 2)) atTop
      (𝓝 (ℓ / 2 * (‖y - xbar‖ ^ 2 - ‖xbar - xbar‖ ^ 2))) := by
    have h1 : Tendsto (fun k => y - extrap x κ (mm k)) atTop (𝓝 (y - xbar)) :=
      tendsto_const_nhds.sub hum
    have h2 : Tendsto (fun k => x (mm k + 1) - extrap x κ (mm k)) atTop (𝓝 (xbar - xbar)) :=
      hym.sub hum
    exact ((h1.norm.pow 2).sub (h2.norm.pow 2)).const_mul (ℓ / 2)
  have hcvec : Tendsto (fun k => (τ (mm k) * ratio f g (x (mm k))) • gs (mm k)) atTop
      (𝓝 ((τs * L) • gb)) :=
    (htm.mul hθm).smul hgm
  have hE3 : Tendsto (fun k => 1 / (2 * τ (mm k)) *
          (‖y - extrap x μ (mm k) - (τ (mm k) * ratio f g (x (mm k))) • gs (mm k)‖ ^ 2
            - ‖x (mm k + 1) - extrap x μ (mm k) - (τ (mm k) * ratio f g (x (mm k))) •
              gs (mm k)‖ ^ 2)) atTop
      (𝓝 (1 / (2 * τs) * (‖y - xbar - (τs * L) • gb‖ ^ 2
          - ‖xbar - xbar - (τs * L) • gb‖ ^ 2))) := by
    have hinv : Tendsto (fun k => 1 / (2 * τ (mm k))) atTop (𝓝 (1 / (2 * τs))) :=
      tendsto_const_nhds.div (htm.const_mul 2) (by positivity)
    have h1 : Tendsto (fun k => y - extrap x μ (mm k) - (τ (mm k) * ratio f g (x (mm k))) •
        gs (mm k)) atTop (𝓝 (y - xbar - (τs * L) • gb)) :=
      (tendsto_const_nhds.sub hvm).sub hcvec
    have h2 : Tendsto (fun k => x (mm k + 1) - extrap x μ (mm k) -
        (τ (mm k) * ratio f g (x (mm k))) • gs (mm k)) atTop
        (𝓝 (xbar - xbar - (τs * L) • gb)) :=
      (hym.sub hvm).sub hcvec
    exact hinv.mul ((h1.norm.pow 2).sub (h2.norm.pow 2))
  have hEt := ((hE1.add hE2).add hE3).add hE4
  have hup := le_of_tendsto_of_tendsto hA (tendsto_const_nhds.add hEt)
    (Eventually.of_forall hupk)
  rw [hLF] at hup
  -- convexity of fs
  have hF1 : ∀ z, HasGradientAt fs (gradient fs z) z := fun z =>
    ((hA1.fs_contDiff.differentiable one_ne_zero) z).hasGradientAt
  have hcvx := P3483.convex_fo hF1 hA1.fs_convex xbar y
  -- simplify the limit
  have hsq : ‖y - xbar - (τs * L) • gb‖ ^ 2 - ‖xbar - xbar - (τs * L) • gb‖ ^ 2 =
      ‖y - xbar‖ ^ 2 - 2 * (τs * L) * ⟪y - xbar, gb⟫_ℝ := by
    rw [norm_sub_sq_real, inner_smul_right, sub_self, zero_sub, norm_neg, norm_smul]
    rw [mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hsq2 : 1 / (2 * τs) * (‖y - xbar - (τs * L) • gb‖ ^ 2 - ‖xbar - xbar - (τs * L) • gb‖ ^ 2)
      = 1 / (2 * τs) * ‖y - xbar‖ ^ 2 - L * ⟪y - xbar, gb⟫_ℝ := by
    rw [hsq]; field_simp
  rw [hsq2] at hup
  simp only [sub_self, norm_zero] at hup
  have hdecr : 1 / (2 * τs) * ‖y - xbar‖ ^ 2 ≤ 1 / (2 * τbar) * ‖y - xbar‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le (by positivity) (by linarith)) (by positivity)
  have hcomm : ⟪gb, xbar - y⟫_ℝ = -⟪y - xbar, gb⟫_ℝ := by
    rw [real_inner_comm, ← inner_neg_left]; congr 1; abel
  rw [← hLeq, hcomm]
  have hFyF : (f y).toReal = fs y + Fy0 := hFy
  have hFxF : (f xbar).toReal = fs xbar + F0 := hF
  nlinarith [hup, hcvx, hdecr]

