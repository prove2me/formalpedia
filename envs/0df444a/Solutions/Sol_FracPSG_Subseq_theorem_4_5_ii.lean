-- Prove2me | solution 1 for FracPSG.Subseq.theorem_4_5_ii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T07:33:48.064222+00:00
-- url     : https://prove2.me/submissions/3629fc83-82aa-4d15-a46d-6f2f593ec77c

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

open Filter Topology FracPSG.Subseq NonconvexSplitting.Shared in
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
    (hS0 : Bornology.IsBounded (S0 S (objF fs fn) g (x 0))) :
    Bornology.IsBounded (Set.range x) ∧
    Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0) ∧
    Summable (fun n => ‖x (n + 1) - x n‖ ^ 2) := by
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
  have hΦ0 : Φ 0 = θ 0 := by
    simp [hΦdef, xPrev]
  have hΦle : ∀ n, Φ n ≤ Φ 0 := fun n =>
    antitone_nat_of_succ_le (fun k => le_trans (le_add_of_nonneg_right
      (mul_nonneg hα.le (sq_nonneg _))) (hΦ k)) (Nat.zero_le n)
  refine ⟨?_, ?_, ?_⟩
  · refine hS0.subset ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨(hdom n).1, (hdom n).2, ?_⟩
    have h1 : θ n ≤ Φ n := le_add_of_nonneg_right (by positivity)
    have h2 := hΦle n
    rw [hΦ0] at h2
    exact le_trans h1 h2
  · have hsum : ∀ N', ∑ i ∈ Finset.range N', α * a i ^ 2 ≤ Φ 0 := by
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
    have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at h1
    exact h1.congr (fun n => Real.sqrt_sq (norm_nonneg _))
  · have hsum : ∀ N', ∑ i ∈ Finset.range N', α * a i ^ 2 ≤ Φ 0 := by
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
    refine summable_of_sum_range_le (c := Φ 0 / α) (fun n => sq_nonneg _) (fun N' => ?_)
    rw [le_div_iff₀ hα]
    have h := hsum N'
    rw [← Finset.mul_sum] at h
    linarith
