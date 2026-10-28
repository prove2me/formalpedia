-- Prove2me | solution 1 for FracPSG.Enhanced.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T05:58:12.332783+00:00
-- url     : https://prove2.me/submissions/eedd7d7b-7e5d-4ec7-9e49-26eb1a83f416

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_FracPSG_Enhanced_Basic
import Definitions.Def_FracPSG_Enhanced_Algorithm2

open Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

namespace P3ddd

open NonconvexSplitting.Shared FracPSG.Subseq FracPSG.Enhanced

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

theorem T_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (xn x1 e gn : E) (μ τ θ : ℝ) :
    ‖xn - (xn + μ • e) - (τ * θ) • gn‖ ^ 2 - ‖x1 - (xn + μ • e) - (τ * θ) • gn‖ ^ 2
      = -‖x1 - xn‖ ^ 2 + 2 * μ * ⟪x1 - xn, e⟫_ℝ + 2 * (τ * θ) * ⟪x1 - xn, gn⟫_ℝ := by
  have h1 : xn - (xn + μ • e) - (τ * θ) • gn = -(μ • e + (τ * θ) • gn) := by module
  have h2 : x1 - (xn + μ • e) - (τ * θ) • gn = (x1 - xn) - (μ • e + (τ * θ) • gn) := by module
  rw [h1, h2, norm_neg, norm_sub_sq_real, inner_add_right, inner_smul_right, inner_smul_right]
  ring

theorem amgm (a b l : ℝ) (hl : 0 < l) : 2 * (a * b) ≤ l * a ^ 2 + b ^ 2 / l := by
  rw [← sub_nonneg]
  have : l * a ^ 2 + b ^ 2 / l - 2 * (a * b) = (l * a - b) ^ 2 / l := by
    field_simp; ring
  rw [this]; positivity


theorem grad_ineq {N : ℕ} {D O : Set (EuclideanSpace ℝ (Fin N))}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {β : ℝ}
    (hwc : IsWeaklyConvexOn D g β) (hO : IsOpen O) (hDO : D ⊆ O) (hcd : ContDiffOn ℝ 1 g O)
    {z y : EuclideanSpace ℝ (Fin N)} (hz : z ∈ D) (hy : y ∈ D) :
    g z + ⟪gradient g z, y - z⟫_ℝ - β / 2 * ‖y - z‖ ^ 2 ≤ g y := by
  have hd : HasGradientAt g (gradient g z) z :=
    ((hcd.differentiableOn one_ne_zero z (hDO hz)).differentiableAt
      (hO.mem_nhds (hDO hz))).hasGradientAt
  apply reg_wc_ineq hwc hz hy
  refine ⟨EReal.coe_ne_top _, fun ε hε => ?_⟩
  have hf := hasGradientAt_iff_hasFDerivAt.mp hd
  have ho := hf.isLittleO
  filter_upwards [ho.def hε] with w hw
  rw [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs] at hw
  have h1 := (abs_le.mp hw).1
  have h2 : g z + (⟪gradient g z, w - z⟫_ℝ - ε * ‖w - z‖) ≤ g w := by
    have : -(ε * ‖w - z‖) ≤ g w - g z - ⟪gradient g z, w - z⟫_ℝ := by
      simpa [Real.norm_eq_abs] using h1
    linarith
  exact_mod_cast h2

theorem cand {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ ε μbar κbar m M : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {w : ℕ → Fin p → EuclideanSpace ℝ (Fin N)}
    {ihat : ℕ → Fin p} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2' S (objF fs fn) gi β m M)
    (hpar : Step1Params ℓ β δ ε ζ μbar κbar m M)
    (hrun : IsEnhancedRun S fs fn gi ℓ β δ ζ ε μbar κbar m M x w ihat τ κ μ) (n : ℕ)
    (hxS : x n ∈ S) (hxf : objF fs fn (x n) ≠ ⊤) (i : Fin p)
    (hi : gi i (x n) = maxFn gi (x n)) :
    i ∈ activeSet ε gi (x n) ∧ w n i ∈ S ∧ objF fs fn (w n i) ≠ ⊤ ∧
    (objF fs fn (w n i)).toReal - ratio (objF fs fn) (maxFn gi) (x n) * maxFn gi (w n i) ≤
      -((1 - Real.sqrt β * ζ) / (2 * τ n)) * ‖w n i - x n‖ ^ 2
      + μ n / τ n * ⟪w n i - x n, x n - xPrev x n⟫_ℝ
      + ℓ * κbar ^ 2 / 2 * ‖x n - xPrev x n‖ ^ 2 := by
  obtain ⟨hδ, hε, hζ, hη, -, -, -, -⟩ := hpar
  have hia : i ∈ activeSet ε gi (x n) := by
    unfold activeSet; rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hi]; linarith⟩
  have hwS := hrun.cand_mem n i hia
  have h := hrun.cand_argmin n i hia (x n) hxS
  obtain ⟨r0, hr0, -, hF0r⟩ := fn_real hA1 hxf
  have hwf : objF fs fn (w n i) ≠ ⊤ := by
    intro hcon
    have hfn : fn (w n i) = ⊤ := by
      by_contra hne
      have hbot := hA1.fn_proper.1 (w n i)
      obtain ⟨r', hr'⟩ : ∃ r' : ℝ, fn (w n i) = r' := ⟨_, (EReal.coe_toReal hne hbot).symm⟩
      unfold objF at hcon; rw [hr', ← EReal.coe_add] at hcon; exact EReal.coe_ne_top _ hcon
    unfold subObj at h
    rw [hfn, hr0, EReal.top_add_coe, ← EReal.coe_add] at h
    exact EReal.coe_ne_top _ (top_le_iff.mp h)
  obtain ⟨r1, hr1, -, hF1r⟩ := fn_real hA1 hwf
  refine ⟨hia, hwS, hwf, ?_⟩
  unfold subObj at h
  rw [hr1, hr0, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  set θ := ratio (objF fs fn) (maxFn gi) (x n) with hθ
  set G := gradient (gi i) (x n) with hG
  have hβ0 : 0 ≤ β := (hA2.weakly_convex i).1
  have hτ := hrun.step_pos n
  obtain ⟨hμ0, hμ1⟩ := hrun.mu_mem n
  obtain ⟨hκ0, hκ1⟩ := hrun.kappa_mem n
  have hg0 : 0 < maxFn gi (x n) := hA2.g_pos _ hxS
  have hFnn : 0 ≤ (objF fs fn (x n)).toReal := EReal.toReal_nonneg (hA1.nonneg _ hxS hxf)
  have hθ0 : 0 ≤ θ := div_nonneg hFnn hg0.le
  have hFθ : (objF fs fn (x n)).toReal = θ * maxFn gi (x n) := by
    rw [hθ]; unfold ratio; field_simp
  have hF : ∀ y, HasGradientAt fs (gradient fs y) y := fun y =>
    ((hA1.fs_contDiff.differentiable one_ne_zero) y).hasGradientAt
  have hdesc := descent hF hA1.grad_lipschitz (extrap x κ n) (w n i)
  have hcvx := convex_fo hF hA1.fs_convex (extrap x κ n) (x n)
  have hT := T_identity (x n) (w n i) (x n - xPrev x n) G (μ n) (τ n) θ
  have hextμ : extrap x μ n = x n + μ n • (x n - xPrev x n) := rfl
  have hxu : x n - (extrap x κ n) = -(κ n • (x n - xPrev x n)) := by
    show x n - (x n + κ n • (x n - xPrev x n)) = _; abel
  have hxu2 : ‖x n - (extrap x κ n)‖ ^ 2 = κ n ^ 2 * ‖(x n - xPrev x n)‖ ^ 2 := by
    rw [hxu, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hextμ] at h
  have hsplit : 1 / (2 * τ n) * ‖x n - (x n + μ n • (x n - xPrev x n)) - (τ n * θ) • G‖ ^ 2
      - 1 / (2 * τ n) * ‖w n i - (x n + μ n • (x n - xPrev x n)) - (τ n * θ) • G‖ ^ 2
      = -(1 / (2 * τ n) * ‖w n i - x n‖ ^ 2) + μ n / τ n * ⟪w n i - x n, x n - xPrev x n⟫_ℝ
        + θ * ⟪w n i - x n, G⟫_ℝ := by
    rw [← mul_sub, hT]; field_simp
  obtain ⟨O, hO, hSO, hcd⟩ := hA2.contDiff i
  have hwc := grad_ineq (hA2.weakly_convex i) hO hSO hcd hxS hwS
  have hmax : gi i (w n i) ≤ maxFn gi (w n i) := by
    show gi i (w n i) ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => gi j (w n i))
    exact Finset.le_sup' (fun j => gi j (w n i)) (Finset.mem_univ i)
  have hgD : θ * (maxFn gi (x n) + ⟪G, w n i - x n⟫_ℝ - β / 2 * ‖w n i - x n‖ ^ 2)
      ≤ θ * maxFn gi (w n i) := mul_le_mul_of_nonneg_left (by rw [← hi]; linarith) hθ0
  have hMx : 0 < max (Real.sqrt β * θ / ζ) δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hstep := hrun.step_le n
  have hmaxle : max (Real.sqrt β * θ / ζ) δ ≤ 1 / τ n := by
    rw [le_div_iff₀ hτ]
    have := (le_div_iff₀ hMx).mp hstep
    linarith
  have hu1 : Real.sqrt β * θ ≤ (1 / τ n) * ζ := by
    have := le_trans (le_max_left _ _) hmaxle
    rwa [div_le_iff₀ hζ] at this
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0
  have hA : β * θ / 2 - 1 / (2 * τ n) ≤ -((1 - Real.sqrt β * ζ) / (2 * τ n)) := by
    have h1 : β * θ ≤ Real.sqrt β * ((1 / τ n) * ζ) := by
      calc β * θ = Real.sqrt β * (Real.sqrt β * θ) := by rw [← mul_assoc, hsq]
        _ ≤ Real.sqrt β * ((1 / τ n) * ζ) :=
          mul_le_mul_of_nonneg_left hu1 (Real.sqrt_nonneg _)
    have h2 : 1 / (2 * τ n) = (1 / τ n) / 2 := by field_simp
    have h3 : -((1 - Real.sqrt β * ζ) / (2 * τ n))
        = -((1 / τ n) / 2) + Real.sqrt β * ((1 / τ n) * ζ) / 2 := by field_simp; ring
    rw [h2, h3]
    linarith
  have hAa := mul_le_mul_of_nonneg_left hA (sq_nonneg ‖w n i - x n‖)
  have hgs : ⟪w n i - x n, G⟫_ℝ = ⟪G, w n i - x n⟫_ℝ := real_inner_comm _ _
  have hℓ : 0 ≤ ℓ := hA1.ell_nonneg
  have hC : ℓ / 2 * (κ n ^ 2 * ‖(x n - xPrev x n)‖ ^ 2) ≤ ℓ * κbar ^ 2 / 2 * ‖(x n - xPrev x n)‖ ^ 2 := by
    have h0 : κ n ^ 2 ≤ κbar ^ 2 := pow_le_pow_left₀ hκ0 hκ1 2
    have h' : ℓ / 2 * κ n ^ 2 ≤ ℓ / 2 * κbar ^ 2 := mul_le_mul_of_nonneg_left h0 (by positivity)
    calc ℓ / 2 * (κ n ^ 2 * ‖(x n - xPrev x n)‖ ^ 2) = (ℓ / 2 * κ n ^ 2) * ‖(x n - xPrev x n)‖ ^ 2 := by ring
      _ ≤ (ℓ / 2 * κbar ^ 2) * ‖(x n - xPrev x n)‖ ^ 2 := mul_le_mul_of_nonneg_right h' (sq_nonneg _)
      _ = ℓ * κbar ^ 2 / 2 * ‖(x n - xPrev x n)‖ ^ 2 := by ring
  rw [hxu2] at h
  rw [hF1r]
  rw [hF0r] at hFθ
  have s1 : fs (w n i) + r1 ≤ r0 + fs (x n)
      + (1 / (2 * τ n) * ‖x n - (x n + μ n • (x n - xPrev x n)) - (τ n * θ) • G‖ ^ 2
        - 1 / (2 * τ n) * ‖w n i - (x n + μ n • (x n - xPrev x n)) - (τ n * θ) • G‖ ^ 2)
      + ℓ / 2 * (κ n ^ 2 * ‖x n - xPrev x n‖ ^ 2) := by linarith
  rw [hsplit] at s1
  have s3 : θ * maxFn gi (x n) + θ * ⟪G, w n i - x n⟫_ℝ - θ * (β / 2 * ‖w n i - x n‖ ^ 2)
      ≤ θ * maxFn gi (w n i) := by
    have := hgD; rw [mul_sub, mul_add] at this; exact this
  have s4 : θ * (β / 2 * ‖w n i - x n‖ ^ 2) - 1 / (2 * τ n) * ‖w n i - x n‖ ^ 2
      ≤ -((1 - Real.sqrt β * ζ) / (2 * τ n)) * ‖w n i - x n‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hA (sq_nonneg ‖w n i - x n‖)
    have e : (β * θ / 2 - 1 / (2 * τ n)) * ‖w n i - x n‖ ^ 2
        = θ * (β / 2 * ‖w n i - x n‖ ^ 2) - 1 / (2 * τ n) * ‖w n i - x n‖ ^ 2 := by ring
    rw [e] at this; exact this
  rw [hgs] at s1
  linarith

/-- The constant `c` of the Lyapunov inequality: `(μ̄√(mM)/(2M) + ℓκ̄²/2)/m`. -/
noncomputable def cc (ℓ μbar κbar m M : ℝ) : ℝ :=
  (μbar * Real.sqrt (m * M) / (2 * M) + ℓ * κbar ^ 2 / 2) / m

noncomputable def KK (β δ ζ μbar m M : ℝ) : ℝ :=
  (1 - Real.sqrt β * ζ) * δ - M / Real.sqrt (m * M) * μbar

noncomputable def αc (ℓ β δ ζ μbar κbar m M : ℝ) : ℝ :=
  KK β δ ζ μbar m M / (2 * M) - cc ℓ μbar κbar m M

theorem alpha_pos {ℓ β δ ε ζ μbar κbar m M : ℝ} (hpar : Step1Params ℓ β δ ε ζ μbar κbar m M)
    (hm : 0 < m) (hM : 0 < M) : 0 < αc ℓ β δ ζ μbar κbar m M := by
  obtain ⟨hδ, hε, hζ, hη, hμb0, hμb1, hκb0, hκb1⟩ := hpar
  have hs : 0 < Real.sqrt (m * M) := Real.sqrt_pos.mpr (by positivity)
  have hss : Real.sqrt (m * M) * Real.sqrt (m * M) = m * M := Real.mul_self_sqrt (by positivity)
  set s := Real.sqrt (m * M) with hsdef
  set η := 1 - Real.sqrt β * ζ with hηdef
  have e1 : 2 * m * μbar / s = 2 * μbar * s / M := by
    rw [div_eq_div_iff hs.ne' hM.ne']; linear_combination (-(2 * μbar)) * hss
  rw [e1] at hκb1
  have e2 : m * δ * η / M - 2 * μbar * s / M = (m * δ * η - 2 * μbar * s) / M := by ring
  rw [e2, lt_div_iff₀ hM] at hκb1
  have key : αc ℓ β δ ζ μbar κbar m M
      = (m * η * δ - 2 * μbar * s - M * (ℓ * κbar ^ 2)) / (2 * M * m) := by
    have hMs : M / s = s / m := by
      rw [div_eq_div_iff hs.ne' hm.ne']; linear_combination -hss
    unfold αc KK cc
    rw [← hsdef, ← hηdef, hMs]
    field_simp
    ring
  rw [key]
  apply div_pos _ (by positivity)
  nlinarith

theorem step {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ ε μbar κbar m M : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {w : ℕ → Fin p → EuclideanSpace ℝ (Fin N)}
    {ihat : ℕ → Fin p} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2' S (objF fs fn) gi β m M)
    (hpar : Step1Params ℓ β δ ε ζ μbar κbar m M)
    (hrun : IsEnhancedRun S fs fn gi ℓ β δ ζ ε μbar κbar m M x w ihat τ κ μ) (n : ℕ)
    (hxS : x n ∈ S) (hxf : objF fs fn (x n) ≠ ⊤) :
    x (n + 1) ∈ S ∧ objF fs fn (x (n + 1)) ≠ ⊤ ∧
    ratio (objF fs fn) (maxFn gi) (x (n + 1)) + cc ℓ μbar κbar m M * ‖x (n + 1) - x n‖ ^ 2 ≤
      ratio (objF fs fn) (maxFn gi) (x n) + cc ℓ μbar κbar m M * ‖x n - xPrev x n‖ ^ 2
        - αc ℓ β δ ζ μbar κbar m M * ‖x (n + 1) - x n‖ ^ 2 := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => gi i (x n))
  have hi : gi i0 (x n) = maxFn gi (x n) := hi0.symm
  obtain ⟨hia, hwS, hwf, hc⟩ := cand hA1 hA2 hpar hrun n hxS hxf i0 hi
  obtain ⟨hδ, hε, hζ, hη, hμb0, hμb1, hκb0, hκb1⟩ := hpar
  obtain ⟨hm, hM, hbc⟩ := hA2.bc
  have hsel := hrun.ihat_argmin n i0 hia
  rw [← hrun.next_eq n] at hsel
  have hx1S : x (n + 1) ∈ S := by
    rw [hrun.next_eq n]; exact hrun.cand_mem n _ (hrun.ihat_mem n)
  obtain ⟨r1, -, hFw, hFwr⟩ := fn_real hA1 hwf
  unfold selObj at hsel
  rw [hFw, ← EReal.coe_add] at hsel
  have hx1f : objF fs fn (x (n + 1)) ≠ ⊤ := by
    intro hcon; rw [hcon, EReal.top_add_coe] at hsel
    exact EReal.coe_ne_top _ (top_le_iff.mp hsel)
  obtain ⟨r2, -, hF1, hF1r⟩ := fn_real hA1 hx1f
  rw [hF1, ← EReal.coe_add, EReal.coe_le_coe_iff] at hsel
  refine ⟨hx1S, hx1f, ?_⟩
  have hF1θ : (objF fs fn (x (n + 1))).toReal
      = ratio (objF fs fn) (maxFn gi) (x (n + 1)) * maxFn gi (x (n + 1)) := by
    have hg1pos : 0 < maxFn gi (x (n + 1)) := hA2.g_pos _ hx1S
    unfold ratio; field_simp
  have hτ := hrun.step_pos n
  obtain ⟨hμ0, hμ1⟩ := hrun.mu_mem n
  have hs : 0 < Real.sqrt (m * M) := Real.sqrt_pos.mpr (by positivity)
  set s := Real.sqrt (m * M) with hsdef
  set η := 1 - Real.sqrt β * ζ with hηdef
  set θ := ratio (objF fs fn) (maxFn gi) (x n) with hθ
  set θ1 := ratio (objF fs fn) (maxFn gi) (x (n + 1)) with hθ1
  set g1 := maxFn gi (x (n + 1)) with hg1
  set gw := maxFn gi (w n i0) with hgw
  set a := ‖x (n + 1) - x n‖ with ha
  set aw := ‖w n i0 - x n‖ with haw
  set b := ‖x n - xPrev x n‖ with hb
  obtain ⟨u, hu⟩ : ∃ u, u = 1 / τ n := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν, ν = μ n / τ n := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = M / s := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have id1 : η / (2 * τ n) = η * u / 2 := by rw [hu]; ring
  have id2 : 1 / 2 * (η / τ n - M * μ n / (s * τ n)) = η * u / 2 - lam * ν / 2 := by
    rw [hu, hν, hlam]; ring
  rw [id1, ← hν] at hc
  rw [id2] at hsel
  -- bounds on u and ν
  have hMx : 0 < max (Real.sqrt β * θ / ζ) δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hstep := hrun.step_le n
  have hmaxle : max (Real.sqrt β * θ / ζ) δ ≤ 1 / τ n := by
    rw [le_div_iff₀ hτ]
    have := (le_div_iff₀ hMx).mp hstep
    linarith
  have hu2 : δ ≤ u := by rw [hu]; exact le_trans (le_max_right _ _) hmaxle
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hν1 : ν ≤ μbar := by rw [hν, div_le_iff₀ hτ]; linarith
  -- inner product / AM-GM
  have e1 : ⟪w n i0 - x n, x n - xPrev x n⟫_ℝ ≤ aw * b := real_inner_le_norm _ _
  have e2 : ν * ⟪w n i0 - x n, x n - xPrev x n⟫_ℝ ≤ ν * (aw * b) :=
    mul_le_mul_of_nonneg_left e1 hν0
  have e6 : b ^ 2 / lam = s / M * b ^ 2 := by rw [hlam]; field_simp
  have e3 : 2 * (aw * b) ≤ lam * aw ^ 2 + s / M * b ^ 2 := by
    rw [← e6]; exact amgm aw b lam hlam0
  have e4 : ν * (2 * (aw * b)) ≤ ν * (lam * aw ^ 2 + s / M * b ^ 2) :=
    mul_le_mul_of_nonneg_left e3 hν0
  have e5 : ν * (s / M * b ^ 2) ≤ μbar * (s / M * b ^ 2) :=
    mul_le_mul_of_nonneg_right hν1 (by positivity)
  have e7a : η * δ ≤ η * u := mul_le_mul_of_nonneg_left hu2 hη.le
  have e7b : lam * ν ≤ lam * μbar := mul_le_mul_of_nonneg_left hν1 hlam0.le
  have hKK : KK β δ ζ μbar m M = η * δ - lam * μbar := by
    unfold KK; rw [← hsdef, ← hηdef, hlam]; try ring
  have e8 : KK β δ ζ μbar m M / 2 * a ^ 2 ≤ (η * u / 2 - lam * ν / 2) * a ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [hKK]; linarith
  -- combined real inequality
  have hcomb : θ1 * g1 - θ * g1 ≤
      -(KK β δ ζ μbar m M / 2 * a ^ 2) + (μbar * (s / M) / 2 + ℓ * κbar ^ 2 / 2) * b ^ 2 := by
    rw [hF1r] at hF1θ
    rw [hFwr] at hc
    have q1 : (η * u / 2 - lam * ν / 2) * aw ^ 2 = η * u / 2 * aw ^ 2 - lam * ν / 2 * aw ^ 2 := by ring
    have q2 : -(η * u / 2) * aw ^ 2 = -(η * u / 2 * aw ^ 2) := by ring
    have q3 : ν * (2 * (aw * b)) = 2 * (ν * (aw * b)) := by ring
    have q4 : ν * (lam * aw ^ 2 + s / M * b ^ 2) = 2 * (lam * ν / 2 * aw ^ 2) + ν * (s / M * b ^ 2) := by ring
    have q5 : μbar * (s / M * b ^ 2) = 2 * (μbar * (s / M) / 2 * b ^ 2) := by ring
    have q6 : (μbar * (s / M) / 2 + ℓ * κbar ^ 2 / 2) * b ^ 2
        = μbar * (s / M) / 2 * b ^ 2 + ℓ * κbar ^ 2 / 2 * b ^ 2 := by ring
    rw [q1] at hsel
    rw [q2] at hc
    rw [q3, q4] at e4
    rw [q5] at e5
    rw [q6]
    linarith
  -- divide by g1 ∈ [m, M]
  obtain ⟨hg1m, hg1M⟩ := hbc _ hx1S hx1f
  have hg1pos : 0 < g1 := lt_of_lt_of_le hm hg1m
  set X := -(KK β δ ζ μbar m M / 2 * a ^ 2) with hX
  set Y := (μbar * (s / M) / 2 + ℓ * κbar ^ 2 / 2) * b ^ 2 with hY
  have hKpos : 0 < KK β δ ζ μbar m M := by
    rw [hKK]
    have : lam * μbar < η * δ / 2 := by
      have h' : μbar * M < δ * η * s / 2 := by
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * M)] at hμb1; linarith
      rw [hlam, div_mul_eq_mul_div, div_lt_iff₀ hs]; linarith
    have := mul_pos hη hδ
    linarith
  have hX0 : X ≤ 0 := by
    rw [hX]
    have : 0 ≤ KK β δ ζ μbar m M / 2 * a ^ 2 :=
      mul_nonneg (div_nonneg hKpos.le zero_le_two) (sq_nonneg a)
    linarith
  have hY0 : 0 ≤ Y := by rw [hY]; have := hA1.ell_nonneg; positivity
  have hXd : X ≤ g1 * (X / M) := by
    have : g1 * (X / M) - X = X * (g1 - M) / M := by field_simp
    have : 0 ≤ X * (g1 - M) / M :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos hX0 (by linarith)) hM.le
    linarith
  have hYd : Y ≤ g1 * (Y / m) := by
    have : g1 * (Y / m) - Y = Y * (g1 - m) / m := by field_simp
    have : 0 ≤ Y * (g1 - m) / m := div_nonneg (mul_nonneg hY0 (by linarith)) hm.le
    linarith
  have hdiv : θ1 - θ ≤ X / M + Y / m := by
    have : g1 * (θ1 - θ) ≤ g1 * (X / M + Y / m) := by
      have e : g1 * (θ1 - θ) = θ1 * g1 - θ * g1 := by ring
      have e' : g1 * (X / M + Y / m) = g1 * (X / M) + g1 * (Y / m) := by ring
      rw [e, e']; linarith
    exact le_of_mul_le_mul_left this hg1pos
  have hXM : X / M = -(KK β δ ζ μbar m M / (2 * M)) * a ^ 2 := by rw [hX]; field_simp
  have hYm : Y / m = cc ℓ μbar κbar m M * b ^ 2 := by
    rw [hY]; unfold cc; rw [← hsdef]; field_simp
  unfold αc
  rw [hXM, hYm] at hdiv
  have q7 : (KK β δ ζ μbar m M / (2 * M) - cc ℓ μbar κbar m M) * a ^ 2
      = KK β δ ζ μbar m M / (2 * M) * a ^ 2 - cc ℓ μbar κbar m M * a ^ 2 := by ring
  have q8 : -(KK β δ ζ μbar m M / (2 * M)) * a ^ 2 = -(KK β δ ζ μbar m M / (2 * M) * a ^ 2) := by ring
  rw [q7]; rw [q8] at hdiv
  linarith

end P3ddd

namespace P2e99

open NonconvexSplitting.Shared FracPSG.Enhanced

theorem fn_real {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))} {fs : EuclideanSpace ℝ (Fin N) → ℝ}
    {fn : EuclideanSpace ℝ (Fin N) → EReal} {ℓ : ℝ} (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ)
    {y : EuclideanSpace ℝ (Fin N)} (hy : FracPSG.Subseq.objF fs fn y ≠ ⊤) :
    ∃ r : ℝ, fn y = r ∧ FracPSG.Subseq.objF fs fn y = ((fs y + r : ℝ) : EReal) ∧
      (FracPSG.Subseq.objF fs fn y).toReal = fs y + r := by
  have h1 : fn y ≠ ⊥ := hA1.fn_proper.1 y
  have h2 : fn y ≠ ⊤ := by
    intro h; apply hy; simp [FracPSG.Subseq.objF, h]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, fn y = r := ⟨_, (EReal.coe_toReal h2 h1).symm⟩
  have h3 : FracPSG.Subseq.objF fs fn y = ((fs y + r : ℝ) : EReal) := by
    unfold FracPSG.Subseq.objF; rw [hr, EReal.coe_add]
  exact ⟨r, hr, h3, by rw [h3, EReal.toReal_coe]⟩

/-- The Step-2 optimality of `x (n+1)` tested against `y = xbar`, in real form. -/
theorem step_upper {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ ε μbar κbar m M : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {w : ℕ → Fin p → EuclideanSpace ℝ (Fin N)}
    {ihat : ℕ → Fin p} {τ κ μ : ℕ → ℝ}
    (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ)
    (hrun : IsEnhancedRun S fs fn gi ℓ β δ ζ ε μbar κbar m M x w ihat τ κ μ) (n : ℕ)
    {xbar : EuclideanSpace ℝ (Fin N)} (hxbS : xbar ∈ S)
    (hxbf : FracPSG.Subseq.objF fs fn xbar ≠ ⊤)
    (hyf : FracPSG.Subseq.objF fs fn (x (n + 1)) ≠ ⊤) :
    (FracPSG.Subseq.objF fs fn (x (n + 1))).toReal ≤ (FracPSG.Subseq.objF fs fn xbar).toReal
      + (fs (x (n + 1)) - fs xbar)
      + ⟪gradient fs (FracPSG.Subseq.extrap x κ n), xbar - x (n + 1)⟫_ℝ
      + 1 / (2 * τ n) *
          (‖xbar - FracPSG.Subseq.extrap x μ n - (τ n * FracPSG.Subseq.ratio
              (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n)) • gradient (gi (ihat n)) (x n)‖ ^ 2
            - ‖x (n + 1) - FracPSG.Subseq.extrap x μ n - (τ n * FracPSG.Subseq.ratio
              (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n)) • gradient (gi (ihat n)) (x n)‖ ^ 2)
      + ℓ / 2 * (‖xbar - FracPSG.Subseq.extrap x κ n‖ ^ 2
          - ‖x (n + 1) - FracPSG.Subseq.extrap x κ n‖ ^ 2) := by
  have h := hrun.cand_argmin n (ihat n) (hrun.ihat_mem n) xbar hxbS
  rw [← hrun.next_eq n] at h
  obtain ⟨r1, hr1, -, ha⟩ := fn_real hA1 hyf
  obtain ⟨r2, hr2, -, hb⟩ := fn_real hA1 hxbf
  unfold FracPSG.Subseq.subObj at h
  rw [hr1, hr2, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [ha, hb]
  have e : ⟪gradient fs (FracPSG.Subseq.extrap x κ n), xbar - x (n + 1)⟫_ℝ =
      ⟪gradient fs (FracPSG.Subseq.extrap x κ n), xbar - FracPSG.Subseq.extrap x κ n⟫_ℝ -
      ⟪gradient fs (FracPSG.Subseq.extrap x κ n), x (n + 1) - FracPSG.Subseq.extrap x κ n⟫_ℝ := by
    rw [← inner_sub_right]; congr 1; abel
  rw [e]
  have e2 : ∀ (a b : ℝ), 1 / (2 * τ n) * (a - b) = 1 / (2 * τ n) * a - 1 / (2 * τ n) * b := by
    intro a b; ring
  rw [e2]
  linarith

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

theorem gradient_continuousAt {N : ℕ} {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    {O : Set (EuclideanSpace ℝ (Fin N))} (hO : IsOpen O) (hC : ContDiffOn ℝ 1 φ O)
    {z : EuclideanSpace ℝ (Fin N)} (hz : z ∈ O) :
    ContinuousAt (fun y => gradient φ y) z := by
  have h1 := (hC.continuousOn_fderiv_of_isOpen hO le_rfl).continuousAt (hO.mem_nhds hz)
  have h2 : Continuous (fun L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ =>
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm L) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.continuous
  exact h2.continuousAt.comp h1

theorem common_open {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {f : EuclideanSpace ℝ (Fin N) → EReal} {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ}
    {β m M : ℝ} (hA2 : Assumption2' S f gi β m M) :
    ∃ O : Set (EuclideanSpace ℝ (Fin N)), IsOpen O ∧ S ⊆ O ∧ ∀ i, ContDiffOn ℝ 1 (gi i) O := by
  choose O hO hSO hC using hA2.contDiff
  exact ⟨⋂ i, O i, isOpen_iInter_of_finite hO, Set.subset_iInter hSO,
    fun i => (hC i).mono (Set.iInter_subset _ i)⟩

/-- Part (3): the limit of the ratios equals the ratio at any cluster point. -/
theorem ratio_limit_eq {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ ε μbar κbar m M : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {w : ℕ → Fin p → EuclideanSpace ℝ (Fin N)}
    {ihat : ℕ → Fin p} {τ κ μ : ℕ → ℝ}
    (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ)
    (hA2 : Assumption2' S (FracPSG.Subseq.objF fs fn) gi β m M)
    (hpar : Step1Params ℓ β δ ε ζ μbar κbar m M)
    (hrun : IsEnhancedRun S fs fn gi ℓ β δ ζ ε μbar κbar m M x w ihat τ κ μ)
    (hτ : 0 < Filter.liminf τ atTop)
    (hxn : ∀ n, x n ∈ S ∧ FracPSG.Subseq.objF fs fn (x n) ≠ ⊤)
    {L : ℝ} (hL : Tendsto (fun n => FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n))
      atTop (𝓝 L))
    (hstep : Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0))
    {xbar : EuclideanSpace ℝ (Fin N)} (hcl : MapClusterPt xbar atTop x) (hxbS : xbar ∈ S)
    (hxbf : FracPSG.Subseq.objF fs fn xbar ≠ ⊤)
    (hlsc : LowerSemicontinuous (FracPSG.Subseq.objF fs fn)) :
    L = FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) xbar := by
  set f := FracPSG.Subseq.objF fs fn with hf
  set g := maxFn gi with hg
  have hδ : 0 < δ := hpar.1
  obtain ⟨O, hO, hSO, hCO⟩ := common_open hA2
  have hxbO : xbar ∈ O := hSO hxbS
  have hdiff : ∀ i, DifferentiableAt ℝ (gi i) xbar := fun i =>
    ((hCO i).differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hxbO)
  have hgcont : ContinuousAt g xbar := by
    have := ContinuousAt.finset_sup'_apply (s := Finset.univ) (f := gi) (x := xbar)
      Finset.univ_nonempty (fun i _ => (hdiff i).continuousAt)
    exact this
  have hgradc : ∀ i, ContinuousAt (fun z => gradient (gi i) z) xbar := fun i =>
    gradient_continuousAt hO (hCO i) hxbO
  have hgpos : 0 < g xbar := hA2.g_pos xbar hxbS
  have hτle : ∀ n, τ n ≤ 1 / δ := fun n =>
    (hrun.step_le n).trans (one_div_le_one_div_of_le hδ (le_max_right _ _))
  -- subsequence
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
  have hprevd : Tendsto (fun n => x n - FracPSG.Subseq.xPrev x n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 := hstep.comp (tendsto_sub_atTop_nat 1)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp, FracPSG.Subseq.xPrev, if_neg (by omega : n ≠ 0),
      Nat.sub_add_cancel hn]
  have hprevk := hprevd.comp hnnt
  have hu : Tendsto (fun k => FracPSG.Subseq.extrap x κ (nn k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => κ (nn k) • (x (nn k) - FracPSG.Subseq.xPrev x (nn k))) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k => κbar * ‖x (nn k) - FracPSG.Subseq.xPrev x (nn k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.kappa_mem (nn k)).1]
        exact mul_le_mul_of_nonneg_right (hrun.kappa_mem (nn k)).2 (norm_nonneg _)
      · simpa using (hprevk.norm).const_mul κbar
    have := hx0.add hz
    simpa [FracPSG.Subseq.extrap] using this
  have hv : Tendsto (fun k => FracPSG.Subseq.extrap x μ (nn k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => μ (nn k) • (x (nn k) - FracPSG.Subseq.xPrev x (nn k))) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm
        (a := fun k => (μbar * (1 / δ)) * ‖x (nn k) - FracPSG.Subseq.xPrev x (nn k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.mu_mem (nn k)).1]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (hrun.mu_mem (nn k)).2.trans
          (mul_le_mul_of_nonneg_left (hτle _) hpar.2.2.2.2.1)
      · simpa using (hprevk.norm).const_mul (μbar * (1 / δ))
    have := hx0.add hz
    simpa [FracPSG.Subseq.extrap] using this
  -- a_k
  set a : ℕ → ℝ := fun k => (f (x (nn k + 1))).toReal with ha
  have ha_eq : ∀ k, a k = FracPSG.Subseq.ratio f g (x (nn k + 1)) * g (x (nn k + 1)) := by
    intro k
    have hp : 0 < g (x (nn k + 1)) := hA2.g_pos _ (hxn _).1
    simp only [ha, FracPSG.Subseq.ratio]
    field_simp
  have hA : Tendsto a atTop (𝓝 (L * g xbar)) := by
    have := (hL.comp hnnt1).mul (hgcont.tendsto.comp hy)
    refine this.congr (fun k => ?_)
    rw [ha_eq k]; rfl
  obtain ⟨F0, -, hF0, hF⟩ := fn_real hA1 hxbf
  set F := (f xbar).toReal with hFdef
  -- lower bound by lower semicontinuity
  have hlow : F ≤ L * g xbar := by
    have hfin : ∀ k, f (x (nn k + 1)) = ((a k : ℝ) : EReal) := by
      intro k
      obtain ⟨r, -, h1, h2⟩ := fn_real hA1 (hxn (nn k + 1)).2
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
      + ⟪gradient fs (FracPSG.Subseq.extrap x κ (nn k)), xbar - x (nn k + 1)⟫_ℝ
      + 1 / (2 * τ (nn k)) *
          (‖xbar - FracPSG.Subseq.extrap x μ (nn k) - (τ (nn k) * FracPSG.Subseq.ratio f g
              (x (nn k))) • gradient (gi (ihat (nn k))) (x (nn k))‖ ^ 2
            - ‖x (nn k + 1) - FracPSG.Subseq.extrap x μ (nn k) - (τ (nn k) * FracPSG.Subseq.ratio
              f g (x (nn k))) • gradient (gi (ihat (nn k))) (x (nn k))‖ ^ 2)
      + ℓ / 2 * (‖xbar - FracPSG.Subseq.extrap x κ (nn k)‖ ^ 2
          - ‖x (nn k + 1) - FracPSG.Subseq.extrap x κ (nn k)‖ ^ 2) with hE
  have hupk : ∀ k, a k ≤ F + E k := by
    intro k
    have := step_upper hA1 hrun (nn k) hxbS hxbf (hxn (nn k + 1)).2
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
  have hE2 : Tendsto (fun k => ⟪gradient fs (FracPSG.Subseq.extrap x κ (nn k)),
      xbar - x (nn k + 1)⟫_ℝ) atTop (𝓝 0) := by
    have := Filter.Tendsto.inner (𝕜 := ℝ) ((hgfs.tendsto xbar).comp hu) hdy
    simpa using this
  have hE4 : Tendsto (fun k => ℓ / 2 * (‖xbar - FracPSG.Subseq.extrap x κ (nn k)‖ ^ 2
          - ‖x (nn k + 1) - FracPSG.Subseq.extrap x κ (nn k)‖ ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => xbar - FracPSG.Subseq.extrap x κ (nn k)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := xbar)).sub hu; simpa using this
    have h2 : Tendsto (fun k => x (nn k + 1) - FracPSG.Subseq.extrap x κ (nn k)) atTop (𝓝 0) := by
      have := hy.sub hu; simpa using this
    have := ((h1.norm.pow 2).sub (h2.norm.pow 2)).const_mul (ℓ / 2)
    simpa using this
  -- the quadratic term, by a squeeze
  set T0 := Filter.liminf τ atTop / 2 with hT0
  have hT0pos : 0 < T0 := by rw [hT0]; linarith
  set Θ := |L| + 1
  set Γ := ∑ i, (‖gradient (gi i) xbar‖ + 1)
  have ev1 : ∀ᶠ k in atTop, T0 ≤ τ (nn k) := by
    have h := Filter.eventually_lt_of_lt_liminf (f := atTop) (u := τ) (b := T0)
      (by rw [hT0]; linarith) (isBoundedUnder_of ⟨0, fun n => (hrun.step_pos n).le⟩)
    exact (hnnt.eventually h).mono fun k hk => hk.le
  have ev2 : ∀ᶠ k in atTop, |FracPSG.Subseq.ratio f g (x (nn k))| ≤ Θ := by
    have := (hL.comp hnnt).eventually (Metric.ball_mem_nhds L one_pos)
    filter_upwards [this] with k hk
    have hk' : |FracPSG.Subseq.ratio f g (x (nn k)) - L| < 1 := by
      simpa [Real.dist_eq] using hk
    have := abs_sub_abs_le_abs_sub (FracPSG.Subseq.ratio f g (x (nn k))) L
    linarith
  have ev3 : ∀ᶠ k in atTop, ∀ i, ‖gradient (gi i) (x (nn k))‖ ≤ ‖gradient (gi i) xbar‖ + 1 := by
    refine eventually_all.2 fun i => ?_
    have := (((hgradc i).tendsto.comp hx0).norm).eventually
      (gt_mem_nhds (lt_add_one ‖gradient (gi i) xbar‖))
    exact this.mono fun k hk => hk.le
  have ev4 : ∀ᶠ k in atTop, ‖xbar - FracPSG.Subseq.extrap x μ (nn k)‖ ≤ 1 := by
    have h1 : Tendsto (fun k => ‖xbar - FracPSG.Subseq.extrap x μ (nn k)‖) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := xbar)).sub hv).norm; simpa using this
    exact (h1.eventually (gt_mem_nhds one_pos)).mono fun k hk => hk.le
  have ev5 : ∀ᶠ k in atTop, ‖x (nn k + 1) - FracPSG.Subseq.extrap x μ (nn k)‖ ≤ 1 := by
    have h1 : Tendsto (fun k => ‖x (nn k + 1) - FracPSG.Subseq.extrap x μ (nn k)‖) atTop
        (𝓝 0) := by
      have := (hy.sub hv).norm; simpa using this
    exact (h1.eventually (gt_mem_nhds one_pos)).mono fun k hk => hk.le
  have hE3 : Tendsto (fun k => 1 / (2 * τ (nn k)) *
          (‖xbar - FracPSG.Subseq.extrap x μ (nn k) - (τ (nn k) * FracPSG.Subseq.ratio f g
              (x (nn k))) • gradient (gi (ihat (nn k))) (x (nn k))‖ ^ 2
            - ‖x (nn k + 1) - FracPSG.Subseq.extrap x μ (nn k) - (τ (nn k) * FracPSG.Subseq.ratio
              f g (x (nn k))) • gradient (gi (ihat (nn k))) (x (nn k))‖ ^ 2)) atTop (𝓝 0) := by
    have hb : Tendsto (fun k => 1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)) *
        ‖xbar - x (nn k + 1)‖) atTop (𝓝 0) := by
      have := (hdy.norm).const_mul (1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)))
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [ev1, ev2, ev3, ev4, ev5] with k h1 h2 h3 h4 h5
    rw [Real.norm_eq_abs]
    refine T2_bound _ _ _ _ _ _ T0 δ Θ Γ hT0pos h1 (hτle _) hδ h2 ?_ h4 h5
    exact (h3 _).trans (Finset.single_le_sum (f := fun i => ‖gradient (gi i) xbar‖ + 1)
      (fun i _ => by positivity) (Finset.mem_univ _))
  have hEt : Tendsto E atTop (𝓝 0) := by
    have := ((hE1.add hE2).add hE3).add hE4
    simpa [hE] using this
  have hup : L * g xbar ≤ F := by
    have := le_of_tendsto_of_tendsto hA ((tendsto_const_nhds (x := F)).add hEt)
      (Eventually.of_forall hupk)
    simpa using this
  have heq : L * g xbar = F := le_antisymm hup hlow
  simp only [FracPSG.Subseq.ratio]
  rw [← hFdef, ← heq]
  field_simp

end P2e99

namespace P2e99

open NonconvexSplitting.Shared FracPSG.Enhanced

theorem objF_lsc {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))} {fs : EuclideanSpace ℝ (Fin N) → ℝ}
    {fn : EuclideanSpace ℝ (Fin N) → EReal} {ℓ : ℝ} (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ) :
    LowerSemicontinuous (FracPSG.Subseq.objF fs fn) := by
  have h1 : LowerSemicontinuous (fun y => ((fs y : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hA1.fs_contDiff.continuous).lowerSemicontinuous
  show LowerSemicontinuous (fun y => ((fs y : ℝ) : EReal) + fn y)
  exact LowerSemicontinuous.add' h1 hA1.fn_lsc (fun y =>
    EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))


end P2e99

namespace Pfbd

open NonconvexSplitting.Shared FracPSG.Subseq FracPSG.Enhanced

theorem sq_diff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (y w v G : E) (c : ℝ) :
    ‖y - v - c • G‖ ^ 2 - ‖w - v - c • G‖ ^ 2
      = ‖y - v‖ ^ 2 - ‖w - v‖ ^ 2 - 2 * c * ⟪y - w, G⟫_ℝ := by
  rw [norm_sub_sq_real (y - v), norm_sub_sq_real (w - v), inner_smul_right, inner_smul_right]
  have : ⟪y - w, G⟫_ℝ = ⟪y - v, G⟫_ℝ - ⟪w - v, G⟫_ℝ := by
    rw [← inner_sub_left]; congr 1; abel
  rw [this]; ring

theorem sq_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w x e : E) (μ : ℝ) :
    ‖w - (x + μ • e)‖ ^ 2 = ‖w - x‖ ^ 2 - 2 * μ * ⟪w - x, e⟫_ℝ + μ ^ 2 * ‖e‖ ^ 2 := by
  have h : w - (x + μ • e) = (w - x) - μ • e := by abel
  rw [h, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- Core inequality: selection (Step 3) against an ε-active candidate, whose Step-2 subproblem is
compared with an arbitrary feasible point `y`. -/
theorem core {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ ε μbar κbar m M : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {w : ℕ → Fin p → EuclideanSpace ℝ (Fin N)}
    {ihat : ℕ → Fin p} {τ κ μ : ℕ → ℝ}
    (hA1 : Assumption1 S fs fn ℓ) (hA2 : Assumption2' S (objF fs fn) gi β m M)
    (hpar : Step1Params ℓ β δ ε ζ μbar κbar m M)
    (hrun : IsEnhancedRun S fs fn gi ℓ β δ ζ ε μbar κbar m M x w ihat τ κ μ) (n : ℕ)
    (hxS : x n ∈ S) (hxf : objF fs fn (x n) ≠ ⊤) (i : Fin p)
    (hia : i ∈ activeSet ε gi (x n)) (y : EuclideanSpace ℝ (Fin N)) (hyS : y ∈ S)
    (r : ℝ) (hry : fn y = r) :
    maxFn gi (x (n + 1)) * (ratio (objF fs fn) (maxFn gi) (x (n + 1))
        - ratio (objF fs fn) (maxFn gi) (x n))
      + ratio (objF fs fn) (maxFn gi) (x n) * gi i (x n)
      + ratio (objF fs fn) (maxFn gi) (x n) * ⟪gradient (gi i) (x n), y - x n⟫_ℝ
      - fs (extrap x κ n) - ⟪gradient fs (extrap x κ n), y - extrap x κ n⟫_ℝ
      - 1 / (2 * τ n) * ‖y - extrap x μ n‖ ^ 2 - ℓ / 2 * ‖y - extrap x κ n‖ ^ 2
      - μbar * (Real.sqrt (m * M) / M) / 2 * ‖x n - xPrev x n‖ ^ 2 ≤ r := by
  obtain ⟨hδ, hε, hζ, hη, hμb0, hμb1, hκb0, hκb1⟩ := hpar
  obtain ⟨hm, hM, -⟩ := hA2.bc
  have hwS := hrun.cand_mem n i hia
  have h := hrun.cand_argmin n i hia y hyS
  set θ := ratio (objF fs fn) (maxFn gi) (x n) with hθ
  set G := gradient (gi i) (x n) with hG
  set u := extrap x κ n with hu
  set v := extrap x μ n with hv
  set e := x n - xPrev x n with he
  have hfnw : fn (w n i) ≠ ⊤ := by
    intro hcon
    unfold subObj at h
    rw [hcon, hry, EReal.top_add_coe, ← EReal.coe_add] at h
    exact EReal.coe_ne_top _ (top_le_iff.mp h)
  have hwf : objF fs fn (w n i) ≠ ⊤ := by
    have hbot := hA1.fn_proper.1 (w n i)
    obtain ⟨r', hr'⟩ : ∃ r' : ℝ, fn (w n i) = r' := ⟨_, (EReal.coe_toReal hfnw hbot).symm⟩
    unfold objF; rw [hr', ← EReal.coe_add]; exact EReal.coe_ne_top _
  obtain ⟨r1, hr1, hFw, hFwr⟩ := P3ddd.fn_real hA1 hwf
  unfold subObj at h
  rw [hr1, hry, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  -- selection
  have hsel := hrun.ihat_argmin n i hia
  rw [← hrun.next_eq n] at hsel
  have hx1S : x (n + 1) ∈ S := by
    rw [hrun.next_eq n]; exact hrun.cand_mem n _ (hrun.ihat_mem n)
  unfold selObj at hsel
  rw [hFw, ← EReal.coe_add] at hsel
  have hx1f : objF fs fn (x (n + 1)) ≠ ⊤ := by
    intro hcon; rw [hcon, EReal.top_add_coe] at hsel
    exact EReal.coe_ne_top _ (top_le_iff.mp hsel)
  obtain ⟨r2, -, hF1, hF1r⟩ := P3ddd.fn_real hA1 hx1f
  rw [hF1, ← EReal.coe_add, EReal.coe_le_coe_iff] at hsel
  have hF1θ : fs (x (n + 1)) + r2
      = ratio (objF fs fn) (maxFn gi) (x (n + 1)) * maxFn gi (x (n + 1)) := by
    have hg1pos : 0 < maxFn gi (x (n + 1)) := hA2.g_pos _ hx1S
    rw [← hF1r]; unfold ratio; field_simp
  -- basic facts
  have hβ0 : 0 ≤ β := (hA2.weakly_convex i).1
  have hτ := hrun.step_pos n
  obtain ⟨hμ0, hμ1⟩ := hrun.mu_mem n
  have hg0 : 0 < maxFn gi (x n) := hA2.g_pos _ hxS
  have hFnn : 0 ≤ (objF fs fn (x n)).toReal := EReal.toReal_nonneg (hA1.nonneg _ hxS hxf)
  have hθ0 : 0 ≤ θ := div_nonneg hFnn hg0.le
  have hF : ∀ z, HasGradientAt fs (gradient fs z) z := fun z =>
    ((hA1.fs_contDiff.differentiable one_ne_zero) z).hasGradientAt
  have hdesc := P3ddd.descent hF hA1.grad_lipschitz u (w n i)
  obtain ⟨O, hO, hSO, hcd⟩ := hA2.contDiff i
  have hwc := P3ddd.grad_ineq (hA2.weakly_convex i) hO hSO hcd hxS hwS
  have hmax : gi i (w n i) ≤ maxFn gi (w n i) := by
    show gi i (w n i) ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => gi j (w n i))
    exact Finset.le_sup' (fun j => gi j (w n i)) (Finset.mem_univ i)
  have hgD : θ * (gi i (x n) + ⟪G, w n i - x n⟫_ℝ - β / 2 * ‖w n i - x n‖ ^ 2)
      ≤ θ * maxFn gi (w n i) := mul_le_mul_of_nonneg_left (by linarith) hθ0
  rw [mul_sub, mul_add] at hgD
  -- step-size bound: θ β ≤ √β ζ / τ
  have hMx : 0 < max (Real.sqrt β * θ / ζ) δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hstep := hrun.step_le n
  have hmaxle : max (Real.sqrt β * θ / ζ) δ ≤ 1 / τ n := by
    rw [le_div_iff₀ hτ]
    have := (le_div_iff₀ hMx).mp hstep
    linarith
  have hu1 : Real.sqrt β * θ ≤ (1 / τ n) * ζ := by
    have := le_trans (le_max_left _ _) hmaxle
    rwa [div_le_iff₀ hζ] at this
  have hu2 : δ ≤ 1 / τ n := le_trans (le_max_right _ _) hmaxle
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0
  have hβθ : β * θ ≤ Real.sqrt β * ζ * (1 / τ n) := by
    calc β * θ = Real.sqrt β * (Real.sqrt β * θ) := by rw [← mul_assoc, hsq]
      _ ≤ Real.sqrt β * ((1 / τ n) * ζ) := mul_le_mul_of_nonneg_left hu1 (Real.sqrt_nonneg _)
      _ = Real.sqrt β * ζ * (1 / τ n) := by ring
  -- abbreviations
  have hs : 0 < Real.sqrt (m * M) := Real.sqrt_pos.mpr (by positivity)
  set s := Real.sqrt (m * M) with hsdef
  set η := 1 - Real.sqrt β * ζ with hηdef
  obtain ⟨t, ht⟩ : ∃ t, t = 1 / τ n := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν, ν = μ n / τ n := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = M / s := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hν1 : ν ≤ μbar := by rw [hν, div_le_iff₀ hτ]; linarith
  have hlamν : lam * ν ≤ η * t := by
    -- M μ / s ≤ η / τ
    have h1 : lam * ν ≤ lam * μbar := mul_le_mul_of_nonneg_left hν1 hlam0.le
    have h2 : lam * μbar ≤ η * δ := by
      rw [hlam, div_mul_eq_mul_div, div_le_iff₀ hs]
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * M)).mp hμb1
      have := mul_pos (mul_pos hδ hη) hs
      linarith
    have h3 : η * δ ≤ η * t := mul_le_mul_of_nonneg_left (ht ▸ hu2) hη.le
    linarith
  have idc : 1 / 2 * ((1 - Real.sqrt β * ζ) / τ n - M * μ n / (Real.sqrt (m * M) * τ n))
      = η * t / 2 - lam * ν / 2 := by
    rw [ht, hν, hlam]; ring
  rw [idc] at hsel
  -- expansions
  have hQ := sq_diff y (w n i) v G (τ n * θ)
  have hW : ‖w n i - v‖ ^ 2 = ‖w n i - x n‖ ^ 2 - 2 * μ n * ⟪w n i - x n, e⟫_ℝ
      + μ n ^ 2 * ‖e‖ ^ 2 := sq_shift (w n i) (x n) e (μ n)
  have hyw : ⟪y - w n i, G⟫_ℝ + ⟪G, w n i - x n⟫_ℝ = ⟪G, y - x n⟫_ℝ := by
    rw [real_inner_comm, ← inner_add_right]; congr 1; abel
  set aw := ‖w n i - x n‖ with haw
  set b := ‖e‖ with hb
  set a := ‖x (n + 1) - x n‖ with ha
  -- AM-GM on the cross term
  have e1 : ⟪w n i - x n, e⟫_ℝ ≤ aw * b := real_inner_le_norm _ _
  have e2 : ν * ⟪w n i - x n, e⟫_ℝ ≤ ν * (aw * b) := mul_le_mul_of_nonneg_left e1 hν0
  have e6 : b ^ 2 / lam = s / M * b ^ 2 := by rw [hlam]; field_simp
  have e3 : 2 * (aw * b) ≤ lam * aw ^ 2 + s / M * b ^ 2 := by
    rw [← e6]; exact P3ddd.amgm aw b lam hlam0
  have e4 : ν * (2 * (aw * b)) ≤ ν * (lam * aw ^ 2 + s / M * b ^ 2) :=
    mul_le_mul_of_nonneg_left e3 hν0
  have e5 : ν * (s / M * b ^ 2) ≤ μbar * (s / M * b ^ 2) :=
    mul_le_mul_of_nonneg_right hν1 (by positivity)
  have e7 : (β * θ) * aw ^ 2 ≤ (Real.sqrt β * ζ * t) * aw ^ 2 :=
    mul_le_mul_of_nonneg_right (ht ▸ hβθ) (sq_nonneg _)
  have e8 : 0 ≤ (η * t / 2 - lam * ν / 2) * a ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have e9 : 0 ≤ μ n ^ 2 * b ^ 2 * t := by rw [ht]; positivity
  -- convert 1/(2τ) terms
  have k1 : 1 / (2 * τ n) = t / 2 := by rw [ht]; ring
  have k2 : μ n / τ n = ν := hν.symm
  have k3 : 1 / (2 * τ n) * (2 * (τ n * θ)) = θ := by field_simp
  -- assemble
  have s1 : fs (w n i) + r1 ≤ r + fs u + ⟪gradient fs u, y - u⟫_ℝ
      + 1 / (2 * τ n) * (‖y - v - (τ n * θ) • G‖ ^ 2 - ‖w n i - v - (τ n * θ) • G‖ ^ 2)
      + ℓ / 2 * ‖y - u‖ ^ 2 := by
    rw [mul_sub]; linarith
  rw [hQ, hW] at s1
  have s2 : 1 / (2 * τ n) * (‖y - v‖ ^ 2 - (aw ^ 2 - 2 * μ n * ⟪w n i - x n, e⟫_ℝ
      + μ n ^ 2 * b ^ 2) - 2 * (τ n * θ) * ⟪y - w n i, G⟫_ℝ)
      = t / 2 * ‖y - v‖ ^ 2 - t / 2 * aw ^ 2 + ν * ⟪w n i - x n, e⟫_ℝ
        - μ n ^ 2 * b ^ 2 * t / 2 - θ * ⟪y - w n i, G⟫_ℝ := by
    rw [ht, hν]; field_simp; ring
  rw [s2] at s1
  have hη' : η = 1 - Real.sqrt β * ζ := hηdef
  have hyw' : θ * ⟪y - w n i, G⟫_ℝ + θ * ⟪G, w n i - x n⟫_ℝ = θ * ⟪G, y - x n⟫_ℝ := by
    rw [← mul_add, hyw]
  have hηt : η * t * aw ^ 2 = t * aw ^ 2 - Real.sqrt β * ζ * t * aw ^ 2 := by
    rw [hη']; ring
  rw [k1]
  linarith [s1, hsel, hgD, hyw', e2, e4, e5, e7, e8, e9, hF1θ, hηt]

end Pfbd

namespace Pfbd

open NonconvexSplitting.Shared FracPSG.Subseq FracPSG.Enhanced

/-- A global quadratic lower bound on `F` over `S` makes `v` a regular, hence limiting,
subgradient of `F + ι_S` at `xbar`. -/
theorem lim_of_ineq {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {F : EuclideanSpace ℝ (Fin N) → EReal} {xbar v : EuclideanSpace ℝ (Fin N)} {C : ℝ}
    (hC : 0 < C) (hxS : xbar ∈ S) (hFx : F xbar ≠ ⊤)
    (hineq : ∀ z ∈ S, F xbar + ((⟪v, z - xbar⟫_ℝ - C * ‖z - xbar‖ ^ 2 : ℝ) : EReal) ≤ F z) :
    v ∈ LimitingSubdiff (addInd F S) xbar := by
  have hreg : IsRegularSubgrad (addInd F S) xbar v := by
    refine ⟨?_, fun ε hε => ?_⟩
    · simp only [addInd, if_pos hxS]; exact hFx
    · filter_upwards [Metric.ball_mem_nhds xbar (div_pos hε hC)] with z hz
      by_cases hzS : z ∈ S
      · simp only [addInd, if_pos hxS, if_pos hzS]
        have hd : ‖z - xbar‖ * C < ε := by
          have : ‖z - xbar‖ < ε / C := by
            have hz' : dist z xbar < ε / C := hz
            rwa [dist_eq_norm] at hz'
          rwa [lt_div_iff₀ hC] at this
        have hd0 : 0 ≤ ‖z - xbar‖ := norm_nonneg _
        have key : ⟪v, z - xbar⟫_ℝ - ε * ‖z - xbar‖ ≤ ⟪v, z - xbar⟫_ℝ - C * ‖z - xbar‖ ^ 2 := by
          have := mul_le_mul_of_nonneg_left hd.le hd0
          nlinarith
        exact (add_le_add le_rfl (EReal.coe_le_coe_iff.2 key)).trans (hineq z hzS)
      · simp [addInd, hzS]
  refine ⟨?_, fun _ => xbar, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
    tendsto_const_nhds, fun _ => hreg⟩
  simp only [addInd, if_pos hxS]; exact hFx

end Pfbd

open Filter Topology FracPSG.Subseq NonconvexSplitting.Shared FracPSG.Enhanced InnerProductSpace in
theorem solution
    {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ ε μbar κbar m M : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {w : ℕ → Fin p → EuclideanSpace ℝ (Fin N)}
    {ihat : ℕ → Fin p} {τ κ μ : ℕ → ℝ}
    (hS : IsClosed S) (hSconv : Convex ℝ S)
    (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ) (hA2 : Assumption2' S (FracPSG.Subseq.objF fs fn) gi β m M)
    (hpar : Step1Params ℓ β δ ε ζ μbar κbar m M)
    (hrun : IsEnhancedRun S fs fn gi ℓ β δ ζ ε μbar κbar m M x w ihat τ κ μ)
    (hS0 : Bornology.IsBounded (FracPSG.Subseq.S0 S (FracPSG.Subseq.objF fs fn) (maxFn gi) (x 0)))
    (hτ : 0 < Filter.liminf τ atTop) :
    ∀ xbar : EuclideanSpace ℝ (Fin N), MapClusterPt xbar atTop x →
      xbar ∈ S ∧ FracPSG.Subseq.objF fs fn xbar ≠ ⊤ ∧
      ∀ i ∈ activeSet 0 gi xbar,
        FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) xbar • gradient (gi i) xbar ∈
          LimitingSubdiff (FracPSG.Subseq.addInd (FracPSG.Subseq.objF fs fn) S) xbar := by
  intro xbar hcl
  have hall : ∀ n, x n ∈ S ∧ objF fs fn (x n) ≠ ⊤ := by
    intro n
    induction n with
    | zero => exact ⟨hrun.start_mem, hrun.start_dom⟩
    | succ k ih =>
      obtain ⟨h1, h2, -⟩ := P3ddd.step hA1 hA2 hpar hrun k ih.1 ih.2
      exact ⟨h1, h2⟩
  obtain ⟨hm, hM, hbc⟩ := hA2.bc
  have hδ : 0 < δ := hpar.1
  have hμb0 : 0 ≤ μbar := hpar.2.2.2.2.1
  have hα := P3ddd.alpha_pos hpar hm hM
  set α := P3ddd.αc ℓ β δ ζ μbar κbar m M with hαdef
  set c := P3ddd.cc ℓ μbar κbar m M with hcdef
  have hc0 : 0 ≤ c := by
    rw [hcdef]; unfold P3ddd.cc
    have := hA1.ell_nonneg
    positivity
  set L : ℕ → ℝ := fun n => ratio (objF fs fn) (maxFn gi) (x n) + c * ‖x n - xPrev x n‖ ^ 2
    with hLdef
  have hprev : ∀ n, xPrev x (n + 1) = x n := fun n => by simp [xPrev]
  have hL : ∀ n, L (n + 1) ≤ L n - α * ‖x (n + 1) - x n‖ ^ 2 := by
    intro n
    obtain ⟨-, -, h⟩ := P3ddd.step hA1 hA2 hpar hrun n (hall n).1 (hall n).2
    simp only [hLdef, hprev]
    linarith
  have hθnn : ∀ n, 0 ≤ ratio (objF fs fn) (maxFn gi) (x n) := by
    intro n
    exact div_nonneg (EReal.toReal_nonneg (hA1.nonneg _ (hall n).1 (hall n).2))
      (hA2.g_pos _ (hall n).1).le
  have hLnn : ∀ n, 0 ≤ L n := fun n => by
    simp only [hLdef]; have := hθnn n; positivity
  have hanti : Antitone L := by
    apply antitone_nat_of_succ_le
    intro n
    have := hL n
    have : 0 ≤ α * ‖x (n + 1) - x n‖ ^ 2 := by positivity
    linarith
  have hsum : ∀ n, α * ∑ k ∈ Finset.range n, ‖x (k + 1) - x k‖ ^ 2 ≤ L 0 - L n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hL k
      linarith
  have hsumm : Summable (fun n => ‖x (n + 1) - x n‖ ^ 2) := by
    apply summable_of_sum_range_le (c := L 0 / α) (fun n => sq_nonneg _)
    intro n
    rw [le_div_iff₀ hα]
    have := hsum n
    have := hLnn n
    linarith
  have hsq0 := hsumm.tendsto_atTop_zero
  have hstep : Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0) := by
    have h2 := (Real.continuous_sqrt.tendsto 0).comp hsq0
    rw [Real.sqrt_zero] at h2
    refine h2.congr (fun n => ?_)
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (norm_nonneg _)
  have hb2 : Tendsto (fun n => ‖x n - xPrev x n‖ ^ 2) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    refine hsq0.congr (fun n => ?_)
    rw [hprev]
  obtain ⟨Lim, hLim⟩ : ∃ Lim, Tendsto (fun n => ratio (objF fs fn) (maxFn gi) (x n)) atTop (𝓝 Lim) := by
    obtain ⟨L1, hL1⟩ : ∃ L1, Tendsto L atTop (𝓝 L1) :=
      ⟨_, tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨n, rfl⟩; exact hLnn n⟩⟩
    refine ⟨L1 - c * 0, ?_⟩
    have := hL1.sub (hb2.const_mul c)
    refine this.congr (fun n => ?_)
    simp [hLdef]
  have hθle : ∀ n, ratio (objF fs fn) (maxFn gi) (x n) ≤ L 0 := by
    intro n
    have h1 := hanti (Nat.zero_le n)
    have : 0 ≤ c * ‖x n - xPrev x n‖ ^ 2 := by positivity
    simp only [hLdef] at h1 ⊢
    linarith
  have hbound : ∀ n, (objF fs fn (x n)).toReal ≤ L 0 * M := by
    intro n
    have hg := hA2.g_pos _ (hall n).1
    have hgM := (hbc _ (hall n).1 (hall n).2).2
    have e : (objF fs fn (x n)).toReal = ratio (objF fs fn) (maxFn gi) (x n) * maxFn gi (x n) := by
      unfold ratio; field_simp
    rw [e]
    exact mul_le_mul (hθle n) hgM hg.le ((hθnn 0).trans (hθle 0))
  -- subsequence
  obtain ⟨ψ, hψm, hψt⟩ := hcl.tendsto_subseq
  have hψtt : Tendsto ψ atTop atTop := hψm.tendsto_atTop
  have hxbS : xbar ∈ S := hS.mem_of_tendsto hψt (Eventually.of_forall fun k => (hall (ψ k)).1)
  have hlsc := P2e99.objF_lsc hA1
  have hxbf : objF fs fn xbar ≠ ⊤ := by
    intro htop
    have hlt : (((L 0 * M : ℝ)) : EReal) < objF fs fn xbar := by
      rw [htop]; exact EReal.coe_lt_top _
    obtain ⟨k, hk⟩ := (hψt.eventually (hlsc xbar _ hlt)).exists
    obtain ⟨r, -, h1, h2⟩ := P3ddd.fn_real hA1 (hall (ψ k)).2
    simp only [Function.comp] at hk
    rw [h1] at hk
    have hk' : L 0 * M < fs (x (ψ k)) + r := EReal.coe_lt_coe_iff.mp hk
    have := hbound (ψ k)
    rw [h2] at this
    linarith
  have hLeq := P2e99.ratio_limit_eq hA1 hA2 hpar hrun hτ hall hLim hstep hcl hxbS hxbf hlsc
  refine ⟨hxbS, hxbf, fun i hi => ?_⟩
  -- continuity facts at xbar
  obtain ⟨O, hO, hSO, hCO⟩ := P2e99.common_open hA2
  have hxbO : xbar ∈ O := hSO hxbS
  have hdiff : ∀ j, DifferentiableAt ℝ (gi j) xbar := fun j =>
    ((hCO j).differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hxbO)
  have hgcont : ContinuousAt (maxFn gi) xbar := by
    have := ContinuousAt.finset_sup'_apply (s := Finset.univ) (f := gi) (x := xbar)
      Finset.univ_nonempty (fun j _ => (hdiff j).continuousAt)
    exact this
  have hgradc : ContinuousAt (fun z => gradient (gi i) z) xbar :=
    P2e99.gradient_continuousAt hO (hCO i) hxbO
  have hfsgc : Continuous (fun z => gradient fs z) := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    exact P2e99.gradient_continuousAt isOpen_univ hA1.fs_contDiff.contDiffOn (Set.mem_univ z)
  have hfsc : Continuous fs := hA1.fs_contDiff.continuous
  have hia0 : maxFn gi xbar ≤ gi i xbar := by
    have := (Finset.mem_filter.mp hi).2; linarith
  have hiaeq : gi i xbar = maxFn gi xbar := le_antisymm
    (Finset.le_sup' (fun j => gi j xbar) (Finset.mem_univ i)) hia0
  -- sequences along ψ
  have hx0 : Tendsto (fun k => x (ψ k)) atTop (𝓝 xbar) := hψt
  have hτle : ∀ n, τ n ≤ 1 / δ := fun n =>
    (hrun.step_le n).trans (one_div_le_one_div_of_le hδ (le_max_right _ _))
  have hprevd : Tendsto (fun n => ‖x n - xPrev x n‖) atTop (𝓝 0) := by
    have h2 := (Real.continuous_sqrt.tendsto 0).comp hb2
    rw [Real.sqrt_zero] at h2
    refine h2.congr (fun n => ?_)
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (norm_nonneg _)
  have hprevk := hprevd.comp hψtt
  have hu : Tendsto (fun k => extrap x κ (ψ k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => κ (ψ k) • (x (ψ k) - xPrev x (ψ k))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k => κbar * ‖x (ψ k) - xPrev x (ψ k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.kappa_mem (ψ k)).1]
        exact mul_le_mul_of_nonneg_right (hrun.kappa_mem (ψ k)).2 (norm_nonneg _)
      · simpa using hprevk.const_mul κbar
    have := hx0.add hz
    simpa [extrap] using this
  have hv : Tendsto (fun k => extrap x μ (ψ k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => μ (ψ k) • (x (ψ k) - xPrev x (ψ k))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k => (μbar * (1 / δ)) * ‖x (ψ k) - xPrev x (ψ k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.mu_mem (ψ k)).1]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (hrun.mu_mem (ψ k)).2.trans (mul_le_mul_of_nonneg_left (hτle _) hμb0)
      · simpa using hprevk.const_mul (μbar * (1 / δ))
    have := hx0.add hz
    simpa [extrap] using this
  -- step-size lower bound
  set T0 := Filter.liminf τ atTop / 2 with hT0
  have hT0pos : 0 < T0 := by rw [hT0]; linarith
  have evτ : ∀ᶠ k in atTop, T0 ≤ τ (ψ k) := by
    have h := Filter.eventually_lt_of_lt_liminf (f := atTop) (u := τ) (b := T0)
      (by rw [hT0]; linarith) (isBoundedUnder_of ⟨0, fun n => (hrun.step_pos n).le⟩)
    exact (hψtt.eventually h).mono fun k hk => hk.le
  -- i is eventually ε-active
  have evact : ∀ᶠ k in atTop, i ∈ activeSet ε gi (x (ψ k)) := by
    have ht : Tendsto (fun k => maxFn gi (x (ψ k)) - gi i (x (ψ k))) atTop
        (𝓝 (maxFn gi xbar - gi i xbar)) :=
      (hgcont.tendsto.comp hx0).sub ((hdiff i).continuousAt.tendsto.comp hx0)
    have hlt : maxFn gi xbar - gi i xbar < ε := by rw [hiaeq]; simpa using hpar.2.1
    filter_upwards [ht.eventually (gt_mem_nhds hlt)] with k hk
    unfold activeSet; rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by linarith⟩
  -- the limit inequality
  set θb := ratio (objF fs fn) (maxFn gi) xbar with hθb
  have hlim : ∀ y ∈ S, ∀ r : ℝ, fn y = r →
      θb * gi i xbar + θb * ⟪gradient (gi i) xbar, y - xbar⟫_ℝ - fs xbar
        - ⟪gradient fs xbar, y - xbar⟫_ℝ - 1 / (2 * T0) * ‖y - xbar‖ ^ 2
        - ℓ / 2 * ‖y - xbar‖ ^ 2 ≤ r := by
    intro y hyS r hry
    set K := μbar * (Real.sqrt (m * M) / M) / 2 with hK
    have hev : ∀ᶠ k in atTop,
        maxFn gi (x (ψ k + 1)) * (ratio (objF fs fn) (maxFn gi) (x (ψ k + 1))
            - ratio (objF fs fn) (maxFn gi) (x (ψ k)))
          + ratio (objF fs fn) (maxFn gi) (x (ψ k)) * gi i (x (ψ k))
          + ratio (objF fs fn) (maxFn gi) (x (ψ k)) * ⟪gradient (gi i) (x (ψ k)), y - x (ψ k)⟫_ℝ
          - fs (extrap x κ (ψ k)) - ⟪gradient fs (extrap x κ (ψ k)), y - extrap x κ (ψ k)⟫_ℝ
          - 1 / (2 * T0) * ‖y - extrap x μ (ψ k)‖ ^ 2 - ℓ / 2 * ‖y - extrap x κ (ψ k)‖ ^ 2
          - K * ‖x (ψ k) - xPrev x (ψ k)‖ ^ 2 ≤ r := by
      filter_upwards [evτ, evact] with k hk1 hk2
      have hc := Pfbd.core hA1 hA2 hpar hrun (ψ k) (hall (ψ k)).1 (hall (ψ k)).2 i hk2 y hyS r hry
      have h1 : 1 / (2 * τ (ψ k)) ≤ 1 / (2 * T0) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖y - extrap x μ (ψ k)‖)
      rw [← hK] at hc
      linarith
    have t1 : Tendsto (fun k => maxFn gi (x (ψ k + 1)) * (ratio (objF fs fn) (maxFn gi) (x (ψ k + 1))
            - ratio (objF fs fn) (maxFn gi) (x (ψ k)))) atTop (𝓝 0) := by
      have hd : Tendsto (fun n => ratio (objF fs fn) (maxFn gi) (x (n + 1))
          - ratio (objF fs fn) (maxFn gi) (x n)) atTop (𝓝 0) := by
        have := (hLim.comp (tendsto_add_atTop_nat 1)).sub hLim
        simpa using this
      have hdk := hd.comp hψtt
      refine squeeze_zero_norm (a := fun k => M * ‖ratio (objF fs fn) (maxFn gi) (x (ψ k + 1))
            - ratio (objF fs fn) (maxFn gi) (x (ψ k))‖) (fun k => ?_) ?_
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hg := hA2.g_pos _ (hall (ψ k + 1)).1
        rw [Real.norm_eq_abs, abs_of_pos hg]
        exact (hbc _ (hall (ψ k + 1)).1 (hall (ψ k + 1)).2).2
      · simpa using (hdk.norm).const_mul M
    have hθk := hLim.comp hψtt
    rw [hLeq] at hθk
    have t2 : Tendsto (fun k => ratio (objF fs fn) (maxFn gi) (x (ψ k)) * gi i (x (ψ k))) atTop
        (𝓝 (θb * gi i xbar)) := hθk.mul ((hdiff i).continuousAt.tendsto.comp hx0)
    have t3 : Tendsto (fun k => ratio (objF fs fn) (maxFn gi) (x (ψ k))
        * ⟪gradient (gi i) (x (ψ k)), y - x (ψ k)⟫_ℝ) atTop
        (𝓝 (θb * ⟪gradient (gi i) xbar, y - xbar⟫_ℝ)) :=
      hθk.mul (Tendsto.inner (𝕜 := ℝ) (hgradc.tendsto.comp hx0)
        ((tendsto_const_nhds (x := y)).sub hx0))
    have t4 : Tendsto (fun k => fs (extrap x κ (ψ k))) atTop (𝓝 (fs xbar)) :=
      (hfsc.tendsto xbar).comp hu
    have t5 : Tendsto (fun k => ⟪gradient fs (extrap x κ (ψ k)), y - extrap x κ (ψ k)⟫_ℝ) atTop
        (𝓝 ⟪gradient fs xbar, y - xbar⟫_ℝ) :=
      Tendsto.inner (𝕜 := ℝ) ((hfsgc.tendsto xbar).comp hu) ((tendsto_const_nhds (x := y)).sub hu)
    have t6 : Tendsto (fun k => 1 / (2 * T0) * ‖y - extrap x μ (ψ k)‖ ^ 2) atTop
        (𝓝 (1 / (2 * T0) * ‖y - xbar‖ ^ 2)) :=
      ((((tendsto_const_nhds (x := y)).sub hv).norm).pow 2).const_mul _
    have t7 : Tendsto (fun k => ℓ / 2 * ‖y - extrap x κ (ψ k)‖ ^ 2) atTop
        (𝓝 (ℓ / 2 * ‖y - xbar‖ ^ 2)) :=
      ((((tendsto_const_nhds (x := y)).sub hu).norm).pow 2).const_mul _
    have t8 : Tendsto (fun k => K * ‖x (ψ k) - xPrev x (ψ k)‖ ^ 2) atTop (𝓝 (K * 0)) :=
      (hb2.comp hψtt).const_mul K
    have hT := ((((((t1.add t2).add t3).sub t4).sub t5).sub t6).sub t7).sub t8
    have := le_of_tendsto hT hev
    simp only [mul_zero, zero_add, sub_zero] at this
    linarith
  -- conclude
  have hg0 : 0 < maxFn gi xbar := hA2.g_pos _ hxbS
  obtain ⟨rb, -, hFb, hFbr⟩ := P3ddd.fn_real hA1 hxbf
  have hFθ : fs xbar + rb = θb * gi i xbar := by
    rw [hiaeq, ← hFbr, hθb]; unfold ratio; field_simp
  have hF : ∀ z, HasGradientAt fs (gradient fs z) z := fun z =>
    ((hA1.fs_contDiff.differentiable one_ne_zero) z).hasGradientAt
  have hCpos : 0 < 1 / (2 * T0) + ℓ / 2 := by
    have : 0 < 1 / (2 * T0) := by positivity
    have := hA1.ell_nonneg
    linarith
  refine Pfbd.lim_of_ineq hCpos hxbS hxbf (fun z hzS => ?_)
  by_cases hzf : objF fs fn z = ⊤
  · rw [hzf]; exact le_top
  obtain ⟨rz, hrz, hFz, -⟩ := P3ddd.fn_real hA1 hzf
  have h1 := hlim z hzS rz hrz
  have h2 := P3ddd.convex_fo hF hA1.fs_convex xbar z
  rw [hFb, hFz, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_smul_left]
  simp only [conj_trivial]
  nlinarith [h1, h2, hFθ]
