-- Prove2me | solution 1 for FracPSG.Enhanced.theorem_6_1_i
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T09:13:49.534878+00:00
-- url     : https://prove2.me/submissions/ed0924ac-c54b-44a7-b484-a2dfdd855ffb

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

open Filter Topology FracPSG.Subseq NonconvexSplitting.Shared FracPSG.Enhanced in
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
    (hS0 : Bornology.IsBounded (FracPSG.Subseq.S0 S (FracPSG.Subseq.objF fs fn) (maxFn gi) (x 0))) :
    (∀ n, x n ∈ S ∧ FracPSG.Subseq.objF fs fn (x n) ≠ ⊤) ∧
    Antitone (lyap (FracPSG.Subseq.objF fs fn) (maxFn gi) ℓ μbar κbar m M x) ∧
    (∃ L : ℝ, Tendsto (lyap (FracPSG.Subseq.objF fs fn) (maxFn gi) ℓ μbar κbar m M x) atTop (𝓝 L)) ∧
    ∃ L : ℝ, Tendsto (fun n => FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n)) atTop (𝓝 L) := by
  have hall : ∀ n, x n ∈ S ∧ objF fs fn (x n) ≠ ⊤ := by
    intro n
    induction n with
    | zero => exact ⟨hrun.start_mem, hrun.start_dom⟩
    | succ k ih =>
      obtain ⟨h1, h2, -⟩ := P3ddd.step hA1 hA2 hpar hrun k ih.1 ih.2
      exact ⟨h1, h2⟩
  obtain ⟨hm, hM, -⟩ := hA2.bc
  have hα := P3ddd.alpha_pos hpar hm hM
  have hs : 0 < Real.sqrt (m * M) := Real.sqrt_pos.mpr (by positivity)
  have hss : Real.sqrt (m * M) * Real.sqrt (m * M) = m * M := Real.mul_self_sqrt (by positivity)
  have hccoef : P3ddd.cc ℓ μbar κbar m M
      = ℓ * κbar ^ 2 / (2 * m) + μbar / (2 * Real.sqrt (m * M)) := by
    have e : μbar * Real.sqrt (m * M) / (2 * M) / m = μbar / (2 * Real.sqrt (m * M)) := by
      rw [div_div, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (2 * μbar) * hss
    calc P3ddd.cc ℓ μbar κbar m M
        = μbar * Real.sqrt (m * M) / (2 * M) / m + ℓ * κbar ^ 2 / (2 * m) := by
          unfold P3ddd.cc; ring
      _ = ℓ * κbar ^ 2 / (2 * m) + μbar / (2 * Real.sqrt (m * M)) := by rw [e]; ring
  set α := P3ddd.αc ℓ β δ ζ μbar κbar m M with hαdef
  have hc0 : 0 ≤ P3ddd.cc ℓ μbar κbar m M := by
    unfold P3ddd.cc
    have := hA1.ell_nonneg
    have := hpar.2.2.2.2.1
    positivity
  have hprev : ∀ n, xPrev x (n + 1) = x n := fun n => by simp [xPrev]
  have hLdef : ∀ n, lyap (objF fs fn) (maxFn gi) ℓ μbar κbar m M x n
      = ratio (objF fs fn) (maxFn gi) (x n) + P3ddd.cc ℓ μbar κbar m M * ‖x n - xPrev x n‖ ^ 2 := by
    intro n; unfold lyap; rw [hccoef]
  set L := lyap (objF fs fn) (maxFn gi) ℓ μbar κbar m M x with hL'
  have hL : ∀ n, L (n + 1) ≤ L n - α * ‖x (n + 1) - x n‖ ^ 2 := by
    intro n
    obtain ⟨-, -, h⟩ := P3ddd.step hA1 hA2 hpar hrun n (hall n).1 (hall n).2
    rw [hLdef, hLdef, hprev]
    linarith
  have hθnn : ∀ n, 0 ≤ ratio (objF fs fn) (maxFn gi) (x n) := by
    intro n
    exact div_nonneg (EReal.toReal_nonneg (hA1.nonneg _ (hall n).1 (hall n).2))
      (hA2.g_pos _ (hall n).1).le
  have hLnn : ∀ n, 0 ≤ L n := fun n => by
    rw [hLdef]; have := hθnn n; positivity
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
  have hlim : Tendsto L atTop (𝓝 (⨅ n, L n)) :=
    tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨n, rfl⟩; exact hLnn n⟩
  have hb : Tendsto (fun n => ‖x n - xPrev x n‖ ^ 2) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    refine hsumm.tendsto_atTop_zero.congr (fun n => ?_)
    show ‖x (n + 1) - x n‖ ^ 2 = ‖x (n + 1) - xPrev x (n + 1)‖ ^ 2
    rw [hprev]
  refine ⟨hall, hanti, ⟨_, hlim⟩, ⟨⨅ n, L n, ?_⟩⟩
  have h2 := hlim.sub (hb.const_mul (P3ddd.cc ℓ μbar κbar m M))
  rw [mul_zero, sub_zero] at h2
  refine h2.congr (fun n => ?_)
  show L n - P3ddd.cc ℓ μbar κbar m M * ‖x n - xPrev x n‖ ^ 2 = _
  rw [hLdef]; ring
