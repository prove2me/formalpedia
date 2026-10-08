-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.rsmd_complexity_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:00:39.295986+00:00
-- url     : https://prove2.me/submissions/f5409a7f-47d2-4175-b493-111cd3fe5b76

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

namespace RSMD5b507335

open scoped RealInnerProductSpace
open MeasureTheory FirstOrderOpt.Prox Filter Topology

/-- Descent inequality (with constant `L`, enough here) for a function whose gradient is
`L`-Lipschitz along a convex set. -/
lemma descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (hXconv : Convex ℝ X) (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (fGrad : E → E)
    (hGrad : ∀ x ∈ X, HasGradientWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (x y : E) (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪fGrad x, y - x⟫ + L * ‖y - x‖ ^ 2 := by
  set s := X ∩ Metric.closedBall x ‖y - x‖ with hs
  have hsc : Convex ℝ s := hXconv.inter (convex_closedBall _ _)
  have hxs : x ∈ s := ⟨hx, Metric.mem_closedBall_self (norm_nonneg _)⟩
  have hys : y ∈ s := ⟨hy, by simp [Metric.mem_closedBall, dist_eq_norm]⟩
  let g : E → ℝ := fun z => f z - ⟪fGrad x, z⟫
  have hg : ∀ z ∈ s, HasFDerivWithinAt g (innerSL ℝ (fGrad z - fGrad x)) s z := by
    intro z hz
    have h1 := (hasGradientWithinAt_iff_hasFDerivWithinAt.mp (hGrad z hz.1)).mono
      (Set.inter_subset_left : s ⊆ X)
    have h2 : HasFDerivWithinAt (fun z => ⟪fGrad x, z⟫) (innerSL ℝ (fGrad x)) s z :=
      (innerSL ℝ (fGrad x)).hasFDerivWithinAt
    have h3 := h1.sub h2
    have e : InnerProductSpace.toDual ℝ E (fGrad z) - innerSL ℝ (fGrad x)
        = innerSL ℝ (fGrad z - fGrad x) := by
      ext v; simp [InnerProductSpace.toDual_apply_apply, inner_sub_left]
    rw [e] at h3
    exact h3
  have hb : ∀ z ∈ s, ‖innerSL ℝ (fGrad z - fGrad x)‖ ≤ L * ‖y - x‖ := by
    intro z hz
    rw [innerSL_apply_norm]
    have hz2 : ‖z - x‖ ≤ ‖y - x‖ := by
      have := hz.2; rwa [Metric.mem_closedBall, dist_eq_norm] at this
    calc ‖fGrad z - fGrad x‖ ≤ L * ‖z - x‖ := hSmooth z hz.1 x hx
      _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left hz2 hL
  have hmv := hsc.norm_image_sub_le_of_norm_hasFDerivWithin_le hg hb hxs hys
  have hle : g y - g x ≤ L * ‖y - x‖ * ‖y - x‖ := le_trans (Real.le_norm_self _) hmv
  simp only [g] at hle
  rw [inner_sub_right]
  have hsq : ‖y - x‖ ^ 2 = ‖y - x‖ * ‖y - x‖ := sq _
  linarith

/-- Three-point inequality at `u = x` for the prox step. -/
lemma three_point {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X) (γ : ℝ) (hγ : 0 < γ) (G x xp : E)
    (hx : x ∈ X) (hxp : xp ∈ X)
    (hmin : ∀ u ∈ X, ⟪G, xp⟫ + (1 / γ) * ν.V x xp + h xp ≤ ⟪G, u⟫ + (1 / γ) * ν.V x u + h u) :
    ‖x - xp‖ ^ 2 ≤ γ * (⟪G, x - xp⟫ + h x - h xp) := by
  set d := x - xp with hd
  set K := γ * ⟪G, d⟫ - ν.dω x d + γ * (h x - h xp) with hK
  have hc : γ * (1 / γ) = 1 := by field_simp
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → -(t * K) ≤ ν.ω (xp + t • d) - ν.ω xp := by
    intro t ht0 ht1
    have hut : xp + t • d = (1 - t) • xp + t • x := by
      rw [hd, smul_sub, sub_smul, one_smul]; abel
    have hmem : xp + t • d ∈ X := by
      rw [hut]; exact hXconv hxp hx (by linarith) ht0.le (by ring)
    have hm := hmin _ hmem
    have hh : h (xp + t • d) ≤ (1 - t) * h xp + t * h x := by
      rw [hut]
      have := hhconv.2 hxp hx (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      simpa [smul_eq_mul] using this
    simp only [DistanceGeneratingFunction.V] at hm
    have hlin : ν.dω x (xp + t • d - x) = ν.dω x (xp - x) + t * ν.dω x d := by
      rw [show xp + t • d - x = (xp - x) + t • d by abel, map_add, map_smul, smul_eq_mul]
    have hinner : ⟪G, xp + t • d⟫ = ⟪G, xp⟫ + t * ⟪G, d⟫ := by
      rw [inner_add_right, real_inner_smul_right]
    rw [hlin, hinner] at hm
    set Y := ν.ω (xp + t • d) - ν.ω xp - t * ν.dω x d with hY
    have hB : 0 ≤ t * ⟪G, d⟫ + (1 / γ) * Y + t * (h x - h xp) := by
      rw [hY]; nlinarith [hm, hh]
    have hγB := mul_nonneg hγ.le hB
    have e : ν.ω (xp + t • d) - ν.ω xp + t * K
        = γ * (t * ⟪G, d⟫ + (1 / γ) * Y + t * (h x - h xp)) := by
      rw [hK, hY]; linear_combination (-(ν.ω (xp + t • d) - ν.ω xp - t * ν.dω x d)) * hc
    linarith
  have hderiv := ν.hasFDerivWithinAt xp hxp
  have hlim : Tendsto (fun n : ℕ => ((n:ℝ) + 1) • (ν.ω (xp + ((1:ℝ) / ((n:ℝ) + 1)) • d) - ν.ω xp))
      atTop (𝓝 (ν.dω xp d)) := by
    apply hderiv.lim
    · have : Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this.smul_const d
    · filter_upwards with n
      have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have ht1 : (1:ℝ) / ((n:ℝ) + 1) ≤ 1 := by
        rw [div_le_one hn]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
      have hut : xp + ((1:ℝ) / ((n:ℝ) + 1)) • d
          = (1 - (1:ℝ) / ((n:ℝ) + 1)) • xp + ((1:ℝ) / ((n:ℝ) + 1)) • x := by
        rw [hd, smul_sub, sub_smul, one_smul]; abel
      rw [hut]; exact hXconv hxp hx (by linarith) (by positivity) (by ring)
    · have : (fun n : ℕ => ((n:ℝ) + 1) • (((1:ℝ) / ((n:ℝ) + 1)) • d)) = fun _ => d := by
        funext n
        have hn : ((n:ℝ) + 1) ≠ 0 := by positivity
        rw [smul_smul, mul_one_div_cancel hn, one_smul]
      rw [this]; exact tendsto_const_nhds
  have hge : -K ≤ ν.dω xp d := by
    apply ge_of_tendsto hlim
    filter_upwards with n
    have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have ht1 : (1:ℝ) / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have h1 := key (1 / ((n:ℝ) + 1)) (by positivity) ht1
    have h2 := mul_le_mul_of_nonneg_left h1 hn.le
    rw [smul_eq_mul]
    have e : ((n:ℝ) + 1) * (-(1 / ((n:ℝ) + 1) * K)) = -K := by field_simp
    linarith
  have sc1 := ν.strongConvex x hx xp hxp
  have sc2 := ν.strongConvex xp hxp x hx
  have e1 : ν.dω x (xp - x) = - ν.dω x d := by
    rw [show xp - x = -d by rw [hd]; abel, map_neg]
  have e2 : ‖xp - x‖ = ‖d‖ := by rw [hd, norm_sub_rev]
  rw [e1, e2] at sc1
  rw [← hd] at sc2
  have : ‖d‖ ^ 2 ≤ ν.dω x d - ν.dω xp d := by linarith
  rw [hK] at hge
  nlinarith

/-- One deterministic step: sufficient decrease of `Ψ = f + h`. -/
lemma step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (hXconv : Convex ℝ X) (f h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X) (L : ℝ) (hL : 0 ≤ L) (fGrad : E → E)
    (hGrad : ∀ x ∈ X, HasGradientWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (γ : ℝ) (hγ : 0 < γ) (G x xp : E) (hG : G = fGrad x) (hx : x ∈ X) (hxp : xp ∈ X)
    (hmin : ∀ u ∈ X, ⟪G, xp⟫ + (1 / γ) * ν.V x xp + h xp ≤ ⟪G, u⟫ + (1 / γ) * ν.V x u + h u) :
    (γ - L * γ ^ 2) * ‖(1 / γ) • (x - xp)‖ ^ 2 ≤ (f x + h x) - (f xp + h xp) := by
  have A := three_point X hXconv h hhconv ν γ hγ G x xp hx hxp hmin
  have B := descent X hXconv f L hL fGrad hGrad hSmooth x xp hx hxp
  rw [← hG] at B
  have e1 : xp - x = -(x - xp) := by abel
  rw [e1, inner_neg_right, norm_neg] at B
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / γ)]
  set q := ‖x - xp‖ ^ 2 with hq
  set W := ⟪G, x - xp⟫ + h x - h xp with hW
  have e : (γ - L * γ ^ 2) * ((1 / γ) ^ 2 * q) = q / γ - L * q := by
    field_simp
  have hqW : q / γ ≤ W := by rw [div_le_iff₀ hγ]; linarith
  rw [e]
  linarith

/-- Composition of a Lipschitz-on-`X` map with a strongly measurable `X`-valued map. -/
lemma sm_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} (m : MeasurableSpace Ω) (X : Set E) (fGrad : E → E) (L : ℝ) (hL : 0 ≤ L)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (y : Ω → E) (hy : StronglyMeasurable[m] y) (hyX : ∀ ω, y ω ∈ X) :
    StronglyMeasurable[m] (fun ω => fGrad (y ω)) := by
  have hsep := hy.isSeparable_range
  have := hsep.secondCountableTopology
  have hm : Measurable[m] (Set.rangeFactorization y) := hy.measurable.subtype_mk
  have hs : StronglyMeasurable[m] (Set.rangeFactorization y) := hm.stronglyMeasurable
  let F : Set.range y → E := fun z => fGrad z.1
  have hF : Continuous F := by
    have hL' : ∀ a b : Set.range y, dist (F a) (F b) ≤ (Real.toNNReal L : ℝ) * dist a b := by
      intro a b
      obtain ⟨ωa, ha⟩ := a.2
      obtain ⟨ωb, hb⟩ := b.2
      rw [Real.coe_toNNReal L hL, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
      have haX : (a : E) ∈ X := ha ▸ hyX ωa
      have hbX : (b : E) ∈ X := hb ▸ hyX ωb
      exact hSmooth a.1 haX b.1 hbX
    exact (LipschitzWith.of_dist_le_mul hL').continuous
  exact hF.comp_stronglyMeasurable hs

end RSMD5b507335

open scoped RealInnerProductSpace in open MeasureTheory FirstOrderOpt.Prox in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : Filtration ℕ m0)
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X) (L σ : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ)
    (fGrad : E → E)
    (hGrad : ∀ x ∈ X, HasGradientWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (N : ℕ) (hN : 1 ≤ N)
    (x1 : E) (hx1 : x1 ∈ X)
    (x G xPlus gXtilde : ℕ → Ω → E) (γ mBatch : ℕ → ℝ)
    (hmBatch : ∀ k, 1 ≤ k → k ≤ N → 0 < mBatch k)
    (hx1def : ∀ ω, x 1 ω = x1)
    (hxMeas : ∀ k, 1 ≤ k → StronglyMeasurable[𝒢 (k - 1)] (x k))
    (hGMeas : ∀ k, 1 ≤ k → StronglyMeasurable[𝒢 (k - 1)] (G k))
    (hx : ∀ k, ∀ ω, x k ω ∈ X) (hxPlusMem : ∀ k, ∀ ω, xPlus k ω ∈ X)
    (hxPlusDef : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, ∀ u ∈ X,
      ⟪G k ω, xPlus k ω⟫ + (1 / γ k) * ν.V (x k ω) (xPlus k ω) + h (xPlus k ω) ≤
        ⟪G k ω, u⟫ + (1 / γ k) * ν.V (x k ω) u + h u)
    (hxNext : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, x (k + 1) ω = xPlus k ω)
    (hgXtilde : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, gXtilde k ω = (1 / γ k) • (x k ω - xPlus k ω))
    (hγpos : ∀ k, 1 ≤ k → k ≤ N → 0 < γ k) (hγub : ∀ k, 1 ≤ k → k ≤ N → γ k ≤ 1 / L)
    (hγstrict : ∃ k, 1 ≤ k ∧ k ≤ N ∧ γ k < 1 / L)
    (hDeltaInt : ∀ k, 1 ≤ k → k ≤ N → Integrable (fun ω => G k ω - fGrad (x k ω)) P)
    (hDeltaSqInt : ∀ k, 1 ≤ k → k ≤ N →
      Integrable (fun ω => ‖G k ω - fGrad (x k ω)‖ ^ 2) P)
    (hUnbiased : ∀ k, 1 ≤ k → k ≤ N →
      condExp (𝒢 (k - 1)) P (fun ω => G k ω - fGrad (x k ω)) =ᵐ[P] 0)
    (hVariance : ∀ k, 1 ≤ k → k ≤ N →
      condExp (𝒢 (k - 1)) P (fun ω => ‖G k ω - fGrad (x k ω)‖ ^ 2) ≤ᵐ[P]
        (fun _ => σ ^ 2 / mBatch k))
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f x1 + h x1 - ΨStar) / L))
    (R : Ω → ℕ) (hRmeas : Measurable R) (hRsupp : ∀ ω, 1 ≤ R ω ∧ R ω ≤ N)
    (PR : ℕ → ℝ)
    (hPR : ∀ k, 1 ≤ k → k ≤ N →
      PR k = (γ k - L * (γ k) ^ 2) / ∑ j ∈ Finset.Icc 1 N, (γ j - L * (γ j) ^ 2))
    (hRlaw : ∀ k, 1 ≤ k → k ≤ N → P {ω | R ω = k} = ENNReal.ofReal (PR k))
    (hRindep : ∀ k, 1 ≤ k → k ≤ N → ProbabilityTheory.IndepFun R (gXtilde k) P)
    (gXtildeR : Ω → E) (hgXtildeR : ∀ ω, gXtildeR ω = gXtilde (R ω) ω)
    (hgXtildeRInt : Integrable (fun ω => ‖gXtildeR ω‖ ^ 2) P) :
    ∫ ω, ‖gXtildeR ω‖ ^ 2 ∂P ≤
      (L * DΨ ^ 2 + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, (γ k / mBatch k)) /
        ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2) := by
  -- Step 1: `G k` and `x k` are both `𝒢 (k-1)`-measurable, so the noise equals its own
  -- conditional mean, which is `0`: the iteration is a.s. the deterministic one.
  have hδ0 : ∀ k ∈ Finset.Icc 1 N, ∀ᵐ ω ∂P, G k ω = fGrad (x k ω) := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have hsm : StronglyMeasurable[𝒢 (k - 1)] (fun ω => G k ω - fGrad (x k ω)) :=
      (hGMeas k hk1).sub
        (RSMD5b507335.sm_comp (𝒢 (k - 1)) X fGrad L hL.le hSmooth (x k) (hxMeas k hk1) (hx k))
    have hce := condExp_of_stronglyMeasurable (𝒢.le (k - 1)) hsm (hDeltaInt k hk1 hkN)
    have h0 := hUnbiased k hk1 hkN
    rw [hce] at h0
    filter_upwards [h0] with ω hω
    simpa [sub_eq_zero] using hω
  have hgood : ∀ᵐ ω ∂P, ∀ k ∈ Finset.Icc 1 N, G k ω = fGrad (x k ω) :=
    (Filter.eventually_all_finset _).2 hδ0
  set C := f x1 + h x1 - ΨStar with hCdef
  have hC0 : 0 ≤ C := by
    have : ΨStar ≤ f x1 + h x1 := hΨStar.1 ⟨x1, hx1, rfl⟩
    linarith
  -- Step 2: deterministic descent and telescoping.
  have hstep : ∀ ω, (∀ k ∈ Finset.Icc 1 N, G k ω = fGrad (x k ω)) → ∀ k, 1 ≤ k → k ≤ N →
      (γ k - L * γ k ^ 2) * ‖gXtilde k ω‖ ^ 2 ≤
        (f (x k ω) + h (x k ω)) - (f (x (k + 1) ω) + h (x (k + 1) ω)) := by
    intro ω hω k hk1 hkN
    rw [hgXtilde k hk1 hkN ω, hxNext k hk1 hkN ω]
    exact RSMD5b507335.step X hXconv f h hhconv ν L hL.le fGrad hGrad hSmooth (γ k)
      (hγpos k hk1 hkN) (G k ω) (x k ω) (xPlus k ω) (hω k (Finset.mem_Icc.2 ⟨hk1, hkN⟩))
      (hx k ω) (hxPlusMem k ω) (hxPlusDef k hk1 hkN ω)
  have htel : ∀ ω, (∀ k ∈ Finset.Icc 1 N, G k ω = fGrad (x k ω)) → ∀ n, n ≤ N →
      ∑ k ∈ Finset.Icc 1 n, (γ k - L * γ k ^ 2) * ‖gXtilde k ω‖ ^ 2 ≤
        (f (x 1 ω) + h (x 1 ω)) - (f (x (n + 1) ω) + h (x (n + 1) ω)) := by
    intro ω hω n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h1 := hstep ω hω (n + 1) (by omega) hn
      have h2 := ih (by omega)
      linarith
  have hbound : ∀ᵐ ω ∂P,
      ∑ k ∈ Finset.Icc 1 N, (γ k - L * γ k ^ 2) * ‖gXtilde k ω‖ ^ 2 ≤ C := by
    filter_upwards [hgood] with ω hω
    have h1 := htel ω hω N le_rfl
    rw [hx1def ω] at h1
    have h2 : ΨStar ≤ f (x (N + 1) ω) + h (x (N + 1) ω) := hΨStar.1 ⟨x (N + 1) ω, hx _ _, rfl⟩
    linarith
  -- Step 3: expectations.
  have ha0 : ∀ k ∈ Finset.Icc 1 N, 0 ≤ γ k - L * γ k ^ 2 := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have h1 := hγub k hk1 hkN
    have h2 := hγpos k hk1 hkN
    have h3 : γ k * L ≤ 1 := by rwa [le_div_iff₀ hL] at h1
    nlinarith
  set S := ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2) with hSdef
  have hS : 0 < S := by
    obtain ⟨k, hk1, hkN, hlt⟩ := hγstrict
    apply Finset.sum_pos' ha0
    refine ⟨k, Finset.mem_Icc.2 ⟨hk1, hkN⟩, ?_⟩
    have h2 := hγpos k hk1 hkN
    have h3 : γ k * L < 1 := by rwa [lt_div_iff₀ hL] at hlt
    nlinarith
  have hgsm : ∀ k, 1 ≤ k → k ≤ N → StronglyMeasurable (gXtilde k) := by
    intro k hk1 hkN
    have e : gXtilde k = fun ω => (1 / γ k) • (x k ω - x (k + 1) ω) := by
      funext ω; rw [hgXtilde k hk1 hkN ω, hxNext k hk1 hkN ω]
    rw [e]
    exact (((hxMeas k hk1).mono (𝒢.le _)).sub
      ((hxMeas (k + 1) (by omega)).mono (𝒢.le _))).const_smul _
  have hφm : ∀ k : ℕ, Measurable (fun ω => if R ω = k then (1:ℝ) else 0) := by
    intro k
    exact (measurable_from_nat (f := fun n : ℕ => if n = k then (1:ℝ) else 0)).comp hRmeas
  -- pointwise decomposition of ‖gXtildeR‖²
  have hdecomp : ∀ ω, ‖gXtildeR ω‖ ^ 2 =
      ∑ k ∈ Finset.Icc 1 N, (if R ω = k then (1:ℝ) else 0) * ‖gXtilde k ω‖ ^ 2 := by
    intro ω
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_Icc.2 (hRsupp ω)), hgXtildeR ω]
  have hterm_int : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => (if R ω = k then (1:ℝ) else 0) * ‖gXtilde k ω‖ ^ 2) P := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    refine Integrable.mono' hgXtildeRInt
      ((hφm k).aestronglyMeasurable.mul ((hgsm k hk1 hkN).norm.pow 2).aestronglyMeasurable) ?_
    filter_upwards with ω
    by_cases hR : R ω = k
    · simp [hR, hgXtildeR ω]
    · simp [hR]
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      ∫ ω, (if R ω = k then (1:ℝ) else 0) * ‖gXtilde k ω‖ ^ 2 ∂P
        = PR k * ∫ ω, ‖gXtilde k ω‖ ^ 2 ∂P := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have hind : ProbabilityTheory.IndepFun (fun ω => if R ω = k then (1:ℝ) else 0)
        (fun ω => ‖gXtilde k ω‖ ^ 2) P :=
      (hRindep k hk1 hkN).comp (measurable_from_nat (f := fun n : ℕ => if n = k then (1:ℝ) else 0))
        ((continuous_norm.pow 2).measurable)
    have hmul := hind.integral_mul_eq_mul_integral (hφm k).aestronglyMeasurable
      ((hgsm k hk1 hkN).norm.pow 2).aestronglyMeasurable
    have hPRnn : 0 ≤ PR k := by
      rw [hPR k hk1 hkN]; exact div_nonneg (ha0 k hk) hS.le
    have hind1 : ∫ ω, (if R ω = k then (1:ℝ) else 0) ∂P = PR k := by
      have e : (fun ω => if R ω = k then (1:ℝ) else 0) = Set.indicator {ω | R ω = k} 1 := by
        funext ω; simp [Set.indicator_apply]
      rw [e]
      refine (integral_indicator_one
        (hRmeas (measurableSet_singleton k) : MeasurableSet {ω | R ω = k})).trans ?_
      rw [measureReal_def]
      show (P {ω | R ω = k}).toReal = PR k
      rw [hRlaw k hk1 hkN, ENNReal.toReal_ofReal hPRnn]
    have : ∫ ω, (if R ω = k then (1:ℝ) else 0) * ‖gXtilde k ω‖ ^ 2 ∂P
        = ∫ ω, ((fun ω => if R ω = k then (1:ℝ) else 0) * (fun ω => ‖gXtilde k ω‖ ^ 2)) ω ∂P := rfl
    rw [this, hmul, hind1]
  have hF_int : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => (γ k - L * γ k ^ 2) * ‖gXtilde k ω‖ ^ 2) P := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    refine Integrable.mono' (integrable_const C)
      (((hgsm k hk1 hkN).norm.pow 2).const_mul _).aestronglyMeasurable ?_
    filter_upwards [hbound] with ω hω
    have hnn : 0 ≤ (γ k - L * γ k ^ 2) * ‖gXtilde k ω‖ ^ 2 :=
      mul_nonneg (ha0 k hk) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine le_trans ?_ hω
    exact Finset.single_le_sum (f := fun k => (γ k - L * γ k ^ 2) * ‖gXtilde k ω‖ ^ 2)
      (fun j hj => mul_nonneg (ha0 j hj) (by positivity)) hk
  have hmain : S * ∫ ω, ‖gXtildeR ω‖ ^ 2 ∂P ≤ C := by
    have e1 : ∫ ω, ‖gXtildeR ω‖ ^ 2 ∂P
        = ∑ k ∈ Finset.Icc 1 N, PR k * ∫ ω, ‖gXtilde k ω‖ ^ 2 ∂P := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hdecomp), integral_finsetSum _ hterm_int]
      exact Finset.sum_congr rfl hterm
    have e2 : S * ∑ k ∈ Finset.Icc 1 N, PR k * ∫ ω, ‖gXtilde k ω‖ ^ 2 ∂P
        = ∫ ω, ∑ k ∈ Finset.Icc 1 N, (γ k - L * γ k ^ 2) * ‖gXtilde k ω‖ ^ 2 ∂P := by
      rw [integral_finsetSum _ hF_int, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k hk
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
      rw [integral_const_mul, hPR k hk1 hkN, ← mul_assoc, mul_div_cancel₀ _ hS.ne']
    rw [e1, e2]
    have := integral_mono_ae (integrable_finsetSum _ hF_int) (integrable_const C) hbound
    simpa using this
  have hLD : L * DΨ ^ 2 = C := by
    rw [hDΨ, Real.sq_sqrt (div_nonneg hC0 hL.le)]
    field_simp
  have hT : 0 ≤ ∑ k ∈ Finset.Icc 1 N, (γ k / mBatch k) := by
    apply Finset.sum_nonneg
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    exact div_nonneg (hγpos k hk1 hkN).le (hmBatch k hk1 hkN).le
  rw [hLD, le_div_iff₀ hS]
  nlinarith [mul_nonneg (sq_nonneg σ) hT]
