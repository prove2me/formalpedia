-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.nonconvex_md_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:48:27.74371+00:00
-- url     : https://prove2.me/submissions/e2f32ca7-2d46-4e5a-b243-ccea13cb825f

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox Filter Topology

namespace GP88

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma three_point {X : Set E} (ν : DistanceGeneratingFunction X) (x xp u : E) :
    ν.V x u - ν.V xp u - ν.V x xp = ν.dω xp (u - xp) - ν.dω x (u - xp) := by
  simp only [DistanceGeneratingFunction.V]
  have : u - x = (u - xp) + (xp - x) := by abel
  rw [this, map_add]; ring

lemma slope_lim {X : Set E} (hXconv : Convex ℝ X) (ν : DistanceGeneratingFunction X)
    {xp u : E} (hxp : xp ∈ X) (hu : u ∈ X) :
    Tendsto (fun t : ℝ => t⁻¹ * (ν.ω (xp + t • (u - xp)) - ν.ω xp)) (𝓝[Set.Ioc 0 1] 0)
      (𝓝 (ν.dω xp (u - xp))) := by
  have hmap : Set.MapsTo (fun t : ℝ => xp + t • (u - xp)) (Set.Icc 0 1) X := by
    intro t ht
    have := hXconv.add_smul_sub_mem hxp hu ht
    simpa using this
  have hl : HasDerivWithinAt (fun t : ℝ => xp + t • (u - xp)) (u - xp) (Set.Icc 0 1) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const (u - xp)).const_add xp
    simpa using this.hasDerivWithinAt
  have hd : HasDerivWithinAt (fun t : ℝ => ν.ω (xp + t • (u - xp))) (ν.dω xp (u - xp))
      (Set.Icc 0 1) 0 := by
    have h0 : HasFDerivWithinAt ν.ω (ν.dω xp) X (xp + (0:ℝ) • (u - xp)) := by
      simpa using ν.hasFDerivWithinAt xp hxp
    exact h0.comp_hasDerivWithinAt 0 hl hmap
  have := hasDerivWithinAt_iff_tendsto_slope.1 hd
  have hs : Set.Icc (0:ℝ) 1 \ {0} = Set.Ioc 0 1 := by
    ext t; simp only [Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm h3), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1.ne'⟩
  rw [hs] at this
  refine this.congr (fun t => ?_)
  simp [slope_def_field, div_eq_inv_mul]

end GP88

theorem GP88.gp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * ν.V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * ν.V x u + h u) :
    ∀ u ∈ X, ⟪g, xPlus⟫ + h xPlus + (1 / γ) * ν.V x xPlus ≤
      ⟪g, u⟫ + h u + (1 / γ) * (ν.V x u - ν.V xPlus u) := by
  intro u hu
  set d := u - xPlus with hd
  -- key directional inequality
  have key : 0 ≤ ⟪g, d⟫ + (h u - h xPlus) + (1 / γ) * (ν.dω xPlus d - ν.dω x d) := by
    have hF : ∀ t ∈ Set.Ioc (0:ℝ) 1, 0 ≤ ⟪g, d⟫ + (h u - h xPlus) +
        (1 / γ) * (t⁻¹ * (ν.ω (xPlus + t • d) - ν.ω xPlus) - ν.dω x d) := by
      rintro t ⟨ht0, ht1⟩
      have hut : xPlus + t • d ∈ X := by
        have := hXconv.add_smul_sub_mem hxPlus hu ⟨ht0.le, ht1⟩; simpa [hd] using this
      have h1 := hmin _ hut
      have hconv : h (xPlus + t • d) ≤ (1 - t) * h xPlus + t * h u := by
        have := hhconv.2 hxPlus hu (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
        have e : (1 - t) • xPlus + t • u = xPlus + t • d := by
          simp only [hd, smul_sub, sub_smul, one_smul]; abel
        simpa [e, smul_eq_mul] using this
      have hV : ν.V x (xPlus + t • d) - ν.V x xPlus =
          ν.ω (xPlus + t • d) - ν.ω xPlus - t * ν.dω x d := by
        simp only [DistanceGeneratingFunction.V]
        have : xPlus + t • d - x = (xPlus - x) + t • d := by abel
        rw [this, map_add, map_smul, smul_eq_mul]; ring
      have hinner : ⟪g, xPlus + t • d⟫ = ⟪g, xPlus⟫ + t * ⟪g, d⟫ := by
        rw [inner_add_right, inner_smul_right]
      have hmain : 0 ≤ t * ⟪g, d⟫ + t * (h u - h xPlus) +
          (1 / γ) * (ν.ω (xPlus + t • d) - ν.ω xPlus - t * ν.dω x d) := by
        rw [← hV]; rw [hinner] at h1
        have : (1 / γ) * ν.V x (xPlus + t • d) - (1 / γ) * ν.V x xPlus
            = (1 / γ) * (ν.V x (xPlus + t • d) - ν.V x xPlus) := by ring
        nlinarith
      have e : ⟪g, d⟫ + (h u - h xPlus) +
          (1 / γ) * (t⁻¹ * (ν.ω (xPlus + t • d) - ν.ω xPlus) - ν.dω x d) =
          t⁻¹ * (t * ⟪g, d⟫ + t * (h u - h xPlus) +
            (1 / γ) * (ν.ω (xPlus + t • d) - ν.ω xPlus - t * ν.dω x d)) := by
        field_simp
      rw [e]; exact mul_nonneg (inv_nonneg.2 ht0.le) hmain
    have hlim : Tendsto (fun t : ℝ => ⟪g, d⟫ + (h u - h xPlus) +
        (1 / γ) * (t⁻¹ * (ν.ω (xPlus + t • d) - ν.ω xPlus) - ν.dω x d)) (𝓝[Set.Ioc 0 1] 0)
        (𝓝 (⟪g, d⟫ + (h u - h xPlus) + (1 / γ) * (ν.dω xPlus d - ν.dω x d))) := by
      have := GP88.slope_lim hXconv ν hxPlus hu
      exact tendsto_const_nhds.add ((this.sub tendsto_const_nhds).const_mul _)
    have : (𝓝[Set.Ioc (0:ℝ) 1] 0).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc (by norm_num)]
      exact ⟨le_rfl, zero_le_one⟩
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hF)
  have htp := GP88.three_point ν x xPlus u
  rw [← hd] at htp
  have hγ' : 0 < 1 / γ := by positivity
  have e : (1 / γ) * (ν.V x u - ν.V xPlus u) =
      (1 / γ) * ν.V x xPlus + (1 / γ) * (ν.dω xPlus d - ν.dω x d) := by
    rw [← htp]; ring
  have hgi : ⟪g, d⟫ = ⟪g, u⟫ - ⟪g, xPlus⟫ := by rw [hd, inner_sub_right]
  rw [e]; linarith

namespace MD88
open scoped RealInnerProductSpace
-- descent lemma along a convex set, from the accepted GhadimiLan2016 theorem_2 solution
lemma descentOn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (L : ℝ) (hL : 0 ≤ L) (Q : Set V) (hQ : Convex ℝ Q)
    (hg : ∀ x ∈ Q, HasGradientWithinAt f (gradf x) Q x)
    (hlip : ∀ x ∈ Q, ∀ y ∈ Q, ‖gradf x - gradf y‖ ≤ L * ‖x - y‖)
    (x y : V) (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤ f x + inner ℝ (gradf x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set h := y - x
  let φ : ℝ → ℝ := fun t => f (x + t • h) - t * inner ℝ (gradf x) h - L / 2 * t ^ 2 * ‖h‖ ^ 2
  have hmaps : Set.MapsTo (fun s : ℝ => x + s • h) (Set.Icc 0 1) Q := by
    intro s hs
    have := hQ hx hy (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hs.1 (by ring)
    convert this using 1
    simp only [h]; module
  have hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt φ (inner ℝ (gradf (x + t • h)) h
      - inner ℝ (gradf x) h - L * t * ‖h‖ ^ 2) (Set.Icc 0 1) t := by
    intro t ht
    have hl : HasDerivWithinAt (fun s : ℝ => x + s • h) h (Set.Icc 0 1) t :=
      ((((hasDerivAt_id t).smul_const h).const_add x).congr_deriv (one_smul ℝ h)).hasDerivWithinAt
    have h1 := (hg _ (hmaps ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t hl hmaps
    rw [InnerProductSpace.toDual_apply_apply] at h1
    have h2 := ((hasDerivAt_id t).mul_const (inner ℝ (gradf x) h)).hasDerivWithinAt
      (s := Set.Icc 0 1)
    have h3 := (((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖h‖ ^ 2)).hasDerivWithinAt
      (s := Set.Icc 0 1)
    exact ((h1.sub h2).sub h3).congr_deriv (by simp only [Nat.cast_ofNat, one_mul]; ring)
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · exact fun t ht => (hd t ht).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t (Set.Ioo_subset_Icc_self ht)).mono (by rw [interior_Icc]; exact Set.Ioo_subset_Icc_self)
    · intro t ht
      rw [interior_Icc] at ht
      have e2 := real_inner_le_norm (gradf (x + t • h) - gradf x) h
      have e3 := hlip (x + t • h) (hmaps (Set.Ioo_subset_Icc_self ht)) x hx
      have e4 : ‖x + t • h - x‖ = t * ‖h‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      rw [e4] at e3
      have e5 := mul_le_mul_of_nonneg_right e3 (norm_nonneg h)
      rw [inner_sub_left] at e2
      nlinarith
  have := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [φ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow, mul_one] at this
  have hy' : x + h = y := by simp [h]
  rw [hy'] at this
  have : (0:ℝ) ^ 2 = 0 := by norm_num
  simp_all
  linarith


lemma V_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Set E}
    (ν : FirstOrderOpt.Prox.DistanceGeneratingFunction X) (a : E) : ν.V a a = 0 := by
  simp [FirstOrderOpt.Prox.DistanceGeneratingFunction.V]

lemma V_ge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Set E}
    (ν : FirstOrderOpt.Prox.DistanceGeneratingFunction X) {a b : E} (ha : a ∈ X) (hb : b ∈ X) :
    (1 / 2) * ‖b - a‖ ^ 2 ≤ ν.V a b := by
  have := ν.strongConvex a ha b hb
  simp only [FirstOrderOpt.Prox.DistanceGeneratingFunction.V]; linarith

end MD88

open FirstOrderOpt.Prox in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X) (L : ℝ) (hL : 0 < L) (fGrad : E → E)
    (hGrad : ∀ x ∈ X, HasGradientWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → E) (γ : ℕ → ℝ) (gX : ℕ → E)
    (hx : ∀ k, x k ∈ X)
    (hxDef : ∀ k, 1 ≤ k → k ≤ N → ∀ u ∈ X,
      ⟪fGrad (x k), x (k + 1)⟫ + (1 / γ k) * ν.V (x k) (x (k + 1)) + h (x (k + 1)) ≤
        ⟪fGrad (x k), u⟫ + (1 / γ k) * ν.V (x k) u + h u)
    (hgX : ∀ k, 1 ≤ k → k ≤ N → gX k = (1 / γ k) • (x k - x (k + 1)))
    (hγpos : ∀ k, 1 ≤ k → k ≤ N → 0 < γ k) (hγub : ∀ k, 1 ≤ k → k ≤ N → γ k ≤ 2 / L)
    (hγstrict : ∃ k, 1 ≤ k ∧ k ≤ N ∧ γ k < 2 / L)
    (R : ℕ) (hR : 1 ≤ R ∧ R ≤ N) (hRmin : ∀ k, 1 ≤ k → k ≤ N → ‖gX R‖ ≤ ‖gX k‖)
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f (x 1) + h (x 1) - ΨStar) / L)) :
    ‖gX R‖ ^ 2 ≤ (L * DΨ ^ 2) / ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2 / 2) := by
  set Ψ : E → ℝ := fun z => f z + h z with hΨ
  set c : ℕ → ℝ := fun k => γ k - L * (γ k) ^ 2 / 2 with hc
  -- one step
  have step : ∀ k, 1 ≤ k → k ≤ N → c k * ‖gX k‖ ^ 2 ≤ Ψ (x k) - Ψ (x (k + 1)) := by
    intro k hk1 hkN
    have hγk := hγpos k hk1 hkN
    have tp := GP88.gp X hXconv hXclosed h hhconv ν (x k) (x (k + 1)) (fGrad (x k)) (γ k) hγk
      (hx k) (hx (k + 1)) (hxDef k hk1 hkN) (x k) (hx k)
    rw [MD88.V_self] at tp
    have v1 := MD88.V_ge ν (hx k) (hx (k + 1))
    have v2 := MD88.V_ge ν (hx (k + 1)) (hx k)
    have hdesc := MD88.descentOn f fGrad L hL.le X hXconv hGrad hSmooth (x k) (x (k + 1))
      (hx k) (hx (k + 1))
    set d := x (k + 1) - x k with hd
    have hnd : ‖x k - x (k + 1)‖ = ‖d‖ := by rw [hd, norm_sub_rev]
    rw [hnd] at v2
    have hinner : ⟪fGrad (x k), d⟫ = ⟪fGrad (x k), x (k + 1)⟫ - ⟪fGrad (x k), x k⟫ := by
      rw [hd, inner_sub_right]
    have hg : ‖gX k‖ = ‖d‖ / γ k := by
      rw [hgX k hk1 hkN, norm_smul, hnd, Real.norm_of_nonneg (by positivity)]; ring
    have hinv : 0 < 1 / γ k := by positivity
    -- combine: ⟨∇f, d⟩ + h(x_{k+1}) - h(x_k) ≤ -(1/γ)‖d‖²
    have hA : ⟪fGrad (x k), d⟫ + h (x (k + 1)) - h (x k) ≤ -(1 / γ k) * ‖d‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left (add_le_add v1 v2) hinv.le
      nlinarith
    have hB : Ψ (x (k + 1)) ≤ Ψ (x k) - (1 / γ k - L / 2) * ‖d‖ ^ 2 := by
      simp only [hΨ]; nlinarith
    rw [hg]
    have e : c k * (‖d‖ / γ k) ^ 2 = (1 / γ k - L / 2) * ‖d‖ ^ 2 := by
      simp only [hc]; field_simp
    rw [e]; linarith
  -- telescoping
  have tele : ∀ n, 1 ≤ n → n ≤ N →
      ∑ k ∈ Finset.Icc 1 n, c k * ‖gX k‖ ^ 2 ≤ Ψ (x 1) - Ψ (x (n + 1)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro h1; simpa using step 1 le_rfl h1
    | succ n hn ih =>
      intro hnN
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := step (n + 1) (by omega) hnN
      have := ih (by omega)
      linarith
  have hT := tele N hN le_rfl
  have hlow : ΨStar ≤ Ψ (x (N + 1)) := hΨStar.1 ⟨_, hx (N + 1), rfl⟩
  have hlow1 : ΨStar ≤ Ψ (x 1) := hΨStar.1 ⟨_, hx 1, rfl⟩
  have hc0 : ∀ k ∈ Finset.Icc 1 N, 0 ≤ c k := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    have h1 := hγpos k hk1 hkN; have h2 := hγub k hk1 hkN
    have : L * γ k ≤ 2 := by rw [le_div_iff₀ hL] at h2; linarith
    simp only [hc]; nlinarith
  have hS : 0 < ∑ k ∈ Finset.Icc 1 N, c k := by
    obtain ⟨k, hk1, hkN, hk⟩ := hγstrict
    have hkm : k ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨hk1, hkN⟩
    have hpos : 0 < c k := by
      have h1 := hγpos k hk1 hkN
      have : L * γ k < 2 := by rw [lt_div_iff₀ hL] at hk; linarith
      simp only [hc]; nlinarith
    calc 0 < c k := hpos
      _ ≤ _ := Finset.single_le_sum hc0 hkm
  have hmin : ‖gX R‖ ^ 2 * ∑ k ∈ Finset.Icc 1 N, c k ≤ ∑ k ∈ Finset.Icc 1 N, c k * ‖gX k‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    have := hRmin k hk1 hkN
    have h2 : ‖gX R‖ ^ 2 ≤ ‖gX k‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    have := hc0 k hk
    nlinarith
  have hD : L * DΨ ^ 2 = Ψ (x 1) - ΨStar := by
    rw [hDΨ, Real.sq_sqrt (div_nonneg (by simp only [hΨ] at hlow1; linarith) hL.le)]
    field_simp
    rfl
  rw [hD, le_div_iff₀ hS]
  linarith
