-- Prove2me | solution 1 for ConvexOptAlg.StochMD.theorem_6_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:14:56.501699+00:00
-- url     : https://prove2.me/submissions/d27e74e0-8cac-4886-89a2-a7dffc8ed9bb

import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs

set_option autoImplicit false

/-- Descent lemma on a convex set from a within-set derivative with Lipschitz gradient. -/
theorem afecad10_descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hX : Convex ℝ X) (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ)
    (hd : ∀ x ∈ X, HasFDerivWithinAt f (f' x) X x)
    (hlip : ∀ x ∈ X, ∀ y ∈ X, ‖f' x - f' y‖ ≤ β * ‖x - y‖)
    (a b : E) (ha : a ∈ X) (hb : b ∈ X) :
    f b ≤ f a + f' a (b - a) + β / 2 * ‖b - a‖ ^ 2 := by
  set v := b - a with hv
  let p : ℝ → E := fun s => a + s • v
  have hpX : ∀ s ∈ Set.Icc (0:ℝ) 1, p s ∈ X := fun s hs => hX.add_smul_sub_mem ha hb hs
  let G : ℝ → ℝ := fun s => f (p s) - f a - s * f' a v - β / 2 * s ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt G
      (f' (p s) v - f' a v - β * s * ‖v‖ ^ 2) (Set.Icc 0 1) s := by
    intro s hs
    have hpd : HasDerivWithinAt p v (Set.Icc 0 1) s := by
      have := (((hasDerivAt_id s).smul_const v).const_add a).hasDerivWithinAt (s := Set.Icc 0 1)
      simpa [p] using this
    have h1 : HasDerivWithinAt (fun s => f (p s)) (f' (p s) v) (Set.Icc 0 1) s :=
      (hd (p s) (hpX s hs)).comp_hasDerivWithinAt s hpd (fun t ht => hpX t ht)
    have h2 : HasDerivWithinAt (fun s : ℝ => s * f' a v) (f' a v) (Set.Icc 0 1) s := by
      simpa using ((hasDerivAt_id s).mul_const (f' a v)).hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun s : ℝ => β / 2 * s ^ 2 * ‖v‖ ^ 2) (β * s * ‖v‖ ^ 2)
        (Set.Icc 0 1) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
      exact (this.congr_deriv (by push_cast; ring)).hasDerivWithinAt
    exact ((h1.sub_const (f a)).sub h2).sub h3
  have hnonpos : ∀ s ∈ Set.Icc (0:ℝ) 1, f' (p s) v - f' a v - β * s * ‖v‖ ^ 2 ≤ 0 := by
    intro s hs
    have hle := hlip (p s) (hpX s hs) a ha
    have hps : p s - a = s • v := by simp [p]
    rw [hps, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at hle
    have hop : (f' (p s) - f' a) v ≤ ‖f' (p s) - f' a‖ * ‖v‖ :=
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using (f' (p s) - f' a).le_opNorm v)
    rw [ContinuousLinearMap.sub_apply] at hop
    have : ‖f' (p s) - f' a‖ * ‖v‖ ≤ β * (s * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    nlinarith
  have hanti : AntitoneOn G (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro s hs; exact (hderiv s hs).continuousWithinAt
    · intro s hs
      exact (hderiv s (interior_subset hs)).mono interior_subset
    · intro s hs
      exact hnonpos s (interior_subset hs)
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have hp0 : p 0 = a := by simp [p]
  have hp1 : p 1 = b := by simp [p, v]
  simp only [G, hp0, hp1] at h01
  nlinarith

/-- First-order condition for a convex function differentiable within its convex domain. -/
theorem afecad10_convex_fo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hX : Convex ℝ X) (f : E → ℝ) (f' : E →L[ℝ] ℝ)
    (hf : ConvexOn ℝ X f) (x y : E) (hx : x ∈ X) (hy : y ∈ X)
    (hd : HasFDerivWithinAt f f' X x) :
    f x + f' (y - x) ≤ f y := by
  set v := y - x with hv
  let p : ℝ → E := fun s => x + s • v
  have hpX : ∀ s ∈ Set.Icc (0:ℝ) 1, p s ∈ X := fun s hs => hX.add_smul_sub_mem hx hy hs
  let φ : ℝ → ℝ := fun s => f (p s) - s * (f y - f x)
  have hmax : IsMaxOn φ (Set.Icc 0 1) 0 := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    show φ s ≤ φ 0
    simp only [φ]
    have hp0 : p 0 = x := by simp [p]
    rw [hp0]
    have h := hf.2 hx hy (show (0:ℝ) ≤ 1 - s by linarith) hs0 (show 1 - s + s = 1 by ring)
    have heq : (1 - s) • x + s • y = p s := by
      simp only [p, v, smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at h
    nlinarith
  have hpd : HasDerivWithinAt p v (Set.Icc 0 1) 0 := by
    have := (((hasDerivAt_id (0:ℝ)).smul_const v).const_add x).hasDerivWithinAt
      (s := Set.Icc 0 1)
    simpa [p] using this
  have hp0 : p 0 = x := by simp [p]
  have h1 : HasDerivWithinAt (fun s => f (p s)) (f' v) (Set.Icc 0 1) 0 := by
    have hd' : HasFDerivWithinAt f f' X (p 0) := by rw [hp0]; exact hd
    exact hd'.comp_hasDerivWithinAt (0:ℝ) hpd (fun t ht => hpX t ht)
  have h2 : HasDerivWithinAt φ (f' v - (f y - f x)) (Set.Icc 0 1) 0 := by
    exact h1.sub (hasDerivAt_mul_const (f y - f x)).hasDerivWithinAt
  have hcone : (1:ℝ) ∈ posTangentConeAt (Set.Icc (0:ℝ) 1) 0 := by
    have := sub_mem_posTangentConeAt_of_segment_subset (s := Set.Icc (0:ℝ) 1) (x := 0) (y := 1)
      (by rw [segment_eq_Icc zero_le_one])
    simpa using this
  have := hmax.localize.hasFDerivWithinAt_nonpos h2.hasFDerivWithinAt hcone
  simp at this
  linarith

/-- First-order optimality of the mirror step, valid on all of `X`. -/
theorem afecad10_mirror_fo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D) (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hDopen : IsOpen D) (hDconv : Convex ℝ D)
    (hΦd : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x)
    (γ : ℝ) (xs xs1 : E) (g : E →L[ℝ] ℝ) (hxs1 : xs1 ∈ X ∩ D)
    (hstep : ∀ z ∈ X ∩ D,
      γ * g xs1 + ConvexOptAlg.StochMD.bregman Φ Φ' xs1 xs ≤
        γ * g z + ConvexOptAlg.StochMD.bregman Φ Φ' z xs)
    (xstar : E) (hxstar : xstar ∈ X) :
    0 ≤ γ * g (xstar - xs1) + (Φ' xs1 - Φ' xs) (xstar - xs1) := by
  set L : E →L[ℝ] ℝ := γ • g + (Φ' xs1 - Φ' xs) with hL
  have hLapp : ∀ w, L w = γ * g w + (Φ' xs1 - Φ' xs) w := by
    intro w; simp [L]
  -- the minimised function and its derivative
  let h : E → ℝ := fun z => γ * g z + (Φ z - Φ xs - (Φ' xs z - Φ' xs xs))
  have hh : HasFDerivAt h L xs1 := by
    have := (g.hasFDerivAt.const_mul γ).add
      (((hΦd xs1 hxs1.2).sub_const (Φ xs)).sub ((Φ' xs).hasFDerivAt.sub_const (Φ' xs xs)))
    exact this
  have hbr : ∀ z, γ * g z + ConvexOptAlg.StochMD.bregman Φ Φ' z xs = h z := by
    intro z; simp [h, ConvexOptAlg.StochMD.bregman, map_sub]
  have hmin : IsMinOn h (X ∩ D) xs1 := by
    intro z hz
    simp only [Set.mem_setOf_eq]
    rw [← hbr, ← hbr]; exact hstep z hz
  have hS : ∀ z ∈ X ∩ D, 0 ≤ L (z - xs1) := by
    intro z hz
    apply hmin.localize.hasFDerivWithinAt_nonneg hh.hasFDerivWithinAt
    exact sub_mem_posTangentConeAt_of_segment_subset
      ((hXconv.inter hDconv).segment_subset hxs1 hz)
  have hclosed : IsClosed {z : E | 0 ≤ L (z - xs1)} :=
    isClosed_le continuous_const (L.continuous.comp (continuous_id.sub continuous_const))
  have hcl : xstar ∈ closure (X ∩ D) := by
    obtain ⟨q, hq⟩ := hXDne
    let c : ℝ → E := fun t => xstar + t • (q - xstar)
    have hc : Filter.Tendsto c (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds xstar) := by
      have : Continuous c := continuous_const.add (continuous_id.smul continuous_const)
      have h0 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa [c] using h0
    apply mem_closure_of_tendsto hc
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    refine ⟨hXconv.add_smul_sub_mem hxstar hq.1 ⟨ht.1.le, ht.2.le⟩, ?_⟩
    have := hDconv.add_smul_sub_mem_interior' (hXD hxstar) (by rw [hDopen.interior_eq]; exact hq.2)
      ⟨ht.1, ht.2.le⟩
    rwa [hDopen.interior_eq] at this
  have := closure_minimal hS hclosed hcl
  simp only [Set.mem_setOf_eq, hLapp] at this
  exact this

open ConvexOptAlg.StochMD in
theorem afecad10_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D) (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (hΦsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsSmoothWRT X f f' β)
    (η : ℝ) (hη : 0 < η)
    (xs xs1 : E) (g : E →L[ℝ] ℝ) (hxs : xs ∈ X ∩ D) (hxs1 : xs1 ∈ X ∩ D)
    (hstep : ∀ z ∈ X ∩ D,
      1 / (β + 1 / η) * g xs1 + bregman Φ Φ' xs1 xs ≤ 1 / (β + 1 / η) * g z + bregman Φ Φ' z xs)
    (xstar : E) (hxstar : xstar ∈ X) :
    f xs1 ≤ f xs + g (xstar - xs) +
        (β + 1 / η) * (bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1) +
        η / 2 * ‖f' xs - g‖ ^ 2 ∧
      f xs + g (xstar - xs) +
          (β + 1 / η) * (bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1) +
          η / 2 * ‖f' xs - g‖ ^ 2 ≤
        f xstar + (g - f' xs) (xstar - xs) +
          (β + 1 / η) * (bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1) +
          η / 2 * ‖f' xs - g‖ ^ 2 := by
  obtain ⟨hDopen, hDconv, _, hΦd, _, _⟩ := hΦ
  obtain ⟨hfd, hlip⟩ := hsmooth
  refine ⟨?_, ?_⟩
  · set L := β + 1 / η with hLdef
    have hLpos : 0 < L := by positivity
    have hfo := afecad10_mirror_fo X D hXconv hXD hXDne Φ Φ' hDopen hDconv hΦd (1 / L) xs xs1 g
      hxs1 hstep xstar hxstar
    have h3 : (Φ' xs1 - Φ' xs) (xstar - xs1) =
        bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1 - bregman Φ Φ' xs1 xs := by
      simp only [bregman, ContinuousLinearMap.sub_apply, map_sub]; ring
    rw [h3] at hfo
    have hfo' : 0 ≤ g (xstar - xs1) + L * (bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1 -
        bregman Φ Φ' xs1 xs) := by
      have := mul_nonneg hLpos.le hfo
      have e : L * (1 / L * g (xstar - xs1) + (bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1 -
          bregman Φ Φ' xs1 xs)) = g (xstar - xs1) + L * (bregman Φ Φ' xstar xs -
          bregman Φ Φ' xstar xs1 - bregman Φ Φ' xs1 xs) := by
        field_simp
      linarith
    have hsc := hΦsc xs hxs xs1 hxs1
    have hD1 : 1 / 2 * ‖xs1 - xs‖ ^ 2 ≤ bregman Φ Φ' xs1 xs := by
      have e : ‖xs - xs1‖ = ‖xs1 - xs‖ := norm_sub_rev _ _
      simp only [bregman]
      rw [e] at hsc
      have : Φ' xs (xs - xs1) = - Φ' xs (xs1 - xs) := by
        rw [← map_neg, neg_sub]
      linarith
    have hdesc := afecad10_descent X hXconv f f' β hfd hlip xs xs1 hxs.1 hxs1.1
    set r := ‖xs1 - xs‖
    set a := ‖f' xs - g‖
    have hcs : (f' xs - g) (xs1 - xs) ≤ a * r :=
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using (f' xs - g).le_opNorm (xs1 - xs))
    rw [ContinuousLinearMap.sub_apply] at hcs
    have ham : a * r ≤ η / 2 * a ^ 2 + 1 / (2 * η) * r ^ 2 := by
      have key : η / 2 * a ^ 2 + 1 / (2 * η) * r ^ 2 - a * r = (η * a - r) ^ 2 / (2 * η) := by
        field_simp; ring
      have : 0 ≤ (η * a - r) ^ 2 / (2 * η) := by positivity
      linarith
    have hgsplit : g (xs1 - xs) = g (xstar - xs) - g (xstar - xs1) := by
      rw [← map_sub]; congr 1; abel
    have hLD : L * (1 / 2 * r ^ 2) ≤ L * bregman Φ Φ' xs1 xs :=
      mul_le_mul_of_nonneg_left hD1 hLpos.le
    have hL2 : L * (1 / 2 * r ^ 2) = β / 2 * r ^ 2 + 1 / (2 * η) * r ^ 2 := by
      rw [hLdef]; ring
    nlinarith
  · have hc := afecad10_convex_fo X hXconv f (f' xs) hf xs xstar hxs.1 hxstar (hfd xs hxs.1)
    simp only [ContinuousLinearMap.sub_apply]
    linarith

/-- Bregman telescoping bound, valid for any comparator in `X`. -/
theorem afecad10_breg_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D) (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hDopen : IsOpen D) (hDconv : Convex ℝ D)
    (hΦd : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x)
    (hΦsc : ConvexOptAlg.StochMD.IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    (x₁ : E) (hx₁ : x₁ ∈ X ∩ D) (hmin : ∀ z ∈ X ∩ D, Φ x₁ ≤ Φ z)
    (R : ℝ) (hR : ∀ z ∈ X ∩ D, Φ z - Φ x₁ ≤ R ^ 2)
    (y : E) (hy : y ∈ X ∩ D) (xstar : E) (hxstar : xstar ∈ X) :
    ConvexOptAlg.StochMD.bregman Φ Φ' xstar x₁ - ConvexOptAlg.StochMD.bregman Φ Φ' xstar y
      ≤ R ^ 2 := by
  have hS : ∀ z ∈ X ∩ D, Φ y + Φ' y (z - y) - Φ x₁ - Φ' x₁ (z - x₁) ≤ R ^ 2 := by
    intro z hz
    have h1 : 0 ≤ Φ' x₁ (z - x₁) := by
      have hm : IsMinOn Φ (X ∩ D) x₁ := isMinOn_iff.mpr hmin
      exact hm.localize.hasFDerivWithinAt_nonneg (hΦd x₁ hx₁.2).hasFDerivWithinAt
        (sub_mem_posTangentConeAt_of_segment_subset
          ((hXconv.inter hDconv).segment_subset hx₁ hz))
    have h2 := hΦsc y hy z hz
    have h3 : Φ' y (y - z) = - Φ' y (z - y) := by rw [← map_neg, neg_sub]
    have h4 := hR z hz
    have h5 := sq_nonneg ‖y - z‖
    linarith
  have hclosed : IsClosed {z : E | Φ y + Φ' y (z - y) - Φ x₁ - Φ' x₁ (z - x₁) ≤ R ^ 2} := by
    apply isClosed_le _ continuous_const
    fun_prop
  have hcl : xstar ∈ closure (X ∩ D) := by
    obtain ⟨q, hq⟩ := hXDne
    let c : ℝ → E := fun t => xstar + t • (q - xstar)
    have hc : Filter.Tendsto c (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds xstar) := by
      have : Continuous c := continuous_const.add (continuous_id.smul continuous_const)
      have h0 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa [c] using h0
    apply mem_closure_of_tendsto hc
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    refine ⟨hXconv.add_smul_sub_mem hxstar hq.1 ⟨ht.1.le, ht.2.le⟩, ?_⟩
    have := hDconv.add_smul_sub_mem_interior' (hXD hxstar) (by rw [hDopen.interior_eq]; exact hq.2)
      ⟨ht.1, ht.2.le⟩
    rwa [hDopen.interior_eq] at this
  have h' : Φ y + Φ' y (xstar - y) - Φ x₁ - Φ' x₁ (xstar - x₁) ≤ R ^ 2 :=
    closure_minimal hS hclosed hcl
  simp only [ConvexOptAlg.StochMD.bregman]
  linarith

theorem afecad10_alg (β R σ t u : ℝ) (hR : 0 < R) (hσ : 0 < σ) (ht : 0 < t) (hu : 0 < u)
    (hu2 : u ^ 2 = 2 / t) :
    (1 / t) * ((β + 1 / (R / σ * u)) * R ^ 2 + (R / σ * u) / 2 * (t * σ ^ 2)) =
      R * σ * u + β * R ^ 2 / t := by
  have htu : t = 2 / u ^ 2 := by
    field_simp at hu2 ⊢; linarith
  subst htu
  field_simp
  ring

open ConvexOptAlg.StochMD MeasureTheory in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X D : Set E) (hXcpt : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (hΦsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    (x₁ : E) (R : ℝ) (hRpos : 0 < R) (hR : ∀ z ∈ X ∩ D, Φ z - Φ x₁ ≤ R ^ 2)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsSmoothWRT X f f' β)
    (xstar : E) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (σ : ℝ) (hσ : 0 < σ) (x : ℕ → Ω → E) (gt : ℕ → Ω → E →L[ℝ] ℝ)
    (horacle : IsSmoothStochOracle μ f' σ x gt)
    (t : ℕ) (ht : 1 ≤ t)
    (hrun : IsSMDRun X D Φ Φ' (1 / (β + 1 / (R / σ * Real.sqrt (2 / (t : ℝ))))) x₁ x gt) :
    Integrable (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x (s + 1) ω)) μ ∧
      (∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x (s + 1) ω) ∂μ) - f xstar ≤
        R * σ * Real.sqrt (2 / (t : ℝ)) + β * R ^ 2 / t := by
  have hΦ0 := hΦ
  obtain ⟨hDopen, hDconv, -, hΦd, -, -⟩ := hΦ0
  have htpos : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  set u : ℝ := Real.sqrt (2 / (t : ℝ)) with hudef
  have hupos : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hu2 : u ^ 2 = 2 / t := Real.sq_sqrt (by positivity)
  set η : ℝ := R / σ * u with hηdef
  have hηpos : 0 < η := by positivity
  set L : ℝ := β + 1 / η with hLdef
  have hLpos : 0 < L := by positivity
  -- iterates stay in X ∩ D
  have hmem : ∀ ω, ∀ s, 1 ≤ s → x s ω ∈ X ∩ D := by
    intro ω s hs
    match s, hs with
    | 1, _ =>
      have h := (hrun ω).2.1
      have h' : x 1 ω = x₁ := h
      rw [h']; exact (hrun ω).1.1
    | k + 2, _ => exact ((hrun ω).2.2 (k + 1) (by omega)).1
  -- the pathwise telescoped inequality
  let c : ℕ → Ω → ℝ := fun s ω => (gt s ω - f' (x s ω)) (xstar - x s ω)
  let q : ℕ → Ω → ℝ := fun s ω => ‖gt s ω - f' (x s ω)‖ ^ 2
  have hpath : ∀ ω, ∀ n : ℕ,
      ∑ s ∈ Finset.Icc 1 n, f (x (s + 1) ω) ≤ n * f xstar + ∑ s ∈ Finset.Icc 1 n, c s ω +
        L * (bregman Φ Φ' xstar (x 1 ω) - bregman Φ Φ' xstar (x (n + 1) ω)) +
        η / 2 * ∑ s ∈ Finset.Icc 1 n, q s ω := by
    intro ω n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have hstep : ∀ z ∈ X ∩ D,
          1 / (β + 1 / η) * gt (n + 1) ω (x (n + 1 + 1) ω) + bregman Φ Φ' (x (n + 1 + 1) ω)
            (x (n + 1) ω) ≤
          1 / (β + 1 / η) * gt (n + 1) ω z + bregman Φ Φ' z (x (n + 1) ω) :=
        ((hrun ω).2.2 (n + 1) (by omega)).2
      have hs := afecad10_step X D hXconv hXD hXDne Φ Φ' hΦ hΦsc f f' β hβ hf hsmooth η hηpos
        (x (n + 1) ω) (x (n + 1 + 1) ω) (gt (n + 1) ω) (hmem ω (n + 1) (by omega))
        (hmem ω (n + 1 + 1) (by omega)) hstep xstar hxstar
      have hs' := hs.1.trans hs.2
      have hn : ‖f' (x (n + 1) ω) - gt (n + 1) ω‖ = ‖gt (n + 1) ω - f' (x (n + 1) ω)‖ :=
        norm_sub_rev _ _
      rw [hn] at hs'
      simp only [c, q] at ih ⊢
      have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
      rw [hcast]
      rw [← hLdef] at hs'
      nlinarith
  -- Jensen and the final pathwise bound
  have hwsum : ∑ _s ∈ Finset.Icc 1 t, (1 / (t : ℝ)) = 1 := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    field_simp
    simp
  have havgX : ∀ ω, (1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x (s + 1) ω ∈ X := by
    intro ω
    rw [Finset.smul_sum]
    exact hXconv.sum_mem (fun _ _ => by positivity) hwsum
      (fun s hs => (hmem ω (s + 1) (by omega)).1)
  have hptw : ∀ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x (s + 1) ω) ≤
      f xstar + (1 / (t : ℝ)) * (∑ s ∈ Finset.Icc 1 t, c s ω + L * R ^ 2 +
        η / 2 * ∑ s ∈ Finset.Icc 1 t, q s ω) := by
    intro ω
    have hJ : f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x (s + 1) ω) ≤
        (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, f (x (s + 1) ω) := by
      rw [Finset.smul_sum, Finset.mul_sum]
      have := hf.map_sum_le (t := Finset.Icc 1 t) (w := fun _ => 1 / (t : ℝ))
        (p := fun s => x (s + 1) ω) (fun _ _ => by positivity) hwsum
        (fun s hs => (hmem ω (s + 1) (by simp at hs; omega)).1)
      simpa [smul_eq_mul] using this
    have hP := hpath ω t
    have hx1 : x 1 ω = x₁ := (hrun ω).2.1
    have hB := afecad10_breg_bound X D hXconv hXD hXDne Φ Φ' hDopen hDconv hΦd hΦsc x₁
      (hrun ω).1.1 (hrun ω).1.2 R hR (x (t + 1) ω) (hmem ω (t + 1) (by omega)) xstar hxstar
    rw [hx1] at hP
    have hLB := mul_le_mul_of_nonneg_left hB hLpos.le
    have h2 : ∑ s ∈ Finset.Icc 1 t, f (x (s + 1) ω) ≤ t * f xstar +
        (∑ s ∈ Finset.Icc 1 t, c s ω + L * R ^ 2 + η / 2 * ∑ s ∈ Finset.Icc 1 t, q s ω) := by
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 1 / t by positivity)
    have h4 : (1 / (t : ℝ)) * (t * f xstar + (∑ s ∈ Finset.Icc 1 t, c s ω + L * R ^ 2 +
        η / 2 * ∑ s ∈ Finset.Icc 1 t, q s ω)) = f xstar + (1 / (t : ℝ)) *
        (∑ s ∈ Finset.Icc 1 t, c s ω + L * R ^ 2 + η / 2 * ∑ s ∈ Finset.Icc 1 t, q s ω) := by
      field_simp
    linarith
  -- integrability and expectations
  have hxmeas : ∀ s, 1 ≤ s → Measurable (x s) := fun s hs => (horacle s hs).1
  have hfc : ContinuousOn f X := fun y hy => (hsmooth.1 y hy).continuousWithinAt
  obtain ⟨Cf, hCf⟩ := hXcpt.exists_bound_of_continuousOn hfc
  obtain ⟨M, hM⟩ := hXcpt.isBounded.exists_norm_le
  have havgm : Measurable (fun ω => (1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x (s + 1) ω) := by
    apply Measurable.const_smul
    exact Finset.measurable_sum (f := fun s => x (s + 1)) _
      (fun s hs => hxmeas (s + 1) (by omega))
  have hint : Integrable
      (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x (s + 1) ω)) μ := by
    have hF : Measurable (X.restrict f) := hfc.restrict.measurable
    have hcod : Measurable (fun ω =>
        (⟨(1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x (s + 1) ω, havgX ω⟩ : X)) :=
      havgm.subtype_mk
    have hm' : Measurable (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x (s + 1) ω)) :=
      hF.comp hcod
    exact Integrable.of_bound hm'.aestronglyMeasurable Cf
      (Filter.Eventually.of_forall (fun ω => hCf _ (havgX ω)))
  have hc : ∀ s, 1 ≤ s → Integrable (c s) μ ∧ ∫ ω, c s ω ∂μ = 0 := by
    intro s hs
    obtain ⟨hxm, hgi, hunb, -, -⟩ := horacle s hs
    have hm : MeasurableSpace.comap (x s) ‹MeasurableSpace E› ≤ ‹MeasurableSpace Ω› :=
      hxm.comap_le
    set m := MeasurableSpace.comap (x s) ‹MeasurableSpace E› with hmdef
    have hxs' : StronglyMeasurable[m] (x s) := (comap_measurable (x s)).stronglyMeasurable
    have hv : StronglyMeasurable[m] (fun ω => xstar - x s ω) :=
      stronglyMeasurable_const.sub hxs'
    have hvb : ∀ ω, ‖xstar - x s ω‖ ≤ ‖xstar‖ + M := fun ω =>
      (norm_sub_le _ _).trans (by linarith [hM _ (hmem ω s hs).1])
    have hgv : Integrable (fun ω => gt s ω (xstar - x s ω)) μ := by
      refine Integrable.mono' (hgi.norm.mul_const (‖xstar‖ + M)) ?_ ?_
      · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
          hgi.aestronglyMeasurable (aestronglyMeasurable_const.sub hxm.aestronglyMeasurable)
      · filter_upwards with ω
        exact ((gt s ω).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hvb ω) (norm_nonneg _))
    have hce := condExp_bilin_of_stronglyMeasurable_left (μ := μ) (m := m)
      (ContinuousLinearMap.apply ℝ ℝ) hv (g := gt s) (by simpa using hgv) hgi
    simp only [ContinuousLinearMap.apply_apply] at hce
    have hae : (fun ω => (μ[gt s | m] ω) (xstar - x s ω)) =ᵐ[μ]
        fun ω => f' (x s ω) (xstar - x s ω) := by
      filter_upwards [hunb] with ω hω
      rw [hω]
    have hfi : Integrable (fun ω => f' (x s ω) (xstar - x s ω)) μ :=
      integrable_condExp.congr (hce.trans hae)
    have h1 : ∫ ω, gt s ω (xstar - x s ω) ∂μ = ∫ ω, f' (x s ω) (xstar - x s ω) ∂μ :=
      (integral_condExp hm).symm.trans (integral_congr_ae (hce.trans hae))
    have hceq : c s = fun ω => gt s ω (xstar - x s ω) - f' (x s ω) (xstar - x s ω) := by
      funext ω; simp [c]
    rw [hceq]
    exact ⟨hgv.sub hfi, by rw [integral_sub hgv hfi, h1, sub_self]⟩
  have hq : ∀ s, 1 ≤ s → Integrable (q s) μ ∧ ∫ ω, q s ω ∂μ ≤ σ ^ 2 := by
    intro s hs
    obtain ⟨hxm, -, -, hqi, hvar⟩ := horacle s hs
    have hm : MeasurableSpace.comap (x s) ‹MeasurableSpace E› ≤ ‹MeasurableSpace Ω› :=
      hxm.comap_le
    refine ⟨hqi, ?_⟩
    calc ∫ ω, q s ω ∂μ = ∫ ω, (μ[fun ω => ‖gt s ω - f' (x s ω)‖ ^ 2 |
          MeasurableSpace.comap (x s) ‹MeasurableSpace E›]) ω ∂μ := (integral_condExp hm).symm
      _ ≤ ∫ _ω, σ ^ 2 ∂μ := integral_mono_ae integrable_condExp (integrable_const _) hvar
      _ = σ ^ 2 := by simp
  refine ⟨hint, ?_⟩
  have hsc : Integrable (fun ω => ∑ s ∈ Finset.Icc 1 t, c s ω) μ :=
    integrable_finsetSum _ (fun s hs => (hc s (by simp at hs; omega)).1)
  have hsq : Integrable (fun ω => ∑ s ∈ Finset.Icc 1 t, q s ω) μ :=
    integrable_finsetSum _ (fun s hs => (hq s (by simp at hs; omega)).1)
  have hRHSint : Integrable (fun ω => f xstar + (1 / (t : ℝ)) * (∑ s ∈ Finset.Icc 1 t, c s ω +
      L * R ^ 2 + η / 2 * ∑ s ∈ Finset.Icc 1 t, q s ω)) μ :=
    (integrable_const _).add (((hsc.add (integrable_const _)).add (hsq.const_mul _)).const_mul _)
  have hmono := integral_mono hint hRHSint hptw
  have hIc : ∫ ω, ∑ s ∈ Finset.Icc 1 t, c s ω ∂μ = 0 := by
    rw [integral_finsetSum _ (fun s hs => (hc s (by simp at hs; omega)).1)]
    exact Finset.sum_eq_zero (fun s hs => (hc s (by simp at hs; omega)).2)
  have hIq : ∫ ω, ∑ s ∈ Finset.Icc 1 t, q s ω ∂μ ≤ t * σ ^ 2 := by
    rw [integral_finsetSum _ (fun s hs => (hq s (by simp at hs; omega)).1)]
    calc ∑ s ∈ Finset.Icc 1 t, ∫ ω, q s ω ∂μ ≤ ∑ _s ∈ Finset.Icc 1 t, σ ^ 2 :=
          Finset.sum_le_sum (fun s hs => (hq s (by simp at hs; omega)).2)
      _ = t * σ ^ 2 := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have hcalc : ∫ ω, (f xstar + (1 / (t : ℝ)) * (∑ s ∈ Finset.Icc 1 t, c s ω +
      L * R ^ 2 + η / 2 * ∑ s ∈ Finset.Icc 1 t, q s ω)) ∂μ =
      f xstar + (1 / (t : ℝ)) * (∫ ω, ∑ s ∈ Finset.Icc 1 t, c s ω ∂μ + L * R ^ 2 +
        η / 2 * ∫ ω, ∑ s ∈ Finset.Icc 1 t, q s ω ∂μ) := by
    have i0 : Integrable (fun ω => ∑ s ∈ Finset.Icc 1 t, c s ω + L * R ^ 2) μ :=
      hsc.add (integrable_const _)
    have i2 : Integrable (fun ω => η / 2 * ∑ s ∈ Finset.Icc 1 t, q s ω) μ := hsq.const_mul _
    have i1 : Integrable (fun ω => ∑ s ∈ Finset.Icc 1 t, c s ω + L * R ^ 2 +
        η / 2 * ∑ s ∈ Finset.Icc 1 t, q s ω) μ := i0.add i2
    have i3 : Integrable (fun ω => (1 / (t : ℝ)) * (∑ s ∈ Finset.Icc 1 t, c s ω + L * R ^ 2 +
        η / 2 * ∑ s ∈ Finset.Icc 1 t, q s ω)) μ := i1.const_mul _
    rw [integral_add (integrable_const _) i3, integral_const_mul, integral_add i0 i2,
      integral_add hsc (integrable_const _), integral_const_mul (η / 2)]
    simp
  rw [hcalc, hIc] at hmono
  have hfin := afecad10_alg β R σ t u hRpos hσ htpos hupos hu2
  have hq2 : (1 / (t : ℝ)) * (0 + L * R ^ 2 + η / 2 * ∫ ω, ∑ s ∈ Finset.Icc 1 t, q s ω ∂μ) ≤
      (1 / (t : ℝ)) * (L * R ^ 2 + η / 2 * (t * σ ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_left hIq (show 0 ≤ η / 2 by positivity)
    linarith
  rw [hLdef, hηdef] at hq2
  rw [hηdef] at hmono
  linarith
