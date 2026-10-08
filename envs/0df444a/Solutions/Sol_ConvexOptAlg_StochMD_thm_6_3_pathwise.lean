-- Prove2me | solution 1 for ConvexOptAlg.StochMD.thm_6_3_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:04:16.370206+00:00
-- url     : https://prove2.me/submissions/9b4ff37f-1218-454e-8adc-2a2d03f5c2bc

import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs

set_option autoImplicit false

/-- Descent lemma on a convex set from a within-set derivative with Lipschitz gradient. -/
theorem f7b0f506_descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
theorem f7b0f506_convex_fo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
theorem f7b0f506_mirror_fo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
    have hfo := f7b0f506_mirror_fo X D hXconv hXD hXDne Φ Φ' hDopen hDconv hΦd (1 / L) xs xs1 g
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
    have hdesc := f7b0f506_descent X hXconv f f' β hfd hlip xs xs1 hxs.1 hxs1.1
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
  · have hc := f7b0f506_convex_fo X hXconv f (f' xs) hf xs xstar hxs.1 hxstar (hfd xs hxs.1)
    simp only [ContinuousLinearMap.sub_apply]
    linarith
