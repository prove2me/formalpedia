-- Prove2me | solution 1 for ConvexOptAlg.StochMD.thm_6_3_expected_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:46:56.118016+00:00
-- url     : https://prove2.me/submissions/27e65ce6-4e69-464a-8538-a7858a601193

import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs



namespace ConvexOptAlg.StochMD

open MeasureTheory

lemma smd_descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} (hX : Convex ℝ X) {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {β : ℝ}
    (hs : IsSmoothWRT X f f' β) {a b : E} (ha : a ∈ X) (hb : b ∈ X) :
    f b - f a ≤ f' a (b - a) + β / 2 * ‖b - a‖ ^ 2 := by
  set v := b - a with hv
  let line : ℝ → E := fun t => a + t • v
  have hmaps : Set.MapsTo line (Set.Icc 0 1) X := by
    intro t ht
    have := hX.add_smul_sub_mem ha hb ht
    simpa [line, hv] using this
  let φ : ℝ → ℝ := fun t => f (line t) - t * f' a v - β / 2 * t ^ 2 * ‖v‖ ^ 2
  have hder : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt φ
      (f' (line t) v - f' a v - β * t * ‖v‖ ^ 2) (Set.Icc 0 1) t := by
    intro t ht
    have hl : HasDerivWithinAt line v (Set.Icc 0 1) t := by
      have : HasDerivAt line ((1:ℝ) • v) t := ((hasDerivAt_id t).smul_const v).const_add a
      simpa using this.hasDerivWithinAt
    have h1 := (hs.1 _ (hmaps ht)).comp_hasDerivWithinAt t hl hmaps
    have h2 : HasDerivWithinAt (fun t : ℝ => t * f' a v) (1 * f' a v) (Set.Icc 0 1) t :=
      ((hasDerivAt_id t).mul_const _).hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun t : ℝ => β / 2 * t ^ 2 * ‖v‖ ^ 2)
        (β / 2 * (↑2 * t ^ (2 - 1)) * ‖v‖ ^ 2) (Set.Icc 0 1) t :=
      (((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖v‖ ^ 2)).hasDerivWithinAt
    exact ((h1.sub h2).sub h3).congr_deriv (by simp only [one_mul, Nat.add_one_sub_one, pow_one]; ring)
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro t ht; exact (hder t ht).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht ⊢
      exact (hder t (Set.Ioo_subset_Icc_self ht)).mono Set.Ioo_subset_Icc_self
    · intro t ht
      rw [interior_Icc] at ht
      have hp := hs.2 _ (hmaps (Set.Ioo_subset_Icc_self ht)) _ ha
      have : f' (line t) v - f' a v ≤ β * t * ‖v‖ ^ 2 := by
        calc f' (line t) v - f' a v = (f' (line t) - f' a) v := by simp
          _ ≤ ‖f' (line t) - f' a‖ * ‖v‖ :=
              (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _)
          _ ≤ β * ‖line t - a‖ * ‖v‖ := by gcongr
          _ = β * t * ‖v‖ ^ 2 := by
              simp [line, norm_smul, abs_of_pos ht.1]; ring
      linarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have hva : f' a v = f' a b - f' a a := by rw [hv, map_sub]
  simp [φ, line, hv] at this
  have hn : ‖v‖ = ‖b - a‖ := rfl
  rw [hva, hn]
  linarith

lemma smd_convex_grad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {β : ℝ} (hf : ConvexOn ℝ X f)
    (hs : IsSmoothWRT X f f' β) {y z : E} (hy : y ∈ X) (hz : z ∈ X) :
    f y - f z ≤ f' y (y - z) := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap y z
  have hg : ∀ t : ℝ, g t = y + t • (z - y) := by
    intro t; simp [g, AffineMap.lineMap_apply]; abel
  have hmaps : Set.MapsTo g (Set.Icc 0 1) X := by
    intro t ht; rw [hg]; exact hf.1.add_smul_sub_mem hy hz ht
  have hc : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (f ∘ g) :=
    (hf.comp_affineMap g).subset hmaps (convex_Icc 0 1)
  have hl : HasDerivWithinAt g (z - y) (Set.Icc 0 1) 0 := by
    have : HasDerivAt (fun t : ℝ => y + t • (z - y)) ((1:ℝ) • (z - y)) 0 :=
      ((hasDerivAt_id (0:ℝ)).smul_const (z - y)).const_add y
    have e : (fun t : ℝ => y + t • (z - y)) = g := funext fun t => (hg t).symm
    rw [e] at this; simpa using this.hasDerivWithinAt
  have hg0 : g 0 = y := by simp [hg]
  have hfy : HasFDerivWithinAt f (f' y) X (g 0) := by rw [hg0]; exact hs.1 y hy
  have h1 := hfy.comp_hasDerivWithinAt (0:ℝ) hl hmaps
  have := hc.le_slope_of_hasDerivWithinAt (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one) zero_lt_one h1
  simp [slope, hg] at this
  have e2 : f' y (y - z) = - f' y (z - y) := by
    rw [← map_neg]; congr 1; abel
  rw [e2, map_sub]; linarith

/-- First-order optimality / three-point inequality. -/
lemma smd_three_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X D : Set E} (hX : Convex ℝ X) {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} (hΦ : IsMirrorMap D Φ Φ')
    {γ : ℝ} {g : E →L[ℝ] ℝ} {xs x' : E} (hx' : x' ∈ X ∩ D)
    (hmin : ∀ z ∈ X ∩ D, γ * g x' + bregman Φ Φ' x' xs ≤ γ * g z + bregman Φ Φ' z xs)
    {z : E} (hz : z ∈ X) :
    γ * g (x' - z) ≤ bregman Φ Φ' z xs - bregman Φ Φ' z x' - bregman Φ Φ' x' xs := by
  let h : E → ℝ := fun y => γ * g y + bregman Φ Φ' y xs
  have hd : HasFDerivAt h (γ • g + (Φ' x' - Φ' xs)) x' := by
    have hp := hΦ.2.2.2.1 x' hx'.2
    have := ((g.hasFDerivAt (x := x')).const_mul γ).add
      ((hp.sub_const (Φ xs)).sub ((Φ' xs).hasFDerivAt.sub_const (Φ' xs xs)))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp only [h, bregman, map_sub, Pi.add_apply, Pi.sub_apply]
  have hloc : IsLocalMinOn h X x' := by
    have hD : D ∈ nhds x' := hΦ.1.mem_nhds hx'.2
    show ∀ᶠ y in nhdsWithin x' X, h x' ≤ h y
    filter_upwards [mem_nhdsWithin_of_mem_nhds hD, self_mem_nhdsWithin] with y hyD hyX
    exact hmin y ⟨hyX, hyD⟩
  have hcone : z - x' ∈ posTangentConeAt X x' :=
    sub_mem_posTangentConeAt_of_segment_subset (hX.segment_subset hx'.1 hz)
  have := hloc.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul] at this
  have e1 : g (x' - z) = - g (z - x') := by rw [← map_neg]; congr 1; abel
  rw [e1]
  simp only [bregman, map_sub]
  simp only [map_sub] at this
  linarith

lemma smd_dens {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X D : Set E} (hXconv : Convex ℝ X) (hXD : X ⊆ closure D) (hXDne : (X ∩ D).Nonempty)
    (hDopen : IsOpen D) (hDconv : Convex ℝ D) {ℓ : E →L[ℝ] ℝ} {y : E} {C : ℝ}
    (h : ∀ z ∈ X ∩ D, ℓ (z - y) ≤ C) {z : E} (hz : z ∈ X) : ℓ (z - y) ≤ C := by
  obtain ⟨p, hpX, hpD⟩ := hXDne
  have key : ∀ t ∈ Set.Ioo (0:ℝ) 1, ℓ (z - y) + t * ℓ (p - z) ≤ C := by
    intro t ht
    have hmem : z + t • (p - z) ∈ X ∩ D := by
      refine ⟨hXconv.add_smul_sub_mem hz hpX ⟨ht.1.le, ht.2.le⟩, ?_⟩
      have hpi : p ∈ interior D := by rw [hDopen.interior_eq]; exact hpD
      have := hDconv.add_smul_sub_mem_interior' (hXD hz) hpi ⟨ht.1, ht.2.le⟩
      rwa [hDopen.interior_eq] at this
    have := h _ hmem
    have e : z + t • (p - z) - y = (z - y) + t • (p - z) := by abel
    rw [e, map_add, map_smul, smul_eq_mul] at this
    exact this
  have ht : Filter.Tendsto (fun t : ℝ => ℓ (z - y) + t * ℓ (p - z)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ℓ (z - y) + 0 * ℓ (p - z))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at ht
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht' using key t ht'

lemma smd_step_pt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X D : Set E} (hXconv : Convex ℝ X) {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ}
    (hΦ : IsMirrorMap D Φ Φ') (hΦsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {β η : ℝ} (hf : ConvexOn ℝ X f)
    (hsmooth : IsSmoothWRT X f f' β) (hβ : 0 ≤ β) (hη : 0 < η)
    {g : E →L[ℝ] ℝ} {y y' xstar : E} (hy : y ∈ X ∩ D) (hy' : y' ∈ X ∩ D)
    (hmin : ∀ z ∈ X ∩ D, (1 / (β + 1 / η)) * g y' + bregman Φ Φ' y' y ≤
      (1 / (β + 1 / η)) * g z + bregman Φ Φ' z y)
    (hxstar : xstar ∈ X) :
    f y' - f xstar ≤ (β + 1 / η) * (bregman Φ Φ' xstar y - bregman Φ Φ' xstar y') +
      η * ‖g - f' y‖ ^ 2 / 2 + (f' y - g) (y - xstar) := by
  have hLpos : 0 < β + 1 / η := by positivity
  have h3 := smd_three_point hXconv hΦ hy' hmin hxstar
  have hDsc : 1 / 2 * ‖y' - y‖ ^ 2 ≤ bregman Φ Φ' y' y := by
    have := hΦsc y hy y' hy'
    have e : Φ' y (y - y') = - Φ' y (y' - y) := by rw [← map_neg]; congr 1; abel
    rw [e, norm_sub_rev] at this
    simp only [bregman]; linarith
  have hdesc := smd_descent hXconv hsmooth hy.1 hy'.1
  have hcvx := smd_convex_grad hf hsmooth hy.1 hxstar
  have hg : g (y' - xstar) ≤ (β + 1 / η) * (bregman Φ Φ' xstar y - bregman Φ Φ' xstar y' -
      bregman Φ Φ' y' y) := by
    have := mul_le_mul_of_nonneg_left h3 hLpos.le
    rw [← mul_assoc, mul_one_div_cancel hLpos.ne', one_mul] at this
    exact this
  have hLD := mul_le_mul_of_nonneg_left hDsc hLpos.le
  have hed : (f' y - g) (y' - y) ≤ η / 2 * ‖f' y - g‖ ^ 2 + 1 / (2 * η) * ‖y' - y‖ ^ 2 := by
    have h1 : (f' y - g) (y' - y) ≤ ‖f' y - g‖ * ‖y' - y‖ :=
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact (f' y - g).le_opNorm _)
    have h2 : η / 2 * ‖f' y - g‖ ^ 2 + 1 / (2 * η) * ‖y' - y‖ ^ 2 - ‖f' y - g‖ * ‖y' - y‖ =
        (η * ‖f' y - g‖ - ‖y' - y‖) ^ 2 / (2 * η) := by
      field_simp; ring
    have h4 : 0 ≤ (η * ‖f' y - g‖ - ‖y' - y‖) ^ 2 / (2 * η) := by positivity
    linarith
  have hsplit : f' y (y' - y) + f' y (y - xstar) =
      g (y' - xstar) + (f' y - g) (y' - y) + (f' y - g) (y - xstar) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]; ring
  have hL2 : (β + 1 / η) * (1 / 2 * ‖y' - y‖ ^ 2) =
      β / 2 * ‖y' - y‖ ^ 2 + 1 / (2 * η) * ‖y' - y‖ ^ 2 := by
    field_simp
  have hn : ‖g - f' y‖ = ‖f' y - g‖ := norm_sub_rev _ _
  rw [hn]
  nlinarith

lemma smd_meas_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Ω : Type*} [MeasurableSpace Ω]
    {S : Set E} {h : E → ℝ} (hc : ContinuousOn h S) {x : Ω → E} (hx : Measurable x)
    (hS : ∀ ω, x ω ∈ S) : Measurable (fun ω => h (x ω)) := by
  have h1 : Measurable (fun ω => (⟨x ω, hS ω⟩ : S)) := hx.subtype_mk
  have h2 : Continuous (S.restrict h) := hc.restrict
  exact h2.measurable.comp h1

theorem step_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X D : Set E) (hXcpt : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (hΦsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    (x₁ : E) (R : ℝ) (hR : ∀ z ∈ X ∩ D, Φ z - Φ x₁ ≤ R ^ 2)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsSmoothWRT X f f' β)
    (σ : ℝ) (x : ℕ → Ω → E) (gt : ℕ → Ω → E →L[ℝ] ℝ)
    (horacle : IsSmoothStochOracle μ f' σ x gt)
    (η : ℝ) (hη : 0 < η) (hrun : IsSMDRun X D Φ Φ' (1 / (β + 1 / η)) x₁ x gt)
    (xstar : E) (hxstar : xstar ∈ X) (s : ℕ) (hs : 1 ≤ s) :
    Integrable (fun ω => f (x (s + 1) ω)) μ ∧
      Integrable (fun ω => bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω)) μ ∧
      (∫ ω, f (x (s + 1) ω) ∂μ) - f xstar ≤
        (β + 1 / η) *
            (∫ ω, (bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω)) ∂μ) +
          η * σ ^ 2 / 2 := by
  have hLpos : 0 < β + 1 / η := by positivity
  have hγ : 0 < 1 / (β + 1 / η) := by positivity
  set γ := 1 / (β + 1 / η) with hγdef
  have hΦ0 := hΦ
  obtain ⟨hDopen, hDconv, -, hΦd, -, -⟩ := hΦ0
  -- membership
  have hmemXD : ∀ k, 1 ≤ k → ∀ ω, x k ω ∈ X ∩ D := by
    intro k hk ω
    rcases Nat.lt_or_ge k 2 with h | h
    · have : k = 1 := by omega
      subst this
      have h1 : x 1 ω = x₁ := (hrun ω).2.1
      rw [h1]; exact (hrun ω).1.1
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact ((hrun ω).2.2 j (by omega)).1
  have hmeas : ∀ k, 1 ≤ k → Measurable (x k) := fun k hk => (horacle k hk).1
  -- bounds
  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ X, ‖y - xstar‖ ≤ M := by
    obtain ⟨C, hC⟩ := hXcpt.isBounded.exists_norm_le
    exact ⟨C + ‖xstar‖, fun y hy => (norm_sub_le _ _).trans (by linarith [hC y hy])⟩
  have hM0 : 0 ≤ M := by have := hM xstar hxstar; simp at this; linarith
  have hfc : ContinuousOn f X := fun y hy => (hsmooth.1 y hy).continuousWithinAt
  obtain ⟨Cf, hCf⟩ := hXcpt.exists_bound_of_continuousOn hfc
  have hKf : ∀ y ∈ X, ‖f' y‖ ≤ ‖f' xstar‖ + β * M := by
    intro y hy
    have := hsmooth.2 y hy xstar hxstar
    have h2 : ‖f' y‖ ≤ ‖f' xstar‖ + ‖f' y - f' xstar‖ := by
      have := norm_add_le (f' xstar) (f' y - f' xstar); simp at this; linarith
    nlinarith [hM y hy]
  -- Breg lower bound
  set c0 := Φ xstar - Φ x₁ - R ^ 2 with hc0
  have hBlow : ∀ y ∈ X ∩ D, c0 ≤ bregman Φ Φ' xstar y := by
    intro y hy
    have hd : Φ' y (xstar - y) ≤ Φ x₁ + R ^ 2 - Φ y := by
      refine smd_dens hXconv hXD hXDne hDopen hDconv (fun z hz => ?_) hxstar
      have h1 := hΦsc y hy z hz
      have e : Φ' y (y - z) = - Φ' y (z - y) := by rw [← map_neg]; congr 1; abel
      rw [e] at h1
      have h2 := hR z hz
      nlinarith [sq_nonneg ‖y - z‖]
    simp only [bregman, hc0]; linarith
  -- Breg step bound
  have hBstep : ∀ k, 1 ≤ k → ∀ ω, bregman Φ Φ' xstar (x (k + 1) ω) ≤
      bregman Φ Φ' xstar (x k ω) + γ * (‖gt k ω‖ * M) := by
    intro k hk ω
    have hrk := (hrun ω).2.2 k hk
    have h3 := smd_three_point hXconv hΦ hrk.1 hrk.2 hxstar
    have hy := hmemXD k hk ω
    have hDnn : 0 ≤ bregman Φ Φ' (x (k + 1) ω) (x k ω) := by
      have := hΦsc (x k ω) hy (x (k + 1) ω) hrk.1
      have e : Φ' (x k ω) (x k ω - x (k + 1) ω) = - Φ' (x k ω) (x (k + 1) ω - x k ω) := by
        rw [← map_neg]; congr 1; abel
      rw [e] at this
      simp only [bregman]; nlinarith [sq_nonneg ‖x k ω - x (k + 1) ω‖]
    have hgb : - (gt k ω) (x (k + 1) ω - xstar) ≤ ‖gt k ω‖ * M := by
      have h1 : - (gt k ω) (x (k + 1) ω - xstar) ≤ ‖gt k ω‖ * ‖x (k + 1) ω - xstar‖ :=
        (neg_le_abs _).trans (by rw [← Real.norm_eq_abs]; exact (gt k ω).le_opNorm _)
      exact h1.trans (mul_le_mul_of_nonneg_left (hM _ hrk.1.1) (norm_nonneg _))
    have := mul_le_mul_of_nonneg_left hgb hγ.le
    nlinarith
  have hBup : ∀ k, 1 ≤ k → ∀ ω, bregman Φ Φ' xstar (x k ω) ≤
      bregman Φ Φ' xstar x₁ + γ * M * ∑ j ∈ Finset.Ico 1 k, ‖gt j ω‖ := by
    intro k hk ω
    induction k, hk using Nat.le_induction with
    | base =>
      have h1 : x 1 ω = x₁ := (hrun ω).2.1
      rw [h1]; simp
    | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top hk, mul_add]
      have := hBstep k hk ω
      linarith
  -- measurability of Bregman terms
  have hBmeas : ∀ k, 1 ≤ k → AEStronglyMeasurable (fun ω => bregman Φ Φ' xstar (x k ω)) μ := by
    intro k hk
    have hΦc : ContinuousOn Φ D := fun y hy => (hΦd y hy).continuousAt.continuousWithinAt
    have h1 : Measurable (fun ω => Φ (x k ω)) :=
      smd_meas_comp hΦc (hmeas k hk) (fun ω => (hmemXD k hk ω).2)
    have h2 : (fun ω => Φ' (x k ω)) = fun ω => fderiv ℝ Φ (x k ω) := by
      funext ω; exact ((hΦd _ (hmemXD k hk ω).2).fderiv).symm
    have h3 : AEStronglyMeasurable (fun ω => Φ' (x k ω)) μ := by
      rw [h2]; exact ((measurable_fderiv ℝ Φ).comp (hmeas k hk)).aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun ω => xstar - x k ω) μ :=
      (measurable_const.sub (hmeas k hk)).aestronglyMeasurable
    have h5 : AEStronglyMeasurable (fun ω => Φ' (x k ω) (xstar - x k ω)) μ := by
      have := (ContinuousLinearMap.apply ℝ ℝ (E := E)).aestronglyMeasurable_comp₂ h4 h3
      simpa using this
    have := ((aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => Φ xstar) μ).sub
      h1.aestronglyMeasurable).sub h5
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [bregman, Pi.sub_apply]
  have hgint : ∀ j, 1 ≤ j → Integrable (fun ω => ‖gt j ω‖) μ := fun j hj =>
    (horacle j hj).2.1.norm
  have hBint : ∀ k, 1 ≤ k → Integrable (fun ω => bregman Φ Φ' xstar (x k ω)) μ := by
    intro k hk
    have hS : Integrable (fun ω => |c0| + |bregman Φ Φ' xstar x₁| +
        γ * M * ∑ j ∈ Finset.Ico 1 k, ‖gt j ω‖) μ := by
      refine (integrable_const _).add (Integrable.const_mul ?_ _)
      exact integrable_finset_sum _ (fun j hj => hgint j (Finset.mem_Ico.1 hj).1)
    refine Integrable.mono' hS (hBmeas k hk) (Filter.Eventually.of_forall fun ω => ?_)
    have hl := hBlow _ (hmemXD k hk ω)
    have hu := hBup k hk ω
    have hS0 : 0 ≤ γ * M * ∑ j ∈ Finset.Ico 1 k, ‖gt j ω‖ :=
      mul_nonneg (mul_nonneg hγ.le hM0) (Finset.sum_nonneg fun j _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le c0, abs_nonneg (bregman Φ Φ' xstar x₁)]
    · linarith [le_abs_self (bregman Φ Φ' xstar x₁), abs_nonneg c0]
  -- integrability of f
  have hFint : Integrable (fun ω => f (x (s + 1) ω)) μ := by
    refine Integrable.of_bound (smd_meas_comp hfc (hmeas (s + 1) (by omega))
      (fun ω => (hmemXD (s + 1) (by omega) ω).1)).aestronglyMeasurable Cf
      (Filter.Eventually.of_forall fun ω => hCf _ (hmemXD (s + 1) (by omega) ω).1)
  have hΔint : Integrable (fun ω => bregman Φ Φ' xstar (x s ω) -
      bregman Φ Φ' xstar (x (s + 1) ω)) μ := (hBint s hs).sub (hBint (s + 1) (by omega))
  refine ⟨hFint, hΔint, ?_⟩
  -- oracle facts
  obtain ⟨hxm, hgi, hunb, hVint, hVle⟩ := horacle s hs
  have hmle : MeasurableSpace.comap (x s) (inferInstance : MeasurableSpace E) ≤
      (inferInstance : MeasurableSpace Ω) := hxm.comap_le
  -- variance
  have hV : ∫ ω, ‖gt s ω - f' (x s ω)‖ ^ 2 ∂μ ≤ σ ^ 2 := by
    rw [← integral_condExp hmle]
    calc ∫ ω, (μ[fun ω => ‖gt s ω - f' (x s ω)‖ ^ 2 | MeasurableSpace.comap (x s) (inferInstance : MeasurableSpace E)]) ω ∂μ ≤ ∫ ω, σ ^ 2 ∂μ :=
          integral_mono_ae integrable_condExp (integrable_const _) hVle
      _ = σ ^ 2 := by simp
  -- cross term
  set v : Ω → E := fun ω => x s ω - xstar with hv
  have hvsm : StronglyMeasurable[MeasurableSpace.comap (x s) (inferInstance : MeasurableSpace E)] v := by
    have : Measurable[MeasurableSpace.comap (x s) (inferInstance : MeasurableSpace E)] (x s) := comap_measurable (x s)
    exact (this.sub_const xstar).stronglyMeasurable
  have hvbd : ∀ ω, ‖v ω‖ ≤ M := fun ω => hM _ (hmemXD s hs ω).1
  have hf'meas : AEStronglyMeasurable (fun ω => f' (x s ω)) μ :=
    integrable_condExp.1.congr hunb
  have hKf' : ∀ ω, ‖f' (x s ω)‖ ≤ ‖f' xstar‖ + β * M := fun ω => hKf _ (hmemXD s hs ω).1
  have hvmeas : AEStronglyMeasurable v μ :=
    ((hmeas s hs).sub_const xstar).aestronglyMeasurable
  have hQint : Integrable (fun ω => gt s ω (v ω)) μ := by
    refine Integrable.mono' (hgi.norm.mul_const M) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have := (ContinuousLinearMap.apply ℝ ℝ (E := E)).aestronglyMeasurable_comp₂ hvmeas hgi.1
      simpa using this
    · exact ((gt s ω).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hvbd ω) (norm_nonneg _))
  have hPint : Integrable (fun ω => f' (x s ω) (v ω)) μ := by
    refine Integrable.mono' (integrable_const ((‖f' xstar‖ + β * M) * M)) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · have := (ContinuousLinearMap.apply ℝ ℝ (E := E)).aestronglyMeasurable_comp₂ hvmeas hf'meas
      simpa using this
    · exact ((f' (x s ω)).le_opNorm _).trans
        (mul_le_mul (hKf' ω) (hvbd ω) (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (mul_nonneg hβ hM0)))
  have hPQ : ∫ ω, gt s ω (v ω) ∂μ = ∫ ω, f' (x s ω) (v ω) ∂μ := by
    have h1 := condExp_bilin_of_stronglyMeasurable_left (μ := μ) (m := MeasurableSpace.comap (x s) (inferInstance : MeasurableSpace E))
      (ContinuousLinearMap.apply ℝ ℝ (E := E)) hvsm (by simpa using hQint) hgi
    rw [← integral_condExp hmle]
    have h2 : (μ[fun ω => gt s ω (v ω) | MeasurableSpace.comap (x s) (inferInstance : MeasurableSpace E)]) =ᵐ[μ] fun ω => f' (x s ω) (v ω) := by
      have h1' : (μ[fun ω => gt s ω (v ω) | MeasurableSpace.comap (x s) (inferInstance : MeasurableSpace E)]) =ᵐ[μ]
          fun ω => (μ[gt s | MeasurableSpace.comap (x s) (inferInstance : MeasurableSpace E)] ω) (v ω) := by simpa using h1
      filter_upwards [h1', hunb] with ω h1ω h2ω
      rw [h1ω, h2ω]
    exact integral_congr_ae h2
  have hVint' : Integrable (fun ω => ‖gt s ω - f' (x s ω)‖ ^ 2) μ := hVint
  -- pointwise inequality
  have hpt : ∀ ω, f (x (s + 1) ω) ≤ f xstar +
      (β + 1 / η) * (bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω)) +
      η / 2 * ‖gt s ω - f' (x s ω)‖ ^ 2 + (f' (x s ω) (v ω) - gt s ω (v ω)) := by
    intro ω
    have hrk := (hrun ω).2.2 s hs
    have := smd_step_pt hXconv hΦ hΦsc hf hsmooth hβ hη (hmemXD s hs ω) hrk.1 hrk.2 hxstar
    simp only [ContinuousLinearMap.sub_apply] at this
    simp only [hv]
    linarith
  have hIL : Integrable (fun ω => (β + 1 / η) *
      (bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω))) μ := hΔint.const_mul _
  have hIV : Integrable (fun ω => η / 2 * ‖gt s ω - f' (x s ω)‖ ^ 2) μ := hVint'.const_mul _
  have hI1 : Integrable (fun ω => f xstar + (β + 1 / η) *
      (bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω))) μ :=
    (integrable_const _).add hIL
  have hI2 : Integrable (fun ω => f xstar + (β + 1 / η) *
      (bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω)) +
      η / 2 * ‖gt s ω - f' (x s ω)‖ ^ 2) μ := hI1.add hIV
  have hI3 : Integrable (fun ω => f' (x s ω) (v ω) - gt s ω (v ω)) μ := hPint.sub hQint
  have hmono : ∫ ω, f (x (s + 1) ω) ∂μ ≤ ∫ ω, (f xstar +
      (β + 1 / η) * (bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω)) +
      η / 2 * ‖gt s ω - f' (x s ω)‖ ^ 2 + (f' (x s ω) (v ω) - gt s ω (v ω))) ∂μ :=
    integral_mono hFint (hI2.add hI3) hpt
  rw [integral_add hI2 hI3, integral_add hI1 hIV, integral_add (integrable_const _) hIL,
    integral_sub hPint hQint, hPQ, integral_const_mul, integral_const_mul] at hmono
  simp only [integral_const, probReal_univ, one_smul, sub_self, add_zero] at hmono
  have : η / 2 * ∫ ω, ‖gt s ω - f' (x s ω)‖ ^ 2 ∂μ ≤ η / 2 * σ ^ 2 :=
    mul_le_mul_of_nonneg_left hV (by positivity)
  linarith

end ConvexOptAlg.StochMD

open ConvexOptAlg.StochMD
open MeasureTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X D : Set E) (hXcpt : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (hΦsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    (x₁ : E) (R : ℝ) (hR : ∀ z ∈ X ∩ D, Φ z - Φ x₁ ≤ R ^ 2)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsSmoothWRT X f f' β)
    (σ : ℝ) (x : ℕ → Ω → E) (gt : ℕ → Ω → E →L[ℝ] ℝ)
    (horacle : IsSmoothStochOracle μ f' σ x gt)
    (η : ℝ) (hη : 0 < η) (hrun : IsSMDRun X D Φ Φ' (1 / (β + 1 / η)) x₁ x gt)
    (xstar : E) (hxstar : xstar ∈ X) (s : ℕ) (hs : 1 ≤ s) :
    Integrable (fun ω => f (x (s + 1) ω)) μ ∧
      Integrable (fun ω => bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω)) μ ∧
      (∫ ω, f (x (s + 1) ω) ∂μ) - f xstar ≤
        (β + 1 / η) *
            (∫ ω, (bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω)) ∂μ) +
          η * σ ^ 2 / 2 := by
  exact step_core μ X D hXcpt hXconv hXD hXDne Φ Φ' hΦ hΦsc x₁ R hR f f' β hβ hf hsmooth σ x gt horacle η hη hrun xstar hxstar s hs
