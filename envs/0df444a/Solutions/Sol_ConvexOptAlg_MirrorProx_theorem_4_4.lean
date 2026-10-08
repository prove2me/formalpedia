-- Prove2me | solution 1 for ConvexOptAlg.MirrorProx.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:24:25.393467+00:00
-- url     : https://prove2.me/submissions/08369a96-32f6-4dd3-b933-82cc3207c0de

/-
Bubeck, Convex Optimization: Algorithms and Complexity, Theorem 4.4: mirror prox with step `ρ/β` on a
convex `β`-smooth function and a `ρ`-strongly convex mirror map satisfies
`f((1/t)∑ y_{s+1}) - f(x*) ≤ βR²/(ρt)`.

For a comparator `u ∈ X ∩ D` and `η = ρ/β`, with `b = D_Φ` the Bregman divergence, the two projections give, by
the three-point identity and the Pythagoras inequality of a Bregman projection (from first-order optimality),
`η f'(y_{s+1})(x_{s+1} - u) ≤ b(u,x_s) - b(u,x_{s+1}) - b(x_{s+1},x_s)` and
`η f'(x_s)(y_{s+1} - x_{s+1}) ≤ b(x_{s+1},x_s) - b(x_{s+1},y_{s+1}) - b(y_{s+1},x_s)`.
Smoothness bounds `η (f'(y_{s+1}) - f'(x_s))(y_{s+1} - x_{s+1})` by `(ρ/2)(‖y_{s+1} - x_s‖² +
‖y_{s+1} - x_{s+1}‖²)`, which strong convexity absorbs. Convexity of `f` gives
`η (f(y_{s+1}) - f(u)) ≤ b(u,x_s) - b(u,x_{s+1})`; summing and Jensen give the bound for `u ∈ X ∩ D`, and the
comparator `x*` on the boundary of `D` is handled by approximating it with `(1 - θ)x* + θ x_1`.
-/
import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

set_option autoImplicit false

namespace MPLib
open ConvexOptAlg.MirrorProx

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem opt_nonneg {C : Set E} (hC : Convex ℝ C) {ψ : E → ℝ} {ℓ : E →L[ℝ] ℝ} {z : E}
    (hz : z ∈ C) (hd : HasFDerivAt ψ ℓ z) (hmin : ∀ x ∈ C, ψ z ≤ ψ x) {x : E} (hx : x ∈ C) :
    0 ≤ ℓ (x - z) := by
  have hmin' : IsLocalMinOn ψ C z :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => hmin y hy)
  exact hmin'.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset (x := z) (y := x - z) (by simpa using hC.segment_subset hz hx))

theorem breg_opt {X D : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} (hXc : Convex ℝ X)
    (hDc : Convex ℝ D) (hd : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) {y z : E}
    (hproj : IsBregmanProj X D Φ Φ' y z) {u : E} (hu : u ∈ X ∩ D) :
    0 ≤ (Φ' z - Φ' y) (u - z) := by
  obtain ⟨hz, hmin⟩ := hproj
  have hder : HasFDerivAt (fun x => bregman Φ Φ' x y) (Φ' z - Φ' y) z := by
    unfold bregman
    have h1 := (hd z hz.2).sub_const (Φ y)
    have h2 : HasFDerivAt (fun x : E => Φ' y (x - y)) (Φ' y) z := by
      have := ((Φ' y).hasFDerivAt (x := z - y)).comp z ((hasFDerivAt_id z).sub_const y)
      exact this.congr_fderiv (by ext; simp)
    exact h1.sub h2
  exact opt_nonneg (hXc.inter hDc) hz hder (fun x hx => hmin x hx) hu

/-- The three-point identity for the Bregman divergence. -/
theorem three_point (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (a b c u : E) :
    (Φ' a - Φ' b) (c - u) =
      bregman Φ Φ' u a - bregman Φ Φ' u b + bregman Φ Φ' c b - bregman Φ Φ' c a := by
  unfold bregman
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring

/-- The generalized Pythagoras inequality for a Bregman projection. -/
theorem pyth {X D : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} (hXc : Convex ℝ X)
    (hDc : Convex ℝ D) (hd : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) {y z : E}
    (hproj : IsBregmanProj X D Φ Φ' y z) {u : E} (hu : u ∈ X ∩ D) :
    bregman Φ Φ' u z + bregman Φ Φ' z y ≤ bregman Φ Φ' u y := by
  have h := breg_opt hXc hDc hd hproj hu
  unfold bregman at h ⊢
  simp only [map_sub, ContinuousLinearMap.sub_apply] at h ⊢
  linarith

theorem breg_lower {S : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} {ρ : ℝ}
    (hΦ : IsStronglyConvexWRT S Φ Φ' ρ) {u v : E} (hu : u ∈ S) (hv : v ∈ S) :
    ρ / 2 * ‖u - v‖ ^ 2 ≤ bregman Φ Φ' u v := by
  have := hΦ v hv u hu
  unfold bregman
  have h3 : (Φ' v) (u - v) = -(Φ' v) (v - u) := by rw [← map_neg, neg_sub]
  have h4 : ‖v - u‖ = ‖u - v‖ := norm_sub_rev _ _
  rw [h4] at this
  linarith

/-- First-order inequality for a convex function with a derivative within `X`. -/
theorem first_order_within {X : Set E} (hXc : Convex ℝ X) {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ConvexOn ℝ X f) {y : E} (hy : y ∈ X) (hd : HasFDerivWithinAt f (f' y) X y) {u : E}
    (hu : u ∈ X) : f y + f' y (u - y) ≤ f u := by
  set φ : ℝ → ℝ := fun θ => f (y + θ • (u - y)) with hφ
  have hline : HasDerivWithinAt (fun θ : ℝ => y + θ • (u - y)) (u - y) (Set.Icc 0 1) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (u - y)).const_add y).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun θ : ℝ => y + θ • (u - y)) (Set.Icc 0 1) X := by
    intro θ hθ
    have := hXc.add_smul_sub_mem hy hu hθ
    simpa using this
  have hd' : HasDerivWithinAt φ (f' y (u - y)) (Set.Icc 0 1) 0 := by
    have hd0 : HasFDerivWithinAt f (f' y) X (y + (0 : ℝ) • (u - y)) := by simpa using hd
    exact hd0.comp_hasDerivWithinAt (0 : ℝ) hline hmaps
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
    have := hf.comp_affineMap (AffineMap.lineMap y u : ℝ →ᵃ[ℝ] E)
    have e : φ = f ∘ ⇑(AffineMap.lineMap y u : ℝ →ᵃ[ℝ] E) := by
      funext θ; simp [hφ, AffineMap.lineMap_apply, add_comm]
    rw [e]
    refine ConvexOn.subset this ?_ (convex_Icc 0 1)
    intro θ hθ
    simp only [Set.mem_preimage]
    have := hXc.add_smul_sub_mem hy hu hθ
    simpa [AffineMap.lineMap_apply, add_comm] using this
  have hIoi : HasDerivWithinAt φ (f' y (u - y)) (Set.Ioi 0) 0 :=
    hd'.mono_of_mem_nhdsWithin (by
      exact Filter.mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩))
  have := hconv.le_slope_of_hasDerivWithinAt_Ioi (Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩)
    (Set.mem_Icc.2 ⟨zero_le_one, le_rfl⟩) zero_lt_one hIoi
  simp [slope_def_field, hφ] at this
  have e : f' y (u - y) = f' y u - f' y y := map_sub _ _ _
  linarith

theorem mp_step {X D : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {ρ β η : ℝ} (hXc : Convex ℝ X) (hDc : Convex ℝ D)
    (hd : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) (hΦ : IsStronglyConvexWRT (X ∩ D) Φ Φ' ρ)
    (hf : ConvexOn ℝ X f) (hfd : ∀ x ∈ X, HasFDerivWithinAt f (f' x) X x)
    (hsm : ∀ x ∈ X, ∀ y ∈ X, ‖f' x - f' y‖ ≤ β * ‖x - y‖) (hη : η * β = ρ) (hη0 : 0 ≤ η) (hρ0 : 0 ≤ ρ)
    {xs y y' x' xn : E} (hxs : xs ∈ X ∩ D) (hy' : Φ' y' = Φ' xs - η • f' xs)
    (hy : IsBregmanProj X D Φ Φ' y' y) (hx' : Φ' x' = Φ' xs - η • f' y)
    (hxn : IsBregmanProj X D Φ Φ' x' xn) {u : E} (hu : u ∈ X ∩ D) :
    η * (f y - f u) ≤ bregman Φ Φ' u xs - bregman Φ Φ' u xn := by
  have hyX : y ∈ X ∩ D := hy.1
  have hxnX : xn ∈ X ∩ D := hxn.1
  have c1 := first_order_within hXc hf hyX.1 (hfd y hyX.1) hu.1
  have hP1 := pyth hXc hDc hd hxn hu
  have hP2 := pyth hXc hDc hd hy hxnX
  have t1 := three_point Φ Φ' xs x' xn u
  have t2 := three_point Φ Φ' xs y' y xn
  have hΔ1 : Φ' xs - Φ' x' = η • f' y := by rw [hx']; abel
  have hΔ2 : Φ' xs - Φ' y' = η • f' xs := by rw [hy']; abel
  rw [hΔ1] at t1
  rw [hΔ2] at t2
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at t1 t2
  have hs1 := breg_lower hΦ hyX hxs
  have hs2 := breg_lower hΦ hxnX hyX
  have hnorm : (f' y - f' xs) (y - xn) ≤ β * ‖y - xs‖ * ‖y - xn‖ := by
    calc (f' y - f' xs) (y - xn) ≤ ‖(f' y - f' xs) (y - xn)‖ := Real.le_norm_self _
      _ ≤ ‖f' y - f' xs‖ * ‖y - xn‖ := (f' y - f' xs).le_opNorm _
      _ ≤ β * ‖y - xs‖ * ‖y - xn‖ := by
        gcongr
        exact hsm y hyX.1 xs hxs.1
  have e1 : f' y (y - u) = f' y (xn - u) + f' xs (y - xn) + (f' y - f' xs) (y - xn) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]; ring
  have e2 : ‖xn - y‖ = ‖y - xn‖ := norm_sub_rev _ _
  have hm : η * (f' y - f' xs) (y - xn) ≤ ρ * ‖y - xs‖ * ‖y - xn‖ := by
    have := mul_le_mul_of_nonneg_left hnorm hη0
    have e : η * (β * ‖y - xs‖ * ‖y - xn‖) = ρ * ‖y - xs‖ * ‖y - xn‖ := by rw [← hη]; ring
    linarith
  have hq : ρ * ‖y - xs‖ * ‖y - xn‖ ≤ ρ / 2 * ‖y - xs‖ ^ 2 + ρ / 2 * ‖y - xn‖ ^ 2 := by
    nlinarith [sq_nonneg (‖y - xs‖ - ‖y - xn‖)]
  have hc1 : η * (f y - f u) ≤ η * f' y (y - u) := by
    have h := mul_le_mul_of_nonneg_left (show f y - f u ≤ f' y (y - u) by
      have : f' y (u - y) = -f' y (y - u) := by rw [← map_neg, neg_sub]
      linarith) hη0
    exact h
  have hE : η * f' y (y - u) = η * f' y (xn - u) + η * f' xs (y - xn) + η * (f' y - f' xs) (y - xn) := by
    rw [e1]; ring
  rw [e2] at hs2
  nlinarith [hc1, hE, t1, t2, hP1, hP2, hs1, hs2, hm, hq]

theorem mp_final {X D : Set E} (hXc : Convex ℝ X) (hXD : X ⊆ closure D)
    {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hd : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) {ρ : ℝ} (hρ : 0 < ρ)
    (hsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' ρ) {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ConvexOn ℝ X f) {β : ℝ} (hβ : 0 < β)
    (hfd : ∀ x ∈ X, HasFDerivWithinAt f (f' x) X x)
    (hsm : ∀ x ∈ X, ∀ y ∈ X, ‖f' x - f' y‖ ≤ β * ‖x - y‖) {xstar : E} (hxstar : xstar ∈ X)
    {x y y' x' : ℕ → E} (hrun : IsMirrorProxRun X D Φ Φ' f' (ρ / β) x y y' x')
    (hx1 : ∀ w ∈ X ∩ D, Φ (x 1) ≤ Φ w) {R : ℝ} (hR : ∀ w ∈ X ∩ D, Φ w - Φ (x 1) ≤ R ^ 2)
    {t : ℕ} (ht : 1 ≤ t) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, y (s + 1)) - f xstar ≤ β * R ^ 2 / (ρ * t) := by
  set η : ℝ := ρ / β with hηdef
  have hηpos : 0 < η := by positivity
  have hηβ : η * β = ρ := by rw [hηdef]; field_simp
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  obtain ⟨hx1m, hstep⟩ := hrun
  -- iterates stay in `X ∩ D`
  have hxmem : ∀ s, 1 ≤ s → x s ∈ X ∩ D := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact hx1m
    | succ s hs ih => exact (hstep s hs).2.2.2.2.2.1
  have hymem : ∀ s, 1 ≤ s → y (s + 1) ∈ X ∩ D := fun s hs => (hstep s hs).2.2.1.1
  -- comparator in `X ∩ D`
  have key : ∀ u ∈ X ∩ D, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, y (s + 1)) - f u ≤
      β * R ^ 2 / (ρ * t) := by
    intro u hu
    have htele : ∀ m, m ≤ t → ∑ s ∈ Finset.Icc 1 m, η * (f (y (s + 1)) - f u) ≤
        bregman Φ Φ' u (x 1) - bregman Φ Φ' u (x (m + 1)) := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        have ih' := ih (by omega)
        rw [Finset.sum_Icc_succ_top (by omega)]
        obtain ⟨hy'D, hy', hy, hx'D, hx', hxn⟩ := hstep (m + 1) (by omega)
        have := mp_step hXc hDc hd hsc hf hfd hsm hηβ hηpos.le hρ.le (hxmem (m + 1) (by omega))
          hy' hy hx' hxn hu
        linarith
    have h1 := htele t le_rfl
    have h2 : bregman Φ Φ' u (x 1) ≤ R ^ 2 := by
      have hxm := hxmem 1 le_rfl
      have hopt := opt_nonneg (hXc.inter hDc) hxm (hd _ hxm.2) (fun z hz => hx1 z hz) hu
      have := hR u hu
      unfold bregman
      linarith
    have h3 : 0 ≤ bregman Φ Φ' u (x (t + 1)) := by
      have := breg_lower hsc hu (hxmem (t + 1) (by omega))
      have : 0 ≤ ρ / 2 * ‖u - x (t + 1)‖ ^ 2 := by positivity
      linarith
    rw [← Finset.mul_sum] at h1
    have hsum : ∑ s ∈ Finset.Icc 1 t, (f (y (s + 1)) - f u) ≤ R ^ 2 / η := by
      rw [le_div_iff₀ hηpos]; linarith
    -- Jensen
    have hjensen : f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, y (s + 1)) ≤
        (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, f (y (s + 1)) := by
      rw [Finset.smul_sum]
      have hcard : ∑ _s ∈ Finset.Icc 1 t, (1 / (t : ℝ)) = 1 := by
        simp [Finset.sum_const, Nat.card_Icc]
        field_simp
      have := hf.map_sum_le (t := Finset.Icc 1 t) (w := fun _ => 1 / (t : ℝ)) (p := fun s => y (s + 1))
        (fun _ _ => by positivity) hcard
        (fun s hs => (hymem s (Finset.mem_Icc.1 hs).1).1)
      simpa [Finset.mul_sum] using this
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc] at hsum
    simp only [Nat.add_sub_cancel, nsmul_eq_mul] at hsum
    have e : β * R ^ 2 / (ρ * t) = (1 / (t : ℝ)) * (R ^ 2 / η) := by
      rw [hηdef]; field_simp
    rw [e]
    have : (1 / (t : ℝ)) * (∑ s ∈ Finset.Icc 1 t, f (y (s + 1)) - t * f u) ≤
        (1 / (t : ℝ)) * (R ^ 2 / η) := mul_le_mul_of_nonneg_left hsum (by positivity)
    have e2 : (1 / (t : ℝ)) * (∑ s ∈ Finset.Icc 1 t, f (y (s + 1)) - t * f u) =
        (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, f (y (s + 1)) - f u := by field_simp
    linarith
  -- the comparator `xstar` may lie on the boundary of `D`
  have hz0 : x 1 ∈ X ∩ D := hxmem 1 le_rfl
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set c : ℝ := |f (x 1) - f xstar| + 1 with hc
  have hcpos : 0 < c := by positivity
  set θ : ℝ := min (1 / 2) (ε / c) with hθ
  have hθpos : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ ≤ 1 / 2 := min_le_left _ _
  have hθc : θ * c ≤ ε := by
    have : θ ≤ ε / c := min_le_right _ _
    calc θ * c ≤ ε / c * c := by gcongr
      _ = ε := by field_simp
  have hint : interior D = D := hDo.interior_eq
  have hmemD : (1 - θ) • xstar + θ • x 1 ∈ D := by
    have h1 := hDc.openSegment_closure_interior_subset_interior (hXD hxstar)
      (by rw [hint]; exact hz0.2)
    rw [hint] at h1
    exact h1 ⟨1 - θ, θ, by linarith, hθpos, by ring, rfl⟩
  have hmemX : (1 - θ) • xstar + θ • x 1 ∈ X := hXc hxstar hz0.1 (by linarith) hθpos.le (by ring)
  have hk := key _ ⟨hmemX, hmemD⟩
  have hconv := hf.2 hxstar hz0.1 (by linarith : 0 ≤ 1 - θ) hθpos.le (by ring)
  simp only [smul_eq_mul] at hconv
  have hab : θ * (f (x 1) - f xstar) ≤ θ * c := by
    apply mul_le_mul_of_nonneg_left _ hθpos.le
    have := le_abs_self (f (x 1) - f xstar)
    linarith
  nlinarith [hk, hconv, hab, hθc]

end MPLib

open ConvexOptAlg.MirrorProx in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' ρ)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (hf : ConvexOn ℝ X f)
    (β : ℝ) (hβ : 0 < β) (hsm : IsSmoothWRT X f f' β)
    (xstar : E) (hxstar : xstar ∈ X ∧ ∀ w ∈ X, f xstar ≤ f w)
    (x y y' x' : ℕ → E) (hrun : IsMirrorProxRun X D Φ Φ' f' (ρ / β) x y y' x')
    (hx1 : ∀ w ∈ X ∩ D, Φ (x 1) ≤ Φ w)
    (R : ℝ) (hR : ∀ w ∈ X ∩ D, Φ w - Φ (x 1) ≤ R ^ 2)
    (t : ℕ) (ht : 1 ≤ t) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, y (s + 1)) - f xstar
      ≤ β * R ^ 2 / (ρ * t) :=
  MPLib.mp_final hXconv hXD hΦ.1 hΦ.2.1 hΦ.2.2.2.1 hρ hsc hf hβ hsm.1 hsm.2 hxstar.1 hrun hx1 hR ht
