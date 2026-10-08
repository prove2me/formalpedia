-- Prove2me | solution 1 for ConvexOptAlg.MirrorDescent.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T16:52:15.903974+00:00
-- url     : https://prove2.me/submissions/c0781283-ba6d-49dd-9c3d-22986fbb7e05

/-
Bubeck, Convex Optimization: Algorithms and Complexity, Theorem 4.2: mirror descent with a
`ρ`-strongly convex mirror map and the step `η = (R/L)√(2ρ/t)` satisfies
`f((1/t)∑ x_s) - f(x*) ≤ R L √(2/(ρ t))`.

For a comparator `u ∈ X ∩ D`: with `b(u, x) = D_Φ(u, x)` the Bregman divergence, the three-point
identity, the first-order optimality condition of the Bregman projection (`breg_opt`, from
`IsLocalMinOn.hasFDerivWithinAt_nonneg` along the segment to `u`) and strong convexity give, for the
subgradient step `∇Φ(y_{s+1}) = ∇Φ(x_s) - η g_s`,
`η g_s(x_s - u) ≤ b(u, x_s) - b(u, x_{s+1}) + η² L²/(2ρ)` (`step_ineq`). Summing and using
`b(u, x_1) ≤ Φ(u) - Φ(x_1) ≤ R²` (first-order optimality of `x_1`) and `b ≥ 0` yields
`∑ (f(x_s) - f(u)) ≤ R²/η + t η L²/(2ρ)` (`md_bound`). Jensen bounds `f` at the average. The comparator `x*`
may lie on the boundary of `D`: the points `(1 - θ)x* + θ x_1` lie in `X ∩ D` (open segment from a closure point
to an interior point) and, by convexity of `f`, `f` at them is at most `f(x*) + θ(f(x_1) - f(x*))`, so
the bound passes to the limit `θ → 0`.
-/
import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

set_option autoImplicit false

namespace MirLib
open ConvexOptAlg.MirrorDescent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem opt_nonneg {C : Set E} (hC : Convex ℝ C) {ψ : E → ℝ} {ℓ : E →L[ℝ] ℝ} {z : E}
    (hz : z ∈ C) (hd : HasFDerivAt ψ ℓ z) (hmin : ∀ x ∈ C, ψ z ≤ ψ x) {x : E} (hx : x ∈ C) :
    0 ≤ ℓ (x - z) := by
  have hmin' : IsLocalMinOn ψ C z :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => hmin y hy)
  exact hmin'.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset (x := z) (y := x - z) (by simpa using hC.segment_subset hz hx))

/-- First-order optimality of a Bregman projection. -/
theorem breg_opt {X D : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} (hXc : Convex ℝ X)
    (hDc : Convex ℝ D) (hd : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) {y z : E}
    (hproj : IsBregmanProjection X D Φ Φ' y z) {u : E} (hu : u ∈ X ∩ D) :
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

theorem quad_aux {ρ η L r : ℝ} (hρ : 0 < ρ) : η * L * r - ρ / 2 * r ^ 2 ≤ η ^ 2 * L ^ 2 / (2 * ρ) := by
  have h : 0 ≤ ρ / 2 * (r - η * L / ρ) ^ 2 := by positivity
  have e : η ^ 2 * L ^ 2 / (2 * ρ) - (η * L * r - ρ / 2 * r ^ 2) = ρ / 2 * (r - η * L / ρ) ^ 2 := by
    field_simp; ring
  linarith

/-- One step of mirror descent against a comparator `u ∈ X ∩ D`. -/
theorem step_ineq {X D : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} (hXc : Convex ℝ X)
    (hDc : Convex ℝ D) (hd : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) {ρ : ℝ} (hρ : 0 < ρ)
    (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ) {η L : ℝ} (hη0 : 0 ≤ η) {xs y z : E} {g : E →L[ℝ] ℝ}
    (hxs : xs ∈ X ∩ D) (hgy : Φ' y = Φ' xs - η • g) (hproj : IsBregmanProjection X D Φ Φ' y z)
    (hgL : ‖g‖ ≤ L) {u : E} (hu : u ∈ X ∩ D) :
    η * g (xs - u) ≤ bregman Φ Φ' u xs - bregman Φ Φ' u z + η ^ 2 * L ^ 2 / (2 * ρ) := by
  have hP := breg_opt hXc hDc hd hproj hu
  have hz : z ∈ X ∩ D := hproj.1
  have hS := hΦ xs hxs z hz
  have hη : Φ' xs - Φ' y = η • g := by rw [hgy]; abel
  have hgz : g (xs - z) ≤ L * ‖xs - z‖ :=
    calc g (xs - z) ≤ ‖g (xs - z)‖ := Real.le_norm_self _
      _ ≤ ‖g‖ * ‖xs - z‖ := g.le_opNorm _
      _ ≤ L * ‖xs - z‖ := by gcongr
  simp only [bregman, map_sub, ContinuousLinearMap.sub_apply] at hP hS ⊢
  have e1 : (Φ' xs - Φ' y) (xs - u) = η * g (xs - u) := by rw [hη]; simp
  have e2 : (Φ' xs - Φ' y) (xs - z) = η * g (xs - z) := by rw [hη]; simp
  simp only [ContinuousLinearMap.sub_apply, map_sub] at e1 e2
  have hq := quad_aux (η := η) (L := L) (r := ‖xs - z‖) hρ
  -- the linear-functional bookkeeping
  have hz' : η * g (xs - z) ≤ η * L * ‖xs - z‖ := by
    have := mul_le_mul_of_nonneg_left hgz hη0
    linarith
  simp only [map_sub] at hz'
  linarith

theorem bregman_nonneg {X D : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ) {u v : E} (hu : u ∈ X ∩ D) (hv : v ∈ X ∩ D) :
    0 ≤ bregman Φ Φ' u v := by
  have := hΦ v hv u hu
  unfold bregman
  have h2 : 0 ≤ ρ / 2 * ‖v - u‖ ^ 2 := by positivity
  have h3 : (Φ' v) (u - v) = -(Φ' v) (v - u) := by rw [← map_neg, neg_sub]
  linarith

/-- Iterates of mirror descent stay in `X ∩ D`. -/
theorem iter_mem {X D : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} {f : E → ℝ} {η : ℝ}
    {x y : ℕ → E} {g : ℕ → E →L[ℝ] ℝ} {T : ℕ} (hrun : IsMirrorDescentRun X D Φ Φ' f η x y g T) :
    ∀ s, 1 ≤ s → s ≤ T + 1 → x s ∈ X ∩ D := by
  intro s hs hsT
  induction s, hs using Nat.le_induction with
  | base => exact hrun.1
  | succ s hs ih =>
    have := (hrun.2.2 s hs (by omega)).2.2.2
    exact this.1

/-- The mirror descent regret bound against a comparator in `X ∩ D`. -/
theorem md_bound {X D : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} (hXc : Convex ℝ X)
    (hDc : Convex ℝ D) (hd : ∀ x ∈ D, HasFDerivAt Φ (Φ' x) x) {ρ : ℝ} (hρ : 0 < ρ)
    (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ) {f : E → ℝ} {η L R : ℝ} (hη : 0 < η)
    {t : ℕ} {x y : ℕ → E} {g : ℕ → E →L[ℝ] ℝ}
    (hgL : ∀ s : ℕ, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (hR : ∀ z ∈ X ∩ D, Φ z - Φ (x 1) ≤ R ^ 2)
    (hrun : IsMirrorDescentRun X D Φ Φ' f η x y g t) {u : E} (hu : u ∈ X ∩ D) :
    ∑ s ∈ Finset.Icc 1 t, (f (x s) - f u) ≤ R ^ 2 / η + t * η * L ^ 2 / (2 * ρ) := by
  have hmem := iter_mem hrun
  have htele : ∀ m, m ≤ t → ∑ s ∈ Finset.Icc 1 m, η * g s (x s - u) ≤
      bregman Φ Φ' u (x 1) - bregman Φ Φ' u (x (m + 1)) + m * (η ^ 2 * L ^ 2 / (2 * ρ)) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have ih' := ih (by omega)
      rw [Finset.sum_Icc_succ_top (by omega)]
      obtain ⟨hsub, _, hgy, hproj⟩ := hrun.2.2 (m + 1) (by omega) hm
      have := step_ineq hXc hDc hd hρ hΦ hη.le (hmem (m + 1) (by omega) (by omega)) hgy hproj
        (hgL (m + 1) (by omega) hm) hu
      push_cast
      linarith
  have hsum : η * ∑ s ∈ Finset.Icc 1 t, (f (x s) - f u) ≤
      ∑ s ∈ Finset.Icc 1 t, η * g s (x s - u) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun s hs => ?_)
    have hs' := Finset.mem_Icc.1 hs
    have hsub := (hrun.2.2 s hs'.1 hs'.2).1
    exact mul_le_mul_of_nonneg_left (hsub u hu.1) hη.le
  have h1 := htele t le_rfl
  have h2 : bregman Φ Φ' u (x 1) ≤ R ^ 2 := by
    have hx1 := hmem 1 le_rfl (by omega)
    have hopt := opt_nonneg (hXc.inter hDc) hx1 (hd _ hx1.2) (fun z hz => hrun.2.1 z hz) hu
    have := hR u hu
    unfold bregman
    linarith
  have h3 := bregman_nonneg hρ hΦ hu (hmem (t + 1) (by omega) le_rfl)
  have : η * ∑ s ∈ Finset.Icc 1 t, (f (x s) - f u) ≤ R ^ 2 + t * (η ^ 2 * L ^ 2 / (2 * ρ)) := by
    linarith
  have e : R ^ 2 / η + t * η * L ^ 2 / (2 * ρ) = (R ^ 2 + t * (η ^ 2 * L ^ 2 / (2 * ρ))) / η := by
    field_simp
  rw [e, le_div_iff₀ hη]
  linarith

theorem sqrt_identity {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    Real.sqrt (2 / (ρ * t)) = Real.sqrt (2 * ρ / t) / ρ := by
  have h : 2 / (ρ * t) = (2 * ρ / t) / ρ ^ 2 := by field_simp
  rw [h, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hρ.le]

theorem md_final {X D : Set E} {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ}
    (hset : IsMirrorSetting X D Φ Φ') {ρ : ℝ} (hρ : 0 < ρ)
    (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ) {f : E → ℝ} (hf : ConvexOn ℝ X f) {L : ℝ}
    (hL0 : 0 < L) {xstar : E} (hxstar : xstar ∈ X) {t : ℕ} (ht : 1 ≤ t) {x y : ℕ → E}
    {g : ℕ → E →L[ℝ] ℝ} (hgL : ∀ s : ℕ, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ z ∈ X ∩ D, Φ z - Φ (x 1) ≤ R ^ 2)
    (hrun : IsMirrorDescentRun X D Φ Φ' f (R / L * Real.sqrt (2 * ρ / t)) x y g t) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) - f xstar ≤
      R * L * Real.sqrt (2 / (ρ * t)) := by
  obtain ⟨_, hXc, hmirror, hXcl, _⟩ := hset
  obtain ⟨hDo, hDc, _, hd, _, _⟩ := hmirror
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  set q : ℝ := Real.sqrt (2 * ρ / t) with hq
  have hqpos : 0 < q := Real.sqrt_pos.2 (by positivity)
  set η : ℝ := R / L * q with hηdef
  have hηpos : 0 < η := by positivity
  have hmem := iter_mem hrun
  -- the bound B for the average
  set B : ℝ := R * L * Real.sqrt (2 / (ρ * t)) with hB
  have hBeq : (1 / (t : ℝ)) * (R ^ 2 / η + t * η * L ^ 2 / (2 * ρ)) = B := by
    rw [hB, sqrt_identity hρ htpos, ← hq]
    have hq2 : q ^ 2 = 2 * ρ / t := Real.sq_sqrt (by positivity)
    rw [hηdef]
    have hq3 : (t : ℝ) * q ^ 2 = 2 * ρ := by rw [hq2]; field_simp
    field_simp
    linarith [hq3]
  -- Jensen for the average
  have hjensen : f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) ≤
      (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, f (x s) := by
    rw [Finset.smul_sum]
    have hcard : ∑ _s ∈ Finset.Icc 1 t, (1 / (t : ℝ)) = 1 := by
      simp [Finset.sum_const, Nat.card_Icc]
      field_simp
    have := hf.map_sum_le (t := Finset.Icc 1 t) (w := fun _ => 1 / (t : ℝ)) (p := x)
      (fun _ _ => by positivity) hcard
      (fun s hs => (hmem s (Finset.mem_Icc.1 hs).1 (by have := (Finset.mem_Icc.1 hs).2; omega)).1)
    simpa [Finset.mul_sum] using this
  -- bound against comparators in X ∩ D
  have key : ∀ u ∈ X ∩ D, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) - f u ≤ B := by
    intro u hu
    have hb := md_bound hXc hDc hd hρ hΦ hηpos hgL hR hrun hu
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc] at hb
    simp only [Nat.add_sub_cancel, nsmul_eq_mul] at hb
    have h2 : (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, f (x s) - f u ≤ B := by
      rw [← hBeq]
      have : (1 / (t : ℝ)) * (∑ s ∈ Finset.Icc 1 t, f (x s) - t * f u) ≤
          (1 / (t : ℝ)) * (R ^ 2 / η + t * η * L ^ 2 / (2 * ρ)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      have e : (1 / (t : ℝ)) * (∑ s ∈ Finset.Icc 1 t, f (x s) - t * f u) =
          (1 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, f (x s) - f u := by field_simp
      linarith
    linarith
  -- the comparator `xstar` may lie on the boundary of `D`
  have hz0 : x 1 ∈ X ∩ D := hmem 1 le_rfl (by omega)
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
    have h1 := hDc.openSegment_closure_interior_subset_interior (hXcl hxstar)
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

end MirLib

open ConvexOptAlg.MirrorDescent in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ)
    (f : E → ℝ) (hf : ConvexOn ℝ X f) (L : ℝ) (hL0 : 0 < L)
    (xstar : E) (hxstar : xstar ∈ X) (hmin : ∀ z ∈ X, f xstar ≤ f z)
    (t : ℕ) (ht : 1 ≤ t) (x y : ℕ → E) (g : ℕ → E →L[ℝ] ℝ)
    (hgL : ∀ s : ℕ, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (R : ℝ) (hR0 : 0 < R) (hR : ∀ z ∈ X ∩ D, Φ z - Φ (x 1) ≤ R ^ 2)
    (hrun : IsMirrorDescentRun X D Φ Φ' f (R / L * Real.sqrt (2 * ρ / t)) x y g t) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) - f xstar ≤
      R * L * Real.sqrt (2 / (ρ * t)) :=
  MirLib.md_final hset hρ hΦ hf hL0 hxstar ht hgL hR0 hR hrun
