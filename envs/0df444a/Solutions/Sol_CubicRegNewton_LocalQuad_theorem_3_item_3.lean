-- Prove2me | solution 1 for CubicRegNewton.LocalQuad.theorem_3_item_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:35:59.746531+00:00
-- url     : https://prove2.me/submissions/0df09b60-fcbe-41b7-9dbe-57347c441ba4

import Mathlib
import Definitions.Def_CubicRegNewton_LocalQuad_StandingAssumptions
import Definitions.Def_CubicRegNewton_LocalQuad_cubicModel
import Definitions.Def_CubicRegNewton_LocalQuad_lamMin
import Definitions.Def_CubicRegNewton_LocalQuad_delta
import Definitions.Def_CubicRegNewton_LocalQuad_IsRelaxedCubicRun
set_option autoImplicit false
open scoped InnerProductSpace

namespace CRN89
open CubicRegNewton.LocalQuad

variable {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {L : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}

/-! ## C7: scalar invariant -/

theorem scalar_base {u0 s m u1 w1 : ℝ} (hu0 : u0 ≤ 1 / 4) (hs : 0 ≤ s) (hm : 0 < m) (hm2 : m ≤ 2)
    (hstep : s + m / 2 * s ^ 2 ≤ u0) (hu1 : u1 ≤ (m / 2 + 1 / 2) * s ^ 2) (hw1 : 1 - s ≤ w1) :
    16 / 25 + 21 / 10 * u1 ≤ w1 ∧ 1875 / 512 * u1 ≤ 1 / 4 := by
  have hms : 0 ≤ m / 2 * s ^ 2 := by positivity
  have hs1 : s ≤ 1 / 4 := by linarith
  have hA : u1 ≤ 3 / 2 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hB : u1 ≤ 1 / 4 - s + s ^ 2 / 2 := by nlinarith
  rcases le_total s (21 / 100) with h | h
  · have h' := mul_le_mul_of_nonneg_left h hs
    constructor <;> nlinarith
  · have h' := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hs1)
    constructor <;> nlinarith

theorem scalar_step {u w s m u' w' : ℝ} (hJ1 : 16 / 25 + 21 / 10 * u ≤ w) (hJ2 : 1875 / 512 * u ≤ 1 / 4)
    (hu : 0 ≤ u) (hs : 0 ≤ s) (hm : 0 < m) (hm2 : m ≤ 2)
    (hstep : w * s + m / 2 * s ^ 2 ≤ u) (hu' : u' ≤ (m / 2 + 1 / 2) * s ^ 2) (hw' : w - s ≤ w') :
    (16 / 25 + 21 / 10 * u' ≤ w' ∧ 1875 / 512 * u' ≤ 1 / 4) ∧
      1875 / 512 * u' ≤ (1875 / 512 * u) ^ 2 := by
  have hw : 16 / 25 ≤ w := by linarith
  have hms : 0 ≤ m / 2 * s ^ 2 := by positivity
  have hws := mul_le_mul_of_nonneg_right hw hs
  have hs1 : 16 / 25 * s ≤ u := by linarith
  have hu'1 : u' ≤ 3 / 2 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hsq0 : (16 / 25 * s) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hs1 2
  have hu'2 : u' ≤ 1875 / 512 * u ^ 2 := by nlinarith
  have hsq : 1875 / 512 * u' ≤ (1875 / 512 * u) ^ 2 := by nlinarith
  have hJu := mul_le_mul_of_nonneg_left hJ2 hu
  refine ⟨⟨?_, ?_⟩, hsq⟩
  · nlinarith
  · nlinarith

/-! ## C5: lamMin facts -/

theorem lamMin_bdd (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    BddBelow (Set.range fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => ⟪H u, u⟫_ℝ) := by
  refine ⟨-‖H‖, ?_⟩
  rintro _ ⟨u, rfl⟩
  have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using u.2
  have h2 : ‖H u‖ ≤ ‖H‖ := by simpa [hu] using H.le_opNorm u
  have h3 : |⟪H u, u⟫_ℝ| ≤ ‖H‖ := (abs_real_inner_le_norm _ _).trans (by rw [hu, mul_one]; exact h2)
  show -‖H‖ ≤ ⟪H u, u⟫_ℝ
  linarith [neg_abs_le (⟪H u, u⟫_ℝ)]

theorem lamMin_mul_le (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) : lamMin H * ‖u‖ ^ 2 ≤ ⟪H u, u⟫_ℝ := by
  by_cases hu : u = 0
  · simp [hu]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨‖u‖⁻¹ • u, by simp [norm_smul, hn.ne']⟩
  have h1 : lamMin H ≤ ⟪H w, w⟫_ℝ := ciInf_le (lamMin_bdd H) w
  have h2 : ⟪H w, w⟫_ℝ = ‖u‖⁻¹ * (‖u‖⁻¹ * ⟪H u, u⟫_ℝ) := by
    simp only [w, map_smul, real_inner_smul_left, real_inner_smul_right]
  have h3 : ⟪H u, u⟫_ℝ = ‖u‖ ^ 2 * ⟪H w, w⟫_ℝ := by
    rw [h2]; field_simp
  rw [h3, mul_comm]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

theorem lamMin_pos (hn : 0 < n) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪H u, u⟫_ℝ) : 0 < lamMin H := by
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
  have hc : ContinuousOn (fun u : EuclideanSpace ℝ (Fin n) => ⟪H u, u⟫_ℝ)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    Continuous.continuousOn (by fun_prop)
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn hne hc
  have hv1 : v ≠ 0 := by rintro rfl; simp at hv
  haveI : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨v, hv⟩⟩
  have : ⟪H v, v⟫_ℝ ≤ lamMin H := le_ciInf fun u => isMinOn_iff.mp hmin _ u.2
  linarith [hH v hv1]

theorem lamMin_sub_le (H H' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    lamMin H - ‖H - H'‖ ≤ lamMin H' := by
  rcases isEmpty_or_nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) with h | h
  · simp [lamMin, Real.iInf_of_isEmpty]
  · show _ ≤ ⨅ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪H' u, u⟫_ℝ
    refine le_ciInf fun u => ?_
    have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using u.2
    have h1 := lamMin_mul_le H u
    have h2' : ‖(H - H') u‖ ≤ ‖H - H'‖ := by simpa [hu] using (H - H').le_opNorm u
    have h2 : |⟪(H - H') u, u⟫_ℝ| ≤ ‖H - H'‖ :=
      (abs_real_inner_le_norm _ _).trans (by rw [hu, mul_one]; exact h2')
    have h3 : ⟪(H - H') u, u⟫_ℝ = ⟪H u, u⟫_ℝ - ⟪H' u, u⟫_ℝ := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_left]
    rw [hu] at h1
    linarith [le_abs_self ⟪(H - H') u, u⟫_ℝ]

/-! ## C2, C3: Taylor bounds -/

theorem seg_mem (hS : StandingAssumptions F f f' f'' L x₀) {x v : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ F) (hxv : x + v ∈ F) : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • v ∈ F := by
  intro t ht
  have := hS.convex hx hxv (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1 (by ring)
  convert this using 1
  simp only [smul_add, sub_smul, one_smul]; abel

theorem Icc_nhds_Ici {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 ∈ nhdsWithin t (Set.Ici t) :=
  mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, ht.2, fun z hz => ⟨le_trans ht.1 hz.2, le_of_lt hz.1⟩⟩

theorem line_deriv (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivWithinAt (fun s : ℝ => x + s • v) v (Set.Icc 0 1) t := by
  simpa using (((hasDerivAt_id t).smul_const v).const_add x).hasDerivWithinAt

theorem grad_taylor_aux (hS : StandingAssumptions F f f' f'' L x₀) {x v : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ F) (hxv : x + v ∈ F) :
    ‖f' (x + v) - f' x - f'' x v‖ ≤ L / 2 * ‖v‖ ^ 2 := by
  have hseg := seg_mem hS hx hxv
  let φ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => f' (x + t • v) - f' x - t • f'' x v
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt φ (f'' (x + t • v) v - f'' x v) (Set.Icc 0 1) t := by
    intro t ht
    have h1 := (hS.hasHessian _ (hseg t ht)).comp_hasDerivWithinAt t (line_deriv x v t)
      (fun s hs => hseg s hs)
    have h2 : HasDerivWithinAt (fun s : ℝ => s • f'' x v) (f'' x v) (Set.Icc 0 1) t := by
      simpa using ((hasDerivAt_id t).smul_const (f'' x v)).hasDerivWithinAt
    exact (h1.sub_const (f' x)).sub h2
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖f'' (x + t • v) v - f'' x v‖ ≤ L * t * ‖v‖ ^ 2 := by
    intro t ht
    have hmem := hseg t (Set.Ico_subset_Icc_self ht)
    rw [← ContinuousLinearMap.sub_apply]
    calc _ ≤ ‖f'' (x + t • v) - f'' x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * ‖x + t • v - x‖) * ‖v‖ := by gcongr; exact hS.hessian_lipschitz _ hmem _ hx
      _ = L * t * ‖v‖ ^ 2 := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]; ring
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => L * t ^ 2 * ‖v‖ ^ 2 / 2) (L * t * ‖v‖ ^ 2) t := by
    intro t
    have := (((hasDerivAt_pow 2 t).const_mul L).mul_const (‖v‖ ^ 2)).div_const 2
    exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]; ring)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := φ) (a := 0) (b := 1) (B := fun t => L * t ^ 2 * ‖v‖ ^ 2 / 2)
    (B' := fun t => L * t * ‖v‖ ^ 2)
    (fun t ht => (hderiv t ht).continuousWithinAt)
    (fun t ht => (hderiv t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_nhds_Ici ht))
    (by simp [φ])
    hB
    hbound
  have := key (Set.right_mem_Icc.mpr zero_le_one)
  simp only [φ, one_smul] at this
  linarith

theorem grad_taylor (hS : StandingAssumptions F f f' f'' L x₀) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ F) (hy : y ∈ F) :
    ‖f' y - f' x - f'' x (y - x)‖ ≤ L / 2 * ‖y - x‖ ^ 2 := by
  have hxy : x + (y - x) = y := by abel
  have := grad_taylor_aux hS (v := y - x) hx (by rw [hxy]; exact hy)
  rwa [hxy] at this

theorem fun_taylor_aux (hS : StandingAssumptions F f f' f'' L x₀) {x v : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ F) (hxv : x + v ∈ F) :
    |f (x + v) - f x - ⟪f' x, v⟫_ℝ - 1 / 2 * ⟪f'' x v, v⟫_ℝ| ≤ L / 6 * ‖v‖ ^ 3 := by
  have hseg := seg_mem hS hx hxv
  let ψ : ℝ → ℝ := fun t => f (x + t • v) - f x - t * ⟪f' x, v⟫_ℝ - t ^ 2 / 2 * ⟪f'' x v, v⟫_ℝ
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt ψ
      (⟪f' (x + t • v), v⟫_ℝ - ⟪f' x, v⟫_ℝ - t * ⟪f'' x v, v⟫_ℝ) (Set.Icc 0 1) t := by
    intro t ht
    have hg : HasFDerivWithinAt f (InnerProductSpace.toDual ℝ _ (f' (x + t • v))) F (x + t • v) :=
      hS.hasGradient _ (hseg t ht)
    have h1 := hg.comp_hasDerivWithinAt t (line_deriv x v t) (fun s hs => hseg s hs)
    rw [InnerProductSpace.toDual_apply_apply] at h1
    have h2 : HasDerivWithinAt (fun s : ℝ => s * ⟪f' x, v⟫_ℝ) (⟪f' x, v⟫_ℝ) (Set.Icc 0 1) t := by
      simpa using ((hasDerivAt_id t).mul_const (⟪f' x, v⟫_ℝ)).hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun s : ℝ => s ^ 2 / 2 * ⟪f'' x v, v⟫_ℝ) (t * ⟪f'' x v, v⟫_ℝ)
        (Set.Icc 0 1) t := by
      have := (((hasDerivAt_pow 2 t).div_const 2).mul_const (⟪f'' x v, v⟫_ℝ)).hasDerivWithinAt
        (s := Set.Icc 0 1)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]; ring)
    exact ((h1.sub_const (f x)).sub h2).sub h3
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖⟪f' (x + t • v), v⟫_ℝ - ⟪f' x, v⟫_ℝ - t * ⟪f'' x v, v⟫_ℝ‖ ≤ L / 2 * t ^ 2 * ‖v‖ ^ 3 := by
    intro t ht
    have hmem := hseg t (Set.Ico_subset_Icc_self ht)
    have hg := grad_taylor_aux hS (v := t • v) hx hmem
    have he : ⟪f' (x + t • v), v⟫_ℝ - ⟪f' x, v⟫_ℝ - t * ⟪f'' x v, v⟫_ℝ =
        ⟪f' (x + t • v) - f' x - f'' x (t • v), v⟫_ℝ := by
      rw [map_smul, inner_sub_left, inner_sub_left, real_inner_smul_left]
    rw [he, Real.norm_eq_abs]
    calc _ ≤ ‖f' (x + t • v) - f' x - f'' x (t • v)‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (L / 2 * ‖t • v‖ ^ 2) * ‖v‖ := by gcongr
      _ = L / 2 * t ^ 2 * ‖v‖ ^ 3 := by
        rw [norm_smul, Real.norm_of_nonneg ht.1]; ring
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => L * t ^ 3 * ‖v‖ ^ 3 / 6) (L / 2 * t ^ 2 * ‖v‖ ^ 3) t := by
    intro t
    have := (((hasDerivAt_pow 3 t).const_mul L).mul_const (‖v‖ ^ 3)).div_const 6
    exact this.congr_deriv (by rw [show (3:ℕ) - 1 = 2 from rfl, Nat.cast_ofNat]; ring)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := ψ) (a := 0) (b := 1) (B := fun t => L * t ^ 3 * ‖v‖ ^ 3 / 6)
    (B' := fun t => L / 2 * t ^ 2 * ‖v‖ ^ 3)
    (fun t ht => (hderiv t ht).continuousWithinAt)
    (fun t ht => (hderiv t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_nhds_Ici ht))
    (by simp [ψ])
    hB
    hbound
  have := key (Set.right_mem_Icc.mpr zero_le_one)
  simp only [ψ, one_smul, Real.norm_eq_abs] at this
  convert this using 2 <;> ring

theorem fun_taylor (hS : StandingAssumptions F f f' f'' L x₀) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ F) (hy : y ∈ F) :
    |f y - f x - ⟪f' x, y - x⟫_ℝ - 1 / 2 * ⟪f'' x (y - x), y - x⟫_ℝ| ≤ L / 6 * ‖y - x‖ ^ 3 := by
  have hxy : x + (y - x) = y := by abel
  have := fun_taylor_aux hS (v := y - x) hx (by rw [hxy]; exact hy)
  rwa [hxy] at this

/-! ## C1: Hessian symmetry at interior points -/

theorem hess_symm (hS : StandingAssumptions F f f' f'' L x₀) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ interior F) (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪f'' x u, v⟫_ℝ = ⟪f'' x v, u⟫_ℝ := by
  have hev : ∀ᶠ y in nhds x, HasFDerivAt f (innerSL ℝ (f' y)) y := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    have h1 : HasFDerivWithinAt f (InnerProductSpace.toDual ℝ _ (f' y)) F y :=
      hS.hasGradient y (interior_subset hy)
    have h2 := h1.hasFDerivAt (mem_interior_iff_mem_nhds.mp hy)
    have he : InnerProductSpace.toDual ℝ _ (f' y) = innerSL ℝ (f' y) := by
      ext w; simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    rwa [he] at h2
  have hd : HasFDerivAt (fun y => innerSL ℝ (f' y)) ((innerSL ℝ).comp (f'' x)) x :=
    (innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hS.hasHessian x (interior_subset hx)).hasFDerivAt (mem_interior_iff_mem_nhds.mp hx))
  have := second_derivative_symmetric_of_eventually hev hd u v
  simpa [innerSL_apply_apply] using this

/-! ## C4: first-order condition of the cubic model -/

theorem cubic_foc {x y : EuclideanSpace ℝ (Fin n)} {M : ℝ}
    (hmin : IsMinOn (cubicModel f' f'' M x) Set.univ y)
    (hsym : ∀ u v, ⟪f'' x u, v⟫_ℝ = ⟪f'' x v, u⟫_ℝ) :
    f' x + f'' x (y - x) + (M / 2 * ‖y - x‖) • (y - x) = 0 := by
  set h := y - x with hh
  set V := f' x + f'' x h + (M / 2 * ‖h‖) • h with hV
  have key : ∀ w, ⟪V, w⟫_ℝ = 0 := by
    intro w
    let φ : ℝ → ℝ := fun t => cubicModel f' f'' M x (y + t • w)
    have hφ : φ = fun t => ⟪f' x, h + t • w⟫_ℝ + 1 / 2 * ⟪f'' x (h + t • w), h + t • w⟫_ℝ
        + M / 6 * ‖h + t • w‖ ^ (3 : ℝ) := by
      funext t
      simp only [φ, cubicModel]
      rw [show y + t • w - x = h + t • w by rw [hh]; abel]
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hmin0 : IsLocalMin φ 0 := Filter.Eventually.of_forall fun t => by
      simpa [φ] using isMinOn_iff.mp hmin (y + t • w) (Set.mem_univ _)
    have hl : HasDerivAt (fun t : ℝ => h + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add h
    have d1 : HasDerivAt (fun t : ℝ => ⟪f' x, h + t • w⟫_ℝ) (⟪f' x, w⟫_ℝ) 0 := by
      have := HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_const (0 : ℝ) (f' x)) hl
      simpa only [zero_smul, add_zero, inner_zero_left] using this
    have d2 : HasDerivAt (fun t : ℝ => ⟪f'' x (h + t • w), h + t • w⟫_ℝ)
        (⟪f'' x h, w⟫_ℝ + ⟪f'' x w, h⟫_ℝ) 0 := by
      have hH : HasDerivAt (fun t : ℝ => f'' x (h + t • w)) (f'' x w) 0 :=
        (f'' x).hasFDerivAt.comp_hasDerivAt 0 hl
      have := HasDerivAt.inner (𝕜 := ℝ) hH hl
      simpa only [zero_smul, add_zero] using this
    have d3 : HasDerivAt (fun t : ℝ => ‖h + t • w‖ ^ (3 : ℝ)) (3 * ‖h‖ * ⟪h, w⟫_ℝ) 0 := by
      have := (hasFDerivAt_norm_rpow (h + (0 : ℝ) • w) (p := 3) (by norm_num)).comp_hasDerivAt 0 hl
      refine this.congr_deriv ?_
      simp only [zero_smul, add_zero, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
      norm_num
    have hd := (d1.add (d2.const_mul (1 / 2))).add (d3.const_mul (M / 6))
    have hd' : HasDerivAt φ (⟪f' x, w⟫_ℝ + 1 / 2 * (⟪f'' x h, w⟫_ℝ + ⟪f'' x w, h⟫_ℝ)
        + M / 6 * (3 * ‖h‖ * ⟪h, w⟫_ℝ)) 0 := by
      rw [hφ]; exact hd
    have h0 := hmin0.hasDerivAt_eq_zero hd'
    have hs := hsym w h
    rw [hV, inner_add_left, inner_add_left, real_inner_smul_left]
    rw [hs] at h0
    linear_combination h0
  have := key V
  rw [real_inner_self_eq_norm_sq] at this
  have hV0 : V = 0 := by simpa using this
  simpa only [hV] using hV0

/-! ## C6: one step of the scheme -/

theorem one_step (hS : StandingAssumptions F f f' f'' L x₀) {x y : EuclideanSpace ℝ (Fin n)} {M : ℝ}
    (hx : x ∈ interior F) (hfx : f x ≤ f x₀) (hlam : 0 < lamMin (f'' x))
    (hδ : L * ‖f' x‖ ≤ lamMin (f'' x) ^ 2 / 4) (hM : 0 < M) (hM2 : M ≤ 2 * L)
    (hmin : IsMinOn (cubicModel f' f'' M x) Set.univ y) :
    y ∈ interior F ∧ f y ≤ f x ∧
      lamMin (f'' x) * ‖y - x‖ + M / 2 * ‖y - x‖ ^ 2 ≤ ‖f' x‖ ∧
      ‖f' y‖ ≤ (M / 2 + L / 2) * ‖y - x‖ ^ 2 ∧
      lamMin (f'' x) - L * ‖y - x‖ ≤ lamMin (f'' y) := by
  have hxF : x ∈ F := interior_subset hx
  have hfoc := cubic_foc hmin (hess_symm hS hx)
  set h := y - x with hh
  have hq : lamMin (f'' x) * ‖h‖ ^ 2 ≤ ⟪f'' x h, h⟫_ℝ := lamMin_mul_le _ _
  have ha : ⟪f' x, h⟫_ℝ = -⟪f'' x h, h⟫_ℝ - M / 2 * ‖h‖ ^ 3 := by
    have := congrArg (fun z => ⟪z, h⟫_ℝ) hfoc
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
      real_inner_self_eq_norm_sq] at this
    linear_combination this
  have hcs : -⟪f' x, h⟫_ℝ ≤ ‖f' x‖ * ‖h‖ := by
    have := abs_real_inner_le_norm (f' x) h
    linarith [neg_abs_le ⟪f' x, h⟫_ℝ]
  have hstep : lamMin (f'' x) * ‖h‖ + M / 2 * ‖h‖ ^ 2 ≤ ‖f' x‖ := by
    rcases (norm_nonneg h).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have : ‖h‖ * (lamMin (f'' x) * ‖h‖ + M / 2 * ‖h‖ ^ 2) ≤ ‖h‖ * ‖f' x‖ := by nlinarith
      exact le_of_mul_le_mul_left this hpos
  have hLr : L * ‖h‖ ≤ lamMin (f'' x) / 4 := by
    have hMh : 0 ≤ M / 2 * ‖h‖ ^ 2 := by positivity
    have h1 : lamMin (f'' x) * ‖h‖ ≤ ‖f' x‖ := by linarith
    have h1' := mul_le_mul_of_nonneg_left h1 hS.L_pos.le
    have h2 : lamMin (f'' x) * (L * ‖h‖) ≤ lamMin (f'' x) * (lamMin (f'' x) / 4) := by nlinarith
    exact le_of_mul_le_mul_left h2 hlam
  have hdec : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ F → f (x + t • h) ≤ f x := by
    intro t ht hz
    have hT := fun_taylor_aux hS (v := t • h) hxF hz
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul,
      Real.norm_of_nonneg ht.1] at hT
    have hT' := (le_abs_self _).trans hT
    rw [ha] at hT'
    have ht1 : 0 ≤ t - t ^ 2 / 2 := by nlinarith [ht.1, ht.2]
    have e1 := mul_le_mul_of_nonneg_left hq ht1
    have e2 : t / 2 * (lamMin (f'' x) * ‖h‖ ^ 2) ≤ (t - t ^ 2 / 2) * (lamMin (f'' x) * ‖h‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith [ht.1, ht.2]) (by positivity)
    have e3 : (t ^ 3 * ‖h‖ ^ 2) * (L * ‖h‖) ≤ (t ^ 3 * ‖h‖ ^ 2) * (lamMin (f'' x) / 4) :=
      mul_le_mul_of_nonneg_left hLr (by have := ht.1; positivity)
    have ht3 : t ^ 3 ≤ t := by nlinarith [ht.1, ht.2, mul_nonneg ht.1 ht.1]
    have e4 : t ^ 3 * (‖h‖ ^ 2 * lamMin (f'' x)) ≤ t * (‖h‖ ^ 2 * lamMin (f'' x)) :=
      mul_le_mul_of_nonneg_right ht3 (by positivity)
    have e5 : 0 ≤ t * (M / 2 * ‖h‖ ^ 3) := mul_nonneg ht.1 (by positivity)
    have e6 : 0 ≤ t * ‖h‖ ^ 2 * lamMin (f'' x) := by have := ht.1; positivity
    nlinarith
  have hcl : IsClosed ({t : ℝ | x + t • h ∈ F} ∩ Set.Icc 0 1) :=
    (hS.isClosed.preimage (by fun_prop)).inter isClosed_Icc
  have hall := IsClosed.Icc_subset_of_forall_mem_nhdsWithin hcl (by simpa using hxF) (by
    intro t ht
    have hzF : x + t • h ∈ F := ht.1
    have hzI : x + t • h ∈ interior F := hS.levelSet_subset_interior
      ⟨hzF, (hdec t (Set.Ico_subset_Icc_self ht.2) hzF).trans hfx⟩
    have hO : {s : ℝ | x + s • h ∈ interior F} ∈ nhds t :=
      (isOpen_interior.preimage (by fun_prop)).mem_nhds hzI
    exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset hO fun s hs => (interior_subset : interior F ⊆ F) hs))
  have h1 : x + (1 : ℝ) • h = y := by rw [one_smul, hh]; abel
  have hyF : y ∈ F := by
    have := hall (Set.right_mem_Icc.mpr zero_le_one)
    rw [Set.mem_setOf_eq, h1] at this; exact this
  have hfy : f y ≤ f x := by
    have := hdec 1 (Set.right_mem_Icc.mpr zero_le_one) (by rw [h1]; exact hyF)
    rwa [h1] at this
  have hyI : y ∈ interior F := hS.levelSet_subset_interior ⟨hyF, hfy.trans hfx⟩
  have hg := grad_taylor hS hxF hyF
  have he : f' y = (f' y - f' x - f'' x h) - (M / 2 * ‖h‖) • h := by
    rw [← sub_eq_zero, ← hfoc]; abel
  have hc0 : 0 ≤ M / 2 * ‖h‖ := mul_nonneg (by linarith) (norm_nonneg h)
  have hgrad : ‖f' y‖ ≤ (M / 2 + L / 2) * ‖h‖ ^ 2 := by
    calc ‖f' y‖ = ‖(f' y - f' x - f'' x h) - (M / 2 * ‖h‖) • h‖ := congrArg _ he
      _ ≤ ‖f' y - f' x - f'' x h‖ + ‖(M / 2 * ‖h‖) • h‖ := norm_sub_le _ _
      _ ≤ L / 2 * ‖h‖ ^ 2 + M / 2 * ‖h‖ * ‖h‖ :=
          add_le_add hg (le_of_eq (by rw [norm_smul, Real.norm_of_nonneg hc0]))
      _ = (M / 2 + L / 2) * ‖h‖ ^ 2 := by ring
  have hlip := hS.hessian_lipschitz x hxF y hyF
  have hxy : ‖x - y‖ = ‖h‖ := by rw [hh, norm_sub_rev]
  have hsub := lamMin_sub_le (f'' x) (f'' y)
  refine ⟨hyI, hfy, hstep, hgrad, ?_⟩
  rw [hxy] at hlip
  linarith

/-! ## C8a: rescaled step and the run invariant -/

theorem step_norm (hS : StandingAssumptions F f f' f'' L x₀) {x y : EuclideanSpace ℝ (Fin n)} {M c : ℝ}
    (hx : x ∈ interior F) (hfx : f x ≤ f x₀) (hM : 0 < M) (hM2 : M ≤ 2 * L)
    (hmin : IsMinOn (cubicModel f' f'' M x) Set.univ y) (hc : 0 < c)
    (hw : 0 < lamMin (f'' x) / c) (hu : L * ‖f' x‖ / c ^ 2 ≤ (lamMin (f'' x) / c) ^ 2 / 4) :
    y ∈ interior F ∧ f y ≤ f x ∧
      lamMin (f'' x) / c * (L * ‖y - x‖ / c) + M / L / 2 * (L * ‖y - x‖ / c) ^ 2 ≤
        L * ‖f' x‖ / c ^ 2 ∧
      L * ‖f' y‖ / c ^ 2 ≤ (M / L / 2 + 1 / 2) * (L * ‖y - x‖ / c) ^ 2 ∧
      lamMin (f'' x) / c - L * ‖y - x‖ / c ≤ lamMin (f'' y) / c := by
  have hL := hS.L_pos
  have hc0 : c ≠ 0 := hc.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hlam : 0 < lamMin (f'' x) := by
    have := mul_pos hw hc; rwa [div_mul_cancel₀ _ hc0] at this
  have hδ : L * ‖f' x‖ ≤ lamMin (f'' x) ^ 2 / 4 := by
    have e1 : L * ‖f' x‖ = L * ‖f' x‖ / c ^ 2 * c ^ 2 := by
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 hc0)]
    have e2 : lamMin (f'' x) ^ 2 / 4 = (lamMin (f'' x) / c) ^ 2 / 4 * c ^ 2 := by
      field_simp
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right hu (sq_nonneg c)
  obtain ⟨h1, h2, h3, h4, h5⟩ := one_step hS hx hfx hlam hδ hM hM2 hmin
  have hLc : 0 ≤ L / c ^ 2 := div_nonneg hL.le (sq_nonneg c)
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · have e : lamMin (f'' x) / c * (L * ‖y - x‖ / c) + M / L / 2 * (L * ‖y - x‖ / c) ^ 2
        = L / c ^ 2 * (lamMin (f'' x) * ‖y - x‖ + M / 2 * ‖y - x‖ ^ 2) := by
      field_simp
    rw [e, show L * ‖f' x‖ / c ^ 2 = L / c ^ 2 * ‖f' x‖ by ring]
    exact mul_le_mul_of_nonneg_left h3 hLc
  · have e : (M / L / 2 + 1 / 2) * (L * ‖y - x‖ / c) ^ 2
        = L / c ^ 2 * ((M / 2 + L / 2) * ‖y - x‖ ^ 2) := by
      field_simp
    rw [e, show L * ‖f' y‖ / c ^ 2 = L / c ^ 2 * ‖f' y‖ by ring]
    exact mul_le_mul_of_nonneg_left h4 hLc
  · rw [← sub_div]; exact div_le_div_of_nonneg_right h5 hc.le

theorem run_inv {x : ℕ → EuclideanSpace ℝ (Fin n)} {M : ℕ → ℝ}
    (hS : StandingAssumptions F f f' f'' L x₀) (hn : 0 < n)
    (hpd : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪f'' x₀ u, u⟫_ℝ)
    (hδ : delta L f' f'' x₀ ≤ 1 / 4)
    (hrun : IsRelaxedCubicRun f' f'' L x M) (hx0 : x 0 = x₀) :
    ∀ k : ℕ, x (k + 1) ∈ interior F ∧ f (x (k + 1)) ≤ f x₀ ∧
      16 / 25 + 21 / 10 * (L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2) ≤
        lamMin (f'' (x (k + 1))) / lamMin (f'' x₀) ∧
      1875 / 512 * (L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2) ≤ 1 / 4 ∧
      1875 / 512 * (L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2) ≤ (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
  have hl0 := lamMin_pos hn _ hpd
  have hL := hS.L_pos
  intro k
  induction k with
  | zero =>
    obtain ⟨hM, hM2, hmin⟩ := hrun 0
    rw [hx0] at hmin
    have hW0 : lamMin (f'' x₀) / lamMin (f'' x₀) = 1 := div_self hl0.ne'
    have hU0 : L * ‖f' x₀‖ / lamMin (f'' x₀) ^ 2 ≤ 1 / 4 := hδ
    obtain ⟨h1, h2, h3, h4, h5⟩ := step_norm hS (c := lamMin (f'' x₀)) hS.x₀_mem_interior le_rfl
      hM hM2 hmin hl0 (by rw [hW0]; norm_num) (by rw [hW0]; linarith)
    rw [hW0] at h3 h5
    have hs0 : 0 ≤ L * ‖x (0 + 1) - x₀‖ / lamMin (f'' x₀) :=
      div_nonneg (mul_nonneg hL.le (norm_nonneg _)) hl0.le
    have hJ := scalar_base hU0 hs0 (div_pos hM hL) (by rw [div_le_iff₀ hL]; linarith)
      (by linarith [h3]) h4 h5
    have e : (1 / 2 : ℝ) ^ (2 ^ (0 + 1)) = 1 / 4 := by norm_num
    exact ⟨h1, h2, hJ.1, hJ.2, by rw [e]; exact hJ.2⟩
  | succ k ih =>
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih
    obtain ⟨hM, hM2, hmin⟩ := hrun (k + 1)
    have hu0 : 0 ≤ L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2 :=
      div_nonneg (mul_nonneg hL.le (norm_nonneg _)) (sq_nonneg _)
    have hw64 : 16 / 25 ≤ lamMin (f'' (x (k + 1))) / lamMin (f'' x₀) := by linarith
    have hwpos : 0 < lamMin (f'' (x (k + 1))) / lamMin (f'' x₀) := by linarith
    have hpre : L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2 ≤
        (lamMin (f'' (x (k + 1))) / lamMin (f'' x₀)) ^ 2 / 4 := by
      nlinarith [mul_le_mul hw64 hw64 (by norm_num) hwpos.le]
    obtain ⟨h1, h2, h3, h4, h5⟩ := step_norm hS i1 i2 hM hM2 hmin hl0 hwpos hpre
    have hs0 : 0 ≤ L * ‖x (k + 1 + 1) - x (k + 1)‖ / lamMin (f'' x₀) :=
      div_nonneg (mul_nonneg hL.le (norm_nonneg _)) hl0.le
    obtain ⟨⟨j1, j2⟩, j3⟩ := scalar_step i3 i4 hu0 hs0 (div_pos hM hL)
      (by rw [div_le_iff₀ hL]; linarith) h3 h4 h5
    refine ⟨h1, h2.trans i2, j1, j2, ?_⟩
    calc _ ≤ _ := j3
      _ ≤ ((1 / 2 : ℝ) ^ (2 ^ (k + 1))) ^ 2 := pow_le_pow_left₀ (by positivity) i5 2
      _ = (1 / 2 : ℝ) ^ (2 ^ (k + 1 + 1)) := by rw [← pow_mul, pow_succ 2 (k + 1)]

/-! ## C8b: per-step facts along the run, and an abstract convergence lemma -/

theorem step_all {x : ℕ → EuclideanSpace ℝ (Fin n)} {M : ℕ → ℝ}
    (hS : StandingAssumptions F f f' f'' L x₀) (hn : 0 < n)
    (hpd : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪f'' x₀ u, u⟫_ℝ)
    (hδ : delta L f' f'' x₀ ≤ 1 / 4)
    (hrun : IsRelaxedCubicRun f' f'' L x M) (hx0 : x 0 = x₀) :
    ∀ k : ℕ, x k ∈ interior F ∧ f (x k) ≤ f x₀ ∧
      16 / 25 * (L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀)) ≤ L * ‖f' (x k)‖ / lamMin (f'' x₀) ^ 2 ∧
      L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2 ≤
        3 / 2 * (L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀)) ^ 2 ∧
      L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀) ≤ 1 / 4 := by
  have hl0 := lamMin_pos hn _ hpd
  have hL := hS.L_pos
  intro k
  have hs0 : 0 ≤ L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀) :=
    div_nonneg (mul_nonneg hL.le (norm_nonneg _)) hl0.le
  obtain ⟨hM, hM2, hmin⟩ := hrun k
  have hm2 : M k / L ≤ 2 := by rw [div_le_iff₀ hL]; linarith
  have hm0 : 0 < M k / L := div_pos hM hL
  have hsq := mul_le_mul_of_nonneg_right hm2 (sq_nonneg (L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀)))
  have hq : 0 ≤ M k / L / 2 * (L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀)) ^ 2 := by positivity
  cases k with
  | zero =>
    rw [hx0] at hmin hs0 hsq hq ⊢
    have hW0 : lamMin (f'' x₀) / lamMin (f'' x₀) = 1 := div_self hl0.ne'
    have hU0 : L * ‖f' x₀‖ / lamMin (f'' x₀) ^ 2 ≤ 1 / 4 := hδ
    obtain ⟨h1, h2, h3, h4, h5⟩ := step_norm hS (c := lamMin (f'' x₀)) hS.x₀_mem_interior le_rfl
      hM hM2 hmin hl0 (by rw [hW0]; norm_num) (by rw [hW0]; linarith)
    rw [hW0] at h3
    refine ⟨hS.x₀_mem_interior, le_rfl, by nlinarith, by nlinarith, by nlinarith⟩
  | succ j =>
    obtain ⟨i1, i2, i3, i4, i5⟩ := run_inv hS hn hpd hδ hrun hx0 j
    have hu0 : 0 ≤ L * ‖f' (x (j + 1))‖ / lamMin (f'' x₀) ^ 2 :=
      div_nonneg (mul_nonneg hL.le (norm_nonneg _)) (sq_nonneg _)
    have hw64 : 16 / 25 ≤ lamMin (f'' (x (j + 1))) / lamMin (f'' x₀) := by linarith
    have hwpos : 0 < lamMin (f'' (x (j + 1))) / lamMin (f'' x₀) := by linarith
    have hpre : L * ‖f' (x (j + 1))‖ / lamMin (f'' x₀) ^ 2 ≤
        (lamMin (f'' (x (j + 1))) / lamMin (f'' x₀)) ^ 2 / 4 := by
      nlinarith [mul_le_mul hw64 hw64 (by norm_num) hwpos.le]
    obtain ⟨h1, h2, h3, h4, h5⟩ := step_norm hS i1 i2 hM hM2 hmin hl0 hwpos hpre
    have hws := mul_le_mul_of_nonneg_right hw64 hs0
    refine ⟨i1, i2, by nlinarith, by nlinarith, by nlinarith⟩

theorem U_succ_le {x : ℕ → EuclideanSpace ℝ (Fin n)} {M : ℕ → ℝ}
    (hS : StandingAssumptions F f f' f'' L x₀) (hn : 0 < n)
    (hpd : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪f'' x₀ u, u⟫_ℝ)
    (hδ : delta L f' f'' x₀ ≤ 1 / 4)
    (hrun : IsRelaxedCubicRun f' f'' L x M) (hx0 : x 0 = x₀) (k : ℕ) :
    L * ‖f' (x (k + 1 + 1))‖ / lamMin (f'' x₀) ^ 2 ≤
      L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2 / 4 := by
  have hl0 := lamMin_pos hn _ hpd
  have hL := hS.L_pos
  obtain ⟨-, -, a3, a4, -⟩ := step_all hS hn hpd hδ hrun hx0 (k + 1)
  obtain ⟨-, -, -, i4, -⟩ := run_inv hS hn hpd hδ hrun hx0 k
  have hs0 : 0 ≤ L * ‖x (k + 1 + 1) - x (k + 1)‖ / lamMin (f'' x₀) :=
    div_nonneg (mul_nonneg hL.le (norm_nonneg _)) hl0.le
  have hu0 : 0 ≤ L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2 :=
    div_nonneg (mul_nonneg hL.le (norm_nonneg _)) (sq_nonneg _)
  have hs1 : L * ‖x (k + 1 + 1) - x (k + 1)‖ / lamMin (f'' x₀) ≤
      25 / 16 * (L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2) := by linarith
  have hs2 := pow_le_pow_left₀ hs0 hs1 2
  nlinarith [mul_le_mul_of_nonneg_left i4 hu0]

theorem seq_conv {z : ℕ → EuclideanSpace ℝ (Fin n)} {U : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hr : ∀ k, ‖z (k + 1) - z k‖ ≤ A * U k) (hU : ∀ k, U (k + 1 + 1) ≤ U (k + 1) / 4) :
    ∃ xs, Filter.Tendsto z Filter.atTop (nhds xs) ∧
      ∀ k, ‖z (k + 1) - xs‖ ≤ 4 / 3 * A * U (k + 1) := by
  obtain ⟨B, hB0, hB1⟩ : ∃ B, U 0 ≤ B ∧ 4 * U 1 ≤ B :=
    ⟨max (U 0) (4 * U 1), le_max_left _ _, le_max_right _ _⟩
  have hgeom1 : ∀ k, U (k + 1) ≤ B * (1 / 4) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp only [zero_add, pow_one]; linarith
    | succ k ih =>
      calc U (k + 1 + 1) ≤ U (k + 1) / 4 := hU k
        _ ≤ B * (1 / 4) ^ (k + 1) / 4 := by linarith
        _ = B * (1 / 4) ^ (k + 1 + 1) := by ring
  have hgeom : ∀ k, U k ≤ B * (1 / 4) ^ k := by
    intro k
    cases k with
    | zero => simpa using hB0
    | succ k => exact hgeom1 k
  have hdist : ∀ k, dist (z k) (z (k + 1)) ≤ A * B * (1 / 4) ^ k := by
    intro k
    rw [dist_comm, dist_eq_norm]
    calc _ ≤ A * U k := hr k
      _ ≤ A * (B * (1 / 4) ^ k) := mul_le_mul_of_nonneg_left (hgeom k) hA
      _ = _ := by ring
  obtain ⟨xs, hxs⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 4 : ℝ) (A * B) (by norm_num) hdist)
  refine ⟨xs, hxs, fun k => ?_⟩
  have hUj : ∀ j, U (j + (k + 1)) ≤ U (k + 1) * (1 / 4) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hU (j + k)
      rw [show j + k + 1 + 1 = j + 1 + (k + 1) by omega, show j + k + 1 = j + (k + 1) by omega] at this
      calc U (j + 1 + (k + 1)) ≤ U (j + (k + 1)) / 4 := this
        _ ≤ U (k + 1) * (1 / 4) ^ j / 4 := by linarith
        _ = _ := by ring
  have hd : ∀ j, dist (z (j + (k + 1))) (z (j + 1 + (k + 1))) ≤ (A * U (k + 1)) * (1 / 4) ^ j := by
    intro j
    rw [dist_comm, dist_eq_norm, show j + 1 + (k + 1) = j + (k + 1) + 1 by omega]
    calc _ ≤ A * U (j + (k + 1)) := hr _
      _ ≤ A * (U (k + 1) * (1 / 4) ^ j) := mul_le_mul_of_nonneg_left (hUj j) hA
      _ = _ := by ring
  have hlim' : Filter.Tendsto (fun j => z (j + (k + 1))) Filter.atTop (nhds xs) :=
    hxs.comp (Filter.tendsto_add_atTop_nat (k + 1))
  have := dist_le_of_le_geometric_of_tendsto (1 / 4 : ℝ) (A * U (k + 1)) (by norm_num) hd hlim' 0
  rw [dist_eq_norm, show (0 : ℕ) + (k + 1) = k + 1 by omega] at this
  calc _ ≤ _ := this
    _ = _ := by ring

end CRN89

open CubicRegNewton.LocalQuad InnerProductSpace in
theorem solution {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {L : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {M : ℕ → ℝ}
    (hS : StandingAssumptions F f f' f'' L x₀)
    (hpd : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪f'' x₀ u, u⟫_ℝ)
    (hδ : delta L f' f'' x₀ ≤ 1 / 4)
    (hrun : IsRelaxedCubicRun f' f'' L x M) (hx0 : x 0 = x₀) :
    ∃ xs : EuclideanSpace ℝ (Fin n),
      Filter.Tendsto x Filter.atTop (nhds xs) ∧
      xs ∈ interior F ∧ f' xs = 0 ∧
      (∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪f'' xs u, u⟫_ℝ) ∧
      IsLocalMin f xs ∧
      (∃ C : ℝ, ∀ k : ℕ, ‖x (k + 1) - xs‖ ≤ C * ‖x k - xs‖ ^ 2) ∧
      (∃ C : ℝ, ∀ k : ℕ, ‖x k - xs‖ ≤ C * (1 / 2 : ℝ) ^ (2 ^ k)) ∧
      ∀ k : ℕ, 1 ≤ k →
        ‖f' (x k)‖ ≤
          lamMin (f'' x₀) ^ 2 * (9 * Real.exp (3 / 2) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
  have hL := hS.L_pos
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hsub : ∀ v w : EuclideanSpace ℝ (Fin 0), v = w := fun v w => by
      ext i; exact Fin.elim0 i
    refine ⟨x₀, tendsto_const_nhds.congr (fun k => hsub _ _), hS.x₀_mem_interior, hsub _ _,
      fun u hu => absurd (hsub u 0) hu,
      Filter.Eventually.of_forall fun y => by rw [hsub y x₀],
      ⟨0, fun k => by rw [hsub (x (k + 1) - x₀) 0, norm_zero]; positivity⟩,
      ⟨0, fun k => by rw [hsub (x k - x₀) 0, norm_zero]; positivity⟩,
      fun k _ => by rw [hsub (f' (x k)) 0, norm_zero]; positivity⟩
  have hl0 := CRN89.lamMin_pos hn _ hpd
  have hall := CRN89.step_all hS hn hpd hδ hrun hx0
  have hinv := CRN89.run_inv hS hn hpd hδ hrun hx0
  have hA : 0 ≤ 25 / 16 * (lamMin (f'' x₀) / L) := by positivity
  have hr : ∀ k, ‖x (k + 1) - x k‖ ≤
      25 / 16 * (lamMin (f'' x₀) / L) * (L * ‖f' (x k)‖ / lamMin (f'' x₀) ^ 2) := by
    intro k
    obtain ⟨-, -, a3, -, -⟩ := hall k
    have e : ‖x (k + 1) - x k‖ =
        lamMin (f'' x₀) / L * (L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀)) := by
      field_simp
    calc ‖x (k + 1) - x k‖ = lamMin (f'' x₀) / L * (L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀)) := e
      _ ≤ lamMin (f'' x₀) / L * (25 / 16 * (L * ‖f' (x k)‖ / lamMin (f'' x₀) ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  obtain ⟨xs, hlim, htail⟩ := CRN89.seq_conv (U := fun k => L * ‖f' (x k)‖ / lamMin (f'' x₀) ^ 2) hA hr
    (CRN89.U_succ_le hS hn hpd hδ hrun hx0)
  have htail' : ∀ k, ‖x (k + 1) - xs‖ ≤
      4 / 3 * (25 / 16 * (lamMin (f'' x₀) / L)) * (L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2) :=
    fun k => htail k
  have hxF : ∀ k, x k ∈ F := fun k => interior_subset (hall k).1
  have hxsF : xs ∈ F := hS.isClosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hxF)
  have hlimF : Filter.Tendsto x Filter.atTop (nhdsWithin xs F) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall hxF⟩
  have hcf : ContinuousWithinAt f F xs :=
    HasFDerivWithinAt.continuousWithinAt (hS.hasGradient xs hxsF)
  have hfxs : f xs ≤ f x₀ :=
    le_of_tendsto (hcf.tendsto.comp hlimF) (Filter.Eventually.of_forall fun k => (hall k).2.1)
  have hxsI : xs ∈ interior F := hS.levelSet_subset_interior ⟨hxsF, hfxs⟩
  -- gradient bound (3.8 shape) along the run
  have hg38 : ∀ k, ‖f' (x (k + 1))‖ ≤
      512 / 1875 * (lamMin (f'' x₀) ^ 2 / L) * (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
    intro k
    have h5 := (hinv k).2.2.2.2
    have e : ‖f' (x (k + 1))‖ =
        lamMin (f'' x₀) ^ 2 / L * (L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2) := by
      field_simp
    rw [e]
    have hpos : 0 ≤ lamMin (f'' x₀) ^ 2 / L := by positivity
    have := mul_le_mul_of_nonneg_left h5 hpos
    nlinarith
  have hT2 : Filter.Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (2 ^ k)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by norm_num))
  have hgrad0 : Filter.Tendsto (fun k => f' (x (k + 1))) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm hg38 ?_
    have := (hT2.comp (Filter.tendsto_add_atTop_nat 1)).const_mul (512 / 1875 * (lamMin (f'' x₀) ^ 2 / L))
    simpa using this
  have hcf' : ContinuousWithinAt f' F xs := (hS.hasHessian xs hxsF).continuousWithinAt
  have hgradxs : Filter.Tendsto (fun k => f' (x (k + 1))) Filter.atTop (nhds (f' xs)) :=
    hcf'.tendsto.comp (hlimF.comp (Filter.tendsto_add_atTop_nat 1))
  have hf'0 : f' xs = 0 := tendsto_nhds_unique hgradxs hgrad0
  -- positive definiteness at the limit
  have hen : Filter.Tendsto (fun k => ‖x (k + 1) - xs‖) Filter.atTop (nhds 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim).comp (Filter.tendsto_add_atTop_nat 1)
  have hlamxs : 16 / 25 * lamMin (f'' x₀) ≤ lamMin (f'' xs) := by
    have h1 : ∀ k, 16 / 25 * lamMin (f'' x₀) - L * ‖x (k + 1) - xs‖ ≤ lamMin (f'' xs) := by
      intro k
      have hw := (hinv k).2.2.1
      have hU0 : 0 ≤ L * ‖f' (x (k + 1))‖ / lamMin (f'' x₀) ^ 2 :=
        div_nonneg (mul_nonneg hL.le (norm_nonneg _)) (sq_nonneg _)
      have hw' : 16 / 25 * lamMin (f'' x₀) ≤ lamMin (f'' (x (k + 1))) := by
        have : 16 / 25 ≤ lamMin (f'' (x (k + 1))) / lamMin (f'' x₀) := by linarith
        rwa [le_div_iff₀ hl0] at this
      have := CRN89.lamMin_sub_le (f'' (x (k + 1))) (f'' xs)
      have hlip := hS.hessian_lipschitz _ (hxF (k + 1)) _ hxsF
      linarith
    have ht : Filter.Tendsto (fun k => 16 / 25 * lamMin (f'' x₀) - L * ‖x (k + 1) - xs‖)
        Filter.atTop (nhds (16 / 25 * lamMin (f'' x₀) - L * 0)) :=
      tendsto_const_nhds.sub (hen.const_mul L)
    have := le_of_tendsto' ht h1
    simpa using this
  have hlpos : 0 < lamMin (f'' xs) := by linarith
  have hpdxs : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪f'' xs u, u⟫_ℝ := fun u hu =>
    lt_of_lt_of_le (mul_pos hlpos (pow_pos (norm_pos_iff.mpr hu) 2)) (CRN89.lamMin_mul_le _ u)
  -- local minimum
  have hloc : IsLocalMin f xs := by
    have hball : Metric.ball xs (3 * lamMin (f'' xs) / L) ∩ interior F ∈ nhds xs :=
      Filter.inter_mem (Metric.ball_mem_nhds _ (by positivity)) (isOpen_interior.mem_nhds hxsI)
    filter_upwards [hball] with z hz
    have hzF := interior_subset hz.2
    have hT := CRN89.fun_taylor hS hxsF hzF
    rw [hf'0, inner_zero_left] at hT
    have hq := CRN89.lamMin_mul_le (f'' xs) (z - xs)
    have hd : ‖z - xs‖ < 3 * lamMin (f'' xs) / L := by rw [← dist_eq_norm]; exact hz.1
    rw [lt_div_iff₀ hL] at hd
    have hLd : L * ‖z - xs‖ ≤ 3 * lamMin (f'' xs) := by nlinarith
    have e1 := mul_le_mul_of_nonneg_left hLd (sq_nonneg ‖z - xs‖)
    nlinarith [neg_abs_le (f z - f xs - 0 - 1 / 2 * ⟪f'' xs (z - xs), z - xs⟫_ℝ)]
  refine ⟨xs, hlim, hxsI, hf'0, hpdxs, hloc, ?_, ?_, ?_⟩
  · -- Q-quadratic rate
    refine ⟨25 / 8 * (L / lamMin (f'' x₀)) * (32 / 7) ^ 2, fun k => ?_⟩
    obtain ⟨-, -, -, a4, a5⟩ := hall k
    have h1 := htail' k
    have h4 : ‖x (k + 1) - x k‖ ≤ ‖x (k + 1) - xs‖ + ‖x k - xs‖ := by
      have := norm_sub_le (x (k + 1) - xs) (x k - xs)
      rwa [sub_sub_sub_cancel_right] at this
    have hA1 : ‖x (k + 1) - xs‖ ≤ 25 / 8 * (L / lamMin (f'' x₀)) * ‖x (k + 1) - x k‖ ^ 2 := by
      have e : 4 / 3 * (25 / 16 * (lamMin (f'' x₀) / L)) *
          (3 / 2 * (L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀)) ^ 2) =
          25 / 8 * (L / lamMin (f'' x₀)) * ‖x (k + 1) - x k‖ ^ 2 := by
        field_simp; ring
      calc _ ≤ _ := h1
        _ ≤ 4 / 3 * (25 / 16 * (lamMin (f'' x₀) / L)) *
            (3 / 2 * (L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀)) ^ 2) :=
          mul_le_mul_of_nonneg_left a4 (by positivity)
        _ = _ := e
    have e2 : 25 / 8 * (L / lamMin (f'' x₀)) * ‖x (k + 1) - x k‖ ^ 2 =
        25 / 8 * ‖x (k + 1) - x k‖ * (L * ‖x (k + 1) - x k‖ / lamMin (f'' x₀)) := by ring
    have hA2 : ‖x (k + 1) - xs‖ ≤ 25 / 32 * ‖x (k + 1) - x k‖ := by
      have := mul_le_mul_of_nonneg_left a5 (by positivity : (0 : ℝ) ≤ 25 / 8 * ‖x (k + 1) - x k‖)
      linarith
    have hr7 : ‖x (k + 1) - x k‖ ≤ 32 / 7 * ‖x k - xs‖ := by linarith
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hr7 2
    calc _ ≤ _ := hA1
      _ ≤ 25 / 8 * (L / lamMin (f'' x₀)) * (32 / 7 * ‖x k - xs‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  · -- R-quadratic rate
    refine ⟨max (2 * ‖x 0 - xs‖) (4 / 3 * (25 / 16 * (lamMin (f'' x₀) / L)) * (512 / 1875)),
      fun k => ?_⟩
    cases k with
    | zero =>
      have := le_max_left (2 * ‖x 0 - xs‖) (4 / 3 * (25 / 16 * (lamMin (f'' x₀) / L)) * (512 / 1875))
      norm_num
      linarith
    | succ j =>
      have h1 := htail' j
      have h5 := (hinv j).2.2.2.2
      have hP : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ (j + 1)) := by positivity
      have hm := le_max_right (2 * ‖x 0 - xs‖) (4 / 3 * (25 / 16 * (lamMin (f'' x₀) / L)) * (512 / 1875))
      have hK : 0 ≤ 4 / 3 * (25 / 16 * (lamMin (f'' x₀) / L)) := by positivity
      have h6 := mul_le_mul_of_nonneg_left h5 hK
      have h7 := mul_le_mul_of_nonneg_right hm hP
      nlinarith
  · -- (3.8)
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hexp : 1 ≤ Real.exp (3 / 2) := Real.one_le_exp (by norm_num)
    have hP : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ (j + 1)) := by positivity
    calc ‖f' (x (j + 1))‖ ≤ 512 / 1875 * (lamMin (f'' x₀) ^ 2 / L) * (1 / 2 : ℝ) ^ (2 ^ (j + 1)) :=
          hg38 j
      _ ≤ 9 * Real.exp (3 / 2) / 16 * (lamMin (f'' x₀) ^ 2 / L) * (1 / 2 : ℝ) ^ (2 ^ (j + 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hP
      _ = _ := by ring
