-- Prove2me | solution 1 for Disjunctive.Polarity.zero_in_hull_iff_reverse_polar
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:15:40.935513+00:00
-- url     : https://prove2.me/submissions/69539abb-716e-4d63-81ac-a5718aae5359

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

set_option autoImplicit false

namespace Disjunctive.Polarity

/-- A set containing all `t • w` for `t ≥ 1`, with `w ≠ 0`, is unbounded. -/
lemma rp859_not_bounded_of_ray {n : ℕ} {T : Set (Fin n → ℝ)} {w : Fin n → ℝ} (hw : w ≠ 0)
    (hT : ∀ t : ℝ, 1 ≤ t → t • w ∈ T) : ¬ Bornology.IsBounded T := by
  intro hb
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hb
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set t : ℝ := max 1 ((|R| + 1) / ‖w‖) with ht
  have h1 : 1 ≤ t := le_max_left _ _
  have h2 : (|R| + 1) / ‖w‖ ≤ t := le_max_right _ _
  have := hR _ (hT t h1)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
  have h3 : |R| + 1 ≤ t * ‖w‖ := by
    rw [div_le_iff₀ hpos] at h2; exact h2
  have := le_abs_self R
  linarith

lemma rp859_dot_eq {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] ℝ) (y : Fin n → ℝ) :
    f y = dotProduct (fun i => f (fun j => if i = j then 1 else 0)) y := by
  have := LinearMap.pi_apply_eq_sum_univ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) y
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

end Disjunctive.Polarity

open Disjunctive.Polarity in
theorem solution {n : ℕ} [NeZero n] (S : Set (Fin n → ℝ)) :
    List.TFAE [0 ∈ closure (convexHull ℝ S), ReversePolar S = ∅,
      Bornology.IsBounded (ReversePolar S)] := by
  tfae_have 1 → 2 := by
    intro h0
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hconv : Convex ℝ {y : Fin n → ℝ | 1 ≤ dotProduct x y} := by
      intro a ha b hb s t hs ht hst
      simp only [Set.mem_ofPred_eq] at ha hb ⊢
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      nlinarith
    have hclosed : IsClosed {y : Fin n → ℝ | 1 ≤ dotProduct x y} :=
      isClosed_le continuous_const (continuous_const.dotProduct continuous_id)
    have hsub : closure (convexHull ℝ S) ⊆ {y : Fin n → ℝ | 1 ≤ dotProduct x y} :=
      closure_minimal (convexHull_min (fun y hy => hx y hy) hconv) hclosed
    have := hsub h0
    simp only [Set.mem_ofPred_eq, dotProduct_zero] at this
    linarith
  tfae_have 2 → 3 := by
    intro h; rw [h]; exact Bornology.isBounded_empty
  tfae_have 3 → 1 := by
    intro hb
    by_contra h0
    obtain ⟨f, u, hfu, hb'⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ S).closure isClosed_closure h0
    rw [map_zero] at hfu
    set v : Fin n → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hv
    rcases S.eq_empty_or_nonempty with hS | ⟨y0, hy0⟩
    · -- S empty: reverse polar is everything
      have huniv : ReversePolar S = Set.univ := by
        ext x; simp [ReversePolar, hS]
      rw [huniv] at hb
      have hw : (Pi.single 0 1 : Fin n → ℝ) ≠ 0 := by
        intro h
        have := congrFun h 0
        simp at this
      exact rp859_not_bounded_of_ray hw (fun t _ => Set.mem_univ _) hb
    · have hmem : ∀ t : ℝ, 1 ≤ t → t • (u⁻¹ • v) ∈ ReversePolar S := by
        intro t ht y hy
        have hy' := hb' y (subset_closure (subset_convexHull ℝ S hy))
        rw [rp859_dot_eq f y, ← hv] at hy'
        rw [smul_smul, smul_dotProduct, smul_eq_mul]
        have hu : 0 < u := hfu
        have : 1 < u⁻¹ * dotProduct v y := by
          rw [lt_inv_mul_iff₀ hu]; linarith
        nlinarith
      have hw : u⁻¹ • v ≠ 0 := by
        intro h
        have := hmem 1 le_rfl y0 hy0
        rw [one_smul, h, zero_dotProduct] at this
        linarith
      exact rp859_not_bounded_of_ray hw hmem hb
  tfae_finish
