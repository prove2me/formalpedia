-- Prove2me | solution 1 for CauchyRiemannIndex.homotopy_lift_of_local_transport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T17:27:55.044136+00:00
-- url     : https://prove2.me/submissions/d963611f-813a-402b-a66a-4f85507e7da8

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_exists_pos_forall_dist_lt_pair_mem



namespace CauchyRiemannIndex

open Matrix

theorem homotopy_lift_of_local_transport_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Submonoid (Matrix ι ι ℝ)) (U : Set ((ι → ℝ) × (ι → ℝ))) (hU : IsOpen U)
    (τ : (ι → ℝ) × (ι → ℝ) → Matrix ι ι ℝ) (hτc : ContinuousOn τ U)
    (hτS : ∀ p ∈ U, τ p ∈ S) (hτv : ∀ p ∈ U, τ p *ᵥ p.1 = p.2)
    (hτ1 : ∀ x, (x, x) ∈ U → τ (x, x) = 1)
    (H : C(unitInterval × unitInterval, ι → ℝ)) (hHU : ∀ p, (H p, H p) ∈ U) (e : ι → ℝ)
    (γ : C(unitInterval, Matrix ι ι ℝ)) (hγS : ∀ t, γ t ∈ S) (hγ : ∀ t, γ t *ᵥ e = H (0, t)) :
    ∃ G : C(unitInterval × unitInterval, Matrix ι ι ℝ), (∀ t, G (0, t) = γ t) ∧
      (∀ p, G p ∈ S) ∧ (∀ p, G p *ᵥ e = H p) ∧
      ∀ t, (∀ s, H (s, t) = H (0, t)) → ∀ s, G (s, t) = γ t := by
  obtain ⟨δ, hδ, hδU⟩ := exists_pos_forall_dist_lt_pair_mem H H.continuous U hU hHU
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  have hN0 : (0 : ℝ) < N + 1 := by positivity
  -- grid points `min s (k / (N + 1))`
  let c : ℕ → unitInterval → unitInterval := fun k s =>
    ⟨min (s : ℝ) (k / (N + 1 : ℝ)), le_min s.2.1 (by positivity), (min_le_left _ _).trans s.2.2⟩
  have hc_cont : ∀ k, Continuous (c k) := fun k =>
    (continuous_subtype_val.min continuous_const).subtype_mk _
  have hc0 : ∀ k, c k 0 = 0 := fun k => Subtype.ext (min_eq_left (by positivity))
  have hcz : ∀ s, c 0 s = 0 := fun s => Subtype.ext (by simp [c, s.2.1])
  have hcN : ∀ s, c (N + 1) s = s := fun s => Subtype.ext (by
    show min (s : ℝ) (((N + 1 : ℕ) : ℝ) / (N + 1 : ℝ)) = s
    rw [Nat.cast_add, Nat.cast_one, div_self hN0.ne']
    exact min_eq_left s.2.2)
  let q : ℕ → unitInterval × unitInterval → unitInterval × unitInterval := fun k p => (c k p.1, p.2)
  have hq : ∀ k p, (H (q k p), H (q (k + 1) p)) ∈ U := by
    intro k p
    apply hδU
    rw [Prod.dist_eq, dist_self, Subtype.dist_eq, Real.dist_eq]
    refine max_lt (lt_of_le_of_lt ?_ hN) hδ
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _), Nat.cast_add, Nat.cast_one, ← sub_div,
      sub_add_cancel_left, abs_div, abs_neg, abs_one, abs_of_pos hN0]
  let pr : ℕ → unitInterval × unitInterval → (ι → ℝ) × (ι → ℝ) := fun k p =>
    (H (q k p), H (q (k + 1) p))
  have hpr_cont : ∀ k, Continuous (pr k) := fun k =>
    (H.continuous.comp (((hc_cont k).comp continuous_fst).prodMk continuous_snd)).prodMk
      (H.continuous.comp (((hc_cont (k + 1)).comp continuous_fst).prodMk continuous_snd))
  let P : ℕ → unitInterval × unitInterval → Matrix ι ι ℝ := fun k p =>
    Nat.rec (motive := fun _ => Matrix ι ι ℝ) 1 (fun j M => τ (pr j p) * M) k
  have hPs : ∀ k p, P (k + 1) p = τ (pr k p) * P k p := fun _ _ => rfl
  have hPc : ∀ k, Continuous (P k) := by
    intro k
    induction k with
    | zero => exact continuous_const
    | succ k ih =>
      have h : P (k + 1) = fun p => τ (pr k p) * P k p := funext (hPs k)
      rw [h]
      exact (hτc.comp_continuous (hpr_cont k) (hq k)).mul ih
  have hPS : ∀ k p, P k p ∈ S := by
    intro k p
    induction k with
    | zero => exact S.one_mem
    | succ k ih => rw [hPs]; exact S.mul_mem (hτS _ (hq k p)) ih
  have hPv : ∀ k p, P k p *ᵥ H (q 0 p) = H (q k p) := by
    intro k p
    induction k with
    | zero => exact one_mulVec _
    | succ k ih => rw [hPs, ← mulVec_mulVec, ih]; exact hτv _ (hq k p)
  have hP1 : ∀ p, (∀ k, H (q k p) = H (q 0 p)) → ∀ k, P k p = 1 := by
    intro p hk k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [hPs, ih, mul_one]
      have h : pr k p = (H (q 0 p), H (q 0 p)) := Prod.ext (hk k) (hk (k + 1))
      rw [h]
      exact hτ1 _ (hHU _)
  let G : C(unitInterval × unitInterval, Matrix ι ι ℝ) :=
    ⟨fun p => P (N + 1) p * γ p.2, Continuous.mul (hPc (N + 1)) (γ.continuous.comp continuous_snd)⟩
  refine ⟨G, fun t => ?_, fun p => S.mul_mem (hPS (N + 1) p) (hγS p.2), fun p => ?_, fun t ht s => ?_⟩
  · show P (N + 1) (0, t) * γ t = γ t
    rw [hP1 (0, t) (fun k => by simp only [q, hc0]) (N + 1), one_mul]
  · show (P (N + 1) p * γ p.2) *ᵥ e = H p
    have h := hPv (N + 1) p
    simp only [q, hcz, hcN] at h
    rw [← mulVec_mulVec, hγ, h]
  · show P (N + 1) (s, t) * γ t = γ t
    rw [hP1 (s, t) (fun k => (ht _).trans (ht _).symm) (N + 1), one_mul]

end CauchyRiemannIndex

open CauchyRiemannIndex

open Matrix

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Submonoid (Matrix ι ι ℝ)) (U : Set ((ι → ℝ) × (ι → ℝ))) (hU : IsOpen U)
    (τ : (ι → ℝ) × (ι → ℝ) → Matrix ι ι ℝ) (hτc : ContinuousOn τ U)
    (hτS : ∀ p ∈ U, τ p ∈ S) (hτv : ∀ p ∈ U, τ p *ᵥ p.1 = p.2)
    (hτ1 : ∀ x, (x, x) ∈ U → τ (x, x) = 1)
    (H : C(unitInterval × unitInterval, ι → ℝ)) (hHU : ∀ p, (H p, H p) ∈ U) (e : ι → ℝ)
    (γ : C(unitInterval, Matrix ι ι ℝ)) (hγS : ∀ t, γ t ∈ S) (hγ : ∀ t, γ t *ᵥ e = H (0, t)) :
    ∃ G : C(unitInterval × unitInterval, Matrix ι ι ℝ), (∀ t, G (0, t) = γ t) ∧
      (∀ p, G p ∈ S) ∧ (∀ p, G p *ᵥ e = H p) ∧
      ∀ t, (∀ s, H (s, t) = H (0, t)) → ∀ s, G (s, t) = γ t :=
  homotopy_lift_of_local_transport_aux S U hU τ hτc hτS hτv hτ1 H hHU e γ hγS hγ
