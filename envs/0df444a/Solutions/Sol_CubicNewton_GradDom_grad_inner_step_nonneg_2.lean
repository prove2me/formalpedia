-- Prove2me | solution 2 for CubicNewton.GradDom.grad_inner_step_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:23:45.971174+00:00
-- url     : https://prove2.me/submissions/ee2ae561-45e6-43aa-91fc-1c249419c9ea

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_GradDom_IsGradDominated2
import Definitions.Def_CubicNewton_GradDom_omegaTilde
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace


namespace CubicNewton.GradDom

lemma gd_foc {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪g x, v⟫ + (1 / 2) * (⟪H x (T - x), v⟫ + ⟪H x v, T - x⟫)
      + M / 2 * ‖T - x‖ * ⟪T - x, v⟫ = 0 := by
  set r := T - x with hr
  let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => r + t • v
  have hγ : ∀ t, HasDerivAt γ v t := fun t =>
    (((hasDerivAt_id t).smul_const v).const_add r).congr_deriv (by simp)
  have e2 : ∀ w : EuclideanSpace ℝ (Fin n), (‖w‖ ^ 2) ^ ((3:ℝ) / 2) = ‖w‖ ^ 3 := by
    intro w
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  let φ : ℝ → ℝ := fun t => ⟪g x, γ t⟫ + (1 / 2) * ⟪H x (γ t), γ t⟫
    + M / 6 * (‖γ t‖ ^ 2) ^ ((3:ℝ) / 2)
  have hφmin : IsLocalMin φ 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h := hT (T + t • v)
    have e1 : T + t • v - x = γ t := by simp only [γ, hr]; abel
    unfold CubicNewton.Shared.cubicModel at h
    rw [e1] at h
    simp only [φ, e2]
    have : γ 0 = r := by simp [γ]
    rw [this]; exact h
  have hd1 : HasDerivAt (fun t => ⟪g x, γ t⟫) (⟪g x, v⟫) 0 := by
    have := (hasDerivAt_const (0:ℝ) (g x)).inner ℝ (hγ 0)
    exact this.congr_deriv (by simp)
  have hHγ : HasDerivAt (fun t => H x (γ t)) (H x v) 0 :=
    (H x).hasFDerivAt.comp_hasDerivAt 0 (hγ 0)
  have hd2 : HasDerivAt (fun t => ⟪H x (γ t), γ t⟫) (⟪H x r, v⟫ + ⟪H x v, r⟫) 0 := by
    have := hHγ.inner ℝ (hγ 0)
    exact this.congr_deriv (by simp [γ])
  have hd3 : HasDerivAt (fun t => (‖γ t‖ ^ 2) ^ ((3:ℝ) / 2)) (3 * ‖r‖ * ⟪r, v⟫) 0 := by
    have := (hγ 0).norm_sq.rpow_const (p := (3:ℝ) / 2) (Or.inr (by norm_num))
    refine this.congr_deriv ?_
    have hg0 : γ 0 = r := by simp [γ]
    rw [hg0]
    have : (‖r‖ ^ 2) ^ ((3:ℝ) / 2 - 1) = ‖r‖ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    rw [this]; ring
  have hφ : HasDerivAt φ (⟪g x, v⟫ + (1 / 2) * (⟪H x r, v⟫ + ⟪H x v, r⟫)
      + M / 6 * (3 * ‖r‖ * ⟪r, v⟫)) 0 :=
    (hd1.add (hd2.const_mul (1 / 2))).add (hd3.const_mul (M / 6))
  have := hφmin.hasDerivAt_eq_zero hφ
  linarith

lemma gd_lim (a b c : ℝ) (h : ∀ ε : ℝ, 0 < ε → 0 ≤ a + ε * b + ε ^ 2 * c) : 0 ≤ a := by
  have hc : Continuous (fun ε : ℝ => a + ε * b + ε ^ 2 * c) := by fun_prop
  have ht : Filter.Tendsto (fun ε : ℝ => a + ε * b + ε ^ 2 * c) (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall (fun ε hε => h ε hε))

/-- model difference formula -/
lemma gd_diff {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) (w : EuclideanSpace ℝ (Fin n)) :
    0 ≤ 1 / 2 * ⟪H x w, w⟫ - M / 2 * ‖T - x‖ * ⟪T - x, w⟫
      + M / 6 * (‖T - x + w‖ ^ 3 - ‖T - x‖ ^ 3) := by
  have h1 := hT (T + w)
  have h2 := gd_foc g H M x T hT w
  have e : T + w - x = (T - x) + w := by abel
  unfold CubicNewton.Shared.cubicModel at h1
  rw [e] at h1
  simp only [map_add, inner_add_left, inner_add_right] at h1
  nlinarith

lemma gd_psd {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪H x v, v⟫ + 1 / 2 * M * ‖x - T‖ * ‖v‖ ^ 2 := by
  rw [← norm_neg (x - T), neg_sub]
  set r := T - x with hr
  -- key: for v with ⟪r, v⟫ ≠ 0
  have key : ∀ v : EuclideanSpace ℝ (Fin n), ⟪r, v⟫ ≠ 0 → 0 ≤ ⟪H x v, v⟫ + 1 / 2 * M * ‖r‖ * ‖v‖ ^ 2 := by
    intro v hv
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    have hvn : 0 < ‖v‖ ^ 2 := by positivity
    set t := -2 * ⟪r, v⟫ / ‖v‖ ^ 2 with ht
    have htv : t * ‖v‖ ^ 2 = -2 * ⟪r, v⟫ := by rw [ht]; field_simp
    have hnorm : ‖r + t • v‖ = ‖r‖ := by
      have : ‖r + t • v‖ ^ 2 = ‖r‖ ^ 2 := by
        rw [@norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
        linear_combination t * htv
      have h0 := norm_nonneg (r + t • v)
      nlinarith [norm_nonneg r]
    have hd := gd_diff g H M x T hT (t • v)
    rw [← hr, hnorm] at hd
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right, sub_self, mul_zero, add_zero] at hd
    have ht0 : t ≠ 0 := by
      rw [ht]; exact div_ne_zero (by simpa using hv) hvn.ne'
    have ht2 : 0 < t ^ 2 := by positivity
    have : 0 ≤ t ^ 2 * (⟪H x v, v⟫ + 1 / 2 * M * ‖r‖ * ‖v‖ ^ 2) := by
      have e2 : t * ⟪r, v⟫ = -(t ^ 2 * ‖v‖ ^ 2) / 2 := by
        have : t * (t * ‖v‖ ^ 2) = t * (-2 * ⟪r, v⟫) := by rw [htv]
        linarith
      rw [e2] at hd
      have e4 : t ^ 2 * (⟪H x v, v⟫ + 1 / 2 * M * ‖r‖ * ‖v‖ ^ 2) = 2 * (1 / 2 * (t * (t * ⟪H x v, v⟫)) - M / 2 * ‖r‖ * (-(t ^ 2 * ‖v‖ ^ 2) / 2)) := by ring
      linarith
    exact (mul_nonneg_iff_of_pos_left ht2).mp this
  by_cases hrv : ⟪r, v⟫ ≠ 0
  · exact key v hrv
  push_neg at hrv
  by_cases hr0 : r = 0
  · -- r = 0: m(t v) ≥ 0
    rw [hr0, norm_zero]
    have hq : ∀ t : ℝ, 0 < t → 0 ≤ 1 / 2 * ⟪H x v, v⟫ + t * (M / 6 * ‖v‖ ^ 3) + t ^ 2 * 0 := by
      intro t htp
      have hd := gd_diff g H M x T hT (t • v)
      rw [← hr, hr0] at hd
      simp only [zero_add, norm_zero, inner_zero_left, mul_zero, sub_zero, map_smul,
        real_inner_smul_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos htp] at hd
      have ht2 : 0 < t ^ 2 := by positivity
      have : 0 ≤ t ^ 2 * (1 / 2 * ⟪H x v, v⟫ + t * (M / 6 * ‖v‖ ^ 3)) := by
        have e3 : (t * ‖v‖) ^ 3 = t ^ 2 * (t * ‖v‖ ^ 3) := by ring
        rw [mul_pow] at hd
        nlinarith
      have := (mul_nonneg_iff_of_pos_left ht2).mp this
      linarith
    have := gd_lim _ _ _ hq
    simp; linarith
  · have hq : ∀ ε : ℝ, 0 < ε → 0 ≤ (⟪H x v, v⟫ + 1 / 2 * M * ‖r‖ * ‖v‖ ^ 2)
        + ε * (⟪H x v, r⟫ + ⟪H x r, v⟫) + ε ^ 2 * (⟪H x r, r⟫ + 1 / 2 * M * ‖r‖ * ‖r‖ ^ 2) := by
      intro ε hε
      have hk := key (v + ε • r) (by
        rw [inner_add_right, hrv, real_inner_smul_right, real_inner_self_eq_norm_sq]
        positivity)
      have hn : ‖v + ε • r‖ ^ 2 = ‖v‖ ^ 2 + ε ^ 2 * ‖r‖ ^ 2 := by
        rw [@norm_add_sq_real, real_inner_smul_right, real_inner_comm, hrv, norm_smul,
          Real.norm_eq_abs, mul_pow, sq_abs]; ring
      rw [hn] at hk
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right] at hk
      nlinarith
    exact gd_lim _ _ _ hq


lemma gd_foc_self {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ⟪g x, T - x⟫ + ⟪H x (T - x), T - x⟫ + M / 2 * ‖x - T‖ ^ 3 = 0 := by
  have h := gd_foc g H M x T hT (T - x)
  rw [real_inner_self_eq_norm_sq, ← norm_neg (T - x), neg_sub] at h
  linear_combination h

theorem md_core {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    CubicNewton.Shared.cubicModel g H M x T ≤ -(M / 12 * ‖x - T‖ ^ 3) := by
  have h1 := gd_foc_self g H M x T hT
  have h2 := gd_psd g H M hM x T hT (T - x)
  unfold CubicNewton.Shared.cubicModel
  rw [← norm_neg (T - x), neg_sub] at h2 ⊢
  nlinarith

theorem gi_core {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    0 ≤ ⟪g x, x - T⟫ := by
  have h1 := gd_foc_self g H M x T hT
  have h2 := gd_psd g H M hM x T hT (T - x)
  rw [← norm_neg (T - x), neg_sub] at h2
  have e : ⟪g x, x - T⟫ = -⟪g x, T - x⟫ := by rw [← inner_neg_right, neg_sub]
  rw [e]
  nlinarith

end CubicNewton.GradDom

open CubicNewton.GradDom


theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hfx : f x ≤ f x₀)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    0 ≤ ⟪g x, x - T⟫ := by
  exact gi_core g H M hM x T hT
