-- Prove2me | solution 2 for CubicNewton.GradDom.cubicStep_first_order
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:26:40.236545+00:00
-- url     : https://prove2.me/submissions/b5ac77e7-174d-4940-babc-1d38d8471c70

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

lemma gd_abs_le_of_deriv (u u' : ℝ → ℝ) (C : ℝ) (p : ℕ)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u (u' t) t)
    (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, |u' t| ≤ C * t ^ p) (h0 : u 0 = 0) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, |u t| ≤ C * t ^ (p+1) / (p+1) := by
  intro t ht
  have hcont : ContinuousOn u (Set.Icc 0 1) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hpoly : ∀ s : ℝ, HasDerivAt (fun s:ℝ => C * s^(p+1)/(p+1)) (C * s^p) s := by
    intro s
    have := ((hasDerivAt_pow (p+1) s).const_mul C).div_const ((p:ℝ)+1)
    refine this.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hpc : ContinuousOn (fun s:ℝ => C * s^(p+1)/(p+1)) (Set.Icc 0 1) :=
    fun s _ => (hpoly s).continuousAt.continuousWithinAt
  have hint : interior (Set.Icc (0:ℝ) 1) = Set.Ioo 0 1 := interior_Icc
  have m1 : MonotoneOn (fun s => C * s^(p+1)/(p+1) - u s) (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) (f' := fun s => C * s^p - u' s)
      (hpc.sub hcont)
    · intro s hs; rw [hint] at hs
      exact ((hpoly s).sub (hu s (Set.Ioo_subset_Icc_self hs))).hasDerivWithinAt
    · intro s hs; rw [hint] at hs
      have := hb s (Set.Ioo_subset_Icc_self hs); have := le_abs_self (u' s)
      linarith
  have m2 : MonotoneOn (fun s => C * s^(p+1)/(p+1) + u s) (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) (f' := fun s => C * s^p + u' s)
      (hpc.add hcont)
    · intro s hs; rw [hint] at hs
      exact ((hpoly s).add (hu s (Set.Ioo_subset_Icc_self hs))).hasDerivWithinAt
    · intro s hs; rw [hint] at hs
      have := hb s (Set.Ioo_subset_Icc_self hs); have := neg_abs_le (u' s)
      linarith
  have a := m1 (Set.left_mem_Icc.2 zero_le_one) ht ht.1
  have b := m2 (Set.left_mem_Icc.2 zero_le_one) ht ht.1
  simp only [h0] at a b
  have e : C * (0:ℝ) ^ (p+1) / (p+1) = 0 := by simp
  rw [e] at a b
  rw [abs_le]; constructor <;> linarith

lemma gd_symm {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hF_convex : Convex ℝ F) (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪H x v, w⟫ = ⟪H x w, v⟫ := by
  let Φ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  have h1 : ∀ y ∈ interior F, HasFDerivAt f (Φ (g y)) y := by
    intro y hy
    refine (hf y (interior_subset hy)).hasFDerivAt.congr_fderiv ?_
    ext z; rfl
  have h2 : HasFDerivAt (fun y => Φ (g y)) (Φ.comp (H x)) x :=
    Φ.hasFDerivAt.comp x (hg x hx)
  have := hF_convex.second_derivative_within_at_symmetric hF_int h1 hx h2.hasFDerivWithinAt v w
  exact this

theorem fo_core {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hF_convex : Convex ℝ F) (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    g x + H x (T - x) + (1 / 2 * M * ‖T - x‖) • (T - x) = 0 := by
  set r := T - x with hr
  set w := g x + H x r + (1 / 2 * M * ‖r‖) • r with hwdef
  have h := gd_foc g H M x T hT w
  rw [← hr] at h
  have hs := gd_symm F f g H hF_convex hF_int hf hg x hx w r
  have : ⟪w, w⟫ = 0 := by
    conv_lhs => rw [hwdef]
    rw [inner_add_left, inner_add_left, real_inner_smul_left]
    rw [hs] at h
    linarith
  exact inner_self_eq_zero.mp this

lemma gd_grad_taylor {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hL0 : 0 ≤ L) (hF_convex : Convex ℝ F) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖) (x T : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ F) (hTF : T ∈ F) :
    ‖g T - g x - H x (T - x)‖ ≤ L / 2 * ‖T - x‖ ^ 2 := by
  set d := T - x with hd
  set e := g T - g x - H x d with he
  let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • d
  have hγF : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ F := fun t ht => hF_convex.add_smul_sub_mem hx hTF ht
  have hγ : ∀ t : ℝ, HasDerivAt γ d t := by
    intro t
    exact (((hasDerivAt_id t).smul_const d).const_add x).congr_deriv (by simp)
  let ψ : ℝ → ℝ := fun t => ⟪g (γ t) - g x - t • H x d, e⟫
  let ψ' : ℝ → ℝ := fun t => ⟪H (γ t) d - H x d, e⟫
  have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (ψ' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => g (γ t)) (H (γ t) d) t :=
      (hg (γ t) (hγF t ht)).comp_hasDerivAt t (hγ t)
    have h2 : HasDerivAt (fun t => g (γ t) - g x - t • H x d) (H (γ t) d - H x d) t :=
      ((h1.sub_const (g x)).sub ((hasDerivAt_id t).smul_const (H x d))).congr_deriv (by simp)
    exact (h2.inner ℝ (hasDerivAt_const t e)).congr_deriv (by simp [ψ'])
  have hb : ∀ t ∈ Set.Icc (0:ℝ) 1, |ψ' t| ≤ (L * ‖d‖ ^ 2 * ‖e‖) * t ^ 1 := by
    intro t ht
    have e1 : ψ' t = ⟪(H (γ t) - H x) d, e⟫ := by simp [ψ', ContinuousLinearMap.sub_apply]
    rw [e1]
    have hn : ‖γ t - x‖ = t * ‖d‖ := by simp [γ, norm_smul, abs_of_nonneg ht.1]
    have hL' := hLip (γ t) (hγF t ht) x hx
    rw [hn] at hL'
    calc |⟪(H (γ t) - H x) d, e⟫| ≤ ‖(H (γ t) - H x) d‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H (γ t) - H x‖ * ‖d‖) * ‖e‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (L * (t * ‖d‖) * ‖d‖) * ‖e‖ := by gcongr
      _ = (L * ‖d‖ ^ 2 * ‖e‖) * t ^ 1 := by ring
  have h0 : ψ 0 = 0 := by simp [ψ, γ]
  have B := gd_abs_le_of_deriv ψ ψ' _ 1 hψ hb h0 1 (Set.right_mem_Icc.2 zero_le_one)
  have hγ1 : γ 1 = T := by simp [γ, hd]
  have e1 : ψ 1 = ‖e‖ ^ 2 := by
    simp only [ψ, hγ1, one_smul]
    rw [← he, real_inner_self_eq_norm_sq]
  rw [e1] at B
  have B' : ‖e‖ ^ 2 ≤ L * ‖d‖ ^ 2 * ‖e‖ / 2 := by
    have := le_abs_self (‖e‖ ^ 2)
    norm_num at B ⊢
    linarith
  rcases eq_or_lt_of_le (norm_nonneg e) with h | h
  · rw [← h]
    positivity
  · have : ‖e‖ * ‖e‖ ≤ (L / 2 * ‖d‖ ^ 2) * ‖e‖ := by nlinarith
    exact le_of_mul_le_mul_right this h

/-- Lemma 3 -/
theorem gn_core {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hL0 : 0 ≤ L) (hF_convex : Convex ℝ F) (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hTF : T ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ‖g T‖ ≤ 1 / 2 * (L + M) * ‖x - T‖ ^ 2 := by
  have hw := fo_core F f g H hF_convex hF_int hf hg M x T hx hT
  set r := T - x with hr
  have ht := gd_grad_taylor F g H L hL0 hF_convex hg hLip x T hx hTF
  rw [← hr] at ht
  have hs : (1 / 2 * M * ‖r‖) • r = -(g x + H x r) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hw
  have e : g T = (g T - g x - H x r) - (1 / 2 * M * ‖r‖) • r := by
    rw [hs]; abel
  rw [e, ← norm_neg (x - T), neg_sub, ← hr]
  have h1 := norm_sub_le (g T - g x - H x r) ((1 / 2 * M * ‖r‖) • r)
  have h2 : ‖(1 / 2 * M * ‖r‖) • r‖ = M / 2 * ‖r‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
  linarith

end CubicNewton.GradDom

open CubicNewton.GradDom


theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    g x + H x (T - x) + (1 / 2 * M * ‖T - x‖) • (T - x) = 0 := by
  exact fo_core F f g H hF_convex hF_int hf hg M x T hx hT
