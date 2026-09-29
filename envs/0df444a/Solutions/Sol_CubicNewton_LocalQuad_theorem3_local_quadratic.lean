-- Prove2me | solution 1 for CubicNewton.LocalQuad.theorem3_local_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:31:25.019984+00:00
-- url     : https://prove2.me/submissions/281cc33b-de1f-4a1a-80d3-219505db1195

import Mathlib
import Definitions.Def_CubicNewton_LocalQuad_IsRelaxedRun
import Definitions.Def_CubicNewton_LocalQuad_deltaMeasure

open scoped RealInnerProductSpace

namespace CubicNewton.LocalQuad

lemma lq_quad_bdd {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    BddBelow (Set.range fun v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ⟪A v, v⟫) := by
  refine ⟨-‖A‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  have hv : ‖(v : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using v.2
  have h1 := abs_real_inner_le_norm (A v) v
  have h2 : ‖A v‖ ≤ ‖A‖ * ‖(v : EuclideanSpace ℝ (Fin n))‖ := A.le_opNorm _
  rw [hv] at h1 h2
  have := neg_abs_le ⟪A v, (v : EuclideanSpace ℝ (Fin n))⟫
  simp only
  linarith

lemma lq_lam_le {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    CubicNewton.Shared.lamMin A * ‖v‖ ^ 2 ≤ ⟪A v, v⟫ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set u := ‖v‖⁻¹ • v with hu
  have hu1 : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    simp [hu, norm_smul, hn.ne']
  have h := ciInf_le (lq_quad_bdd A) ⟨u, hu1⟩
  have e : ⟪A v, v⟫ = ‖v‖ ^ 2 * ⟪A u, u⟫ := by
    have : v = ‖v‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    conv_lhs => rw [this]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  unfold CubicNewton.Shared.lamMin
  rw [e]
  have h' : (⨅ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪A w, w⟫) ≤ ⟪A u, u⟫ := h
  nlinarith [sq_nonneg ‖v‖]

lemma lq_lam_lip {n : ℕ} (hn : 0 < n)
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    CubicNewton.Shared.lamMin A - ‖B - A‖ ≤ CubicNewton.Shared.lamMin B := by
  haveI : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    refine ⟨⟨EuclideanSpace.single ⟨0, hn⟩ 1, ?_⟩⟩; simp
  rw [show CubicNewton.Shared.lamMin B
      = ⨅ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪B v, v⟫ from rfl]
  apply le_ciInf
  intro u
  have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using u.2
  have h1 := lq_lam_le A u
  rw [hu] at h1
  have h2 := abs_real_inner_le_norm ((B - A) u) u
  have h3 : ‖(B - A) u‖ ≤ ‖B - A‖ * ‖(u : EuclideanSpace ℝ (Fin n))‖ := (B - A).le_opNorm _
  rw [hu] at h2 h3
  have h4 := neg_abs_le ⟪(B - A) u, (u : EuclideanSpace ℝ (Fin n))⟫
  have e : ⟪B u, (u : EuclideanSpace ℝ (Fin n))⟫
      = ⟪A u, (u : EuclideanSpace ℝ (Fin n))⟫ + ⟪(B - A) u, (u : EuclideanSpace ℝ (Fin n))⟫ := by
    simp [inner_sub_left]
  rw [e]
  nlinarith

lemma lq_foc {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
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

lemma lq_symm {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (x v w : EuclideanSpace ℝ (Fin n)) : ⟪H x v, w⟫ = ⟪H x w, v⟫ := by
  let Φ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  have h1 : ∀ y, HasFDerivAt f (Φ (g y)) y := by
    intro y
    refine (hf y).hasFDerivAt.congr_fderiv ?_
    ext z; rfl
  have h2 : HasFDerivAt (fun y => Φ (g y)) (Φ.comp (H x)) x :=
    Φ.hasFDerivAt.comp x (hg x)
  have := second_derivative_symmetric (f := f) (f' := fun y => Φ (g y)) h1 h2 v w
  exact this

set_option maxHeartbeats 4000000 in
lemma lq_num (L lam0 : ℝ) (hL : 0 < L) (h0 : 0 < lam0) (lam G ρ M : ℕ → ℝ)
    (hlam0 : lam 0 = lam0) (hG0 : L * G 0 ≤ lam0 ^ 2 / 4)
    (hρ : ∀ k, 0 ≤ ρ k) (hG : ∀ k, 0 ≤ G k) (hM : ∀ k, 0 < M k ∧ M k ≤ 2 * L)
    (ha : ∀ k, lam k * ρ k + M k / 2 * ρ k ^ 2 ≤ G k)
    (hb : ∀ k, G (k + 1) ≤ (L + M k) / 2 * ρ k ^ 2)
    (hc : ∀ k, lam k - L * ρ k ≤ lam (k + 1)) :
    (∀ k, L * ρ k ≤ lam0 * (1 / 2) ^ k) ∧ (∀ k, L * G k ≤ lam0 ^ 2 * (1 / 2) ^ k) ∧
    (∀ k, 1 ≤ k → L * G k ≤ 9 / 16 * lam0 ^ 2 * (1 / 2 : ℝ) ^ (2 ^ k)) ∧
    21 / 32 * lam0 ≤ lam 2 := by
  have hlr : ∀ k, lam k * (L * ρ k) ≤ L * G k := by
    intro k
    have hMρ : 0 ≤ M k / 2 * ρ k ^ 2 := mul_nonneg (by linarith [(hM k).1]) (sq_nonneg _)
    have := mul_le_mul_of_nonneg_left (show lam k * ρ k ≤ G k by linarith [ha k]) hL.le
    linarith
  -- step 0
  have hM0 := hM 0
  have ha0 := ha 0
  rw [hlam0] at ha0
  have hr0 := hρ 0
  have hP0 : L * ρ 0 ≤ lam0 / 4 := by
    have h1 : lam0 * (L * ρ 0) ≤ L * G 0 := by have := hlr 0; rwa [hlam0] at this
    nlinarith
  have hl1 : 3 / 4 * lam0 ≤ lam 1 := by have := hc 0; rw [hlam0] at this; linarith
  have hG1 : L * G 1 ≤ 161 / 2500 * lam0 ^ 2 := by
    have hb0 := hb 0
    have hs1 : L * (M 0 / 2 * ρ 0 ^ 2) ≤ lam0 ^ 2 / 4 - lam0 * (L * ρ 0) := by nlinarith
    have hs2 : L * (M 0 / 2 * ρ 0 ^ 2) ≤ (L * ρ 0) ^ 2 := by nlinarith
    have hLG : L * G 1 ≤ (L * ρ 0) ^ 2 / 2 + L * (M 0 / 2 * ρ 0 ^ 2) := by nlinarith
    set P := L * ρ 0 with hP
    have hP0' : 0 ≤ P := by positivity
    rcases le_or_gt P (259 / 1250 * lam0) with h | h
    · nlinarith
    · nlinarith
  -- step 1
  have hl1pos : 0 < lam 1 := by linarith
  have hP1 : L * ρ 1 ≤ 161 / 1875 * lam0 := by
    have ha1 := ha 1
    have hM1 := hM 1
    have hr1 := hρ 1
    have h1 := hlr 1
    have h2 : 3 / 4 * lam0 * (L * ρ 1) ≤ lam 1 * (L * ρ 1) :=
      mul_le_mul_of_nonneg_right hl1 (by positivity)
    nlinarith
  have hl2 : 21 / 32 * lam0 ≤ lam 2 := by have := hc 1; linarith
  have hGstep : ∀ k, L * G (k + 1) ≤ 3 / 2 * (L * ρ k) ^ 2 := by
    intro k
    have := hb k
    have hM' := hM k
    have hr := hρ k
    have h3 : (L + M k) / 2 * ρ k ^ 2 ≤ 3 * L / 2 * ρ k ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    nlinarith
  have hG2 : L * G 2 ≤ 1 / 64 * lam0 ^ 2 := by
    have h := hGstep 1
    have hr1 := hρ 1
    have : (L * ρ 1) ^ 2 ≤ (161 / 1875 * lam0) ^ 2 := pow_le_pow_left₀ (by positivity) hP1 2
    norm_num at h ⊢
    nlinarith
  -- induction
  have hq : ∀ k, 2 ≤ k → (1 / 2 : ℝ) ^ (2 ^ k) ≤ 1 / 16 := by
    intro k hk
    have : (4:ℕ) ≤ 2 ^ k := by
      calc (4:ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    calc (1 / 2 : ℝ) ^ (2 ^ k) ≤ (1 / 2) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) this
      _ = 1 / 16 := by norm_num
  have hind : ∀ k, 2 ≤ k → lam0 * (5 / 8 + 1 / 2 * (1 / 2 : ℝ) ^ (2 ^ k)) ≤ lam k ∧
      L * G k ≤ 1 / 4 * (1 / 2 : ℝ) ^ (2 ^ k) * lam0 ^ 2 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num; constructor <;> nlinarith
    | succ k hk ih =>
      obtain ⟨ih1, ih2⟩ := ih
      set q := (1 / 2 : ℝ) ^ (2 ^ k) with hqdef
      have hq16 : q ≤ 1 / 16 := hq k hk
      have hq0 : 0 ≤ q := by positivity
      have hqs : (1 / 2 : ℝ) ^ (2 ^ (k + 1)) = q ^ 2 := by
        rw [hqdef, ← pow_mul, pow_succ]
      rw [hqs]
      have hlk : 5 / 8 * lam0 ≤ lam k := by nlinarith
      have hPk : L * ρ k ≤ 2 / 5 * q * lam0 := by
        have hak := ha k
        have hM' := hM k
        have hr := hρ k
        have h1 := hlr k
        have h2 : 5 / 8 * lam0 * (L * ρ k) ≤ lam k * (L * ρ k) :=
          mul_le_mul_of_nonneg_right hlk (by positivity)
        nlinarith
      have hr := hρ k
      constructor
      · have := hc k
        nlinarith
      · have := hGstep k
        have hPk0 : 0 ≤ L * ρ k := by positivity
        have : (L * ρ k) ^ 2 ≤ (2 / 5 * q * lam0) ^ 2 := pow_le_pow_left₀ hPk0 hPk 2
        nlinarith
  have hqk : ∀ k : ℕ, (1 / 2 : ℝ) ^ (2 ^ k) ≤ (1 / 2) ^ k := fun k =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_two_pow_self).le
  have hbig : ∀ k, 2 ≤ k → L * ρ k ≤ 2 / 5 * (1 / 2 : ℝ) ^ (2 ^ k) * lam0 ∧
      L * G k ≤ 1 / 4 * (1 / 2 : ℝ) ^ (2 ^ k) * lam0 ^ 2 := by
    intro k hk
    obtain ⟨ih1, ih2⟩ := hind k hk
    have hq16 := hq k hk
    have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by positivity
    generalize (1 / 2 : ℝ) ^ (2 ^ k) = q at ih1 ih2 hq16 hq0 ⊢
    refine ⟨?_, ih2⟩
    have hlk : 5 / 8 * lam0 ≤ lam k := by nlinarith
    have hr := hρ k
    have h1 := hlr k
    have h2 : 5 / 8 * lam0 * (L * ρ k) ≤ lam k * (L * ρ k) :=
      mul_le_mul_of_nonneg_right hlk (by positivity)
    nlinarith
  refine ⟨?_, ?_, ?_, hl2⟩
  · intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simp; linarith
      · norm_num; linarith
    · have h := (hbig k hk).1
      have := hqk k
      have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by positivity
      generalize (1 / 2 : ℝ) ^ (2 ^ k) = q at h this hq0 ⊢
      nlinarith
  · intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simp; nlinarith [sq_nonneg lam0]
      · norm_num; nlinarith
    · have h := (hbig k hk).2
      have := hqk k
      have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by positivity
      generalize (1 / 2 : ℝ) ^ (2 ^ k) = q at h this hq0 ⊢
      nlinarith
  · intro k hk1
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      norm_num; nlinarith
    · have h := (hbig k hk).2
      have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by positivity
      generalize (1 / 2 : ℝ) ^ (2 ^ k) = q at h hq0 ⊢
      nlinarith

lemma lq_abs_le_of_deriv (u u' : ℝ → ℝ) (C : ℝ) (p : ℕ)
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

theorem lq_taylor {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ F, ∀ y ∈ F,
      |f y - f x - ⟪g x, y - x⟫ - (1 / 2) * ⟪H x (y - x), y - x⟫| ≤ L / 6 * ‖y - x‖ ^ 3 := by
  intro x hx y hy
  set d := y - x with hd
  let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • d
  have hγF : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ F := fun t ht => hF_convex.add_smul_sub_mem hx hy ht
  have hγ : ∀ t : ℝ, HasDerivAt γ d t := by
    intro t
    exact (((hasDerivAt_id t).smul_const d).const_add x).congr_deriv (by simp)
  have hgγ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun t => g (γ t)) (H (γ t) d) t :=
    fun t ht => (hg (γ t) (hγF t ht)).comp_hasDerivAt t (hγ t)
  let ψ : ℝ → ℝ := fun t => ⟪g (γ t), d⟫ - ⟪g x, d⟫ - t * ⟪H x d, d⟫
  let ψ' : ℝ → ℝ := fun t => ⟪H (γ t) d, d⟫ - ⟪H x d, d⟫
  have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (ψ' t) t := by
    intro t ht
    have h1 := (hgγ t ht).inner ℝ (hasDerivAt_const t d)
    have h2 := (hasDerivAt_id t).mul_const (⟪H x d, d⟫)
    exact ((h1.sub_const (⟪g x, d⟫)).sub h2).congr_deriv (by simp [ψ'])
  have hψb : ∀ t ∈ Set.Icc (0:ℝ) 1, |ψ' t| ≤ (L * ‖d‖ ^ 3) * t ^ 1 := by
    intro t ht
    have e : ψ' t = ⟪(H (γ t) - H x) d, d⟫ := by
      simp [ψ', inner_sub_left]
    rw [e]
    have hn : ‖γ t - x‖ = t * ‖d‖ := by
      simp [γ, norm_smul, abs_of_nonneg ht.1]
    have hL := hLip (γ t) (hγF t ht) x hx
    rw [hn] at hL
    calc |⟪(H (γ t) - H x) d, d⟫| ≤ ‖(H (γ t) - H x) d‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H (γ t) - H x‖ * ‖d‖) * ‖d‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (L * (t * ‖d‖) * ‖d‖) * ‖d‖ := by gcongr
      _ = (L * ‖d‖ ^ 3) * t ^ 1 := by ring
  have hψ0 : ψ 0 = 0 := by simp [ψ, γ]
  have Bψ := lq_abs_le_of_deriv ψ ψ' _ 1 hψ hψb hψ0
  let φ : ℝ → ℝ := fun t => f (γ t) - f x - t * ⟪g x, d⟫ - t ^ 2 / 2 * ⟪H x d, d⟫
  have hφ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ (ψ t) t := by
    intro t ht
    have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hf (γ t) (hγF t ht))).comp_hasDerivAt t (hγ t)
    have h2 := (hasDerivAt_id t).mul_const (⟪g x, d⟫)
    have h3 := ((hasDerivAt_pow 2 t).div_const 2).mul_const (⟪H x d, d⟫)
    refine (((h1.sub_const (f x)).sub h2).sub h3).congr_deriv ?_
    simp [ψ, InnerProductSpace.toDual_apply_apply]
  have hφb : ∀ t ∈ Set.Icc (0:ℝ) 1, |ψ t| ≤ (L * ‖d‖ ^ 3 / 2) * t ^ 2 := by
    intro t ht
    have := Bψ t ht
    calc |ψ t| ≤ L * ‖d‖ ^ 3 * t ^ (1 + 1) / (1 + 1) := by exact_mod_cast this
      _ = _ := by ring
  have hφ0 : φ 0 = 0 := by simp [φ, γ]
  have Bφ := lq_abs_le_of_deriv φ ψ _ 2 hφ hφb hφ0 1 (Set.right_mem_Icc.2 zero_le_one)
  have e1 : φ 1 = f y - f x - ⟪g x, y - x⟫ - (1 / 2) * ⟪H x (y - x), y - x⟫ := by
    simp [φ, γ, hd]
  rw [← e1]
  calc |φ 1| ≤ L * ‖d‖ ^ 3 / 2 * 1 ^ (2 + 1) / (2 + 1) := by exact_mod_cast Bφ
    _ = L / 6 * ‖y - x‖ ^ 3 := by rw [hd]; ring


lemma lq_grad_taylor {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hL : 0 ≤ L) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖) (x T : EuclideanSpace ℝ (Fin n)) :
    ‖g T - g x - H x (T - x)‖ ≤ L / 2 * ‖T - x‖ ^ 2 := by
  set d := T - x with hd
  set e := g T - g x - H x d with he
  let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • d
  have hγ : ∀ t : ℝ, HasDerivAt γ d t := by
    intro t
    exact (((hasDerivAt_id t).smul_const d).const_add x).congr_deriv (by simp)
  let ψ : ℝ → ℝ := fun t => ⟪g (γ t) - g x - t • H x d, e⟫
  let ψ' : ℝ → ℝ := fun t => ⟪H (γ t) d - H x d, e⟫
  have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (ψ' t) t := by
    intro t _
    have h1 : HasDerivAt (fun t => g (γ t)) (H (γ t) d) t :=
      (hg (γ t)).comp_hasDerivAt t (hγ t)
    have h2 : HasDerivAt (fun t => g (γ t) - g x - t • H x d) (H (γ t) d - H x d) t :=
      ((h1.sub_const (g x)).sub ((hasDerivAt_id t).smul_const (H x d))).congr_deriv (by simp)
    exact (h2.inner ℝ (hasDerivAt_const t e)).congr_deriv (by simp [ψ'])
  have hb : ∀ t ∈ Set.Icc (0:ℝ) 1, |ψ' t| ≤ (L * ‖d‖ ^ 2 * ‖e‖) * t ^ 1 := by
    intro t ht
    have e1 : ψ' t = ⟪(H (γ t) - H x) d, e⟫ := by simp [ψ', ContinuousLinearMap.sub_apply]
    rw [e1]
    have hn : ‖γ t - x‖ = t * ‖d‖ := by simp [γ, norm_smul, abs_of_nonneg ht.1]
    have hL' := hLip (γ t) x
    rw [hn] at hL'
    calc |⟪(H (γ t) - H x) d, e⟫| ≤ ‖(H (γ t) - H x) d‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H (γ t) - H x‖ * ‖d‖) * ‖e‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (L * (t * ‖d‖) * ‖d‖) * ‖e‖ := by gcongr
      _ = (L * ‖d‖ ^ 2 * ‖e‖) * t ^ 1 := by ring
  have h0 : ψ 0 = 0 := by simp [ψ, γ]
  have B := lq_abs_le_of_deriv ψ ψ' _ 1 hψ hb h0 1 (Set.right_mem_Icc.2 zero_le_one)
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
  · rw [← h]; positivity
  · have : ‖e‖ * ‖e‖ ≤ (L / 2 * ‖d‖ ^ 2) * ‖e‖ := by nlinarith
    exact le_of_mul_le_mul_right this h

lemma lq_step {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖) (M : ℝ) (hM : 0 < M)
    (x T : EuclideanSpace ℝ (Fin n)) (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    CubicNewton.Shared.lamMin (H x) * ‖T - x‖ + M / 2 * ‖T - x‖ ^ 2 ≤ ‖g x‖ ∧
    ‖g T‖ ≤ (L + M) / 2 * ‖T - x‖ ^ 2 ∧
    CubicNewton.Shared.lamMin (H x) - L * ‖T - x‖ ≤ CubicNewton.Shared.lamMin (H T) := by
  set r := T - x with hr
  refine ⟨?_, ?_, ?_⟩
  · have h := lq_foc g H M x T hT r
    rw [← hr] at h
    have h1 := lq_lam_le (H x) r
    have h2 := abs_real_inner_le_norm (g x) r
    have h2' := neg_abs_le ⟪g x, r⟫
    have h3 : ⟪r, r⟫ = ‖r‖ ^ 2 := real_inner_self_eq_norm_sq r
    rw [h3] at h
    rcases eq_or_lt_of_le (norm_nonneg r) with h0 | h0
    · rw [← h0]; simp
    · have : (CubicNewton.Shared.lamMin (H x) * ‖r‖ + M / 2 * ‖r‖ ^ 2) * ‖r‖ ≤ ‖g x‖ * ‖r‖ := by
        nlinarith
      exact le_of_mul_le_mul_right this h0
  · have hw : g x + H x r + (M / 2 * ‖r‖) • r = 0 := by
      set w := g x + H x r + (M / 2 * ‖r‖) • r with hwdef
      have h := lq_foc g H M x T hT w
      rw [← hr] at h
      have hs := lq_symm f g H hf hg x w r
      have : ⟪w, w⟫ = 0 := by
        conv_lhs => rw [hwdef]
        rw [inner_add_left, inner_add_left, real_inner_smul_left]
        rw [hs] at h
        linarith
      exact inner_self_eq_zero.mp this
    have ht := lq_grad_taylor g H L hL hg hLip x T
    rw [← hr] at ht
    have hs : (M / 2 * ‖r‖) • r = -(g x + H x r) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hw
    have e : g T = (g T - g x - H x r) - (M / 2 * ‖r‖) • r := by
      rw [hs]; abel
    rw [e]
    have h1 := norm_sub_le (g T - g x - H x r) ((M / 2 * ‖r‖) • r)
    have h2 : ‖(M / 2 * ‖r‖) • r‖ = M / 2 * ‖r‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    linarith
  · have h := lq_lam_lip hn (H x) (H T)
    have h2 := hLip T x
    rw [← hr] at h2
    nlinarith

theorem lq_core {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hn : 0 < n) (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ)
    (hrun : IsRelaxedRun L g H x M)
    (hpos : 0 < CubicNewton.Shared.lamMin (H (x 0))) (hδ0 : deltaMeasure L g H (x 0) ≤ 1 / 4) :
    ∃ xs : EuclideanSpace ℝ (Fin n),
      Filter.Tendsto x Filter.atTop (nhds xs) ∧ g xs = 0 ∧ 0 < CubicNewton.Shared.lamMin (H xs) ∧
      IsLocalMin f xs ∧
      ∀ k, 1 ≤ k → ‖g (x k)‖ ≤
        CubicNewton.Shared.lamMin (H (x 0)) ^ 2 * (9 * Real.exp (3 / 2) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
  set lam0 := CubicNewton.Shared.lamMin (H (x 0)) with hlam0def
  have hst : ∀ k, _ := fun k =>
    lq_step hn f g H L hL.le hf hg hLip (M k) (hrun k).1.1 (x k) (x (k + 1)) (hrun k).2
  have hG0 : L * ‖g (x 0)‖ ≤ lam0 ^ 2 / 4 := by
    unfold deltaMeasure at hδ0
    rw [div_le_iff₀ (by positivity)] at hδ0
    rw [← hlam0def] at hδ0
    linarith
  obtain ⟨F1, F2, F3, F4⟩ := lq_num L lam0 hL hpos (fun k => CubicNewton.Shared.lamMin (H (x k)))
    (fun k => ‖g (x k)‖) (fun k => ‖x (k + 1) - x k‖) M rfl hG0 (fun k => norm_nonneg _)
    (fun k => norm_nonneg _) (fun k => ⟨(hrun k).1.1, (hrun k).1.2⟩) (fun k => (hst k).1)
    (fun k => (hst k).2.1) (fun k => (hst k).2.2)
  have hu : ∀ k, dist (x k) (x (k + 1)) ≤ lam0 / L * (1 / 2) ^ k := by
    intro k; rw [dist_comm, dist_eq_norm]
    have := F1 k
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]; linarith
  have hcs := cauchySeq_of_le_geometric (1 / 2 : ℝ) (lam0 / L) (by norm_num) hu
  obtain ⟨xs, hxs⟩ := cauchySeq_tendsto_of_complete hcs
  have hgx : Filter.Tendsto (fun k => g (x k)) Filter.atTop (nhds (g xs)) :=
    ((hg xs).continuousAt.tendsto).comp hxs
  have hg0 : Filter.Tendsto (fun k => g (x k)) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun k => lam0 ^ 2 / L * (1 / 2) ^ k)
    · intro k; have := F2 k
      rw [div_mul_eq_mul_div, le_div_iff₀ hL]; linarith
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (lam0 ^ 2 / L)
      simpa using this
  have hgxs : g xs = 0 := tendsto_nhds_unique hgx hg0
  have hd2 := dist_le_of_le_geometric_of_tendsto (1 / 2 : ℝ) (lam0 / L) (by norm_num) hu hxs 2
  have hl := lq_lam_lip hn (H (x 2)) (H xs)
  have hh : ‖H xs - H (x 2)‖ ≤ L * dist (x 2) xs := by
    rw [dist_comm, dist_eq_norm]; exact hLip xs (x 2)
  have hlpos : 0 < CubicNewton.Shared.lamMin (H xs) := by
    have : L * dist (x 2) xs ≤ L * (lam0 / L * (1 / 2) ^ 2 / (1 - 1 / 2)) :=
      mul_le_mul_of_nonneg_left hd2 hL.le
    have e : L * (lam0 / L * (1 / 2) ^ 2 / (1 - 1 / 2)) = lam0 / 2 := by field_simp; ring
    linarith
  set ls := CubicNewton.Shared.lamMin (H xs) with hls
  have hloc : IsLocalMin f xs := by
    have hball : Metric.ball xs (3 * ls / L) ∈ nhds xs := Metric.ball_mem_nhds xs (by positivity)
    filter_upwards [hball] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have ht := lq_taylor Set.univ f g H L convex_univ (fun x _ => hf x) (fun x _ => hg x)
      (fun x _ y _ => hLip x y) xs trivial y trivial
    rw [hgxs, inner_zero_left] at ht
    have hq := lq_lam_le (H xs) (y - xs)
    have ha := neg_abs_le (f y - f xs - 0 - 1 / 2 * ⟪H xs (y - xs), y - xs⟫)
    have hd0 := norm_nonneg (y - xs)
    have h3 : L * ‖y - xs‖ ≤ 3 * ls := by rw [lt_div_iff₀ hL] at hy; linarith
    have : 0 ≤ ‖y - xs‖ ^ 2 * (ls / 2 - L * ‖y - xs‖ / 6) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  refine ⟨xs, hxs, hgxs, hlpos, hloc, ?_⟩
  intro k hk
  have h := F3 k hk
  have he : (1:ℝ) ≤ Real.exp (3 / 2) := Real.one_le_exp (by norm_num)
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by positivity
  generalize (1 / 2 : ℝ) ^ (2 ^ k) = q at h hq0 ⊢
  have eR : lam0 ^ 2 * (9 * Real.exp (3 / 2) / (16 * L)) * q * L
      = 9 / 16 * lam0 ^ 2 * q * Real.exp (3 / 2) := by field_simp
  have h2 : 9 / 16 * lam0 ^ 2 * q ≤ 9 / 16 * lam0 ^ 2 * q * Real.exp (3 / 2) :=
    le_mul_of_one_le_right (by positivity) he
  exact le_of_mul_le_mul_right (by rw [eR]; linarith) hL

end CubicNewton.LocalQuad

open CubicNewton.LocalQuad


theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hn : 0 < n) (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ)
    (hrun : IsRelaxedRun L g H x M)
    (hpos : 0 < CubicNewton.Shared.lamMin (H (x 0))) (hδ0 : deltaMeasure L g H (x 0) ≤ 1 / 4) :
    ∃ xs : EuclideanSpace ℝ (Fin n),
      Filter.Tendsto x Filter.atTop (nhds xs) ∧ g xs = 0 ∧ 0 < CubicNewton.Shared.lamMin (H xs) ∧
      IsLocalMin f xs ∧
      ∀ k, 1 ≤ k → ‖g (x k)‖ ≤
        CubicNewton.Shared.lamMin (H (x 0)) ^ 2 * (9 * Real.exp (3 / 2) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
  exact lq_core f g H L hf hg hL hLip hn x M hrun hpos hδ0
