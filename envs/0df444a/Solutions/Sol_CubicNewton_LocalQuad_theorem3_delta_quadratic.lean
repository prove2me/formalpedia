-- Prove2me | solution 1 for CubicNewton.LocalQuad.theorem3_delta_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:06:12.715132+00:00
-- url     : https://prove2.me/submissions/08db7452-18c1-43f2-ae06-b5089ce8ede2

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import Definitions.Def_CubicNewton_LocalQuad_IsRelaxedRun
import Definitions.Def_CubicNewton_LocalQuad_deltaMeasure

open scoped RealInnerProductSpace

namespace CubicNewton.LocalQuad

lemma aux_eb_quad_bdd {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
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

lemma aux_eb_lam_le {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    CubicNewton.Shared.lamMin A * ‖v‖ ^ 2 ≤ ⟪A v, v⟫ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set u := ‖v‖⁻¹ • v with hu
  have hu1 : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    simp [hu, norm_smul, hn.ne']
  have h := ciInf_le (aux_eb_quad_bdd A) ⟨u, hu1⟩
  have e : ⟪A v, v⟫ = ‖v‖ ^ 2 * ⟪A u, u⟫ := by
    have : v = ‖v‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    conv_lhs => rw [this]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  unfold CubicNewton.Shared.lamMin
  rw [e]
  have h' : (⨅ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪A w, w⟫) ≤ ⟪A u, u⟫ := h
  nlinarith [sq_nonneg ‖v‖]

lemma aux_eb_lam_lip {n : ℕ} (hn : 0 < n)
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    CubicNewton.Shared.lamMin A - ‖B - A‖ ≤ CubicNewton.Shared.lamMin B := by
  haveI : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    refine ⟨⟨EuclideanSpace.single ⟨0, hn⟩ 1, ?_⟩⟩; simp
  rw [show CubicNewton.Shared.lamMin B
      = ⨅ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪B v, v⟫ from rfl]
  apply le_ciInf
  intro u
  have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by simpa using u.2
  have h1 := aux_eb_lam_le A u
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

lemma aux_eb_foc {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
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

lemma aux_eb_symm {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
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

lemma aux_eb_abs_le_of_deriv (u u' : ℝ → ℝ) (C : ℝ) (p : ℕ)
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

lemma aux_eb_grad_taylor {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
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
  have B := aux_eb_abs_le_of_deriv ψ ψ' _ 1 hψ hb h0 1 (Set.right_mem_Icc.2 zero_le_one)
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

lemma aux_eb_step {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
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
  · have h := aux_eb_foc g H M x T hT r
    rw [← hr] at h
    have h1 := aux_eb_lam_le (H x) r
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
      have h := aux_eb_foc g H M x T hT w
      rw [← hr] at h
      have hs := aux_eb_symm f g H hf hg x w r
      have : ⟪w, w⟫ = 0 := by
        conv_lhs => rw [hwdef]
        rw [inner_add_left, inner_add_left, real_inner_smul_left]
        rw [hs] at h
        linarith
      exact inner_self_eq_zero.mp this
    have ht := aux_eb_grad_taylor g H L hL hg hLip x T
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
  · have h := aux_eb_lam_lip hn (H x) (H T)
    have h2 := hLip T x
    rw [← hr] at h2
    nlinarith




lemma delta_num_step (L a b G G' r : ℝ) (hL : 0 < L) (ha : 0 < a) (hr : 0 ≤ r)
    (hG : 0 ≤ G) (hG' : 0 ≤ G') (hd : L*G/a^2 ≤ 1/4)
    (hstep : a*r ≤ G) (hgrad : G' ≤ 3*L/2*r^2) (heig : a-L*r ≤ b) :
    0 < b ∧ L*G'/b^2 ≤ 3/2*(L*G/a^2/(1-L*G/a^2))^2 ∧
      3/2*(L*G/a^2/(1-L*G/a^2))^2 ≤ 8/3*(L*G/a^2)^2 ∧
      8/3*(L*G/a^2)^2 ≤ 2/3*(L*G/a^2) := by
  let d := L*G/a^2
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := hd
  have hden : 0 < 1-d := by linarith
  have hLG : L*G = d*a^2 := by dsimp [d]; field_simp
  have hLr : L*r ≤ d*a := by
    have hh := mul_le_mul_of_nonneg_left hstep hL.le
    apply (mul_le_mul_iff_left₀ ha).mp
    nlinarith
  have hlow : a*(1-d) ≤ b := by nlinarith
  have hb : 0 < b := lt_of_lt_of_le (mul_pos ha hden) hlow
  let q := d/(1-d)
  have hq : 0 ≤ q := div_nonneg hd0 hden.le
  have hqid : q*(1-d)=d := by dsimp [q]; field_simp
  have hprod : d*a ≤ q*b := by
    have hh := mul_le_mul_of_nonneg_left hlow hq
    calc d*a = (q*(1-d))*a := congrArg (fun v : ℝ => v*a) hqid.symm
      _ = q*(a*(1-d)) := by ring
      _ ≤ q*b := hh
  have hbound : L*G'/b^2 ≤ 3/2*q^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
    have h1 := mul_le_mul_of_nonneg_left hgrad hL.le
    have h2 := pow_le_pow_left₀ (mul_nonneg hL.le hr) (hLr.trans hprod) 2
    nlinarith
  have hqhi : q ≤ 4/3*d := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hd0 (show 0 ≤ 1/4-d by linarith)]
  have hq2 := pow_le_pow_left₀ hq hqhi 2
  refine ⟨hb,hbound,?_,?_⟩
  · change 3/2*q^2 ≤ 8/3*d^2
    nlinarith
  · change 8/3*d^2 ≤ 2/3*d
    nlinarith [mul_nonneg hd0 (show 0 ≤ 1/4-d by linarith)]

end CubicNewton.LocalQuad
open CubicNewton.LocalQuad

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x-H y‖ ≤ L*‖x-y‖)
    (hn : 0 < n) (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ)
    (hrun : IsRelaxedRun L g H x M)
    (hpos : 0 < CubicNewton.Shared.lamMin (H (x 0))) (hδ0 : deltaMeasure L g H (x 0) ≤ 1/4) :
    ∀ k, 0 < CubicNewton.Shared.lamMin (H (x k)) ∧
      deltaMeasure L g H (x (k+1)) ≤ 3/2*(deltaMeasure L g H (x k)/(1-deltaMeasure L g H (x k)))^2 ∧
      3/2*(deltaMeasure L g H (x k)/(1-deltaMeasure L g H (x k)))^2 ≤ 8/3*deltaMeasure L g H (x k)^2 ∧
      8/3*deltaMeasure L g H (x k)^2 ≤ 2/3*deltaMeasure L g H (x k) := by
  have hstep (k : ℕ) (hp : 0 < CubicNewton.Shared.lamMin (H (x k)))
      (hd : deltaMeasure L g H (x k) ≤ 1/4) :
      0 < CubicNewton.Shared.lamMin (H (x (k+1))) ∧
      deltaMeasure L g H (x (k+1)) ≤ 3/2*(deltaMeasure L g H (x k)/(1-deltaMeasure L g H (x k)))^2 ∧
      3/2*(deltaMeasure L g H (x k)/(1-deltaMeasure L g H (x k)))^2 ≤ 8/3*deltaMeasure L g H (x k)^2 ∧
      8/3*deltaMeasure L g H (x k)^2 ≤ 2/3*deltaMeasure L g H (x k) := by
    obtain ⟨ha,hb,hc⟩ := aux_eb_step hn f g H L hL.le hf hg hLip (M k) (hrun k).1.1
      (x k) (x (k+1)) (hrun k).2
    have ha' : CubicNewton.Shared.lamMin (H (x k))*‖x (k+1)-x k‖ ≤ ‖g (x k)‖ := by
      have hnon : 0 ≤ M k/2*‖x (k+1)-x k‖^2 := by have := (hrun k).1.1; positivity
      linarith
    have hb' : ‖g (x (k+1))‖ ≤ 3*L/2*‖x (k+1)-x k‖^2 := by
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [(hrun k).1.2]
    exact delta_num_step L _ _ _ _ _ hL hp (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hd ha' hb' hc
  have hmaint : ∀ k, 0 < CubicNewton.Shared.lamMin (H (x k)) ∧ deltaMeasure L g H (x k) ≤ 1/4 := by
    intro k
    induction k with
    | zero => exact ⟨hpos,hδ0⟩
    | succ k ih =>
      have hh := hstep k ih.1 ih.2
      refine ⟨hh.1,?_⟩
      have hchain := hh.2.1.trans (hh.2.2.1.trans hh.2.2.2)
      linarith [ih.2]
  intro k
  exact ⟨(hmaint k).1,(hstep k (hmaint k).1 (hmaint k).2).2⟩
