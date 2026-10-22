-- Prove2me | solution 1 for FiniteEnergyPlane.asympOp_symm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:18:21.239895+00:00
-- url     : https://prove2.me/submissions/98c12ced-4702-4332-9d10-4cbf3a7b0a7d

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

variable {n : ℕ}

lemma g71s_j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring

lemma g71s_j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; simp only [j0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

noncomputable def g71s_j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := g71s_j0_add, map_smul' := g71s_j0_smul }

@[simp] lemma g71s_j0L_apply (u : V n) : (g71s_j0L : V n →L[ℝ] V n) u = j0 u := rfl

lemma g71s_j0_j0 (u : V n) : j0 (j0 u) = -u := by
  funext k
  simp only [j0, Pi.neg_apply]
  by_cases h : (k:ℕ) % 2 = 0
  · have h1 : ¬ ((k:ℕ) + 1) % 2 = 0 := by omega
    rw [dif_pos h]
    simp only [dif_neg h1]
    congr 2
  · have h1 : ((k:ℕ) - 1) % 2 = 0 := by omega
    rw [dif_neg h]
    simp only [dif_pos h1]
    congr 2; ext; simp; omega

lemma g71s_dot_comm (u v : V n) : dot u v = dot v u := by
  simp only [dot]; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

lemma g71s_dot_add_right (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma g71s_dot_smul_right (c : ℝ) (u v : V n) : dot u (c • v) = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)

lemma g71s_dot_neg_left (u v : V n) : dot (-u) v = - dot u v := by
  simp only [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

lemma g71s_dot_j0_skew (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  rw [eq_neg_iff_add_eq_zero]
  simp only [dot, ← Finset.sum_add_distrib]
  let σ : Fin (2 * (n + 1)) → Fin (2 * (n + 1)) := fun k =>
    if h : (k:ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩
  refine Finset.sum_involution (fun k _ => σ k) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro k _
    by_cases h : (k:ℕ) % 2 = 0
    · have h1 : ¬ ((k:ℕ) + 1) % 2 = 0 := by omega
      simp only [σ, j0, dif_pos h, Fin.val_mk, dif_neg h1]
      have e : (⟨(k:ℕ) + 1 - 1, by omega⟩ : Fin (2 * (n + 1))) = k := by ext; simp
      rw [e]; ring
    · have h1 : ((k:ℕ) - 1) % 2 = 0 := by omega
      simp only [σ, j0, dif_neg h, Fin.val_mk, dif_pos h1]
      have e : (⟨(k:ℕ) - 1 + 1, by omega⟩ : Fin (2 * (n + 1))) = k := by ext; simp; omega
      rw [e]; ring
  · intro k _ _ hk
    by_cases h : (k:ℕ) % 2 = 0 <;> simp [σ, h, Fin.ext_iff] at hk <;> omega
  · intro k _
    simp only [σ]
    by_cases h : (k:ℕ) % 2 = 0
    · have h1 : ¬ ((k:ℕ) + 1) % 2 = 0 := by omega
      simp only [dif_pos h, Fin.val_mk, dif_neg h1]; ext; simp
    · have h1 : ((k:ℕ) - 1) % 2 = 0 := by omega
      simp only [dif_neg h, Fin.val_mk, dif_pos h1]; ext; simp; omega

lemma g71s_omega_skew (u v : V n) : omega0 u v = - omega0 v u := by
  simp only [omega0]; rw [g71s_dot_j0_skew, g71s_dot_comm]

lemma g71s_omega_j0_left (g w : V n) : omega0 (j0 g) w = - dot g w := by
  simp only [omega0, g71s_j0_j0, g71s_dot_neg_left]

lemma g71s_omega_j0_right (g w : V n) : omega0 w (j0 g) = dot w g := by
  simp only [omega0]; rw [g71s_dot_j0_skew, g71s_j0_j0]
  simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg]

lemma g71s_clm_eq_dot (L : V n →L[ℝ] ℝ) (w : V n) :
    L w = dot (fun k => L (Pi.single k 1)) w := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]; simp only [dot]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (w k) : V n) = w k • Pi.single k (1:ℝ) by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul, mul_comm]

lemma g71s_fderiv_eq_dot_grad (H : V n → ℝ) (y w : V n) : fderiv ℝ H y w = dot (grad H y) w :=
  g71s_clm_eq_dot _ _

/-- bilinear forms -/
noncomputable def g71s_dotB : V n →L[ℝ] V n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V n →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ dot
        (fun a b c => by simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib])
        (fun c a b => by simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring))
        (fun a b c => g71s_dot_add_right a b c)
        (fun c a b => g71s_dot_smul_right c a b))

@[simp] lemma g71s_dotB_apply (u v : V n) : (g71s_dotB : V n →L[ℝ] V n →L[ℝ] ℝ) u v = dot u v := rfl

noncomputable def g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ := g71s_dotB.comp g71s_j0L

@[simp] lemma g71s_omB_apply (u v : V n) : (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) u v = omega0 u v := rfl

/-! geometry -/

lemma g71s_dot_self_j0 (g : V n) : dot g (j0 g) = 0 := by
  have h := g71s_dot_j0_skew g g
  rw [g71s_dot_comm] at h; linarith

lemma g71s_liouville_ham (H : V n → ℝ) (y : V n) :
    liouville y (hamVF H y) = fderiv ℝ H y y / 2 := by
  simp only [liouville, hamVF, g71s_omega_j0_right, g71s_fderiv_eq_dot_grad, g71s_dot_comm]

lemma g71s_reeb_eq (H : V n → ℝ) (y : V n) :
    reeb H y = (fderiv ℝ H y y / 2)⁻¹ • j0 (grad H y) := by
  show (liouville y (hamVF H y))⁻¹ • hamVF H y = _
  rw [g71s_liouville_ham]; rfl

lemma g71s_contDiff_grad {H : V n → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (grad H) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  exact contDiff_pi.2 (fun k => h1.clm_apply contDiff_const)

lemma g71s_contDiff_F {H : V n → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ H y y / 2) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  exact (h1.clm_apply contDiff_id).div_const _

lemma g71s_reeb_contDiffAt {H : V n → ℝ} (hH : ContDiff ℝ ∞ H) {x : V n}
    (hx : fderiv ℝ H x x ≠ 0) : ContDiffAt ℝ ∞ (reeb H) x := by
  have e : reeb H = fun y => (fderiv ℝ H y y / 2)⁻¹ • g71s_j0L (grad H y) := by
    funext y; rw [g71s_reeb_eq]; rfl
  rw [e]
  refine ContDiffAt.smul (𝕜' := ℝ) ?_ ((g71s_j0L.contDiff.comp (g71s_contDiff_grad hH)).contDiffAt)
  exact ((g71s_contDiff_F hH).contDiffAt).inv (by simpa using hx)

lemma g71s_dH_reeb (H : V n → ℝ) (y : V n) : fderiv ℝ H y (reeb H y) = 0 := by
  rw [g71s_reeb_eq, map_smul, g71s_fderiv_eq_dot_grad H y (j0 _), g71s_dot_self_j0, smul_zero]

lemma g71s_omega_smul_left (c : ℝ) (u v : V n) : omega0 (c • u) v = c * omega0 u v := by
  rw [← g71s_omB_apply, map_smul]; rfl

lemma g71s_omega_reeb_left (H : V n → ℝ) (y w : V n) :
    omega0 (reeb H y) w = -(fderiv ℝ H y y / 2)⁻¹ * fderiv ℝ H y w := by
  rw [g71s_reeb_eq, g71s_omega_smul_left, g71s_omega_j0_left, g71s_fderiv_eq_dot_grad H y w]; ring

lemma g71s_liouville_reeb (H : V n → ℝ) (y : V n) :
    liouville y (reeb H y) = (fderiv ℝ H y y / 2)⁻¹ * (fderiv ℝ H y y / 2) := by
  rw [reeb, liouville, ← g71s_omB_apply, map_smul, g71s_omB_apply, smul_eq_mul, mul_div_assoc,
    ← liouville, g71s_liouville_ham]

section geo
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n} (hx : H x = 1)
include hH hx

lemma g71s_F_pos : 0 < fderiv ℝ H x x / 2 := by have := hH.2.2 x hx; linarith

lemma g71s_reeb_hasFDerivAt : HasFDerivAt (reeb H) (fderiv ℝ (reeb H) x) x :=
  ((g71s_reeb_contDiffAt hH.1 (by have := g71s_F_pos hH hx; intro h; rw [h] at this; norm_num at this)).differentiableAt (by simp)).hasFDerivAt

lemma g71s_hD : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) x) x :=
  ((hH.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt

lemma g71s_F_ne : fderiv ℝ H x x / 2 ≠ 0 := (g71s_F_pos hH hx).ne'

lemma g71s_sym (v w : V n) :
    fderiv ℝ (fderiv ℝ H) x v w = fderiv ℝ (fderiv ℝ H) x w v :=
  (hH.1.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top)) v w

lemma g71s_dH_R' (v : V n) :
    fderiv ℝ H x (fderiv ℝ (reeb H) x v) = - fderiv ℝ (fderiv ℝ H) x v (reeb H x) := by
  have h1 := (g71s_hD hH hx).clm_apply (g71s_reeb_hasFDerivAt hH hx)
  have h0 : HasFDerivAt (fun y => fderiv ℝ H y (reeb H y)) (0 : V n →L[ℝ] ℝ) x := by
    simp only [g71s_dH_reeb]; exact hasFDerivAt_const 0 x
  have := congrArg (fun L => L v) (h1.unique h0)
  simp at this; linarith

lemma g71s_om_R' (v : V n) :
    omega0 x (fderiv ℝ (reeb H) x v) = - omega0 v (reeb H x) := by
  have h1 := (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).hasFDerivAt_of_bilinear (hasFDerivAt_id x)
    (g71s_reeb_hasFDerivAt hH hx)
  have hev : ∀ᶠ y in 𝓝 x, fderiv ℝ H y y / 2 ≠ 0 :=
    (g71s_contDiff_F hH.1).continuous.continuousAt.eventually_ne (g71s_F_ne hH hx)
  have h0 : HasFDerivAt (fun y => (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) (id y) (reeb H y))
      (0 : V n →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const (2:ℝ) x).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    have := g71s_liouville_reeb H y
    rw [inv_mul_cancel₀ hy] at this
    simp only [id, g71s_omB_apply]; unfold liouville at this; linarith
  have := congrArg (fun L => L v) (h1.unique h0)
  simp at this; linarith

lemma g71s_om_R'_left (v w : V n) (hw : fderiv ℝ H x w = 0) :
    omega0 (fderiv ℝ (reeb H) x v) w =
      -(fderiv ℝ H x x / 2)⁻¹ * fderiv ℝ (fderiv ℝ H) x v w := by
  have h1 : HasFDerivAt (fun y => ((g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).flip w) (reeb H y))
      (((g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).flip w).comp (fderiv ℝ (reeb H) x)) x :=
    ((g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).flip w).hasFDerivAt.comp x (g71s_reeb_hasFDerivAt hH hx)
  have hFi := (((g71s_contDiff_F hH.1).differentiable (by simp) x).inv
    (g71s_F_ne hH hx)).hasFDerivAt
  have h2 := hFi.neg.mul ((g71s_hD hH hx).clm_apply (hasFDerivAt_const w x))
  have e : (fun y => ((g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).flip w) (reeb H y)) =
      (fun y => -(fderiv ℝ H y y / 2)⁻¹ * fderiv ℝ H y w) := by
    funext y; simp only [ContinuousLinearMap.flip_apply, g71s_omB_apply, g71s_omega_reeb_left]
  rw [e] at h1
  have := congrArg (fun L => L v) (h1.unique h2)
  simp [hw] at this; rw [this]; ring

lemma g71s_om_R'_right (v w : V n) (hw : fderiv ℝ H x w = 0) :
    omega0 w (fderiv ℝ (reeb H) x v) =
      (fderiv ℝ H x x / 2)⁻¹ * fderiv ℝ (fderiv ℝ H) x v w := by
  rw [g71s_omega_skew, g71s_om_R'_left hH hx v w hw]; ring

/-- the key infinitesimal symplecticity -/
lemma g71s_om_R'_sum (v w : V n) (hv : fderiv ℝ H x v = 0) (hw : fderiv ℝ H x w = 0) :
    omega0 (fderiv ℝ (reeb H) x v) w + omega0 v (fderiv ℝ (reeb H) x w) = 0 := by
  rw [g71s_om_R'_left hH hx v w hw, g71s_om_R'_right hH hx w v hv, g71s_sym hH hx v w]; ring

end geo

lemma g71s_bootstrap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → E}
    {x : ℝ → E} (hx : ∀ τ, HasDerivAt x (g (x τ)) τ) (hg : ∀ τ, ContDiffAt ℝ ∞ g (x τ)) :
    ContDiff ℝ ∞ x := by
  rw [contDiff_infty]; intro m
  induction m with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun τ => (hx τ).continuousAt)
  | succ m ih =>
    rw [show ((m+1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun τ => (hx τ).differentiableAt, by simp, ?_⟩
    have : deriv x = g ∘ x := funext fun τ => (hx τ).deriv
    rw [this, contDiff_iff_contDiffAt]
    intro τ
    exact ((hg τ).of_le (by exact_mod_cast le_top)).comp τ ih.contDiffAt

section orbit
variable {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
include hH

lemma g71s_reeb_cd (τ : ℝ) : ContDiffAt ℝ ∞ (reeb H) (P.x τ) :=
  g71s_reeb_contDiffAt hH.1 (by have := g71s_F_pos hH (P.mem τ); intro h; rw [h] at this; norm_num at this)

lemma g71s_x_cd : ContDiff ℝ ∞ P.x := g71s_bootstrap P.hasDerivAt (g71s_reeb_cd hH P)

omit hH in
lemma g71s_gamma_deriv (t : ℝ) :
    HasDerivAt (fun t => P.x (P.T * t)) (P.T • reeb H (P.x (P.T * t))) t := by
  have := (P.hasDerivAt (P.T * t)).scomp t ((hasDerivAt_id t).const_mul P.T)
  simp only [mul_one, id] at this
  exact this

lemma g71s_Dreeb_cd : ContDiff ℝ ∞ (fun τ => fderiv ℝ (reeb H) (P.x τ)) := by
  rw [contDiff_iff_contDiffAt]; intro τ
  exact ((g71s_reeb_cd hH P τ).fderiv_right (m := ∞) (by simp)).comp τ (g71s_x_cd hH P).contDiffAt

/-- derivative facts for a ξ-loop -/
lemma g71s_xi_deriv_dH (η : ℝ → V n) (hη : IsXiLoop P η) (t : ℝ) :
    fderiv ℝ H (P.x (P.T * t)) (deriv η t) =
      -(P.T * fderiv ℝ (fderiv ℝ H) (P.x (P.T * t)) (reeb H (P.x (P.T * t))) (η t)) := by
  have hηd : HasDerivAt η (deriv η t) t :=
    ((hη.1.differentiable (by simp)) t).hasDerivAt
  have h2 : HasDerivAt (fun t => fderiv ℝ H (P.x (P.T * t)))
      (fderiv ℝ (fderiv ℝ H) (P.x (P.T * t)) (P.T • reeb H (P.x (P.T * t)))) t :=
    (g71s_hD hH (P.mem (P.T * t))).comp_hasDerivAt t (g71s_gamma_deriv P t)
  have h1 : HasDerivAt (fun t => fderiv ℝ H (P.x (P.T * t)) (η t))
      (fderiv ℝ (fderiv ℝ H) (P.x (P.T * t)) (P.T • reeb H (P.x (P.T * t))) (η t) +
        fderiv ℝ H (P.x (P.T * t)) (deriv η t)) t :=
    h2.clm_apply hηd
  have h0 : HasDerivAt (fun t => fderiv ℝ H (P.x (P.T * t)) (η t)) 0 t := by
    have : (fun t => fderiv ℝ H (P.x (P.T * t)) (η t)) = fun _ => 0 := by
      funext s; exact (hη.2.2 s).2
    rw [this]; exact hasDerivAt_const _ _
  have := h1.unique h0
  rw [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul] at this; linarith

lemma g71s_xi_deriv_om (η : ℝ → V n) (hη : IsXiLoop P η) (t : ℝ) :
    omega0 (P.x (P.T * t)) (deriv η t) =
      -(P.T * omega0 (reeb H (P.x (P.T * t))) (η t)) := by
  have hηd : HasDerivAt η (deriv η t) t :=
    ((hη.1.differentiable (by simp)) t).hasDerivAt
  have h1 := (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ).hasDerivAt_of_bilinear
    (fun _ => g71s_gamma_deriv P t) (fun _ => hηd)
  have h0 : HasDerivAt (fun t => (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) (P.x (P.T * t)) (η t)) 0 t := by
    have : (fun t => (g71s_omB : V n →L[ℝ] V n →L[ℝ] ℝ) (P.x (P.T * t)) (η t)) = fun _ => 0 := by
      funext s; have := (hη.2.2 s).1; simp only [g71s_omB_apply]; unfold liouville at this; linarith
    rw [this]; exact hasDerivAt_const _ _
  have := h1.unique h0
  simp at this; linarith

/-- the vector inside `asympOp` lies in ξ -/
lemma g71s_inner_xi (η : ℝ → V n) (hη : IsXiLoop P η) (t : ℝ) :
    IsInXi H (P.x (P.T * t))
      (-(deriv η t) + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (η t)) := by
  have hy := P.mem (P.T * t)
  have hxi := hη.2.2 t
  constructor
  · unfold liouville
    have e1 := g71s_xi_deriv_om hH P η hη t
    have e2 := g71s_om_R' hH hy (η t)
    have e3 := g71s_omega_reeb_left H (P.x (P.T * t)) (η t)
    rw [hxi.2, mul_zero] at e3
    rw [g71s_omega_skew (η t), e3] at e2
    rw [e3] at e1
    have : omega0 (P.x (P.T * t)) (-(deriv η t) + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (η t))
        = -omega0 (P.x (P.T * t)) (deriv η t) +
          P.T * omega0 (P.x (P.T * t)) (fderiv ℝ (reeb H) (P.x (P.T * t)) (η t)) := by
      simp only [← g71s_omB_apply, map_add, map_neg, map_smul, smul_eq_mul]
    rw [this, e1, e2]; simp
  · rw [map_add, map_neg, map_smul, g71s_xi_deriv_dH hH P η hη t, g71s_dH_R' hH hy,
      g71s_sym hH hy]; simp

lemma g71s_asymp_cd (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (η : ℝ → V n) (hη : IsXiLoop P η) : ContDiff ℝ ∞ (asympOp J P η) := by
  have hγ : ContDiff ℝ ∞ (fun t => P.x (P.T * t)) :=
    (g71s_x_cd hH P).comp (contDiff_const.mul contDiff_id)
  have hd : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.mp hη.1).2
  have hR : ContDiff ℝ ∞ (fun t => fderiv ℝ (reeb H) (P.x (P.T * t))) :=
    (g71s_Dreeb_cd hH P).comp (contDiff_const.mul contDiff_id)
  unfold asympOp
  exact (hJ.1.comp hγ).clm_apply (hd.neg.add ((hR.clm_apply hη.1).const_smul P.T))

lemma g71s_asymp_xiLoop (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (η : ℝ → V n) (hη : IsXiLoop P η) : IsXiLoop P (asympOp J P η) := by
  refine ⟨g71s_asymp_cd hH P J hJ η hη, ?_, ?_⟩
  · intro t
    have hp : P.x (P.T * (t + 1)) = P.x (P.T * t) := by rw [mul_add, mul_one, P.periodic]
    have hd : deriv η (t + 1) = deriv η t := by
      have e : η = fun s => η (s + 1) := funext fun s => (hη.2.1 s).symm
      conv_rhs => rw [e]
      rw [deriv_comp_add_const]
    simp only [asympOp, hp, hη.2.1 t, hd]
  · intro t
    have hi := g71s_inner_xi hH P η hη t
    exact (hJ.2 _ (P.mem _) _ _ hi hi).1

end orbit

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (η ζ : ℝ → V n) (hη : IsXiLoop P η) (hζ : IsXiLoop P ζ) :
    IsXiLoop P (asympOp J P η) ∧
      ∫ t in (0 : ℝ)..1, omega0 (asympOp J P η t) (J (P.x (P.T * t)) (ζ t)) =
        ∫ t in (0 : ℝ)..1, omega0 (η t) (J (P.x (P.T * t)) (asympOp J P ζ t)) := by
  refine ⟨g71s_asymp_xiLoop hH P J hJ η hη, ?_⟩
  set B : V n →L[ℝ] V n →L[ℝ] ℝ := g71s_omB
  have hηd : ∀ t, HasDerivAt η (deriv η t) t := fun t =>
    ((hη.1.differentiable (by simp)) t).hasDerivAt
  have hζd : ∀ t, HasDerivAt ζ (deriv ζ t) t := fun t =>
    ((hζ.1.differentiable (by simp)) t).hasDerivAt
  have hηc : Continuous (deriv η) := (contDiff_infty_iff_deriv.mp hη.1).2.continuous
  have hζc : Continuous (deriv ζ) := (contDiff_infty_iff_deriv.mp hζ.1).2.continuous
  -- pointwise identity
  have hpt : ∀ t, omega0 (asympOp J P η t) (J (P.x (P.T * t)) (ζ t)) =
      omega0 (η t) (J (P.x (P.T * t)) (asympOp J P ζ t)) -
        (B (η t) (deriv ζ t) + B (deriv η t) (ζ t)) := by
    intro t
    have hy := P.mem (P.T * t)
    have ha := g71s_inner_xi hH P η hη t
    have hb := g71s_inner_xi hH P ζ hζ t
    have hζx := hζ.2.2 t
    have hηx := hη.2.2 t
    have e1 := (hJ.2 _ hy _ _ ha hζx).2.2.2
    have e2 := (hJ.2 _ hy _ _ hb hb).2.1
    unfold asympOp
    rw [e1, e2]
    have key := g71s_om_R'_sum hH hy (η t) (ζ t) hηx.2 hζx.2
    simp only [B, g71s_omB_apply]
    have l1 : omega0 (-deriv η t + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (η t)) (ζ t) =
        -omega0 (deriv η t) (ζ t) + P.T * omega0 (fderiv ℝ (reeb H) (P.x (P.T * t)) (η t)) (ζ t) := by
      simp only [← g71s_omB_apply, map_add, map_neg, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    have l2 : omega0 (η t) (-(-deriv ζ t + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (ζ t))) =
        omega0 (η t) (deriv ζ t) - P.T * omega0 (η t) (fderiv ℝ (reeb H) (P.x (P.T * t)) (ζ t)) := by
      simp only [← g71s_omB_apply, map_add, map_neg, map_smul, smul_eq_mul]; ring
    rw [l1, l2]
    linear_combination P.T * key
  have hcont1 : Continuous (fun t => omega0 (η t) (J (P.x (P.T * t)) (asympOp J P ζ t))) := by
    have hγ : Continuous (fun t => P.x (P.T * t)) :=
      (g71s_x_cd hH P).continuous.comp (continuous_const.mul continuous_id)
    have hA := (g71s_asymp_cd hH P J hJ ζ hζ).continuous
    have : Continuous (fun t => B (η t) (J (P.x (P.T * t)) (asympOp J P ζ t))) :=
      (B.continuous.comp hη.1.continuous).clm_apply
        ((hJ.1.continuous.comp hγ).clm_apply hA)
    simpa [B] using this
  have hcont2 : Continuous (fun t => B (η t) (deriv ζ t) + B (deriv η t) (ζ t)) :=
    ((B.continuous.comp hη.1.continuous).clm_apply hζc).add
      ((B.continuous.comp hηc).clm_apply hζ.1.continuous)
  have hint0 : ∫ t in (0:ℝ)..1, (B (η t) (deriv ζ t) + B (deriv η t) (ζ t)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => B (η t) (ζ t))]
    · simp only [B, g71s_omB_apply]
      have h1 : η 1 = η 0 := by simpa using hη.2.1 0
      have h2 : ζ 1 = ζ 0 := by simpa using hζ.2.1 0
      rw [h1, h2, sub_self]
    · intro t _
      exact B.hasDerivAt_of_bilinear (fun _ => hηd t) (fun _ => hζd t)
    · exact hcont2.intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun t _ => hpt t),
    intervalIntegral.integral_sub (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _),
    hint0, sub_zero]
