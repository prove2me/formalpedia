-- Prove2me | solution 1 for ClarkeGradients.FlowInvariance.gradient_infDist_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:37:38.064932+00:00
-- url     : https://prove2.me/submissions/9aa9e3eb-06bf-41bf-86f3-5a785b3eb6d7

import Mathlib

namespace ClarkeGradients.FlowInvariance

open InnerProductSpace RealInnerProductSpace

theorem aux_gid_inner {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x v : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient f x, v⟫_ℝ = fderiv ℝ f x v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

theorem aux_gid_norm {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

theorem aux_gid_normle {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (fun y => Metric.infDist y E) x‖ ≤ 1 := by
  rw [aux_gid_norm]
  have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (Metric.lipschitz_infDist_pt (s := E))
  simpa using this

theorem aux_gid_dir {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) (x e : EuclideanSpace ℝ (Fin n))
    (hdiff : DifferentiableAt ℝ (fun y => Metric.infDist y E) x)
    (he : e ∈ E) (hd : dist x e = Metric.infDist x E) (hxe : x ≠ e) :
    ‖x - e‖ ≤ fderiv ℝ (fun y => Metric.infDist y E) x (x - e) := by
  set f := fun y => Metric.infDist y E with hf
  set u := x - e with hu
  set d := ‖u‖ with hdd
  have hdpos : 0 < d := by
    rw [hdd, hu]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hxe)
  have hfx : f x = d := by
    simp only [hf, hdd, hu]; rw [← hd, dist_eq_norm]
  set F := fun y => d * f y - innerSL ℝ u y with hF
  have hderiv : HasFDerivAt F (d • fderiv ℝ f x - innerSL ℝ u) x :=
    (hdiff.hasFDerivAt.const_mul d).sub (innerSL ℝ u).hasFDerivAt
  have hmax : IsLocalMaxOn F (segment ℝ x e) x := by
    apply IsMaxOn.localize
    intro y hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    simp only [Set.mem_ofPred_eq, hF]
    have h1 : f (a • x + b • e) ≤ a * d := by
      have := Metric.infDist_le_dist_of_mem (x := a • x + b • e) he
      refine this.trans (le_of_eq ?_)
      rw [dist_eq_norm]
      have : a • x + b • e - e = a • u := by
        rw [hu, smul_sub]
        have : b = 1 - a := by linarith
        subst this
        rw [sub_smul, one_smul]; abel
      rw [this, norm_smul, Real.norm_of_nonneg ha]
    have h2 : a • x + b • e = x - b • u := by
      have : a = 1 - b := by linarith
      subst this
      rw [hu, sub_smul, one_smul, smul_sub]; abel
    rw [h2, map_sub, map_smul, hfx]
    simp only [innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
    rw [← hdd]
    have : d * f (x - b • u) ≤ d * (a * d) := mul_le_mul_of_nonneg_left (h2 ▸ h1) hdpos.le
    nlinarith
  have hcone : e - x ∈ posTangentConeAt (segment ℝ x e) x :=
    sub_mem_posTangentConeAt_of_segment_subset (subset_refl _)
  have key := hmax.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt hcone
  have hex : e - x = -u := by rw [hu, neg_sub]
  rw [hex] at key
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_neg,
    innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq] at key
  rw [← hdd] at key
  have : d * d ≤ d * fderiv ℝ f x u := by nlinarith
  exact le_of_mul_le_mul_left this hdpos

end ClarkeGradients.FlowInvariance

open ClarkeGradients.FlowInvariance

theorem solution {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : E.Nonempty) (hEc : IsClosed E) (x : EuclideanSpace ℝ (Fin n))
    (hdiff : DifferentiableAt ℝ (fun y => Metric.infDist y E) x)
    (hne : gradient (fun y => Metric.infDist y E) x ≠ 0) :
    x ∉ E ∧
      (∃! e : EuclideanSpace ℝ (Fin n), e ∈ E ∧ dist x e = Metric.infDist x E) ∧
      ∀ e ∈ E, dist x e = Metric.infDist x E →
        gradient (fun y => Metric.infDist y E) x = ‖x - e‖⁻¹ • (x - e) := by
  have hxE : x ∉ E := by
    intro hx
    apply hne
    have hmin : IsLocalMin (fun y => Metric.infDist y E) x := by
      apply Filter.Eventually.of_forall
      intro y
      simp only [Metric.infDist_zero_of_mem hx]
      exact Metric.infDist_nonneg
    have := hmin.fderiv_eq_zero
    simp [gradient, this]
  have hgrad : ∀ e ∈ E, dist x e = Metric.infDist x E →
      gradient (fun y => Metric.infDist y E) x = ‖x - e‖⁻¹ • (x - e) := by
    intro e he hd
    have hxe : x ≠ e := fun h => hxE (h ▸ he)
    have hdir := aux_gid_dir E x e hdiff he hd hxe
    rw [← aux_gid_inner] at hdir
    have hnorm := aux_gid_normle E x
    set g := gradient (fun y => Metric.infDist y E) x
    set u := x - e with hu
    have hupos : 0 < ‖u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxe)
    set w := ‖u‖⁻¹ • u with hw
    have hwn : ‖w‖ = 1 := by
      rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hupos.ne']
    have hgw : 1 ≤ inner ℝ g w := by
      rw [hw, inner_smul_right]
      rw [le_inv_mul_iff₀ hupos]; linarith
    have hsq : ‖g - w‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, hwn]
      have : ‖g‖ ^ 2 ≤ 1 := by
        have h0 := norm_nonneg g
        nlinarith
      nlinarith
    have : ‖g - w‖ = 0 := by
      have := sq_nonneg ‖g - w‖
      have h2 : ‖g - w‖ ^ 2 = 0 := le_antisymm hsq this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  refine ⟨hxE, ?_, hgrad⟩
  obtain ⟨e, he, hed⟩ := hEc.exists_infDist_eq_dist hE x
  refine ⟨e, ⟨he, hed.symm⟩, ?_⟩
  rintro e' ⟨he', hed'⟩
  have h1 := hgrad e he hed.symm
  have h2 := hgrad e' he' hed'
  rw [h1] at h2
  have hn : ‖x - e'‖ = ‖x - e‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, hed', hed]
  rw [hn] at h2
  have hxe : x ≠ e := fun h => hxE (h ▸ he)
  have hupos : 0 < ‖x - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxe)
  have := smul_right_injective _ (inv_ne_zero hupos.ne') h2
  have : x - e' = x - e := this.symm
  exact sub_right_injective this
