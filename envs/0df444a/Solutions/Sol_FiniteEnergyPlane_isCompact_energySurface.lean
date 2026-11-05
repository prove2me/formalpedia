-- Prove2me | solution 1 for FiniteEnergyPlane.isCompact_energySurface
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T16:15:46.823765+00:00
-- url     : https://prove2.me/submissions/54cac601-04be-47fb-8417-4981c6dc973c

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open scoped ContDiff Topology

/-! Algebra helpers for the tube coordinates (copied from Scratch/ZC_L0 `kta_*`). -/




set_option linter.unusedSimpArgs false

def kta_sig {n : ℕ} (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

def kta_sgn {n : ℕ} (k : Fin (2 * (n + 1))) : ℝ := if (k : ℕ) % 2 = 0 then -1 else 1

theorem kta_sig_val {n : ℕ} (k : Fin (2 * (n + 1))) :
    ((kta_sig k : Fin (2 * (n + 1))) : ℕ) = if (k : ℕ) % 2 = 0 then (k : ℕ) + 1 else (k : ℕ) - 1 := by
  unfold kta_sig; split_ifs <;> rfl

theorem kta_sig_sig {n : ℕ} (k : Fin (2 * (n + 1))) : kta_sig (kta_sig k) = k := by
  ext
  rw [kta_sig_val, kta_sig_val]
  split_ifs <;> omega

theorem kta_sgn_sig {n : ℕ} (k : Fin (2 * (n + 1))) : kta_sgn (kta_sig k) = - kta_sgn k := by
  unfold kta_sgn
  rw [kta_sig_val]
  split_ifs <;> (try norm_num) <;> omega

theorem kta_sgn_sq {n : ℕ} (k : Fin (2 * (n + 1))) : kta_sgn k * kta_sgn k = 1 := by
  unfold kta_sgn; split_ifs <;> norm_num

def kta_sigE (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) :=
  Function.Involutive.toPerm kta_sig kta_sig_sig

theorem kta_sigE_apply {n : ℕ} (k : Fin (2 * (n + 1))) : kta_sigE n k = kta_sig k := rfl

theorem kta_j0_apply {n : ℕ} (v : V n) (k : Fin (2 * (n + 1))) :
    j0 v k = kta_sgn k * v (kta_sig k) := by
  unfold j0 kta_sgn kta_sig
  split_ifs <;> simp

theorem kta_j0_j0 {n : ℕ} (v : V n) : j0 (j0 v) = -v := by
  funext k
  rw [kta_j0_apply, kta_j0_apply, kta_sig_sig, kta_sgn_sig]
  simp only [Pi.neg_apply]
  have := kta_sgn_sq k
  linear_combination (-(v k)) * this

theorem kta_j0_smul {n : ℕ} (a : ℝ) (v : V n) : j0 (a • v) = a • j0 v := by
  funext k; simp only [kta_j0_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem kta_j0_add {n : ℕ} (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [kta_j0_apply, Pi.add_apply]; ring

theorem kta_j0_sub {n : ℕ} (u v : V n) : j0 (u - v) = j0 u - j0 v := by
  funext k; simp only [kta_j0_apply, Pi.sub_apply]; ring

theorem kta_dot_comm {n : ℕ} (u v : V n) : dot u v = dot v u := by
  unfold dot; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem kta_dot_smul_right {n : ℕ} (a : ℝ) (u v : V n) : dot u (a • v) = a * dot u v := by
  unfold dot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem kta_dot_smul_left {n : ℕ} (a : ℝ) (u v : V n) : dot (a • u) v = a * dot u v := by
  rw [kta_dot_comm, kta_dot_smul_right, kta_dot_comm]

theorem kta_dot_add_right {n : ℕ} (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem kta_dot_add_left {n : ℕ} (u v w : V n) : dot (v + w) u = dot v u + dot w u := by
  rw [kta_dot_comm, kta_dot_add_right, kta_dot_comm, kta_dot_comm u]

theorem kta_dot_sub_right {n : ℕ} (u v w : V n) : dot u (v - w) = dot u v - dot u w := by
  unfold dot; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem kta_dot_sub_left {n : ℕ} (u v w : V n) : dot (v - w) u = dot v u - dot w u := by
  rw [kta_dot_comm, kta_dot_sub_right, kta_dot_comm, kta_dot_comm u]

theorem kta_dot_neg_right {n : ℕ} (u v : V n) : dot u (-v) = - dot u v := by
  unfold dot; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp)

theorem kta_dot_neg_left {n : ℕ} (u v : V n) : dot (-u) v = - dot u v := by
  rw [kta_dot_comm, kta_dot_neg_right, kta_dot_comm]

theorem kta_dot_j0_left {n : ℕ} (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (kta_sigE n)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [kta_sigE_apply, kta_j0_apply, kta_sig_sig, kta_sgn_sig]
  ring

theorem kta_dot_j0_j0 {n : ℕ} (u v : V n) : dot (j0 u) (j0 v) = dot u v := by
  rw [kta_dot_j0_left, kta_j0_j0, kta_dot_neg_right, neg_neg]

theorem kta_dot_self_j0 {n : ℕ} (u : V n) : dot u (j0 u) = 0 := by
  have := kta_dot_j0_left u u
  rw [kta_dot_comm] at this
  linarith

theorem kta_clm_apply {n : ℕ} (L : V n →L[ℝ] ℝ) (v : V n) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (v k) : V n) = v k • Pi.single k 1 by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul]

theorem kta_fderiv_eq_dot {n : ℕ} (H : V n → ℝ) (x v : V n) :
    fderiv ℝ H x v = dot (grad H x) v := by
  rw [kta_clm_apply]; unfold dot grad
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem kta_liouville_ham {n : ℕ} (H : V n → ℝ) (x : V n) :
    liouville x (hamVF H x) = fderiv ℝ H x x / 2 := by
  unfold liouville omega0 hamVF
  rw [kta_dot_j0_j0, kta_fderiv_eq_dot, kta_dot_comm]

theorem kta_reeb_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  have hpos : 0 < liouville x (hamVF H x) := by
    rw [kta_liouville_ham]; have := hH.2.2 x hx; linarith
  refine ⟨hpos, ?_, ?_, ?_⟩
  · unfold reeb
    have : liouville x ((liouville x (hamVF H x))⁻¹ • hamVF H x) =
        (liouville x (hamVF H x))⁻¹ * liouville x (hamVF H x) := by
      unfold liouville omega0; rw [kta_dot_smul_right]; ring
    rw [this, inv_mul_cancel₀ hpos.ne']
  · unfold reeb hamVF
    rw [map_smul, kta_fderiv_eq_dot, kta_dot_self_j0, smul_zero]
  · intro w hw
    unfold reeb hamVF omega0
    rw [kta_j0_smul, kta_j0_j0, kta_dot_smul_left, kta_dot_neg_left,
      ← kta_fderiv_eq_dot, hw]; ring

theorem kta_om_add_left {n : ℕ} (u v w : V n) : omega0 (u + v) w = omega0 u w + omega0 v w := by
  unfold omega0; rw [kta_j0_add, kta_dot_add_left]
theorem kta_om_add_right {n : ℕ} (u v w : V n) : omega0 w (u + v) = omega0 w u + omega0 w v := by
  unfold omega0; rw [kta_dot_add_right]
theorem kta_om_sub_left {n : ℕ} (u v w : V n) : omega0 (u - v) w = omega0 u w - omega0 v w := by
  unfold omega0; rw [kta_j0_sub, kta_dot_sub_left]
theorem kta_om_sub_right {n : ℕ} (u v w : V n) : omega0 w (u - v) = omega0 w u - omega0 w v := by
  unfold omega0; rw [kta_dot_sub_right]
theorem kta_om_smul_left {n : ℕ} (a : ℝ) (u w : V n) : omega0 (a • u) w = a * omega0 u w := by
  unfold omega0; rw [kta_j0_smul, kta_dot_smul_left]
theorem kta_om_smul_right {n : ℕ} (a : ℝ) (u w : V n) : omega0 w (a • u) = a * omega0 w u := by
  unfold omega0; rw [kta_dot_smul_right]
theorem kta_om_anti {n : ℕ} (u v : V n) : omega0 u v = - omega0 v u := by
  unfold omega0; rw [kta_dot_j0_left, kta_dot_comm]
theorem kta_om_self {n : ℕ} (u : V n) : omega0 u u = 0 := by
  have := kta_om_anti u u; linarith

theorem kta_liouvilleCLM_apply {n : ℕ} (x v : V n) : liouvilleCLM x v = liouville x v := by
  unfold liouvilleCLM liouville omega0 dot
  simp [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem kta_scale_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem kta_scale_unique {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (t : ℝ) (ht : 0 < t) (hHt : H (t • y) = 1) : scaleToS H y = t := by
  obtain ⟨r, _, hu⟩ := hH.2.1 y hy
  have h1 := hu t ⟨ht, hHt⟩
  have h2 := hu (scaleToS H y) (kta_scale_spec H hH y hy)
  rw [h1, h2]



theorem kta_j0_contDiff {n : ℕ} : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 (fun k => ?_)
  have : (fun v : V n => j0 v k) = fun v => kta_sgn k * v (kta_sig k) := by
    funext v; exact kta_j0_apply v k
  rw [this]
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (kta_sig k))

theorem kta_dH_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)

theorem kta_grad_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (grad H) := by
  refine contDiff_pi.2 (fun k => ?_)
  exact (kta_dH_contDiff H hH).clm_apply contDiff_const

theorem kta_hamVF_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamVF H) := kta_j0_contDiff.comp (kta_grad_contDiff H hH)

theorem kta_liouvilleCLM_contDiff {n : ℕ} : ContDiff ℝ ∞ (liouvilleCLM : V n → V n →L[ℝ] ℝ) := by
  unfold liouvilleCLM
  refine ContDiff.const_smul _ (ContDiff.sum (fun k _ => ?_))
  exact ((contDiff_apply ℝ ℝ k).comp kta_j0_contDiff).smul contDiff_const

theorem kta_reeb_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContDiffAt ℝ ∞ (reeb H) x := by
  have hpos := (kta_reeb_spec H hH x hx).1
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [kta_liouvilleCLM_apply]
  have hc : ContDiff ℝ ∞ (fun x => liouville x (hamVF H x)) := by
    rw [hL]; exact kta_liouvilleCLM_contDiff.clm_apply (kta_hamVF_contDiff H hH.1)
  unfold reeb
  exact (hc.contDiffAt.inv hpos.ne').smul (kta_hamVF_contDiff H hH.1).contDiffAt

theorem kta_scale_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y₀ : V n)
    (hy₀ : y₀ ≠ 0) : ContDiffAt ℝ ∞ (scaleToS H) y₀ := by
  obtain ⟨hr, hHx⟩ := kta_scale_spec H hH y₀ hy₀
  set r := scaleToS H y₀
  set f : V n × ℝ → ℝ := fun p => H (p.2 • p.1) with hf
  have hfc : ContDiff ℝ ∞ f := hH.1.comp (ContDiff.smul contDiff_snd contDiff_fst)
  set u : V n × ℝ := (y₀, r)
  have cdf : ContDiffAt ℝ ∞ f u := hfc.contDiffAt
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- derivative
  have hg : HasFDerivAt (fun p : V n × ℝ => p.2 • p.1)
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀) u := by
    have h1 : HasFDerivAt (fun p : V n × ℝ => p.2) (ContinuousLinearMap.snd ℝ (V n) ℝ) u :=
      hasFDerivAt_snd
    have h2 : HasFDerivAt (fun p : V n × ℝ => p.1) (ContinuousLinearMap.fst ℝ (V n) ℝ) u :=
      hasFDerivAt_fst
    exact h1.smul h2
  have hHd : HasFDerivAt H (fderiv ℝ H (r • y₀)) (r • y₀) :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hfd : HasFDerivAt f ((fderiv ℝ H (r • y₀)).comp
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀)) u :=
    hHd.comp u hg
  have hpos : 0 < fderiv ℝ H (r • y₀) y₀ := by
    have := hH.2.2 (r • y₀) hHx
    rw [map_smul, smul_eq_mul] at this
    exact pos_of_mul_pos_right this hr.le
  set c := fderiv ℝ H (r • y₀) y₀
  have hL1 : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ) 1 = c := by
    rw [hfd.fderiv]; simp [c]
  have if₂ : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
      rw [show c⁻¹ = c⁻¹ • (1:ℝ) by simp, map_smul, hL1, smul_eq_mul, inv_mul_cancel₀ hpos.ne']
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply, hL1]
      simp [inv_mul_cancel₀ hpos.ne']
  set ψ := ContDiffAt.implicitFunction cdf pn if₂
  have hψc : ContDiffAt ℝ ∞ ψ y₀ := ContDiffAt.contDiffAt_implicitFunction cdf pn if₂
  have hψ0 : ψ y₀ = r := ContDiffAt.implicitFunction_apply_self cdf pn if₂
  have hψeq := ContDiffAt.eventually_apply_implicitFunction cdf pn if₂
  have hψpos : ∀ᶠ y in 𝓝 y₀, 0 < ψ y := by
    have := hψc.continuousAt.eventually (lt_mem_nhds (show (0:ℝ) < ψ y₀ by rw [hψ0]; exact hr))
    exact this
  have hne : ∀ᶠ y in 𝓝 y₀, y ≠ 0 := isOpen_ne.mem_nhds hy₀
  have hev : ψ =ᶠ[𝓝 y₀] scaleToS H := by
    filter_upwards [hψeq, hψpos, hne] with y h1 h2 h3
    have h1' : H (ψ y • y) = 1 := by
      have : f (y, ψ y) = f u := h1
      simp only [hf, u] at this
      rw [this, hHx]
    exact (kta_scale_unique H hH y h3 (ψ y) h2 h1').symm
  exact hψc.congr_of_eventuallyEq hev.symm

/-! Compactness of a strictly star-shaped level and the Lipschitz bound of its Reeb field. -/


namespace FiniteEnergyPlane

theorem isCompact_energySurface_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    IsCompact (energySurface H) := by
  have hne : ∀ y ∈ sphere (0 : V n) 1, y ≠ 0 := by
    intro y hy h0
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hy
    exact zero_ne_one hy
  have hcont : ContinuousOn (proj H) (sphere (0 : V n) 1) := by
    intro y hy
    have h1 : ContinuousAt (scaleToS H) y :=
      (kta_scale_contDiffAt H hH y (hne y hy)).continuousAt
    exact (h1.smul continuousAt_id).continuousWithinAt
  have hcpt : IsCompact (proj H '' sphere (0 : V n) 1) :=
    (isCompact_sphere (0 : V n) 1).image_of_continuousOn hcont
  have hcl : IsClosed (energySurface H) := isClosed_eq hH.1.continuous continuous_const
  refine hcpt.of_isClosed_subset hcl ?_
  intro y hy
  have hy1 : H y = 1 := hy
  have hy0 : y ≠ 0 := by
    intro h0
    have := hH.2.2 y hy1
    simp [h0] at this
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  set u : V n := ‖y‖⁻¹ • y with hu
  have huy : ‖y‖ • u = y := by
    rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hus : u ∈ sphere (0 : V n) 1 := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  refine ⟨u, hus, ?_⟩
  have := kta_scale_unique H hH u (hne u hus) ‖y‖ hn (by rw [huy]; exact hy1)
  simp only [proj]
  rw [this, huy]

theorem exists_lipschitzOnWith_reeb_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ∃ K : NNReal, LipschitzOnWith K (reeb H) (energySurface H) := by
  refine LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_energySurface_aux H hH) ?_
  intro x hx
  have h1 : ContDiffAt ℝ 1 (reeb H) x := (kta_reeb_contDiffAt H hH x hx).of_le (by simp)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    IsCompact (energySurface H) :=
  isCompact_energySurface_aux H hH
