-- Prove2me | solution 1 for FiniteEnergyPlane.eq_of_proj_add_eq_proj_add
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T20:53:25.498912+00:00
-- url     : https://prove2.me/submissions/f34ac580-8f8f-46d1-884f-0b8c97f631a2

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x

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

/-! F child C2: the tube map `(τ, h) ↦ proj (x τ + h)`, `h ∈ ξ_{x τ}`, is injective on pairs with
`|τ - τ'| ≤ ε`, `‖h‖, ‖h'‖ ≤ ρ`. -/

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

lemma pef_periodic_bdd {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hf : Continuous f) (hper : Function.Periodic f T) : ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  have hb : ∀ x, ‖f x‖ ≤ C := by
    intro x
    obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico₀ hT x
    rw [hfy]; exact hC y (Set.Ico_subset_Icc_self hy)
  exact ⟨C, le_trans (norm_nonneg _) (hb 0), hb⟩

lemma pef_abs_le_norm {n : ℕ} (v : V n) (i : Fin (2 * (n + 1))) : |v i| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i

lemma pef_abs_omega0_le {n : ℕ} (a b : V n) :
    |omega0 a b| ≤ ((2 * (n + 1) : ℕ) : ℝ) * (‖a‖ * ‖b‖) := by
  have hj : ∀ k, |j0 a k| ≤ ‖a‖ := by
    intro k
    unfold j0
    split_ifs
    · rw [abs_neg]; exact pef_abs_le_norm a _
    · exact pef_abs_le_norm a _
  unfold omega0 dot
  calc |∑ k, j0 a k * b k| ≤ ∑ k, |j0 a k * b k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (2 * (n + 1)), ‖a‖ * ‖b‖ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hj k) (pef_abs_le_norm b k) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma pef_abs_liouville_le {n : ℕ} (a b : V n) :
    |liouville a b| ≤ ((2 * (n + 1) : ℕ) : ℝ) * (‖a‖ * ‖b‖) := by
  unfold liouville
  rw [abs_div, abs_two]
  have := pef_abs_omega0_le a b
  have h0 : 0 ≤ ((2 * (n + 1) : ℕ) : ℝ) * (‖a‖ * ‖b‖) := by positivity
  linarith

lemma pef_liouville_add {n : ℕ} (x a b : V n) :
    liouville x (a + b) = liouville x a + liouville x b := by
  unfold liouville; rw [kta_om_add_right]; ring

lemma pef_liouville_sub {n : ℕ} (x a b : V n) :
    liouville x (a - b) = liouville x a - liouville x b := by
  unfold liouville; rw [kta_om_sub_right]; ring

lemma pef_liouville_smul {n : ℕ} (x a : V n) (c : ℝ) :
    liouville x (c • a) = c * liouville x a := by
  unfold liouville; rw [kta_om_smul_right]; ring

lemma pef_liouville_sub_left {n : ℕ} (x y a : V n) :
    liouville x a - liouville y a = liouville (x - y) a := by
  unfold liouville; rw [kta_om_sub_left]; ring

lemma pef_liouville_self {n : ℕ} (y : V n) : liouville y y = 0 := by
  unfold liouville; rw [kta_om_self]; simp

lemma pef_scale_pos {n : ℕ} (H : V n → ℝ) (y : V n) : 0 < scaleToS H y := by
  unfold scaleToS
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact one_pos

lemma pef_eq_smul_of_proj_eq {n : ℕ} (H : V n → ℝ) {y y' : V n} (h : proj H y = proj H y') :
    ∃ κ : ℝ, 0 < κ ∧ y = κ • y' := by
  have hs := pef_scale_pos H y
  have hs' := pef_scale_pos H y'
  refine ⟨(scaleToS H y)⁻¹ * scaleToS H y', by positivity, ?_⟩
  unfold proj at h
  rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

theorem eq_of_proj_add_eq_proj_add_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) :
    ∃ ε > 0, ∃ ρ > 0, ∀ (τ τ' : ℝ) (h h' : V n), |τ - τ'| ≤ ε →
      IsInXi H (P.x τ) h → IsInXi H (P.x τ') h' → ‖h‖ ≤ ρ → ‖h'‖ ≤ ρ →
      proj H (P.x τ + h) = proj H (P.x τ' + h') → τ = τ' ∧ h = h' := by
  have hx : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  set g : ℝ → V n := fun σ => reeb H (P.x σ) with hg
  have hdx : deriv P.x = g := funext fun σ => (P.hasDerivAt σ).deriv
  have hg1 : ContDiff ℝ ∞ g := by
    have := ContDiff.iterate_deriv 1 hx
    simpa [hdx] using this
  have hgd : Differentiable ℝ g := hg1.differentiable (by simp)
  have hg2c : Continuous (deriv g) := hg1.continuous_deriv (by simp)
  have hxper : Function.Periodic P.x P.T := P.periodic
  have hgper : Function.Periodic g P.T := fun σ => by simp only [hg, P.periodic]
  have hg2per : Function.Periodic (deriv g) P.T := by
    intro σ
    have : (fun y => g (y + P.T)) = g := funext fun y => hgper y
    rw [← deriv_comp_add_const, this]
  obtain ⟨M₀, hM₀, hxb⟩ := pef_periodic_bdd P.T_pos hx.continuous hxper
  obtain ⟨L, hL, hgb⟩ := pef_periodic_bdd P.T_pos hg1.continuous hgper
  obtain ⟨L₂, hL₂, hg2b⟩ := pef_periodic_bdd P.T_pos hg2c hg2per
  set Kω : ℝ := ((2 * (n + 1) : ℕ) : ℝ) with hKω
  have hKω0 : 0 ≤ Kω := by positivity
  set A : ℝ := Kω * M₀ * L₂ with hA
  set B : ℝ := Kω * L with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine ⟨1 / (4 * A + 1), by positivity, 1 / (4 * B + 1), by positivity, ?_⟩
  intro τ τ' h h' hττ' hh hh' hρh hρh' hproj
  -- Lipschitz bounds
  have hxlip : ∀ a b : ℝ, ‖P.x b - P.x a‖ ≤ L * ‖b - a‖ := fun a b =>
    (convex_univ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun σ _ => (P.hasDerivAt σ).hasDerivWithinAt) (fun σ _ => hgb σ) (Set.mem_univ a)
      (Set.mem_univ b)
  have hglip : ∀ a b : ℝ, ‖g b - g a‖ ≤ L₂ * ‖b - a‖ := fun a b =>
    (convex_univ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun σ _ => (hgd σ).hasDerivAt.hasDerivWithinAt) (fun σ _ => hg2b σ) (Set.mem_univ a)
      (Set.mem_univ b)
  set δ := τ' - τ with hδ
  have hδabs : |δ| ≤ 1 / (4 * A + 1) := by rw [hδ, abs_sub_comm]; exact hττ'
  -- Taylor remainder
  set E : V n := P.x τ' - P.x τ - δ • g τ with hE
  have hEb : ‖E‖ ≤ L₂ * |δ| * |δ| := by
    set f : ℝ → V n := fun σ => P.x σ - (σ - τ) • g τ with hf
    have hfd : ∀ σ, HasDerivAt f (g σ - (1 : ℝ) • g τ) σ := fun σ =>
      (P.hasDerivAt σ).sub (((hasDerivAt_id σ).sub_const τ).smul_const (g τ))
    have hb : ∀ σ ∈ Set.uIcc τ τ', ‖g σ - (1 : ℝ) • g τ‖ ≤ L₂ * |δ| := by
      intro σ hσ
      rw [one_smul]
      refine le_trans (hglip τ σ) (mul_le_mul_of_nonneg_left ?_ hL₂)
      rw [Real.norm_eq_abs, hδ]
      exact Set.abs_sub_left_of_mem_uIcc hσ
    have := (convex_uIcc τ τ').norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun σ _ => (hfd σ).hasDerivWithinAt) hb Set.left_mem_uIcc Set.right_mem_uIcc
    have hfτ : f τ = P.x τ := by simp [hf]
    have hfτ' : f τ' - f τ = E := by rw [hfτ]; simp only [hf, hE, hδ]; abel
    rw [hfτ', Real.norm_eq_abs, ← hδ] at this
    exact this
  -- step 1: τ = τ'
  obtain ⟨κ, hκ, hy⟩ := pef_eq_smul_of_proj_eq H hproj
  have hreeb := kta_reeb_spec H hH (P.x τ) (P.mem τ)
  have hL1 : liouville (P.x τ) (P.x τ') + liouville (P.x τ) h' = 0 := by
    have := congrArg (liouville (P.x τ)) hy
    rw [pef_liouville_add, pef_liouville_self, hh.1, zero_add, pef_liouville_smul,
      pef_liouville_add] at this
    rcases mul_eq_zero.1 this.symm with h0 | h0
    · exact absurd h0 hκ.ne'
    · exact h0
  have hsplit : liouville (P.x τ) (P.x τ') = δ + liouville (P.x τ) E := by
    have : P.x τ' = P.x τ + (δ • g τ + E) := by rw [hE]; abel
    rw [this, pef_liouville_add, pef_liouville_self, pef_liouville_add, pef_liouville_smul,
      hg]
    simp only [hreeb.2.1]; ring
  have hEl : |liouville (P.x τ) E| ≤ A * (|δ| * |δ|) := by
    refine le_trans (pef_abs_liouville_le _ _) ?_
    calc Kω * (‖P.x τ‖ * ‖E‖) ≤ Kω * (M₀ * (L₂ * |δ| * |δ|)) := by
          gcongr
          · exact hxb τ
    _ = A * (|δ| * |δ|) := by rw [hA]; ring
  have hhl : |liouville (P.x τ) h'| ≤ B * (|δ| * (1 / (4 * B + 1))) := by
    have : liouville (P.x τ) h' = liouville (P.x τ - P.x τ') h' := by
      rw [← pef_liouville_sub_left, hh'.1, sub_zero]
    rw [this]
    refine le_trans (pef_abs_liouville_le _ _) ?_
    have hxx : ‖P.x τ - P.x τ'‖ ≤ L * |δ| := by
      rw [norm_sub_rev]; have := hxlip τ τ'; rwa [Real.norm_eq_abs] at this
    calc Kω * (‖P.x τ - P.x τ'‖ * ‖h'‖) ≤ Kω * ((L * |δ|) * (1 / (4 * B + 1))) := by
          gcongr
    _ = B * (|δ| * (1 / (4 * B + 1))) := by rw [hB]; ring
  have hτeq : τ = τ' := by
    have heq : δ = -(liouville (P.x τ) E + liouville (P.x τ) h') := by linarith
    have hδle : |δ| ≤ A * (|δ| * |δ|) + B * (|δ| * (1 / (4 * B + 1))) := by
      have habs : |δ| = |liouville (P.x τ) E + liouville (P.x τ) h'| := by rw [heq, abs_neg]
      exact habs.le.trans (le_trans (abs_add_le _ _) (add_le_add hEl hhl))
    have h1 : A * (|δ| * |δ|) ≤ |δ| / 4 := by
      have : A * |δ| ≤ 1 / 4 := by
        calc A * |δ| ≤ A * (1 / (4 * A + 1)) := mul_le_mul_of_nonneg_left hδabs hA0
        _ ≤ 1 / 4 := by rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      nlinarith [abs_nonneg δ]
    have h2 : B * (|δ| * (1 / (4 * B + 1))) ≤ |δ| / 4 := by
      have : B * (1 / (4 * B + 1)) ≤ 1 / 4 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      nlinarith [abs_nonneg δ]
    have : |δ| = 0 := by linarith [abs_nonneg δ]
    have : δ = 0 := abs_eq_zero.1 this
    linarith
  -- step 2: h = h'
  subst hτeq
  have hdH := hH.2.2 (P.x τ) (P.mem τ)
  have hκ1 : κ = 1 := by
    have := congrArg (fderiv ℝ H (P.x τ)) hy
    rw [map_add, hh.2, add_zero, map_smul, map_add, hh'.2, add_zero, smul_eq_mul] at this
    have : (κ - 1) * fderiv ℝ H (P.x τ) (P.x τ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · exact absurd h0 hdH.ne'
  rw [hκ1, one_smul] at hy
  exact ⟨rfl, add_left_cancel hy⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) :
    ∃ ε > 0, ∃ ρ > 0, ∀ (τ τ' : ℝ) (h h' : V n), |τ - τ'| ≤ ε →
      IsInXi H (P.x τ) h → IsInXi H (P.x τ') h' → ‖h‖ ≤ ρ → ‖h'‖ ≤ ρ →
      proj H (P.x τ + h) = proj H (P.x τ' + h') → τ = τ' ∧ h = h' :=
  eq_of_proj_add_eq_proj_add_aux H hH P
