-- Prove2me | solution 1 for FiniteEnergyPlane.exists_reebTube_coords_of_drift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T15:29:05.544768+00:00
-- url     : https://prove2.me/submissions/0a7a0351-3682-4457-aa7d-17540197851b

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_exists_smooth_periodic_root_family
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_mul_norm_of_periodic
import Theorems.Thm_FiniteEnergyPlane_exists_bound_iteratedFDeriv_of_periodic
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd
import Theorems.Thm_FiniteEnergyPlane_exists_period_near_of_forall_shift_close
import Theorems.Thm_FiniteEnergyPlane_exists_bound_iteratedFDeriv_comp_periodic

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

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A continuous `T`-periodic positive function has a positive lower bound. -/
lemma ktd_periodic_lb {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : Continuous f)
    (hper : Function.Periodic f T) (hpos : ∀ x, 0 < f x) : ∃ m > 0, ∀ x, m ≤ f x := by
  obtain ⟨x₀, -, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hT.le) hf.continuousOn
  refine ⟨f x₀, hpos x₀, fun x => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico₀ hT x
  rw [hfy]
  exact hmin (Set.Ico_subset_Icc_self hy)

lemma ktd_liouville_self {n : ℕ} (y : V n) : liouville y y = 0 := by
  unfold liouville; rw [kta_om_self]; simp

lemma ktd_liouville_anti {n : ℕ} (a b : V n) : liouville a b = -liouville b a := by
  unfold liouville; rw [kta_om_anti]; ring

lemma ktd_ne_zero_of_mem {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : H y = 1) : y ≠ 0 := by
  intro h
  have := hH.2.2 y hy
  rw [h, map_zero] at this
  exact lt_irrefl _ this

lemma ktd_proj_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : H y = 1) {ρ : ℝ} (hρ : 0 < ρ) : proj H (ρ • y) = y := by
  have hy0 := ktd_ne_zero_of_mem hH hy
  have hne : ρ • y ≠ 0 := smul_ne_zero hρ.ne' hy0
  have hs : scaleToS H (ρ • y) = ρ⁻¹ :=
    kta_scale_unique H hH _ hne ρ⁻¹ (inv_pos.2 hρ) (by rw [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul, hy])
  unfold proj; rw [hs, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

/-- Floor bounds used to place a point in its window. -/
lemma ktd_floor {z : ℝ} (hz : -1 < z) : (⌊z⌋₊ : ℝ) ≤ max z 0 ∧ z < ⌊z⌋₊ + 1 := by
  rcases le_or_gt 0 z with h | h
  · exact ⟨(Nat.floor_le h).trans (le_max_left _ _), Nat.lt_floor_add_one z⟩
  · rw [Nat.floor_eq_zero.2 (by linarith)]
    simp only [Nat.cast_zero, zero_add]
    exact ⟨le_max_right _ _, by linarith⟩

set_option maxHeartbeats 3200000 in
theorem exists_reebTube_coords_of_drift_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (w : ℝ × ℝ → V n) (s₀ : ℝ)
    (hwsm : ContDiffOn ℝ ∞ w (Set.Ioi s₀ ×ˢ Set.univ))
    (hwS : ∀ s > s₀, ∀ t : ℝ, H (w (s, t)) = 1)
    (hwper : ∀ s t : ℝ, w (s, t + 1) = w (s, t))
    (hw : ∀ m : ℕ, ∀ η > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => w p - P.x (ε * P.T * p.2 + c')) (s, t)‖ ≤ η) :
    ∃ (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₁ K : ℝ),
      (∃ s₂ : ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η) ∧
      TendstoZeroCInfty h ∧
      ∀ s ≥ s₁, ∀ t : ℝ,
        τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧ w (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) ∧
        ‖w (s, t) - P.x (τ (s, t))‖ ≤ K * ‖h (s, t)‖ := by
  classical
  obtain ⟨x, T, hT, hxS', hxd, hxper'⟩ := P
  simp only at hw ⊢
  have hxs : ContDiff ℝ ∞ x := ReebOrbit.contDiff_x H hH ⟨x, T, hT, hxS', hxd, hxper'⟩
  have hxper : Function.Periodic x T := hxper'
  have hxS : ∀ τ, H (x τ) = 1 := hxS'
  have hxperε : ∀ τ, x (τ + ε * T) = x τ := by
    intro τ; rcases hε with rfl | rfl
    · rw [one_mul]; exact hxper τ
    · rw [neg_one_mul]; exact hxper.neg τ
  have hεT : ε * T ≠ 0 := mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) hT.ne'
  have habsεT : |ε * T| = T := by
    rcases hε with rfl | rfl <;> simp [abs_of_pos hT]
  have hx0 : ∀ τ, x τ ≠ 0 := fun τ => ktd_ne_zero_of_mem hH (hxS τ)
  have hdH : ContDiff ℝ ∞ (fderiv ℝ H) := kta_dH_contDiff H hH.1
  -- the scalar equation `λ_{x φ + u}(x(φ + σ)) = 0`
  obtain ⟨G, hG_def⟩ : ∃ G : (ℝ × V n) × ℝ → ℝ,
      ∀ q, G q = liouvilleCLM (x q.1.1 + q.1.2) (x (q.1.1 + q.2)) := ⟨_, fun _ => rfl⟩
  have hGs : ContDiff ℝ ∞ G := by
    have h1 : ContDiff ℝ ∞ (fun q : (ℝ × V n) × ℝ => x q.1.1 + q.1.2) :=
      (hxs.comp (contDiff_fst.comp contDiff_fst)).add (contDiff_snd.comp contDiff_fst)
    have h2 : ContDiff ℝ ∞ (fun q : (ℝ × V n) × ℝ => x (q.1.1 + q.2)) :=
      hxs.comp ((contDiff_fst.comp contDiff_fst).add contDiff_snd)
    have : G = fun q => liouvilleCLM (x q.1.1 + q.1.2) (x (q.1.1 + q.2)) := funext hG_def
    rw [this]
    exact (kta_liouvilleCLM_contDiff.comp h1).clm_apply h2
  have hGper : ∀ (φ : ℝ) (u : V n) (σ : ℝ), G ((φ + T, u), σ) = G ((φ, u), σ) := by
    intro φ u σ
    rw [hG_def, hG_def]
    simp only
    rw [hxper φ, show φ + T + σ = (φ + σ) + T by ring, hxper]
  have hG0 : ∀ φ : ℝ, G ((φ, 0), 0) = 0 := by
    intro φ
    rw [hG_def]; simp only [add_zero, kta_liouvilleCLM_apply]
    exact ktd_liouville_self _
  have hGd : ∀ φ : ℝ, deriv (fun σ : ℝ => G ((φ, 0), σ)) 0 ≠ 0 := by
    intro φ
    have hx' : HasDerivAt (fun σ : ℝ => x (φ + σ)) (reeb H (x φ)) 0 :=
      HasDerivAt.comp_const_add φ 0 (by rw [add_zero]; exact hxd φ)
    have hd : HasDerivAt (fun σ : ℝ => G ((φ, 0), σ)) (liouvilleCLM (x φ) (reeb H (x φ))) 0 := by
      have : (fun σ : ℝ => G ((φ, 0), σ)) = fun σ => liouvilleCLM (x φ) (x (φ + σ)) := by
        funext σ; rw [hG_def]; simp
      rw [this]
      exact (liouvilleCLM (x φ)).hasFDerivAt.comp_hasDerivAt 0 hx'
    rw [hd.deriv, kta_liouvilleCLM_apply, (kta_reeb_spec H hH (x φ) (hxS φ)).2.1]
    exact one_ne_zero
  obtain ⟨δ, r, hδ, hδ1, hr, g, hgs, hgper, hg0, hgroot⟩ :=
    exists_smooth_periodic_root_family G hGs T hT hGper hG0 hGd 1 one_pos
  have hgperε : ∀ φ u, g (φ + ε * T, u) = g (φ, u) := by
    intro φ u; rcases hε with rfl | rfl
    · rw [one_mul]; exact hgper φ u
    · rw [neg_one_mul, ← hgper (φ + -T) u, show φ + -T + T = φ by ring]
  -- positive lower bounds along the orbit
  have hNc : Continuous fun τ => fderiv ℝ H (x τ) (x τ) :=
    (hdH.continuous.comp hxs.continuous).clm_apply hxs.continuous
  obtain ⟨m, hm, hmN⟩ := ktd_periodic_lb hT hNc
    (fun τ => by show fderiv ℝ H (x (τ + T)) (x (τ + T)) = _; rw [hxper])
    (fun τ => hH.2.2 _ (hxS τ))
  obtain ⟨d, hd, hdx⟩ := ktd_periodic_lb hT (continuous_norm.comp hxs.continuous)
    (fun τ => by simp only [Function.comp_apply]; rw [hxper])
    (fun τ => norm_pos_iff.2 (hx0 τ))
  -- the denominator `dH(x τ)(w)` and its deviation from `dH(x τ)(x τ)`
  set S := (Set.univ : Set ℝ) ×ˢ ball (0 : V n) r with hS
  have hSo : IsOpen S := isOpen_univ.prod isOpen_ball
  have hτs : ContDiffOn ℝ ∞ (fun q : ℝ × V n => x (q.1 + g q)) S :=
    hxs.comp_contDiffOn (contDiff_fst.contDiffOn.add hgs)
  have hdens : ContDiffOn ℝ ∞ (fun q : ℝ × V n => fderiv ℝ H (x (q.1 + g q)) (x q.1 + q.2)) S :=
    (hdH.comp_contDiffOn hτs).clm_apply
      ((hxs.comp contDiff_fst).add contDiff_snd).contDiffOn
  have hNs : ContDiffOn ℝ ∞
      (fun q : ℝ × V n => fderiv ℝ H (x (q.1 + g q)) (x (q.1 + g q))) S :=
    (hdH.comp_contDiffOn hτs).clm_apply hτs
  obtain ⟨LD, hLD0, hLD⟩ := exists_norm_le_mul_norm_of_periodic
    (fun q : ℝ × V n => fderiv ℝ H (x (q.1 + g q)) (x q.1 + q.2) -
      fderiv ℝ H (x (q.1 + g q)) (x (q.1 + g q))) T r hT hr
    ((hdens.sub hNs).of_le (by simp))
    (fun φ u _ => by
      simp only
      rw [hgper, show φ + T + g (φ, u) = (φ + g (φ, u)) + T by ring, hxper, hxper])
    (fun φ => by simp [hg0])
  set r' := min (r / 2) (m / (2 * (LD + 1))) with hr'
  have hr'pos : 0 < r' := lt_min (by linarith) (div_pos hm (by linarith))
  have hr'r : r' ≤ r / 2 := min_le_left _ _
  have hden : ∀ φ (u : V n), ‖u‖ < r' → m / 2 ≤ fderiv ℝ H (x (φ + g (φ, u))) (x φ + u) := by
    intro φ u hu
    have h1 := hLD φ u (by linarith)
    rw [Real.norm_eq_abs] at h1
    have h2 : LD * ‖u‖ ≤ m / 2 := by
      have hu' : ‖u‖ ≤ m / (2 * (LD + 1)) := hu.le.trans (min_le_right _ _)
      have h3 : LD * ‖u‖ ≤ (LD + 1) * ‖u‖ := by nlinarith [norm_nonneg u]
      have h4 : (LD + 1) * ‖u‖ ≤ (LD + 1) * (m / (2 * (LD + 1))) :=
        mul_le_mul_of_nonneg_left hu' (by linarith)
      have h5 : (LD + 1) * (m / (2 * (LD + 1))) = m / 2 := by field_simp
      linarith
    have h6 := hmN (φ + g (φ, u))
    have h7 := (abs_le.1 (h1.trans h2)).1
    beta_reduce at h6 h7
    linarith
  -- the normal component `h(φ, u) = ρ (x φ + u) - x τ`
  obtain ⟨Hf, hHf⟩ : ∃ Hf : ℝ × V n → V n, ∀ q, Hf q =
      (fderiv ℝ H (x (q.1 + g q)) (x (q.1 + g q)) /
        fderiv ℝ H (x (q.1 + g q)) (x q.1 + q.2)) • (x q.1 + q.2) - x (q.1 + g q) :=
    ⟨_, fun _ => rfl⟩
  have hS' : (Set.univ : Set ℝ) ×ˢ ball (0 : V n) r' ⊆ S :=
    Set.prod_mono le_rfl (ball_subset_ball (by linarith))
  have hHfs : ContDiffOn ℝ ∞ Hf ((Set.univ : Set ℝ) ×ˢ ball (0 : V n) r') := by
    have : Hf = fun q => (fderiv ℝ H (x (q.1 + g q)) (x (q.1 + g q)) /
        fderiv ℝ H (x (q.1 + g q)) (x q.1 + q.2)) • (x q.1 + q.2) - x (q.1 + g q) := funext hHf
    rw [this]
    refine ((((hNs.mono hS').div (hdens.mono hS') ?_).smul
      ((hxs.comp contDiff_fst).add contDiff_snd).contDiffOn)).sub (hτs.mono hS')
    rintro ⟨φ, u⟩ ⟨-, hu⟩
    rw [mem_ball_zero_iff] at hu
    have := hden φ u hu
    exact (by linarith : (0 : ℝ) < _).ne'
  have hHfper : ∀ φ u, Hf (φ + T, u) = Hf (φ, u) := by
    intro φ u
    rw [hHf, hHf]; simp only
    rw [hgper, show φ + T + g (φ, u) = (φ + g (φ, u)) + T by ring, hxper, hxper]
  have hHfperε : ∀ φ u, Hf (φ + ε * T, u) = Hf (φ, u) := by
    intro φ u; rcases hε with rfl | rfl
    · rw [one_mul]; exact hHfper φ u
    · rw [neg_one_mul, ← hHfper (φ + -T) u, show φ + -T + T = φ by ring]
  have hHf0 : ∀ φ, Hf (φ, 0) = 0 := by
    intro φ
    rw [hHf]; simp only [hg0, add_zero]
    rw [div_self (hH.2.2 _ (hxS φ)).ne', one_smul, sub_self]
  -- radial projection near the orbit
  obtain ⟨LP, hLP0, hLP⟩ := exists_norm_le_mul_norm_of_periodic
    (fun q : ℝ × V n => proj H (x q.1 + q.2) - x q.1) T d hT hd
    (by
      intro q hq
      obtain ⟨φ, u⟩ := q
      have hu : ‖u‖ < d := by simpa using hq.2
      have hne : x φ + u ≠ 0 := by
        intro h0
        have : u = -x φ := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h0
        rw [this, norm_neg] at hu
        have := hdx φ
        simp only [Function.comp_apply] at this
        linarith
      have hin : ContDiffAt ℝ ∞ (fun q : ℝ × V n => x q.1 + q.2) (φ, u) :=
        ((hxs.comp contDiff_fst).add contDiff_snd).contDiffAt
      have hpr : ContDiffAt ℝ ∞ (fun q : ℝ × V n => proj H (x q.1 + q.2)) (φ, u) := by
        unfold proj
        exact ((kta_scale_contDiffAt H hH _ hne).comp (φ, u) hin).smul hin
      exact ((hpr.sub (hxs.comp contDiff_fst).contDiffAt).of_le (by simp)).contDiffWithinAt)
    (fun φ u _ => by simp only; rw [hxper])
    (fun φ => by
      simp only [add_zero]
      have := ktd_proj_smul hH (hxS φ) one_pos
      rw [one_smul] at this; rw [this, sub_self])
  -- pointwise tube identities (as in the fixed-phase case)
  have hpt : ∀ (φ : ℝ) (u wv : V n), H wv = 1 → wv = x φ + u → ‖u‖ < r' →
      ‖Hf (φ, u)‖ ≤ d / 2 →
      IsInXi H (x (φ + g (φ, u))) (Hf (φ, u)) ∧ wv = proj H (x (φ + g (φ, u)) + Hf (φ, u)) ∧
        ‖wv - x (φ + g (φ, u))‖ ≤ LP * ‖Hf (φ, u)‖ := by
    intro φ u wv hwv hwu hur' hhsmall
    have hur : ‖u‖ < r := by linarith
    obtain ⟨-, hgG, -⟩ := hgroot φ u hur
    set τ0 := φ + g (φ, u) with hτ0
    set den := fderiv ℝ H (x τ0) (x φ + u) with hden_def
    set N := fderiv ℝ H (x τ0) (x τ0) with hN_def
    have hdenpos : 0 < den := by have := hden φ u hur'; linarith
    have hNpos : 0 < N := lt_of_lt_of_le hm (hmN τ0)
    have hρ : 0 < N / den := div_pos hNpos hdenpos
    have hHfu : Hf (φ, u) = (N / den) • wv - x τ0 := by rw [hHf, hwu]
    have hsum : x τ0 + Hf (φ, u) = (N / den) • wv := by rw [hHfu]; abel
    have hwproj : wv = proj H (x τ0 + Hf (φ, u)) := by
      rw [hsum, ktd_proj_smul hH hwv hρ]
    have hb1 : ‖wv - x τ0‖ ≤ LP * ‖Hf (φ, u)‖ := by
      have := hLP τ0 (Hf (φ, u)) hhsmall
      simp only at this
      rwa [← hwproj] at this
    refine ⟨⟨?_, ?_⟩, hwproj, hb1⟩
    · rw [hHfu, ← kta_liouvilleCLM_apply, map_sub, map_smul, kta_liouvilleCLM_apply,
        kta_liouvilleCLM_apply, ktd_liouville_self, ktd_liouville_anti, hwu]
      have : liouville (x φ + u) (x τ0) = 0 := by
        rw [← kta_liouvilleCLM_apply, ← hgG, hG_def]
      rw [this]; simp
    · rw [hHfu, map_sub, map_smul, hwu, smul_eq_mul, ← hden_def, ← hN_def]
      field_simp
      ring
  -- further Lipschitz constants
  obtain ⟨Lg, hLg0, hLg⟩ := exists_norm_le_mul_norm_of_periodic g T r hT hr
    (hgs.of_le (by simp)) (fun φ u _ => hgper φ u) hg0
  obtain ⟨LH, hLH0, hLH⟩ := exists_norm_le_mul_norm_of_periodic Hf T r' hT hr'pos
    (hHfs.of_le (by simp)) (fun φ u _ => hHfper φ u) hHf0
  -- the `φ`-partial of `g` vanishes along `u = 0`
  have hgdiff : ∀ q ∈ S, DifferentiableAt ℝ g q := fun q hq =>
    (hgs.contDiffAt (hSo.mem_nhds hq)).differentiableAt (by simp)
  have hgφs : ContDiffOn ℝ ∞ (fun q : ℝ × V n => fderiv ℝ g q (1, 0)) S :=
    (hgs.fderiv_of_isOpen hSo (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hgφper : ∀ φ (u : V n), fderiv ℝ g (φ + T, u) (1, 0) = fderiv ℝ g (φ, u) (1, 0) := by
    intro φ u
    have e : (fun q : ℝ × V n => g (q + (T, 0))) = g := by
      funext q; obtain ⟨a, b⟩ := q
      show g (a + T, b + 0) = g (a, b)
      rw [add_zero, hgper]
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := ((φ, u) : ℝ × V n))
      ((T, 0) : ℝ × V n)
    rw [e] at this
    rw [show ((φ + T, u) : ℝ × V n) = (φ, u) + (T, 0) by simp, ← this]
  have hgφ0 : ∀ φ : ℝ, fderiv ℝ g (φ, 0) (1, 0) = 0 := by
    intro φ
    have hmem : ((φ, (0 : V n)) : ℝ × V n) ∈ S := ⟨trivial, by simpa using hr⟩
    have hc : HasDerivAt (fun σ : ℝ => ((σ, (0 : V n)) : ℝ × V n)) ((1 : ℝ), (0 : V n)) φ :=
      (hasDerivAt_id' φ).prodMk (hasDerivAt_const φ (0 : V n))
    have h1 := (hgdiff _ hmem).hasFDerivAt.comp_hasDerivAt φ hc
    have h2 : HasDerivAt (fun σ : ℝ => g (σ, 0)) 0 φ := by
      have : (fun σ : ℝ => g (σ, 0)) = fun _ => 0 := funext hg0
      rw [this]; exact hasDerivAt_const φ 0
    exact h1.unique h2
  obtain ⟨Lφ, hLφ0, hLφ⟩ := exists_norm_le_mul_norm_of_periodic
    (fun q : ℝ × V n => fderiv ℝ g q (1, 0)) T r hT hr (hgφs.of_le (by simp))
    (fun φ u _ => hgφper φ u) hgφ0
  obtain ⟨C1, hC1⟩ := exists_bound_iteratedFDeriv_of_periodic g T r hT hr hgs
    (fun φ u _ => hgper φ u) 1
  -- radii
  set ρ := min (r' / 2) (min (δ / (4 * (Lg + 1))) (d / (2 * (LH + 1)))) with hρdef
  have hρpos : 0 < ρ := lt_min (by linarith) (lt_min (by positivity) (by positivity))
  have hρr' : ρ ≤ r' / 2 := min_le_left _ _
  have hρg : Lg * ρ ≤ δ / 4 := by
    have h1 : ρ ≤ δ / (4 * (Lg + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hρH : LH * ρ ≤ d / 2 := by
    have h1 : ρ ≤ d / (2 * (LH + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  obtain ⟨ηP, hηP, hPer⟩ :=
    exists_period_near_of_forall_shift_close hT hxs.continuous hxper (δ / 4) (by positivity)
  set κ := min (ρ / 3) (ηP / 4) with hκdef
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hκρ : 3 * κ ≤ ρ := by have := min_le_left (ρ / 3) (ηP / 4); linarith
  have hκP : 4 * κ ≤ ηP := by have := min_le_right (ρ / 3) (ηP / 4); linarith
  -- the deviation from a phase `c`
  obtain ⟨U, hU⟩ : ∃ U : ℝ → ℝ × ℝ → V n, ∀ c p, U c p = w p - x (ε * T * p.2 + c) :=
    ⟨_, fun _ _ => rfl⟩
  have hUfun : ∀ c, U c = fun p : ℝ × ℝ => w p - x (ε * T * p.2 + c) := fun c => funext (hU c)
  have hXs : ∀ c, ContDiff ℝ ∞ (fun p : ℝ × ℝ => x (ε * T * p.2 + c)) := fun c =>
    hxs.comp ((contDiff_const.mul contDiff_snd).add contDiff_const)
  have hUs : ∀ c, ContDiffOn ℝ ∞ (U c) (Set.Ioi s₀ ×ˢ Set.univ) := fun c => by
    rw [hUfun]; exact hwsm.sub (hXs c).contDiffOn
  have hO₀ : IsOpen (Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hwat : ∀ p : ℝ × ℝ, s₀ < p.1 → ContDiffAt ℝ ∞ w p := fun p hp =>
    hwsm.contDiffAt (hO₀.mem_nhds ⟨hp, trivial⟩)
  have hUeq : ∀ b c, (∀ y, x (y + b) = x (y + c)) → U b = U c := by
    intro b c hbc; rw [hUfun, hUfun]; funext p; rw [hbc]
  -- comparison of two phases
  have hcmp : ∀ b c : ℝ, (∀ t, ‖x (ε * T * t + b) - x (ε * T * t + c)‖ ≤ ηP) →
      ∃ b', (∀ y, x (y + b') = x (y + b)) ∧ |b' - c| < δ / 4 := by
    intro b c hbc
    obtain ⟨p, hp, hpb⟩ := hPer (b - c) (fun y => by
      have := hbc ((y - c) / (ε * T))
      have ht : ε * T * ((y - c) / (ε * T)) = y - c := by
        rw [mul_div_assoc']; exact mul_div_cancel_left₀ (y - c) hεT
      rwa [ht, show y - c + b = y + (b - c) by ring, show y - c + c = y by ring] at this)
    refine ⟨b - p, fun y => ?_, by rwa [show b - p - c = b - c - p by ring]⟩
    have := hp (y + b - p)
    rw [show y + b - p + p = y + b by ring] at this
    rw [show y + (b - p) = y + b - p by ring]
    exact this.symm
  -- fresh phases with `C¹`-closeness `κ`
  obtain ⟨sA, hsA⟩ := hw 1 κ hκ
  have hex : ∀ s : ℝ, ∃ c : ℝ, s ≥ sA → ∀ j ≤ 1, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (U c) (s, t)‖ ≤ κ := by
    intro s
    by_cases hs : s ≥ sA
    · obtain ⟨c, hc⟩ := hsA s hs
      exact ⟨c, fun _ => by rw [hUfun]; exact hc⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose a ha using hex
  set sD := max sA s₀ with hsD
  have hXd : ∀ c (p : ℝ × ℝ), HasFDerivAt (fun q : ℝ × ℝ => x (ε * T * q.2 + c))
      ((fderiv ℝ (fun y : ℝ => x (ε * T * y + c)) p.2).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    intro c p
    have hd : DifferentiableAt ℝ (fun y : ℝ => x (ε * T * y + c)) p.2 :=
      ((hxs.comp ((contDiff_const.mul contDiff_id).add contDiff_const)).differentiable
        (by simp)) _
    exact hd.hasFDerivAt.comp p hasFDerivAt_snd
  -- the `s`-derivative of `w` is small
  have hws : ∀ σ > sD, ∀ t : ℝ, ‖fderiv ℝ w (σ, t) (1, 0)‖ ≤ κ := by
    intro σ hσ t
    have hσA : σ ≥ sA := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hσ)
    have hσ0 : s₀ < σ := lt_of_le_of_lt (le_max_right _ _) hσ
    have h1 := ha σ hσA 1 le_rfl t
    rw [norm_iteratedFDeriv_one, hUfun] at h1
    have hwd := (hwat (σ, t) hσ0).differentiableAt (by simp)
    have hF := hwd.hasFDerivAt.sub (hXd (a σ) (σ, t))
    rw [show fderiv ℝ (fun p : ℝ × ℝ => w p - x (ε * T * p.2 + a σ)) (σ, t) = _ from
      hF.fderiv] at h1
    set Lw := fderiv ℝ w (σ, t) - (fderiv ℝ (fun y : ℝ => x (ε * T * y + a σ)) (σ, t).2).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ) with hLw
    have h3 : Lw ((1 : ℝ), (0 : ℝ)) = fderiv ℝ w (σ, t) (1, 0) := by simp [hLw]
    have key := Lw.le_opNorm ((1 : ℝ), (0 : ℝ))
    have hn : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
    rw [hn, mul_one, h3] at key
    linarith
  have hdrift : ∀ σ σ' : ℝ, σ > sD → σ' > sD → ∀ t : ℝ,
      ‖w (σ', t) - w (σ, t)‖ ≤ κ * |σ' - σ| := by
    intro σ σ' hσ hσ' t
    have hder : ∀ y ∈ Set.Ioi sD, HasDerivWithinAt (fun z : ℝ => w (z, t))
        (fderiv ℝ w (y, t) (1, 0)) (Set.Ioi sD) y := by
      intro y hy
      have hy0 : s₀ < y := lt_of_le_of_lt (le_max_right _ _) (show sD < y from hy)
      have hc : HasDerivAt (fun z : ℝ => ((z, t) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) y :=
        (hasDerivAt_id' y).prodMk (hasDerivAt_const y t)
      exact (((hwat (y, t) hy0).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt y
        hc).hasDerivWithinAt
    have := (convex_Ioi sD).norm_image_sub_le_of_norm_hasDerivWithin_le hder
      (fun y hy => hws y hy t) hσ hσ'
    rwa [Real.norm_eq_abs] at this
  -- windows `[S0 + k - 2, S0 + k + 2]`
  set S0 := sD + 2 with hS0
  have hSk : ∀ k : ℕ, S0 + k > sD := fun k => by
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  have hfr : ∀ k : ℕ, ∀ t, ‖U (a (S0 + k)) (S0 + k, t)‖ ≤ κ := by
    intro k t
    have := ha (S0 + k) (le_of_lt (lt_of_le_of_lt (le_max_left _ _) (hSk k))) 0 (Nat.zero_le _) t
    simpa [norm_iteratedFDeriv_zero] using this
  have hval : ∀ b c σ₀ κ' : ℝ, σ₀ > sD → (∀ t, ‖U b (σ₀, t)‖ ≤ κ') →
      (∀ y, x (y + c) = x (y + b)) → ∀ σ > sD, ∀ t, ‖U c (σ, t)‖ ≤ κ' + κ * |σ - σ₀| := by
    intro b c σ₀ κ' hσ₀ hb hcb σ hσ t
    rw [hUeq c b hcb]
    have e : U b (σ, t) = U b (σ₀, t) + (w (σ, t) - w (σ₀, t)) := by
      rw [hU, hU]; dsimp only; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (hb t) (hdrift σ₀ σ hσ₀ hσ t))
  have hq : ∀ k : ℕ, ∃ q : ℝ, (∀ y, x (y + q) = x y) ∧
      |a (S0 + ((k + 1 : ℕ) : ℝ)) - a (S0 + k) - q| < δ / 4 := by
    intro k
    set σ := S0 + ((k + 1 : ℕ) : ℝ) with hσ
    have hσ1 : σ - (S0 + k) = 1 := by rw [hσ]; push_cast; ring
    have h1 := hfr (k + 1)
    have h2 := hval (a (S0 + k)) (a (S0 + k)) (S0 + k) κ (hSk k) (hfr k) (fun y => rfl) σ
      (hSk (k + 1))
    obtain ⟨b', hb', hb'c⟩ := hcmp (a σ) (a (S0 + k)) (fun t => by
      have e : x (ε * T * t + a σ) - x (ε * T * t + a (S0 + k)) =
          U (a (S0 + k)) (σ, t) - U (a σ) (σ, t) := by
        rw [hU, hU]; dsimp only; abel
      rw [e]
      calc ‖U (a (S0 + k)) (σ, t) - U (a σ) (σ, t)‖
          ≤ ‖U (a (S0 + k)) (σ, t)‖ + ‖U (a σ) (σ, t)‖ := norm_sub_le _ _
        _ ≤ (κ + κ * |σ - (S0 + k)|) + κ := add_le_add (h2 t) (h1 t)
        _ ≤ ηP := by rw [hσ1, abs_one]; linarith)
    refine ⟨a σ - b', fun y => ?_, ?_⟩
    · have := hb' (y - b')
      rw [show y - b' + b' = y by ring] at this
      rw [show y + (a σ - b') = y - b' + a σ by ring, ← this]
    · rwa [show a σ - a (S0 + k) - (a σ - b') = b' - a (S0 + k) by ring]
  choose q hqper hqc using hq
  set c : ℕ → ℝ := fun k => a (S0 + k) - ∑ i ∈ Finset.range k, q i with hcdef
  have hsumper : ∀ k y, x (y + ∑ i ∈ Finset.range k, q i) = x y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [Finset.sum_range_succ, ← add_assoc, hqper, ih]
  have hcper : ∀ k y, x (y + c k) = x (y + a (S0 + k)) := by
    intro k y
    have := hsumper k (y + c k)
    have e : y + c k + ∑ i ∈ Finset.range k, q i = y + a (S0 + k) := by
      simp only [hcdef]; ring
    rw [e] at this
    exact this.symm
  have hcadj : ∀ k : ℕ, |c (k + 1) - c k| < δ / 4 := by
    intro k
    have e : c (k + 1) - c k = a (S0 + ((k + 1 : ℕ) : ℝ)) - a (S0 + k) - q k := by
      simp only [hcdef, Finset.sum_range_succ]; ring
    rw [e]; exact hqc k
  have hcwin : ∀ (k : ℕ) (σ : ℝ), σ > sD → |σ - (S0 + k)| ≤ 2 → ∀ t,
      ‖U (c k) (σ, t)‖ ≤ 3 * κ := by
    intro k σ hσ hσk t
    have := hval (a (S0 + k)) (c k) (S0 + k) κ (hSk k) (hfr k) (hcper k) σ hσ t
    nlinarith [abs_nonneg (σ - (S0 + k))]
  -- adjacent windows give the same coordinates
  have hagree : ∀ (b c' : ℝ) (p : ℝ × ℝ), ‖U b p‖ ≤ ρ → ‖U c' p‖ ≤ ρ → |b - c'| < δ / 2 →
      b + g (ε * T * p.2 + b, U b p) = c' + g (ε * T * p.2 + c', U c' p) ∧
      Hf (ε * T * p.2 + b, U b p) = Hf (ε * T * p.2 + c', U c' p) := by
    intro b c' p hb hc hbc
    have hbr : ‖U b p‖ < r := by linarith
    have hcr : ‖U c' p‖ < r := by linarith
    obtain ⟨-, hGb, -⟩ := hgroot (ε * T * p.2 + b) _ hbr
    obtain ⟨-, -, huniq⟩ := hgroot (ε * T * p.2 + c') _ hcr
    have hgb : |g (ε * T * p.2 + b, U b p)| ≤ δ / 4 := by
      have := hLg (ε * T * p.2 + b) (U b p) (by linarith)
      rw [Real.norm_eq_abs] at this
      calc |g (ε * T * p.2 + b, U b p)| ≤ Lg * ‖U b p‖ := this
        _ ≤ Lg * ρ := mul_le_mul_of_nonneg_left hb hLg0
        _ ≤ δ / 4 := hρg
    have hwb : x (ε * T * p.2 + b) + U b p = w p := by rw [hU]; abel
    have hwc : x (ε * T * p.2 + c') + U c' p = w p := by rw [hU]; abel
    rw [hG_def] at hGb
    simp only at hGb
    have key := huniq (b - c' + g (ε * T * p.2 + b, U b p))
      (by
        rw [abs_lt]
        have := abs_lt.1 hbc
        have := abs_le.1 hgb
        constructor <;> linarith)
      (by
        rw [hG_def]; simp only
        rw [hwc, show ε * T * p.2 + c' + (b - c' + g (ε * T * p.2 + b, U b p)) =
          ε * T * p.2 + b + g (ε * T * p.2 + b, U b p) by ring, ← hwb]
        exact hGb)
    have e : ε * T * p.2 + b + g (ε * T * p.2 + b, U b p) =
        ε * T * p.2 + c' + g (ε * T * p.2 + c', U c' p) := by linarith
    refine ⟨by linarith, ?_⟩
    rw [hHf, hHf]; simp only
    rw [e, hwb, hwc]
  set C : ℝ → ℝ := fun σ => c ⌊σ - S0⌋₊ with hCdef
  set Θ : ℝ × ℝ → ℝ := fun p => C p.1 + g (ε * T * p.2 + C p.1, U (C p.1) p) with hΘdef
  set hh : ℝ × ℝ → V n := fun p => Hf (ε * T * p.2 + C p.1, U (C p.1) p) with hhdef
  have hadj : ∀ j k : ℕ, j ≤ k + 1 → k ≤ j + 1 → |c j - c k| < δ / 2 := by
    intro j k h1 h2
    rcases (by omega : j = k ∨ j = k + 1 ∨ k = j + 1) with rfl | rfl | rfl
    · simp only [sub_self, abs_zero]; positivity
    · linarith [hcadj k]
    · rw [abs_sub_comm]; linarith [hcadj j]
  have hloc : ∀ σs : ℝ, σs > S0 → ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (σs - 1 / 2) (σs + 1 / 2) →
      Θ p = c ⌊σs - S0⌋₊ + g (ε * T * p.2 + c ⌊σs - S0⌋₊, U (c ⌊σs - S0⌋₊) p) ∧
      hh p = Hf (ε * T * p.2 + c ⌊σs - S0⌋₊, U (c ⌊σs - S0⌋₊) p) ∧
      ‖U (c ⌊σs - S0⌋₊) p‖ ≤ 3 * κ := by
    rintro σs hσs ⟨σ, t⟩ ⟨hp1, hp2⟩
    simp only at hp1 hp2
    set k := ⌊σs - S0⌋₊ with hk
    set j := ⌊σ - S0⌋₊ with hj
    obtain ⟨hk1, hk2⟩ := ktd_floor (show -1 < σs - S0 by linarith)
    obtain ⟨hj1, hj2⟩ := ktd_floor (show -1 < σ - S0 by linarith)
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ σs - S0)] at hk1
    have hm1 : max (σ - S0) 0 < σs - S0 + 1 / 2 := max_lt (by linarith) (by linarith)
    have hm2 : max (σ - S0) 0 ≤ σ - S0 + 1 / 2 := max_le (by linarith) (by linarith)
    have hjk : j ≤ k + 1 := by
      have : (j : ℝ) < ((k + 2 : ℕ) : ℝ) := by push_cast; linarith
      have := Nat.cast_lt.1 this
      omega
    have hkj : k ≤ j + 1 := by
      have : (k : ℝ) < ((j + 2 : ℕ) : ℝ) := by push_cast; linarith
      have := Nat.cast_lt.1 this
      omega
    have hσD : σ > sD := by linarith
    have hvj := hcwin j σ hσD (by rw [abs_le]; constructor <;> linarith) t
    have hvk := hcwin k σ hσD (by rw [abs_le]; constructor <;> linarith) t
    have hag := hagree (c j) (c k) (σ, t) (by linarith) (by linarith) (hadj j k hjk hkj)
    exact ⟨hag.1, hag.2, hvk⟩
  -- local smoothness
  set Ω : ℝ → Set (ℝ × ℝ) := fun σs => Set.Ioo (σs - 1 / 2) (σs + 1 / 2) ×ˢ Set.univ with hΩdef
  have hΩo : ∀ σs, IsOpen (Ω σs) := fun σs => isOpen_Ioo.prod isOpen_univ
  have hΩmem : ∀ σ t : ℝ, ((σ, t) : ℝ × ℝ) ∈ Ω σ := fun σ t =>
    ⟨⟨by linarith, by linarith⟩, trivial⟩
  have hΩsub : ∀ σs, σs > S0 → Ω σs ⊆ Set.Ioi s₀ ×ˢ Set.univ := by
    rintro σs hσs ⟨σ, t⟩ ⟨h1, -⟩
    refine ⟨?_, trivial⟩
    show s₀ < σ
    have := le_max_right sA s₀
    linarith [h1.1]
  have hΩD : ∀ σs, σs > S0 → ∀ q ∈ Ω σs, q.1 > sD := by
    rintro σs hσs ⟨σ, t⟩ ⟨h1, -⟩
    show sD < σ
    linarith [h1.1]
  have hlocU : ∀ σs, σs > S0 → ∀ q ∈ Ω σs, ‖U (c ⌊σs - S0⌋₊) q‖ ≤ 3 * κ :=
    fun σs hσs q hq => (hloc σs hσs q hq.1).2.2
  have hinner : ∀ σs, σs > S0 → ∀ b : ℝ,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => ((ε * T * q.2 + b, U b q) : ℝ × V n)) (Ω σs) :=
    fun σs hσs b => ((contDiff_const.mul contDiff_snd).add contDiff_const).contDiffOn.prodMk
      ((hUs b).mono (hΩsub σs hσs))
  have hgcomp : ∀ σs, σs > S0 → ∀ b : ℝ, (∀ q ∈ Ω σs, ‖U b q‖ ≤ 3 * κ) →
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => g (ε * T * q.2 + b, U b q)) (Ω σs) :=
    fun σs hσs b hb => hgs.comp (hinner σs hσs b)
      (fun q hq => ⟨trivial, mem_ball_zero_iff.2 (by linarith [hb q hq])⟩)
  have hHcomp : ∀ σs, σs > S0 → ∀ b : ℝ, (∀ q ∈ Ω σs, ‖U b q‖ ≤ 3 * κ) →
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => Hf (ε * T * q.2 + b, U b q)) (Ω σs) :=
    fun σs hσs b hb => hHfs.comp (hinner σs hσs b)
      (fun q hq => ⟨trivial, mem_ball_zero_iff.2 (by linarith [hb q hq])⟩)
  have hΘev : ∀ σ t : ℝ, σ > S0 → Θ =ᶠ[𝓝 (σ, t)] fun q =>
      c ⌊σ - S0⌋₊ + g (ε * T * q.2 + c ⌊σ - S0⌋₊, U (c ⌊σ - S0⌋₊) q) := fun σ t hσ =>
    Filter.eventually_of_mem ((hΩo σ).mem_nhds (hΩmem σ t)) (fun q hq => (hloc σ hσ q hq.1).1)
  have hhev : ∀ σ t : ℝ, σ > S0 → hh =ᶠ[𝓝 (σ, t)] fun q =>
      Hf (ε * T * q.2 + c ⌊σ - S0⌋₊, U (c ⌊σ - S0⌋₊) q) := fun σ t hσ =>
    Filter.eventually_of_mem ((hΩo σ).mem_nhds (hΩmem σ t)) (fun q hq => (hloc σ hσ q hq.1).2.1)
  have hgat : ∀ σ t : ℝ, σ > S0 → ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => g (ε * T * q.2 + c ⌊σ - S0⌋₊, U (c ⌊σ - S0⌋₊) q)) (σ, t) :=
    fun σ t hσ => (hgcomp σ hσ _ (hlocU σ hσ)).contDiffAt ((hΩo σ).mem_nhds (hΩmem σ t))
  have hHat : ∀ σ t : ℝ, σ > S0 → ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => Hf (ε * T * q.2 + c ⌊σ - S0⌋₊, U (c ⌊σ - S0⌋₊) q)) (σ, t) :=
    fun σ t hσ => (hHcomp σ hσ _ (hlocU σ hσ)).contDiffAt ((hΩo σ).mem_nhds (hΩmem σ t))
  have hΘs : ContDiffOn ℝ ∞ Θ (Set.Ioi S0 ×ˢ Set.univ) := by
    rintro ⟨σ, t⟩ ⟨hσ, -⟩
    exact ((contDiffAt_const.add (hgat σ t hσ)).congr_of_eventuallyEq
      (hΘev σ t hσ)).contDiffWithinAt
  have hhs : ContDiffOn ℝ ∞ hh (Set.Ioi S0 ×ˢ Set.univ) := by
    rintro ⟨σ, t⟩ ⟨hσ, -⟩
    exact ((hHat σ t hσ).congr_of_eventuallyEq (hhev σ t hσ)).contDiffWithinAt
  -- uniform derivative bounds
  set Xf : ℝ → ℝ × ℝ → V n := fun b q => x (ε * T * q.2 + b) with hXf
  have hUX : ∀ b, U b = w - Xf b := fun b => by rw [hUfun]; rfl
  have hXb : ∀ i : ℕ, ∃ M : ℝ, ∀ (b : ℝ) (p : ℝ × ℝ), ‖iteratedFDeriv ℝ i (Xf b) p‖ ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv_comp_periodic (fun q : ℝ × ℝ => x q.1) T 1
      (ε * T) hT one_pos ((hxs.comp contDiff_fst).contDiffOn) (fun φ v _ => hxper φ) i 0
    refine ⟨M, fun b p => ?_⟩
    have := hM b (fun _ => (0 : ℝ)) Set.univ p isOpen_univ trivial contDiffOn_const
      (fun _ _ => by simp) (fun j _ => by simp)
    simpa using this
  choose MX hMX using hXb
  have hUb : ∀ m : ℕ, ∃ Bu su : ℝ, ∀ (b : ℝ) (p : ℝ × ℝ), su ≤ p.1 → ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (U b) p‖ ≤ Bu := by
    intro m
    obtain ⟨sm, hsm⟩ := hw m 1 one_pos
    refine ⟨1 + 2 * ∑ i ∈ Finset.range (m + 1), |MX i|, max sm (s₀ + 1), ?_⟩
    rintro b ⟨σ, t⟩ hp i hi
    simp only at hp
    have hp0 : s₀ < σ := by linarith [le_max_right sm (s₀ + 1)]
    obtain ⟨c', hc'⟩ := hsm σ (le_trans (le_max_left _ _) hp)
    have h1 : ‖iteratedFDeriv ℝ i (U c') (σ, t)‖ ≤ 1 := by rw [hUfun]; exact hc' i hi t
    have hMi : |MX i| ≤ ∑ j ∈ Finset.range (m + 1), |MX j| :=
      Finset.single_le_sum (f := fun j => |MX j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have hwa : ContDiffAt ℝ i w (σ, t) := (hwat (σ, t) hp0).of_le (by exact_mod_cast le_top)
    have hXa : ∀ b', ContDiffAt ℝ i (Xf b') (σ, t) := fun b' =>
      ((hXs b').of_le (by exact_mod_cast le_top)).contDiffAt
    have e1 : iteratedFDeriv ℝ i (U b) (σ, t) =
        iteratedFDeriv ℝ i w (σ, t) - iteratedFDeriv ℝ i (Xf b) (σ, t) := by
      rw [hUX, iteratedFDeriv_sub_apply hwa (hXa b)]
    have e2 : iteratedFDeriv ℝ i (U c') (σ, t) =
        iteratedFDeriv ℝ i w (σ, t) - iteratedFDeriv ℝ i (Xf c') (σ, t) := by
      rw [hUX, iteratedFDeriv_sub_apply hwa (hXa c')]
    have hx1 := (hMX i b (σ, t)).trans (le_abs_self _)
    have hx2 := (hMX i c' (σ, t)).trans (le_abs_self _)
    calc ‖iteratedFDeriv ℝ i (U b) (σ, t)‖ = ‖iteratedFDeriv ℝ i (U c') (σ, t) +
          (iteratedFDeriv ℝ i (Xf c') (σ, t) - iteratedFDeriv ℝ i (Xf b) (σ, t))‖ := by
          rw [e1, e2]; congr 1; abel
      _ ≤ 1 + (|MX i| + |MX i|) :=
          (norm_add_le _ _).trans (add_le_add h1 ((norm_sub_le _ _).trans (add_le_add hx2 hx1)))
      _ ≤ 1 + 2 * ∑ j ∈ Finset.range (m + 1), |MX j| := by linarith
  have hΘbd : ∀ m : ℕ, ∃ B s' : ℝ, ∀ s ≥ s', ∀ t : ℝ,
      ‖iteratedFDeriv ℝ (m + 1) Θ (s, t)‖ ≤ B := by
    intro m
    obtain ⟨Bu, su, hBu⟩ := hUb (m + 1)
    obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv_comp_periodic g T r (ε * T) hT hr hgs
      (fun φ u _ => hgper φ u) (m + 1) Bu
    refine ⟨M, max su (S0 + 1), fun σ hσ t => ?_⟩
    have hσ' : σ > S0 := by linarith [le_max_right su (S0 + 1)]
    rw [((hΘev σ t hσ').iteratedFDeriv (𝕜 := ℝ) (m + 1)).eq_of_nhds]
    rw [show (fun q : ℝ × ℝ => c ⌊σ - S0⌋₊ +
        g (ε * T * q.2 + c ⌊σ - S0⌋₊, U (c ⌊σ - S0⌋₊) q)) =
        (fun _ => c ⌊σ - S0⌋₊) + (fun q : ℝ × ℝ =>
        g (ε * T * q.2 + c ⌊σ - S0⌋₊, U (c ⌊σ - S0⌋₊) q)) from rfl,
      iteratedFDeriv_add_apply contDiffAt_const
        ((hgat σ t hσ').of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m), Pi.zero_apply, zero_add]
    exact hM _ _ (Ω σ) (σ, t) (hΩo σ) (hΩmem σ t) ((hUs _).mono (hΩsub σ hσ'))
      (fun q hq => by linarith [hlocU σ hσ' q hq])
      (fun i hi => hBu _ (σ, t) (by simp only; linarith [le_max_left su (S0 + 1)]) i hi)
  have hhbd : ∀ m : ℕ, ∃ B s' : ℝ, ∀ s ≥ s', ∀ t : ℝ, ‖iteratedFDeriv ℝ m hh (s, t)‖ ≤ B := by
    intro m
    obtain ⟨Bu, su, hBu⟩ := hUb m
    obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv_comp_periodic Hf T r' (ε * T) hT hr'pos hHfs
      (fun φ u _ => hHfper φ u) m Bu
    refine ⟨M, max su (S0 + 1), fun σ hσ t => ?_⟩
    have hσ' : σ > S0 := by linarith [le_max_right su (S0 + 1)]
    rw [((hhev σ t hσ').iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
    exact hM _ _ (Ω σ) (σ, t) (hΩo σ) (hΩmem σ t) ((hUs _).mono (hΩsub σ hσ'))
      (fun q hq => by linarith [hlocU σ hσ' q hq])
      (fun i hi => hBu _ (σ, t) (by simp only; linarith [le_max_left su (S0 + 1)]) i hi)
  -- a fresh phase at `σ`, adjusted to the window phase
  have hfresh : ∀ η : ℝ, 0 < η → η ≤ κ → ∃ s' : ℝ, ∀ σ ≥ s', ∃ b : ℝ,
      (∀ t, ‖U b (σ, t)‖ ≤ η) ∧ (∀ t, ‖fderiv ℝ (U b) (σ, t)‖ ≤ η) ∧
      |b - c ⌊σ - S0⌋₊| < δ / 4 ∧ σ > S0 ∧ (∀ q ∈ Ω σ, ‖U b q‖ ≤ ρ) := by
    intro η hη hηκ
    obtain ⟨sη, hsη⟩ := hw 1 η hη
    refine ⟨max sη (S0 + 1), fun σ hσ => ?_⟩
    have hσS : σ > S0 := by linarith [le_max_right sη (S0 + 1)]
    obtain ⟨b0, hb0⟩ := hsη σ (le_trans (le_max_left _ _) hσ)
    have hU0 : ∀ t, ‖U b0 (σ, t)‖ ≤ η := fun t => by
      have := hb0 0 (Nat.zero_le _) t
      rw [norm_iteratedFDeriv_zero] at this
      rw [hU]; exact this
    have hU1 : ∀ t, ‖fderiv ℝ (U b0) (σ, t)‖ ≤ η := fun t => by
      have := hb0 1 le_rfl t
      rw [norm_iteratedFDeriv_one] at this
      rw [hUfun]; exact this
    obtain ⟨b', hb', hb'c⟩ := hcmp b0 (c ⌊σ - S0⌋₊) (fun t => by
      have e : x (ε * T * t + b0) - x (ε * T * t + c ⌊σ - S0⌋₊) =
          U (c ⌊σ - S0⌋₊) (σ, t) - U b0 (σ, t) := by
        rw [hU, hU]; dsimp only; abel
      rw [e]
      have := hlocU σ hσS (σ, t) (hΩmem σ t)
      calc ‖U (c ⌊σ - S0⌋₊) (σ, t) - U b0 (σ, t)‖
          ≤ ‖U (c ⌊σ - S0⌋₊) (σ, t)‖ + ‖U b0 (σ, t)‖ := norm_sub_le _ _
        _ ≤ 3 * κ + η := add_le_add this (hU0 t)
        _ ≤ ηP := by linarith)
    have hUb' : U b' = U b0 := hUeq b' b0 hb'
    refine ⟨b', fun t => by rw [hUb']; exact hU0 t, fun t => by rw [hUb']; exact hU1 t, hb'c,
      hσS, ?_⟩
    rintro ⟨σq, tq⟩ hq
    have hσq : σq > sD := hΩD σ hσS (σq, tq) hq
    have := hval b0 b' σ η (by linarith) hU0 hb' σq hσq tq
    have hd' : |σq - σ| ≤ 1 / 2 := by
      have h := hq.1
      simp only [Set.mem_Ioo] at h
      rw [abs_le]; constructor <;> linarith
    nlinarith
  -- `C⁰` smallness of `D θ` and of `h`
  have hagreeF : ∀ σ : ℝ, ∀ b : ℝ, σ > S0 → |b - c ⌊σ - S0⌋₊| < δ / 4 →
      (∀ q ∈ Ω σ, ‖U b q‖ ≤ ρ) → ∀ q ∈ Ω σ,
        Θ q = b + g (ε * T * q.2 + b, U b q) ∧ hh q = Hf (ε * T * q.2 + b, U b q) := by
    intro σ b hσ hbc hbΩ q hq
    have hl := hloc σ hσ q hq.1
    have hag := hagree b (c ⌊σ - S0⌋₊) q (hbΩ q hq) (by linarith [hl.2.2])
      (lt_of_lt_of_le hbc (by linarith))
    exact ⟨hl.1.trans hag.1.symm, hl.2.1.trans hag.2.symm⟩
  have hC1nn : 0 ≤ C1 := le_trans (norm_nonneg _) (hC1 0 0 (by simp; positivity))
  have hθ1 : TendstoZeroUnif (fderiv ℝ Θ) := by
    intro η hη
    have hD : 0 < T * Lφ + C1 + 1 := by positivity
    set η' := min κ (η / (T * Lφ + C1 + 1)) with hη'
    have hη'pos : 0 < η' := lt_min hκ (by positivity)
    have hη'η : (T * Lφ + C1) * η' ≤ η := by
      have h1 : η' ≤ η / (T * Lφ + C1 + 1) := min_le_right _ _
      rw [le_div_iff₀ hD] at h1
      nlinarith
    obtain ⟨s', hs'⟩ := hfresh η' hη'pos (min_le_left _ _)
    refine ⟨s', fun σ hσ t => ?_⟩
    obtain ⟨b, hb0, hb1, hbc, hσS, hbΩ⟩ := hs' σ hσ
    have hev : Θ =ᶠ[𝓝 (σ, t)] fun q => b + g (ε * T * q.2 + b, U b q) :=
      Filter.eventually_of_mem ((hΩo σ).mem_nhds (hΩmem σ t))
        (fun q hq => (hagreeF σ b hσS hbc hbΩ q hq).1)
    rw [hev.fderiv_eq, fderiv_const_add]
    have hUd : DifferentiableAt ℝ (U b) (σ, t) :=
      ((hUs b).contDiffAt (hO₀.mem_nhds (hΩsub σ hσS (hΩmem σ t)))).differentiableAt (by simp)
    have hbt := hb0 t
    have hη'κ : η' ≤ κ := min_le_left _ _
    have hy : ((ε * T * t + b, U b (σ, t)) : ℝ × V n) ∈ S :=
      ⟨trivial, mem_ball_zero_iff.2 (by linarith)⟩
    have hin : HasFDerivAt (fun q : ℝ × ℝ => ((ε * T * q.2 + b, U b q) : ℝ × V n))
        (((ε * T) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod (fderiv ℝ (U b) (σ, t))) (σ, t) :=
      ((hasFDerivAt_snd.const_mul (ε * T)).add_const b).prodMk hUd.hasFDerivAt
    have hcomp := (hgdiff _ hy).hasFDerivAt.comp (σ, t) hin
    rw [show (fun q : ℝ × ℝ => g (ε * T * q.2 + b, U b q)) =
      g ∘ (fun q : ℝ × ℝ => ((ε * T * q.2 + b, U b q) : ℝ × V n)) from rfl, hcomp.fderiv]
    set Lg' := fderiv ℝ g (ε * T * t + b, U b (σ, t)) with hLg'
    set DU := fderiv ℝ (U b) (σ, t) with hDU
    have hgφy : ‖Lg' (1, 0)‖ ≤ Lφ * η' :=
      (hLφ _ _ (by linarith)).trans (mul_le_mul_of_nonneg_left hbt hLφ0)
    have hLg1 : ‖Lg'‖ ≤ C1 := by
      have := hC1 (ε * T * t + b) (U b (σ, t)) (by linarith)
      rwa [norm_iteratedFDeriv_one] at this
    refine ContinuousLinearMap.opNorm_le_bound _ hη.le (fun e => ?_)
    have hsplit : (Lg'.comp (((ε * T) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod DU)) e =
        (ε * T * e.2) • Lg' (1, 0) + Lg' (0, DU e) := by
      rw [ContinuousLinearMap.comp_apply, ← map_smul, ← map_add]
      congr 1
      ext <;> simp
    rw [hsplit]
    have n1 : ‖(ε * T * e.2) • Lg' (1, 0)‖ ≤ T * ‖e‖ * (Lφ * η') := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, habsεT]
      have he2 : |e.2| ≤ ‖e‖ := by
        have := norm_snd_le e
        rwa [Real.norm_eq_abs] at this
      exact mul_le_mul (mul_le_mul_of_nonneg_left he2 hT.le) hgφy (norm_nonneg _)
        (by positivity)
    have n2 : ‖Lg' (0, DU e)‖ ≤ C1 * (η' * ‖e‖) := by
      calc ‖Lg' (0, DU e)‖ ≤ ‖Lg'‖ * ‖((0 : ℝ), DU e)‖ := Lg'.le_opNorm _
        _ ≤ C1 * (η' * ‖e‖) := by
          refine mul_le_mul hLg1 (norm_prod_le_iff.2 ⟨by simp; positivity, ?_⟩)
            (norm_nonneg _) hC1nn
          exact (DU.le_opNorm e).trans (mul_le_mul_of_nonneg_right (hb1 t) (norm_nonneg _))
    calc ‖(ε * T * e.2) • Lg' (1, 0) + Lg' (0, DU e)‖
        ≤ ‖(ε * T * e.2) • Lg' (1, 0)‖ + ‖Lg' (0, DU e)‖ := norm_add_le _ _
      _ ≤ T * ‖e‖ * (Lφ * η') + C1 * (η' * ‖e‖) := add_le_add n1 n2
      _ = ((T * Lφ + C1) * η') * ‖e‖ := by ring
      _ ≤ η * ‖e‖ := mul_le_mul_of_nonneg_right hη'η (norm_nonneg _)
  have hh0 : TendstoZeroUnif hh := by
    intro η hη
    have hD : 0 < LH + 1 := by positivity
    set η' := min κ (η / (LH + 1)) with hη'
    have hη'pos : 0 < η' := lt_min hκ (by positivity)
    have hη'η : LH * η' ≤ η := by
      have h1 : η' ≤ η / (LH + 1) := min_le_right _ _
      rw [le_div_iff₀ hD] at h1
      nlinarith
    obtain ⟨s', hs'⟩ := hfresh η' hη'pos (min_le_left _ _)
    refine ⟨s', fun σ hσ t => ?_⟩
    obtain ⟨b, hb0, -, hbc, hσS, hbΩ⟩ := hs' σ hσ
    rw [(hagreeF σ b hσS hbc hbΩ (σ, t) (hΩmem σ t)).2]
    have hbt := hb0 t
    have hη'κ : η' ≤ κ := min_le_left _ _
    exact (hLH _ _ (by linarith)).trans
      ((mul_le_mul_of_nonneg_left hbt hLH0).trans hη'η)
  -- assemble
  have hΘd : ContDiffOn ℝ ∞ (fderiv ℝ Θ) (Set.Ioi S0 ×ˢ Set.univ) :=
    hΘs.fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) (m := ∞) (by simp)
  have hΘC := tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd (fderiv ℝ Θ) S0 hΘd hθ1 (fun m => by
    obtain ⟨B, s', hB⟩ := hΘbd m
    exact ⟨B, s', fun s hs t => by rw [norm_iteratedFDeriv_fderiv]; exact hB s hs t⟩)
  have hhC := tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd hh S0 hhs hh0 hhbd
  have hτΘ : (fun p : ℝ × ℝ => (ε * T * p.2 + Θ p) - ε * T * p.2) = Θ := by
    funext p; ring
  refine ⟨fun p => ε * T * p.2 + Θ p, hh, S0 + 1, LP, ⟨S0, ?_⟩, ?_, hhC, ?_⟩
  · rw [hτΘ]; exact hΘs
  · intro m hm η hη
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨s', hs'⟩ := hΘC.2 m' η hη
    refine ⟨s', fun s hs t => ?_⟩
    rw [hτΘ, ← norm_iteratedFDeriv_fderiv]
    exact hs' s hs t
  intro σ hσ t
  have hσS : σ > S0 := by linarith
  have hσ0 : σ > s₀ := hΩsub σ hσS (hΩmem σ t) |>.1
  obtain ⟨hΘe, hhe, hUk⟩ := hloc σ hσS (σ, t) (hΩmem σ t).1
  obtain ⟨hΘe1, hhe1, -⟩ := hloc σ hσS (σ, t + 1) (hΩmem σ t).1
  have hu1 : U (c ⌊σ - S0⌋₊) (σ, t + 1) = U (c ⌊σ - S0⌋₊) (σ, t) := by
    rw [hU, hU]; dsimp only
    rw [hwper, show ε * T * (t + 1) + c ⌊σ - S0⌋₊ = ε * T * t + c ⌊σ - S0⌋₊ + ε * T by ring,
      hxperε]
  have hur' : ‖U (c ⌊σ - S0⌋₊) (σ, t)‖ < r' := by linarith
  have hHsmall : ‖Hf (ε * T * t + c ⌊σ - S0⌋₊, U (c ⌊σ - S0⌋₊) (σ, t))‖ ≤ d / 2 :=
    (hLH _ _ (by linarith)).trans
      ((mul_le_mul_of_nonneg_left (by linarith : ‖U (c ⌊σ - S0⌋₊) (σ, t)‖ ≤ ρ) hLH0).trans hρH)
  have hwu : w (σ, t) = x (ε * T * t + c ⌊σ - S0⌋₊) + U (c ⌊σ - S0⌋₊) (σ, t) := by
    rw [hU]; dsimp only; abel
  obtain ⟨hXi, hproj, hK⟩ := hpt _ _ (w (σ, t)) (hwS σ hσ0 t) hwu hur' hHsmall
  have hτe : ε * T * t + Θ (σ, t) = ε * T * t + c ⌊σ - S0⌋₊ +
      g (ε * T * t + c ⌊σ - S0⌋₊, U (c ⌊σ - S0⌋₊) (σ, t)) := by
    rw [hΘe]; ring
  dsimp only
  rw [hτe, hhe]
  refine ⟨?_, ?_, hXi, hproj, hK⟩
  · rw [hΘe1]; dsimp only
    rw [hu1, show ε * T * (t + 1) + c ⌊σ - S0⌋₊ = ε * T * t + c ⌊σ - S0⌋₊ + ε * T by ring,
      hgperε]
    ring
  · rw [hhe1]; dsimp only
    rw [hu1, show ε * T * (t + 1) + c ⌊σ - S0⌋₊ = ε * T * t + c ⌊σ - S0⌋₊ + ε * T by ring,
      hHfperε]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (w : ℝ × ℝ → V n) (s₀ : ℝ)
    (hwsm : ContDiffOn ℝ ∞ w (Set.Ioi s₀ ×ˢ Set.univ))
    (hwS : ∀ s > s₀, ∀ t : ℝ, H (w (s, t)) = 1)
    (hwper : ∀ s t : ℝ, w (s, t + 1) = w (s, t))
    (hw : ∀ m : ℕ, ∀ η > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => w p - P.x (ε * P.T * p.2 + c')) (s, t)‖ ≤ η) :
    ∃ (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₁ K : ℝ),
      (∃ s₂ : ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η) ∧
      TendstoZeroCInfty h ∧
      ∀ s ≥ s₁, ∀ t : ℝ,
        τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧ w (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) ∧
        ‖w (s, t) - P.x (τ (s, t))‖ ≤ K * ‖h (s, t)‖ :=
  exists_reebTube_coords_of_drift_aux H hH P ε hε w s₀ hwsm hwS hwper hw
