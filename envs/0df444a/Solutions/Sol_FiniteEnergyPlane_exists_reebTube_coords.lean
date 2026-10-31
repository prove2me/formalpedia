-- Prove2me | solution 1 for FiniteEnergyPlane.exists_reebTube_coords
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T09:42:49.676169+00:00
-- url     : https://prove2.me/submissions/c85d7853-e044-4c79-b296-d32172c51170

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_exists_smooth_periodic_root_family
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_mul_norm_of_periodic
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_comp_periodic

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
lemma kt_periodic_lb {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : Continuous f)
    (hper : Function.Periodic f T) (hpos : ∀ x, 0 < f x) : ∃ m > 0, ∀ x, m ≤ f x := by
  obtain ⟨x₀, -, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hT.le) hf.continuousOn
  refine ⟨f x₀, hpos x₀, fun x => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico₀ hT x
  rw [hfy]
  exact hmin (Set.Ico_subset_Icc_self hy)

lemma kt_liouville_self {n : ℕ} (y : V n) : liouville y y = 0 := by
  unfold liouville; rw [kta_om_self]; simp

lemma kt_liouville_anti {n : ℕ} (a b : V n) : liouville a b = -liouville b a := by
  unfold liouville; rw [kta_om_anti]; ring

lemma kt_ne_zero_of_mem {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : H y = 1) : y ≠ 0 := by
  intro h
  have := hH.2.2 y hy
  rw [h, map_zero] at this
  exact lt_irrefl _ this

lemma kt_proj_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : H y = 1) {ρ : ℝ} (hρ : 0 < ρ) : proj H (ρ • y) = y := by
  have hy0 := kt_ne_zero_of_mem hH hy
  have hne : ρ • y ≠ 0 := smul_ne_zero hρ.ne' hy0
  have hs : scaleToS H (ρ • y) = ρ⁻¹ :=
    kta_scale_unique H hH _ hne ρ⁻¹ (inv_pos.2 hρ) (by rw [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul, hy])
  unfold proj; rw [hs, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

theorem exists_reebTube_coords_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c : ℝ) (w : ℝ × ℝ → V n) (s₀ : ℝ)
    (hwS : ∀ s > s₀, ∀ t : ℝ, H (w (s, t)) = 1)
    (hwper : ∀ s t : ℝ, w (s, t + 1) = w (s, t))
    (hw : TendstoZeroCInfty (fun p : ℝ × ℝ => w p - P.x (ε * P.T * p.2 + c))) :
    ∃ (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₁ K : ℝ),
      TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) ∧ TendstoZeroCInfty h ∧
      ∀ s ≥ s₁, ∀ t : ℝ,
        τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧ w (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) ∧
        ‖w (s, t) - P.x (τ (s, t))‖ ≤ K * ‖h (s, t)‖ ∧
        ‖w (s, t) - P.x (ε * P.T * t + c)‖ ≤ K * (‖h (s, t)‖ + |τ (s, t) - ε * P.T * t - c|) := by
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
  have hx0 : ∀ τ, x τ ≠ 0 := fun τ => kt_ne_zero_of_mem hH (hxS τ)
  have hdH : ContDiff ℝ ∞ (fderiv ℝ H) := kta_dH_contDiff H hH.1
  -- the deviation `v = w - x(εTt + c)`
  obtain ⟨v, hv_def⟩ : ∃ v : ℝ × ℝ → V n, ∀ p, v p = w p - x (ε * T * p.2 + c) :=
    ⟨_, fun _ => rfl⟩
  have hv : TendstoZeroCInfty v := by
    have : v = fun p : ℝ × ℝ => w p - x (ε * T * p.2 + c) := funext hv_def
    rw [this]; exact hw
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
    exact kt_liouville_self _
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
  -- Lipschitz bound for the orbit along itself
  obtain ⟨LX, hLX0, hLX⟩ := exists_norm_le_mul_norm_of_periodic (E := ℝ)
    (fun q : ℝ × ℝ => x (q.1 + q.2) - x q.1) T 2 hT two_pos
    (((hxs.comp (contDiff_fst.add contDiff_snd)).sub (hxs.comp contDiff_fst)).contDiffOn.of_le
      (by simp))
    (fun φ u _ => by
      show x (φ + T + u) - x (φ + T) = x (φ + u) - x φ
      rw [show φ + T + u = (φ + u) + T by ring, hxper, hxper])
    (fun φ => by simp)
  -- positive lower bounds along the orbit
  have hNc : Continuous fun τ => fderiv ℝ H (x τ) (x τ) :=
    (hdH.continuous.comp hxs.continuous).clm_apply hxs.continuous
  obtain ⟨m, hm, hmN⟩ := kt_periodic_lb hT hNc
    (fun τ => by show fderiv ℝ H (x (τ + T)) (x (τ + T)) = _; rw [hxper])
    (fun τ => hH.2.2 _ (hxS τ))
  obtain ⟨d, hd, hdx⟩ := kt_periodic_lb hT (continuous_norm.comp hxs.continuous)
    (fun τ => by simp only [Function.comp_apply]; rw [hxper])
    (fun τ => norm_pos_iff.2 (hx0 τ))
  -- the denominator `dH(x τ)(w)` and its deviation from `dH(x τ)(x τ)`
  set S := (Set.univ : Set ℝ) ×ˢ ball (0 : V n) r with hS
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
      have := kt_proj_smul hH (hxS φ) one_pos
      rw [one_smul] at this; rw [this, sub_self])
  -- the two maps and their convergence
  have hτconv : TendstoZeroCInfty (fun p : ℝ × ℝ => g (ε * T * p.2 + c, v p)) :=
    tendstoZeroCInfty_comp_periodic g T r (ε * T) c hT hr hgs (fun φ u _ => hgper φ u) hg0 v hv
  have hhconv : TendstoZeroCInfty (fun p : ℝ × ℝ => Hf (ε * T * p.2 + c, v p)) :=
    tendstoZeroCInfty_comp_periodic Hf T r' (ε * T) c hT hr'pos hHfs
      (fun φ u _ => hHfper φ u) hHf0 v hv
  obtain ⟨sa, hsa⟩ := hv.2 0 (r' / 2) (by linarith)
  obtain ⟨sb, hsb⟩ := hhconv.2 0 (d / 2) (by linarith)
  refine ⟨fun p => ε * T * p.2 + c + g (ε * T * p.2 + c, v p),
    fun p => Hf (ε * T * p.2 + c, v p), max (max sa sb) (s₀ + 1), LP + LX, ?_, hhconv, ?_⟩
  · have : (fun p : ℝ × ℝ => ε * T * p.2 + c + g (ε * T * p.2 + c, v p) - ε * T * p.2 - c) =
        fun p => g (ε * T * p.2 + c, v p) := by funext p; ring
    rw [this]; exact hτconv
  intro s hs t
  simp only
  have hsa' : sa ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hsb' : sb ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs0 : s > s₀ := by have := le_trans (le_max_right _ _) hs; linarith
  set φ := ε * T * t + c with hφ
  set u := v (s, t) with hu_def
  have hu : ‖u‖ ≤ r' / 2 := by simpa [norm_iteratedFDeriv_zero] using hsa s hsa' t
  have hur : ‖u‖ < r := by linarith
  have hur' : ‖u‖ < r' := by linarith
  obtain ⟨hgδ, hgG, -⟩ := hgroot φ u hur
  have hwu : w (s, t) = x φ + u := by
    rw [hu_def, hv_def]; show _ = x φ + (w (s, t) - x φ); abel
  have hshift : ε * T * (t + 1) + c = φ + ε * T := by rw [hφ]; ring
  have hv1 : v (s, t + 1) = u := by
    rw [hu_def, hv_def, hv_def]; simp only
    rw [hwper, hshift, hxperε]
  set τ0 := φ + g (φ, u) with hτ0
  set den := fderiv ℝ H (x τ0) (x φ + u) with hden_def
  set N := fderiv ℝ H (x τ0) (x τ0) with hN_def
  have hdenpos : 0 < den := by have := hden φ u hur'; linarith
  have hNpos : 0 < N := lt_of_lt_of_le hm (hmN τ0)
  have hρ : 0 < N / den := div_pos hNpos hdenpos
  have hHfu : Hf (φ, u) = (N / den) • w (s, t) - x τ0 := by rw [hHf, hwu]
  have hsum : x τ0 + Hf (φ, u) = (N / den) • w (s, t) := by rw [hHfu]; abel
  have hwproj : w (s, t) = proj H (x τ0 + Hf (φ, u)) := by
    rw [hsum, kt_proj_smul hH (hwS s hs0 t) hρ]
  have hhsmall : ‖Hf (φ, u)‖ ≤ d / 2 := by
    simpa [norm_iteratedFDeriv_zero] using hsb s hsb' t
  have hb1 : ‖w (s, t) - x τ0‖ ≤ LP * ‖Hf (φ, u)‖ := by
    have := hLP τ0 (Hf (φ, u)) hhsmall
    simp only at this
    rwa [← hwproj] at this
  refine ⟨?_, ?_, ?_, hwproj, ?_, ?_⟩
  · rw [hshift, hv1, hgperε]; ring
  · rw [hshift, hv1, hHfperε]
  · constructor
    · rw [hHfu, ← kta_liouvilleCLM_apply, map_sub, map_smul, kta_liouvilleCLM_apply,
        kta_liouvilleCLM_apply, kt_liouville_self, kt_liouville_anti, hwu]
      have : liouville (x φ + u) (x τ0) = 0 := by
        rw [← kta_liouvilleCLM_apply, ← hgG, hG_def]
      rw [this]; simp
    · rw [hHfu, map_sub, map_smul, hwu, smul_eq_mul, ← hden_def, ← hN_def]
      field_simp
      ring
  · nlinarith [norm_nonneg (Hf (φ, u))]
  · have hb2 : ‖x τ0 - x φ‖ ≤ LX * |g (φ, u)| := by
      have := hLX φ (g (φ, u)) (by rw [Real.norm_eq_abs]; linarith)
      simpa [Real.norm_eq_abs, hτ0] using this
    have htri : ‖w (s, t) - x φ‖ ≤ ‖w (s, t) - x τ0‖ + ‖x τ0 - x φ‖ := by
      have := norm_add_le (w (s, t) - x τ0) (x τ0 - x φ)
      rwa [sub_add_sub_cancel] at this
    have heq : τ0 - ε * T * t - c = g (φ, u) := by rw [hτ0, hφ]; ring
    rw [heq]
    nlinarith [norm_nonneg (Hf (φ, u)), abs_nonneg (g (φ, u))]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c : ℝ) (w : ℝ × ℝ → V n) (s₀ : ℝ)
    (hwS : ∀ s > s₀, ∀ t : ℝ, H (w (s, t)) = 1)
    (hwper : ∀ s t : ℝ, w (s, t + 1) = w (s, t))
    (hw : TendstoZeroCInfty (fun p : ℝ × ℝ => w p - P.x (ε * P.T * p.2 + c))) :
    ∃ (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₁ K : ℝ),
      TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) ∧ TendstoZeroCInfty h ∧
      ∀ s ≥ s₁, ∀ t : ℝ,
        τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧ w (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) ∧
        ‖w (s, t) - P.x (τ (s, t))‖ ≤ K * ‖h (s, t)‖ ∧
        ‖w (s, t) - P.x (ε * P.T * t + c)‖ ≤ K * (‖h (s, t)‖ + |τ (s, t) - ε * P.T * t - c|) :=
  exists_reebTube_coords_aux H hH P ε hε c w s₀ hwS hwper hw
