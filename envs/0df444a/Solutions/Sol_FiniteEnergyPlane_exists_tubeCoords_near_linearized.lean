-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tubeCoords_near_linearized
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T15:56:02.714601+00:00
-- url     : https://prove2.me/submissions/ed393703-0cf8-4415-a20d-a1659a191db5

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_exists_quadratic_remainder_near_compact
import Theorems.Thm_FiniteEnergyPlane_norm_sub_sub_linearized_le
import Theorems.Thm_FiniteEnergyPlane_exists_solution_norm_le_of_isSymLoop
import Theorems.Thm_FiniteEnergyPlane_hasDerivAt_unitaryFrame_apply_of_linearized
import Theorems.Thm_FiniteEnergyPlane_exists_tubeCoords_of_isUnitaryXiFrame

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

/-! Glue for `exists_tubeCoords_near_linearized` over its published children. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

lemma tcg_proj_smul {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V 1}
    (hy : H y = 1) {ρ : ℝ} (hρ : 0 < ρ) : proj H (ρ • y) = y := by
  have hy0 : y ≠ 0 := by
    intro h; have := hH.2.2 y hy; rw [h, map_zero] at this; exact lt_irrefl _ this
  have hne : ρ • y ≠ 0 := smul_ne_zero hρ.ne' hy0
  have hs : scaleToS H (ρ • y) = ρ⁻¹ :=
    kta_scale_unique H hH _ hne ρ⁻¹ (inv_pos.2 hρ)
      (by rw [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul, hy])
  unfold proj; rw [hs, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

lemma tcg_bdd {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {T : ℝ} (hT : 0 < T)
    (hf : Continuous f) (hper : Function.Periodic f T) : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hper.compact_of_continuous hT.ne' hf).isBounded.exists_norm_le
  exact ⟨max M 0, le_max_right _ _, fun t => (hM _ (mem_range_self t)).trans (le_max_left _ _)⟩

set_option maxHeartbeats 800000 in
theorem exists_tubeCoords_near_linearized_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, ∀ ε > 0, ∃ W : Set (V 1), IsOpen W ∧ Set.range P.x ⊆ W ∧
      ∀ y : ℝ → V 1, IsReebTrajectory H y → y 0 ∈ W →
        ∃ (τ₀ : ℝ) (a₀ : CauchyRiemannIndex.Vec 1) (τ : ℝ → ℝ)
          (a ζ : ℝ → CauchyRiemannIndex.Vec 1),
          ‖a₀‖ < ε ∧ (y 0 ∉ Set.range P.x → a₀ ≠ 0) ∧
          (∀ t : ℝ, HasDerivAt ζ
            (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * Sinf t) (ζ t)) t) ∧
          ζ (τ₀ / P.T) = a₀ ∧
          ContinuousOn τ (Set.Icc (-L) L) ∧ ContinuousOn a (Set.Icc (-L) L) ∧
          ∀ σ ∈ Set.Icc (-L) L,
            y σ = proj H (P.x (τ σ) + Z (τ σ / P.T) (a σ)) ∧
            |τ σ - τ₀ - σ| ≤ C * ‖a₀‖ ∧
            ‖a₀‖ ≤ C * ‖ζ ((τ₀ + σ) / P.T)‖ ∧ ‖ζ ((τ₀ + σ) / P.T)‖ ≤ C * ‖a₀‖ ∧
            ‖a σ - ζ ((τ₀ + σ) / P.T)‖ ≤ C * ‖a₀‖ ^ 2 := by
  classical
  have hT : 0 < P.T := P.T_pos
  have hxs : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  have hxc : Continuous P.x := hxs.continuous
  have hxS : ∀ τ, H (P.x τ) = 1 := P.mem
  have hKc : IsCompact (range P.x) :=
    (show Function.Periodic P.x P.T from P.periodic).compact_of_continuous hT.ne' hxc
  -- the Reeb field is `C²` near `S`
  have hO : IsOpen {z : V 1 | ContDiffAt ℝ 2 (reeb H) z} := isOpen_iff_mem_nhds.2 fun z hz =>
    (ContDiffAt.eventually (show ContDiffAt ℝ 2 (reeb H) z from hz) (by decide)).mono
      fun w hw => hw
  have hRO : ContDiffOn ℝ 2 (reeb H) {z : V 1 | ContDiffAt ℝ 2 (reeb H) z} := fun z hz =>
    (show ContDiffAt ℝ 2 (reeb H) z from hz).contDiffWithinAt
  have hKO : range P.x ⊆ {z : V 1 | ContDiffAt ℝ 2 (reeb H) z} := by
    rintro _ ⟨τ, rfl⟩
    exact (kta_reeb_contDiffAt H hH _ (hxS τ)).of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨δR, hδR, DR, hDR, hRb⟩ := exists_quadratic_remainder_near_compact hO hRO hKc hKO
  -- children
  obtain ⟨r, hr, K, hK0, δ, hδ, θ, A, ρ, hθc, hAc, hcoord, hinv, hlin, hLip⟩ :=
    exists_tubeCoords_of_isUnitaryXiFrame H hH J P Z hZ
  obtain ⟨Cζ, hCζ1, hsol, hCζ⟩ :=
    exists_solution_norm_le_of_isSymLoop Sinf hSym (L / P.T) (div_pos hL hT).le
  obtain ⟨MZ, hMZ0, hMZ⟩ := tcg_bdd one_pos hZ.1.continuous hZ.2.1
  obtain ⟨Mx, hMx0, hMx⟩ := tcg_bdd hT hxc P.periodic
  have hθ0 : ∀ φ, θ (φ, 0) = 0 := fun φ => by
    have := (hlin φ 0 (by simpa using hr)).1; simpa using this
  have hA0 : ∀ φ, A (φ, 0) = 0 := fun φ => by
    have := (hlin φ 0 (by simpa using hr)).2; simpa using this
  -- constants
  set E1 := Real.exp (DR * L) with hE1
  set E := Real.exp ((DR + 1) * L) with hE
  have hE10 : 0 < E1 := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  set CV := MZ * Cζ with hCV
  have hCV0 : 0 ≤ CV := mul_nonneg hMZ0 (by linarith)
  set CE := (K * (Mx + 1) + DR * CV ^ 2 * L) * E with hCE
  have hCE0 : 0 ≤ CE := by positivity
  set α₀ := min 1 (min (δR / (2 * (K * E1 + 1))) (min (δR / (CV + 1)) (min (r / (4 * (CV + 1)))
    (min (δ / (CE + 1)) (r / (4 * (CE + 1))))))) with hα₀
  have hα₀pos : 0 < α₀ := by
    simp only [hα₀, lt_min_iff]
    refine ⟨one_pos, ?_, ?_, ?_, ?_, ?_⟩ <;> positivity
  have hα₀1 : α₀ ≤ 1 := min_le_left _ _
  have hα₀a : α₀ ≤ δR / (2 * (K * E1 + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hα₀b : α₀ ≤ δR / (CV + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hα₀c : α₀ ≤ r / (4 * (CV + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hα₀d : α₀ ≤ δ / (CE + 1) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hα₀e : α₀ ≤ r / (4 * (CE + 1)) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨max (max 1 (K * CE)) Cζ, ?_⟩
  set C := max (max 1 (K * CE)) Cζ with hC
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCK : K * CE ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCζC : Cζ ≤ C := le_max_right _ _
  intro ε hε
  set δw := min (min (r / 2) δ) (min 1 (min ε α₀ / (K + 1))) with hδw
  have hδwpos : 0 < δw := by
    simp only [hδw, lt_min_iff]
    exact ⟨⟨by linarith, hδ⟩, one_pos, div_pos (lt_min hε hα₀pos) (by linarith)⟩
  have hδwr : δw ≤ r / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδwδ : δw ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hδw1 : δw ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδwK : δw ≤ min ε α₀ / (K + 1) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨thickening δw (range P.x), isOpen_thickening, self_subset_thickening hδwpos _, ?_⟩
  intro y hy hy0
  obtain ⟨_, ⟨φ₀, rfl⟩, hd0⟩ := mem_thickening_iff.1 hy0
  rw [dist_eq_norm] at hd0
  set u₀ := y 0 - P.x φ₀ with hu₀
  have hy0e : P.x φ₀ + u₀ = y 0 := by rw [hu₀]; abel
  have hu₀r : ‖u₀‖ < r := by linarith
  set τ₀ := φ₀ + θ (φ₀, u₀) with hτ₀
  set a₀ := A (φ₀, u₀) with ha₀
  set α := ‖a₀‖ with hα
  have hα0 : 0 ≤ α := norm_nonneg _
  obtain ⟨hρ₀pos, hρ₀eq⟩ := hcoord φ₀ u₀ hu₀r
  obtain ⟨hdα, hρ₀1⟩ := hinv φ₀ u₀ hu₀r (by rw [hy0e]; exact hy.1 0)
  rw [hy0e] at hρ₀eq hdα
  have ha₀u : α ≤ K * ‖u₀‖ := by
    have := (hLip φ₀ 0 u₀ (by simpa using hr) (by simpa using hd0.le.trans hδwδ)).2
    simpa [hA0] using this
  have hαε : α < min ε α₀ := by
    have h1 : ‖u₀‖ * (K + 1) < min ε α₀ :=
      (lt_div_iff₀ (by linarith : (0:ℝ) < K + 1)).1 (lt_of_lt_of_le hd0 hδwK)
    have h2 : K * ‖u₀‖ ≤ ‖u₀‖ * (K + 1) := by
      have : ‖u₀‖ * (K + 1) = K * ‖u₀‖ + ‖u₀‖ := by ring
      linarith [norm_nonneg u₀]
    linarith
  have hαα₀ : α ≤ α₀ := hαε.le.trans (min_le_right _ _)
  have hα1 : α ≤ 1 := hαα₀.trans hα₀1
  have hy0n : ‖y 0‖ ≤ Mx + 1 := by
    have h1 : ‖y 0‖ ≤ ‖P.x φ₀‖ + ‖u₀‖ := by rw [← hy0e]; exact norm_add_le _ _
    linarith [hMx φ₀]
  -- the linearized solution and its frame image
  obtain ⟨ζ, hζ, hζ0⟩ := hsol (τ₀ / P.T) a₀
  have hvd : ∀ σ, HasDerivAt (fun σ => Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T)))
      (fderiv ℝ (reeb H) (P.x (τ₀ + σ)) (Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T)))) σ :=
    fun σ => (hasDerivAt_unitaryFrame_apply_of_linearized H hH J P Z hZ Sinf hSym hA ζ hζ
      (τ₀ + σ)).comp_const_add τ₀ σ
  have hζb : ∀ σ ∈ Icc (-L) L, ‖ζ ((τ₀ + σ) / P.T)‖ ≤ Cζ * α ∧ α ≤ Cζ * ‖ζ ((τ₀ + σ) / P.T)‖ := by
    intro σ hσ
    have hs : |σ / P.T| ≤ L / P.T := by
      rw [abs_div, abs_of_pos hT]; exact div_le_div_of_nonneg_right (abs_le.2 ⟨hσ.1, hσ.2⟩) hT.le
    have h1 := hCζ ζ hζ (τ₀ / P.T) (σ / P.T) hs
    rwa [← add_div, hζ0] at h1
  have hvb : ∀ σ ∈ Icc (-L) L, ‖Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T))‖ ≤ CV * α := by
    intro σ hσ
    calc _ ≤ MZ * ‖ζ ((τ₀ + σ) / P.T)‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hMZ _)
      _ ≤ MZ * (Cζ * α) := by gcongr; exact (hζb σ hσ).1
      _ = CV * α := by rw [hCV]; ring
  -- comparison with the linearization
  have hCVα : CV * α ≤ δR := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < CV + 1)).1 (hαα₀.trans hα₀b)
    have e : α * (CV + 1) = CV * α + α := by ring
    linarith
  have hy0δ : ‖y 0 - P.x τ₀‖ * E1 < δR := by
    have h1 : α * (2 * (K * E1 + 1)) ≤ δR := (le_div_iff₀ (by positivity)).1 (hαα₀.trans hα₀a)
    have h2 : ‖y 0 - P.x τ₀‖ * E1 ≤ K * α * E1 := mul_le_mul_of_nonneg_right hdα hE10.le
    have e1 : K * α * E1 = α * (K * E1) := by ring
    have e2 : α * (2 * (K * E1 + 1)) = 2 * (α * (K * E1)) + 2 * α := by ring
    have h4 : 0 ≤ α * (K * E1) := mul_nonneg hα0 (mul_nonneg hK0 hE10.le)
    linarith
  have hcmp := norm_sub_sub_linearized_le (R := reeb H) (x := P.x) (y := y)
    (v := fun σ => Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T))) (c := τ₀) (M := CV * α) hDR hL.le
    (fun t z hz z' hz' => (hRb _ (mem_range_self t)).2.1 z hz z' hz')
    (fun t z hz => (hRb _ (mem_range_self t)).2.2 z hz) P.hasDerivAt hy.2 hvd hvb hCVα hy0δ
  have he0 : y 0 - P.x τ₀ - Z ((τ₀ + 0) / P.T) (ζ ((τ₀ + 0) / P.T)) = (1 - ρ (φ₀, u₀)) • y 0 := by
    rw [add_zero, hζ0, sub_smul, one_smul, hρ₀eq]; abel
  have he0b : ‖(1 - ρ (φ₀, u₀)) • y 0‖ ≤ K * (Mx + 1) * α ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
    calc |ρ (φ₀, u₀) - 1| * ‖y 0‖ ≤ K * α ^ 2 * (Mx + 1) :=
          mul_le_mul hρ₀1 hy0n (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hebound : ∀ σ ∈ Icc (-L) L,
      ‖y σ - P.x (τ₀ + σ) - Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T))‖ ≤ CE * α ^ 2 := by
    intro σ hσ
    refine ((hcmp σ hσ).2).trans ?_
    rw [he0]
    have h1 : ‖(1 - ρ (φ₀, u₀)) • y 0‖ + DR * (CV * α) ^ 2 * L ≤
        (K * (Mx + 1) + DR * CV ^ 2 * L) * α ^ 2 := by
      have : DR * (CV * α) ^ 2 * L = DR * CV ^ 2 * L * α ^ 2 := by ring
      have e : (K * (Mx + 1) + DR * CV ^ 2 * L) * α ^ 2 =
          K * (Mx + 1) * α ^ 2 + DR * CV ^ 2 * L * α ^ 2 := by ring
      rw [this, e]; linarith
    calc _ ≤ (K * (Mx + 1) + DR * CV ^ 2 * L) * α ^ 2 * E := mul_le_mul_of_nonneg_right h1 hE0.le
      _ = CE * α ^ 2 := by rw [hCE]; ring
  have hα2 : α ^ 2 ≤ α := pow_le_of_le_one hα0 hα1 (by norm_num)
  have hCEδ : CE * α ^ 2 ≤ δ := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < CE + 1)).1 (hαα₀.trans hα₀d)
    have h2 := mul_le_mul_of_nonneg_left hα2 hCE0
    have e : α * (CE + 1) = CE * α + α := by ring
    linarith
  have hCEr : CE * α ^ 2 ≤ r / 4 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 4 * (CE + 1))).1 (hαα₀.trans hα₀e)
    have h2 := mul_le_mul_of_nonneg_left hα2 hCE0
    have e : α * (4 * (CE + 1)) = 4 * (CE * α) + 4 * α := by ring
    linarith
  have hCVr : CV * α ≤ r / 4 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 4 * (CV + 1))).1 (hαα₀.trans hα₀c)
    have e : α * (4 * (CV + 1)) = 4 * (CV * α) + 4 * α := by ring
    linarith
  -- coordinates along the window
  set uσ : ℝ → V 1 := fun σ => y σ - P.x (τ₀ + σ) with huσ
  have huσr : ∀ σ ∈ Icc (-L) L, ‖uσ σ‖ < r := fun σ hσ => by
    have h1 := hvb σ hσ
    have h2 := hebound σ hσ
    have h3 : uσ σ = Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T)) +
        (y σ - P.x (τ₀ + σ) - Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T))) := by
      simp only [huσ]; abel
    rw [h3]
    have := norm_add_le (Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T)))
      (y σ - P.x (τ₀ + σ) - Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T)))
    linarith
  have hcoordσ : ∀ σ ∈ Icc (-L) L,
      |θ (τ₀ + σ, uσ σ)| ≤ K * (CE * α ^ 2) ∧
      ‖A (τ₀ + σ, uσ σ) - ζ ((τ₀ + σ) / P.T)‖ ≤ K * (CE * α ^ 2) := by
    intro σ hσ
    have hv : ‖Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T))‖ < r := by linarith [hvb σ hσ]
    obtain ⟨h0, h1⟩ := hlin (τ₀ + σ) _ hv
    have hdiff : uσ σ - Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T)) =
        y σ - P.x (τ₀ + σ) - Z ((τ₀ + σ) / P.T) (ζ ((τ₀ + σ) / P.T)) := by simp only [huσ]
    have he := hebound σ hσ
    obtain ⟨ha, hb⟩ := hLip (τ₀ + σ) _ (uσ σ) hv (by rw [hdiff]; exact he.trans hCEδ)
    rw [h0, sub_zero, hdiff] at ha
    rw [h1, hdiff] at hb
    exact ⟨ha.trans (mul_le_mul_of_nonneg_left he hK0), hb.trans (mul_le_mul_of_nonneg_left he hK0)⟩
  have hinner : ContinuousOn (fun σ => ((τ₀ + σ, uσ σ) : ℝ × V 1)) (Icc (-L) L) := by
    have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy.2 t).continuousAt
    exact ((continuous_const.add continuous_id).prodMk
      (hyc.sub (hxc.comp (continuous_const.add continuous_id)))).continuousOn
  have hmaps : MapsTo (fun σ => ((τ₀ + σ, uσ σ) : ℝ × V 1)) (Icc (-L) L)
      (univ ×ˢ ball (0 : V 1) r) := fun σ hσ =>
    ⟨mem_univ _, by rw [mem_ball_zero_iff]; exact huσr σ hσ⟩
  refine ⟨τ₀, a₀, fun σ => τ₀ + σ + θ (τ₀ + σ, uσ σ), fun σ => A (τ₀ + σ, uσ σ), ζ,
    lt_of_lt_of_le hαε (min_le_left _ _), ?_, hζ, hζ0, ?_, ?_, ?_⟩
  · intro hnot h0
    apply hnot
    have hx' : ρ (φ₀, u₀) • y 0 = P.x τ₀ := by rw [hρ₀eq, ← ha₀, h0, map_zero, add_zero]
    have hy0' : y 0 = (ρ (φ₀, u₀))⁻¹ • P.x τ₀ := by
      rw [← hx', smul_smul, inv_mul_cancel₀ hρ₀pos.ne', one_smul]
    have hne : P.x τ₀ ≠ 0 := by
      intro h; have := hH.2.2 _ (hxS τ₀); rw [h, map_zero] at this; exact lt_irrefl _ this
    have h1 := kta_scale_unique H hH _ hne _ (inv_pos.2 hρ₀pos) (by rw [← hy0']; exact hy.1 0)
    have h2 := kta_scale_unique H hH _ hne 1 one_pos (by rw [one_smul]; exact hxS τ₀)
    rw [hy0', ← h1, h2, one_smul]
    exact mem_range_self _
  · exact (continuousOn_const.add continuousOn_id).add (hθc.comp hinner hmaps)
  · exact hAc.comp hinner hmaps
  · intro σ hσ
    obtain ⟨hθb, hAb⟩ := hcoordσ σ hσ
    obtain ⟨hρpos, hρeq⟩ := hcoord (τ₀ + σ) (uσ σ) (huσr σ hσ)
    have hyu : P.x (τ₀ + σ) + uσ σ = y σ := by simp only [huσ]; abel
    rw [hyu] at hρeq
    have hKα : K * (CE * α ^ 2) ≤ C * α ^ 2 := by
      have := mul_le_mul_of_nonneg_right hCK (sq_nonneg α)
      linarith [show K * (CE * α ^ 2) = K * CE * α ^ 2 by ring]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hρeq, tcg_proj_smul hH (hy.1 σ) hρpos]
    · have e1 : τ₀ + σ + θ (τ₀ + σ, uσ σ) - τ₀ - σ = θ (τ₀ + σ, uσ σ) := by ring
      simp only
      rw [e1]
      have := mul_le_mul_of_nonneg_left hα2 (le_trans zero_le_one hC1)
      linarith
    · exact (hζb σ hσ).2.trans (mul_le_mul_of_nonneg_right hCζC (norm_nonneg _))
    · exact (hζb σ hσ).1.trans (mul_le_mul_of_nonneg_right hCζC hα0)
    · exact hAb.trans hKα

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, ∀ ε > 0, ∃ W : Set (V 1), IsOpen W ∧ Set.range P.x ⊆ W ∧
      ∀ y : ℝ → V 1, IsReebTrajectory H y → y 0 ∈ W →
        ∃ (τ₀ : ℝ) (a₀ : CauchyRiemannIndex.Vec 1) (τ : ℝ → ℝ)
          (a ζ : ℝ → CauchyRiemannIndex.Vec 1),
          ‖a₀‖ < ε ∧ (y 0 ∉ Set.range P.x → a₀ ≠ 0) ∧
          (∀ t : ℝ, HasDerivAt ζ
            (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * Sinf t) (ζ t)) t) ∧
          ζ (τ₀ / P.T) = a₀ ∧
          ContinuousOn τ (Set.Icc (-L) L) ∧ ContinuousOn a (Set.Icc (-L) L) ∧
          ∀ σ ∈ Set.Icc (-L) L,
            y σ = proj H (P.x (τ σ) + Z (τ σ / P.T) (a σ)) ∧
            |τ σ - τ₀ - σ| ≤ C * ‖a₀‖ ∧
            ‖a₀‖ ≤ C * ‖ζ ((τ₀ + σ) / P.T)‖ ∧ ‖ζ ((τ₀ + σ) / P.T)‖ ≤ C * ‖a₀‖ ∧
            ‖a σ - ζ ((τ₀ + σ) / P.T)‖ ≤ C * ‖a₀‖ ^ 2 :=
  exists_tubeCoords_near_linearized_aux H hH J hJ P Z hZ Sinf hSym hA L hL
