-- Prove2me | solution 1 for FiniteEnergyPlane.exists_crEquation_tubeNormal_of_drift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T16:19:47.338708+00:00
-- url     : https://prove2.me/submissions/2ca0ed1f-25b2-4267-ba6b-a7f65c9c6aa2

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Theorems.Thm_FiniteEnergyPlane_isInXi_linearizedReeb_deriv
import Theorems.Thm_FiniteEnergyPlane_xiPart_dbar_endW_eq_zero
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_fderiv
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_prodMk
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_comp_periodic
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_comp_periodic_of_drift

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open FiniteEnergyPlane
open scoped ContDiff Topology in
open scoped ContDiff Topology

/-! Basic identities for the symplectization of a star-shaped level (copied, renamed, from the
`ka_*` helpers of accepted solution a386257a). -/


set_option linter.unusedSimpArgs false

def ka_sig {n : ℕ} (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

def ka_sgn {n : ℕ} (k : Fin (2 * (n + 1))) : ℝ := if (k : ℕ) % 2 = 0 then -1 else 1

theorem ka_sig_val {n : ℕ} (k : Fin (2 * (n + 1))) :
    ((ka_sig k : Fin (2 * (n + 1))) : ℕ) = if (k : ℕ) % 2 = 0 then (k : ℕ) + 1 else (k : ℕ) - 1 := by
  unfold ka_sig; split_ifs <;> rfl

theorem ka_sig_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sig (ka_sig k) = k := by
  ext
  rw [ka_sig_val, ka_sig_val]
  split_ifs <;> omega

theorem ka_sgn_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn (ka_sig k) = - ka_sgn k := by
  unfold ka_sgn
  rw [ka_sig_val]
  split_ifs <;> (try norm_num) <;> omega

theorem ka_sgn_sq {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn k * ka_sgn k = 1 := by
  unfold ka_sgn; split_ifs <;> norm_num

def ka_sigE (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) :=
  Function.Involutive.toPerm ka_sig ka_sig_sig

theorem ka_sigE_apply {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sigE n k = ka_sig k := rfl

theorem ka_j0_apply {n : ℕ} (v : V n) (k : Fin (2 * (n + 1))) :
    j0 v k = ka_sgn k * v (ka_sig k) := by
  unfold j0 ka_sgn ka_sig
  split_ifs <;> simp

theorem ka_j0_j0 {n : ℕ} (v : V n) : j0 (j0 v) = -v := by
  funext k
  rw [ka_j0_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  simp only [Pi.neg_apply]
  have := ka_sgn_sq k
  linear_combination (-(v k)) * this

theorem ka_j0_smul {n : ℕ} (a : ℝ) (v : V n) : j0 (a • v) = a • j0 v := by
  funext k; simp only [ka_j0_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem ka_j0_add {n : ℕ} (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [ka_j0_apply, Pi.add_apply]; ring

theorem ka_j0_sub {n : ℕ} (u v : V n) : j0 (u - v) = j0 u - j0 v := by
  funext k; simp only [ka_j0_apply, Pi.sub_apply]; ring

theorem ka_dot_comm {n : ℕ} (u v : V n) : dot u v = dot v u := by
  unfold dot; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_dot_smul_right {n : ℕ} (a : ℝ) (u v : V n) : dot u (a • v) = a * dot u v := by
  unfold dot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_smul_left {n : ℕ} (a : ℝ) (u v : V n) : dot (a • u) v = a * dot u v := by
  rw [ka_dot_comm, ka_dot_smul_right, ka_dot_comm]

theorem ka_dot_add_right {n : ℕ} (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_add_left {n : ℕ} (u v w : V n) : dot (v + w) u = dot v u + dot w u := by
  rw [ka_dot_comm, ka_dot_add_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_sub_right {n : ℕ} (u v w : V n) : dot u (v - w) = dot u v - dot u w := by
  unfold dot; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_sub_left {n : ℕ} (u v w : V n) : dot (v - w) u = dot v u - dot w u := by
  rw [ka_dot_comm, ka_dot_sub_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_neg_right {n : ℕ} (u v : V n) : dot u (-v) = - dot u v := by
  unfold dot; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp)

theorem ka_dot_neg_left {n : ℕ} (u v : V n) : dot (-u) v = - dot u v := by
  rw [ka_dot_comm, ka_dot_neg_right, ka_dot_comm]

theorem ka_dot_j0_left {n : ℕ} (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (ka_sigE n)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [ka_sigE_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  ring

theorem ka_dot_j0_j0 {n : ℕ} (u v : V n) : dot (j0 u) (j0 v) = dot u v := by
  rw [ka_dot_j0_left, ka_j0_j0, ka_dot_neg_right, neg_neg]

theorem ka_dot_self_j0 {n : ℕ} (u : V n) : dot u (j0 u) = 0 := by
  have := ka_dot_j0_left u u
  rw [ka_dot_comm] at this
  linarith

theorem ka_clm_apply {n : ℕ} (L : V n →L[ℝ] ℝ) (v : V n) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (v k) : V n) = v k • Pi.single k 1 by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul]

theorem ka_fderiv_eq_dot {n : ℕ} (H : V n → ℝ) (x v : V n) :
    fderiv ℝ H x v = dot (grad H x) v := by
  rw [ka_clm_apply]; unfold dot grad
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_liouville_ham {n : ℕ} (H : V n → ℝ) (x : V n) :
    liouville x (hamVF H x) = fderiv ℝ H x x / 2 := by
  unfold liouville omega0 hamVF
  rw [ka_dot_j0_j0, ka_fderiv_eq_dot, ka_dot_comm]

theorem ka_reeb_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  have hpos : 0 < liouville x (hamVF H x) := by
    rw [ka_liouville_ham]; have := hH.2.2 x hx; linarith
  refine ⟨hpos, ?_, ?_, ?_⟩
  · unfold reeb
    have : liouville x ((liouville x (hamVF H x))⁻¹ • hamVF H x) =
        (liouville x (hamVF H x))⁻¹ * liouville x (hamVF H x) := by
      unfold liouville omega0; rw [ka_dot_smul_right]; ring
    rw [this, inv_mul_cancel₀ hpos.ne']
  · unfold reeb hamVF
    rw [map_smul, ka_fderiv_eq_dot, ka_dot_self_j0, smul_zero]
  · intro w hw
    unfold reeb hamVF omega0
    rw [ka_j0_smul, ka_j0_j0, ka_dot_smul_left, ka_dot_neg_left,
      ← ka_fderiv_eq_dot, hw]; ring

theorem ka_om_add_left {n : ℕ} (u v w : V n) : omega0 (u + v) w = omega0 u w + omega0 v w := by
  unfold omega0; rw [ka_j0_add, ka_dot_add_left]
theorem ka_om_add_right {n : ℕ} (u v w : V n) : omega0 w (u + v) = omega0 w u + omega0 w v := by
  unfold omega0; rw [ka_dot_add_right]
theorem ka_om_sub_left {n : ℕ} (u v w : V n) : omega0 (u - v) w = omega0 u w - omega0 v w := by
  unfold omega0; rw [ka_j0_sub, ka_dot_sub_left]
theorem ka_om_sub_right {n : ℕ} (u v w : V n) : omega0 w (u - v) = omega0 w u - omega0 w v := by
  unfold omega0; rw [ka_dot_sub_right]
theorem ka_om_smul_left {n : ℕ} (a : ℝ) (u w : V n) : omega0 (a • u) w = a * omega0 u w := by
  unfold omega0; rw [ka_j0_smul, ka_dot_smul_left]
theorem ka_om_smul_right {n : ℕ} (a : ℝ) (u w : V n) : omega0 w (a • u) = a * omega0 w u := by
  unfold omega0; rw [ka_dot_smul_right]
theorem ka_om_anti {n : ℕ} (u v : V n) : omega0 u v = - omega0 v u := by
  unfold omega0; rw [ka_dot_j0_left, ka_dot_comm]
theorem ka_om_self {n : ℕ} (u : V n) : omega0 u u = 0 := by
  have := ka_om_anti u u; linarith

theorem ka_liouvilleCLM_apply {n : ℕ} (x v : V n) : liouvilleCLM x v = liouville x v := by
  unfold liouvilleCLM liouville omega0 dot
  simp [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem ka_scale_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem ka_scale_unique {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (t : ℝ) (ht : 0 < t) (hHt : H (t • y) = 1) : scaleToS H y = t := by
  obtain ⟨r, _, hu⟩ := hH.2.1 y hy
  have h1 := hu t ⟨ht, hHt⟩
  have h2 := hu (scaleToS H y) (ka_scale_spec H hH y hy)
  rw [h1, h2]

theorem ka_scale_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y₀ : V n)
    (hy₀ : y₀ ≠ 0) : ContDiffAt ℝ ∞ (scaleToS H) y₀ := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y₀ hy₀
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
    exact (ka_scale_unique H hH y h3 (ψ y) h2 h1').symm
  exact hψc.congr_of_eventuallyEq hev.symm


theorem ka_j0_contDiff {n : ℕ} : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 (fun k => ?_)
  have : (fun v : V n => j0 v k) = fun v => ka_sgn k * v (ka_sig k) := by
    funext v; exact ka_j0_apply v k
  rw [this]
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (ka_sig k))

theorem ka_dH_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)

theorem ka_grad_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (grad H) := by
  refine contDiff_pi.2 (fun k => ?_)
  exact (ka_dH_contDiff H hH).clm_apply contDiff_const

theorem ka_hamVF_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamVF H) := ka_j0_contDiff.comp (ka_grad_contDiff H hH)

theorem ka_liouvilleCLM_contDiff {n : ℕ} : ContDiff ℝ ∞ (liouvilleCLM : V n → V n →L[ℝ] ℝ) := by
  unfold liouvilleCLM
  refine ContDiff.const_smul _ (ContDiff.sum (fun k _ => ?_))
  exact ((contDiff_apply ℝ ℝ k).comp ka_j0_contDiff).smul contDiff_const

theorem ka_reeb_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContDiffAt ℝ ∞ (reeb H) x := by
  have hpos := (ka_reeb_spec H hH x hx).1
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [ka_liouvilleCLM_apply]
  have hc : ContDiff ℝ ∞ (fun x => liouville x (hamVF H x)) := by
    rw [hL]; exact ka_liouvilleCLM_contDiff.clm_apply (ka_hamVF_contDiff H hH.1)
  unfold reeb
  exact (hc.contDiffAt.inv hpos.ne').smul (ka_hamVF_contDiff H hH.1).contDiffAt

theorem ka_scale_hasFDerivAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) :
    HasFDerivAt (scaleToS H)
      ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)) y := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hy
  have hd : DifferentiableAt ℝ (scaleToS H) y :=
    (ka_scale_contDiffAt H hH y hy).differentiableAt (by simp)
  set r := scaleToS H y
  set x := proj H y
  have hxr : x = r • y := rfl
  set L := fderiv ℝ (scaleToS H) y
  have hm : HasFDerivAt (fun y' => scaleToS H y' • y') (r • ContinuousLinearMap.id ℝ (V n) +
      L.smulRight y) y := hd.hasFDerivAt.smul (hasFDerivAt_id y)
  have hHd : HasFDerivAt H (fderiv ℝ H x) x :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg := hHd.comp y hm
  have hev : (H ∘ fun y' => scaleToS H y' • y') =ᶠ[𝓝 y] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hy] with y' hy'
    exact (ka_scale_spec H hH y' hy').2
  have h0 := hg.fderiv
  rw [hev.fderiv_eq, fderiv_fun_const] at h0
  have hD : 0 < fderiv ℝ H x x := hH.2.2 x hHx
  have hL : ∀ v, L v = -(r ^ 2 / fderiv ℝ H x x) * fderiv ℝ H x v := by
    intro v
    have := congrArg (fun T => T v) h0
    simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      smul_eq_mul] at this
    have hxy : fderiv ℝ H x y = fderiv ℝ H x x / r := by
      rw [hxr, map_smul, smul_eq_mul]; field_simp
    rw [hxy] at this
    field_simp
    field_simp at this
    linarith
  have : L = (-(r ^ 2 / fderiv ℝ H x x)) • fderiv ℝ H x := by
    ext1 v; rw [hL v]; rfl
  rw [← this]; exact hd.hasFDerivAt

theorem ka_hol_abstract {n : ℕ} (A B : V n) (P : V n → Prop) (J' : V n →L[ℝ] V n)
    (α β : V n →L[ℝ] ℝ)
    (hW : ∀ v, P (v - α v • A - β v • B)) (hJP : ∀ w, P w → P (J' w))
    (hαA : α A = 1) (hαB : α B = 0) (hβA : β A = 0) (hβB : β B = 1)
    (hαP : ∀ w, P w → α w = 0) (hβP : ∀ w, P w → β w = 0)
    (hB : ∀ w, P w → omega0 B w = 0) (us ut : V n)
    (hhol : us + (α ut • B - β ut • A + J' (ut - α ut • A - β ut • B)) = 0) :
    α us = β ut ∧ α ut = - β us ∧
      omega0 (us - α us • A) (ut - α ut • A) =
        omega0 (ut - α ut • A - β ut • B) (J' (ut - α ut • A - β ut • B)) ∧
      (β us = 0 → β ut = 0 → ut - α ut • A - β ut • B = 0 → us = 0 ∧ ut = 0) := by
  set w := ut - α ut • A - β ut • B with hwdef
  have hPw : P w := hW ut
  have hPJw := hJP _ hPw
  have hs : us = -(α ut • B - β ut • A + J' w) := eq_neg_of_add_eq_zero_left hhol
  have e1 : α us = β ut := by
    rw [hs, map_neg, map_add, hαP _ hPJw]
    simp only [map_sub, map_smul, hαA, hαB, smul_eq_mul]; ring
  have e2 : β us = - α ut := by
    rw [hs, map_neg, map_add, hβP _ hPJw]
    simp only [map_sub, map_smul, hβA, hβB, smul_eq_mul]; ring
  have hus : us - α us • A = β us • B - J' w := by
    rw [e1, e2]; rw [hs]; module
  have hut : ut - α ut • A = β ut • B + w := by rw [hwdef]; module
  have hBB : omega0 B B = 0 := ka_om_self B
  have hJwB : omega0 (J' w) B = 0 := by rw [ka_om_anti, hB _ hPJw, neg_zero]
  refine ⟨e1, by linarith, ?_, ?_⟩
  · rw [hus, hut]
    simp only [ka_om_add_right, ka_om_sub_left, ka_om_smul_left, ka_om_smul_right,
      hBB, hB _ hPw, hJwB]
    rw [ka_om_anti (J' w) w]; ring
  · intro h1 h2 h3
    have hw0 : w = 0 := h3
    have hα : α ut = 0 := by linarith
    have hJ0 : J' w = 0 := by rw [hw0, map_zero]
    constructor
    · rw [hs, hJ0, h2, hα]; simp
    · have : ut = α ut • A + β ut • B + w := by rw [hwdef]; module
      rw [this, hα, h2, hw0]; simp

theorem ka_clm_complex_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) (h1 : L 1 = 0) (hI : L Complex.I = 0) : L = 0 := by
  ext1 z
  have : z = z.re • (1:ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [this, map_add, map_smul, map_smul, h1, hI]; simp

theorem ka_cr {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
    dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  set y := u z with hydef
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hz
  set r := scaleToS H y with hrdef
  set x := proj H y with hxdef
  have hxr : x = r • y := rfl
  have hx : x ∈ energySurface H := hHx
  have hyx : y = r⁻¹ • x := by rw [hxr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨hc, hR1, hRH, hRw⟩ := ka_reeb_spec H hH x hx
  set R := reeb H x
  set D := fderiv ℝ H x x
  have hD : 0 < D := hH.2.2 x hx
  set α : V n →L[ℝ] ℝ := (r / (2 * D)) • fderiv ℝ H x with hαdef
  set β : V n →L[ℝ] ℝ := r • liouvilleCLM x with hβdef
  set A : V n := (2:ℝ) • y
  set B : V n := r⁻¹ • R
  have hLA : liouvilleCLM x A = 0 := by
    simp only [A, hyx, ka_liouvilleCLM_apply]
    unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring
  -- derivatives
  have hS' := ka_scale_hasFDerivAt H hH y hz
  have ha' : HasFDerivAt (aCoord H) α y := by
    have h1 := (hS'.log hr.ne').const_mul (-1/2 : ℝ)
    have : (fun y => (-1/2 : ℝ) * Real.log (scaleToS H y)) = aCoord H := by
      funext y; unfold aCoord; ring
    rw [this] at h1
    have heq : α = ((-1 / 2 : ℝ) • (scaleToS H y)⁻¹ • -(scaleToS H y ^ 2 /
        (fderiv ℝ H (proj H y)) (proj H y)) • fderiv ℝ H (proj H y)) := by
      ext1 v
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ← hrdef, ← hxdef]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      field_simp
      exact mul_comm _ _
    rw [heq]; exact h1
  have hp' : HasFDerivAt (proj H) (r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A)) y := by
    have h1 := hS'.smul (hasFDerivAt_id y)
    have heq : r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A) =
        scaleToS H y • ContinuousLinearMap.id ℝ (V n) +
        ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)).smulRight y := by
      ext1 v
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul, ← hrdef, ← hxdef, smul_sub, smul_smul]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      rw [sub_eq_add_neg, ← neg_smul]
      congr 2
      field_simp
      ring
    rw [heq]; exact h1
  set us := fderiv ℝ u z 1
  set ut := fderiv ℝ u z Complex.I
  have hdsa : ds (fun z => aCoord H (u z)) z = α us := by
    unfold ds; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdta : dt (fun z => aCoord H (u z)) z = α ut := by
    unfold dt; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdsw : ds (fun z => proj H (u z)) z = r • (us - α us • A) := by
    unfold ds; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdtw : dt (fun z => proj H (u z)) z = r • (ut - α ut • A) := by
    unfold dt; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hWgen : ∀ v, IsInXi H x (v - α v • A - β v • B) := by
    intro v
    simp only [hαdef, hβdef, ContinuousLinearMap.smul_apply, ka_liouvilleCLM_apply, smul_eq_mul]
    constructor
    · unfold liouville
      rw [ka_om_sub_right, ka_om_sub_right]
      simp only [A, B, hyx, ka_om_smul_right]
      have h1 : omega0 x x = 0 := ka_om_self x
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h1, h2]; field_simp; ring
    · simp only [A, B, map_sub, map_smul, smul_eq_mul, hRH, hyx]
      field_simp; ring
  have key := ka_hol_abstract A B (IsInXi H x) (J x) α β hWgen
    (fun w hw => (hJ.2 x hx w w hw hw).1)
    (by
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hyx]
      field_simp
      rfl)
    (by simp only [hαdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hRH]; ring)
    (by
      simp only [hβdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hyx]
      unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring)
    (by
      simp only [hβdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply]
      unfold liouville; simp only [ka_om_smul_right]
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h2]; field_simp)
    (fun w hw => by
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, hw.2]; ring)
    (fun w hw => by
      simp only [hβdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hw.1]; ring)
    (fun w hw => by simp only [B]; rw [ka_om_smul_left, hRw w hw.2]; ring)
    us ut hhol
  obtain ⟨e1, e2, e3, e4⟩ := key
  set W := ut - α ut • A - β ut • B
  have hPW : IsInXi H x W := hWgen ut
  have hm : 0 ≤ omega0 W (J x W) := by
    by_cases h0 : W = 0
    · rw [h0, map_zero, ka_om_self]
    · exact ((hJ.2 x hx W W hPW hPW).2.2.1 h0).le
  have hLs : liouville x (r • (us - α us • A)) = β us := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  have hLt : liouville x (r • (ut - α ut • A)) = β ut := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  refine ⟨?_, ?_⟩
  · rw [hdsa, hdtw, hLt, e1]
  · rw [hdta, hdsw, hLs, e2]



namespace KAo
open FiniteEnergyPlane
variable {n : ℕ}

/-- `j0` as a continuous linear map. -/
noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := ka_j0_add, map_smul' := ka_j0_smul }

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def omegaL : V n →L[ℝ] V n →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k)

theorem omegaL_apply (u v : V n) : omegaL u v = omega0 u v := by
  simp [omegaL, omega0, dot, ContinuousLinearMap.sum_apply, j0L]

end KAo

namespace FiniteEnergyPlane.N1
open FiniteEnergyPlane CauchyRiemannIndex

variable {n : ℕ}

/-- Matrices acting on `ℝ²ⁿ` as continuous linear maps. -/
noncomputable abbrev mE (A : Mat n) : Vec n →L[ℝ] Vec n :=
  Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A

lemma mE_apply (A : Mat n) (v : Vec n) : mE A v = Matrix.toEuclideanLin A v := rfl

lemma mE_JJ (v : Vec n) : mE (J₀ n) (mE (J₀ n) v) = -v := by
  have : mE (J₀ n * J₀ n) v = mE (J₀ n) (mE (J₀ n) v) := by simp [mE, map_mul]
  rw [← this, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _]
  simp [mE, map_neg, map_one]

lemma mE_symm_apply (L : Vec n →L[ℝ] Vec n) :
    mE ((Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)).symm L) = L := by
  simp [mE]

/-- The basis vector `eᵢ`. -/
noncomputable abbrev eb (i : Fin n ⊕ Fin n) : Vec n := EuclideanSpace.single i (1 : ℝ)

/-- A left inverse of a frame map: `v ↦ Σᵢ ω₀(Z(-J₀ eᵢ), v) eᵢ`. -/
noncomputable def Kinv (Zt : Vec n →L[ℝ] V n) : V n →L[ℝ] Vec n :=
  ∑ i, (KAo.omegaL (Zt (-(mE (J₀ n) (eb i))))).smulRight (eb i)

lemma sum_inner_single (b : Vec n) : ∑ i, (inner ℝ (eb i) b) • eb i = b := by
  have := (EuclideanSpace.basisFun (Fin n ⊕ Fin n) ℝ).sum_repr' b
  simpa [eb] using this

lemma Kinv_left (Zt : Vec n →L[ℝ] V n)
    (hω : ∀ a b, omega0 (Zt a) (Zt b) = inner ℝ (Matrix.toEuclideanLin (J₀ n) a) b)
    (b : Vec n) : Kinv Zt (Zt b) = b := by
  simp only [Kinv, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, KAo.omegaL_apply, hω]
  conv_rhs => rw [← sum_inner_single b]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← mE_apply, map_neg, mE_JJ, neg_neg]

lemma Kinv_contDiff : ContDiff ℝ ∞ (Kinv : (Vec n →L[ℝ] V n) → V n →L[ℝ] Vec n) := by
  unfold Kinv
  refine ContDiff.sum (fun i _ => ?_)
  have h1 : ContDiff ℝ ∞ (fun Zt : Vec n →L[ℝ] V n => KAo.omegaL (Zt (-(mE (J₀ n) (eb i))))) :=
    KAo.omegaL.contDiff.comp (contDiff_id.clm_apply contDiff_const)
  exact h1.smulRight contDiff_const

/-- The projection onto `ξ_w` along `w` and `R(w)`. -/
noncomputable def Pr (H : V n → ℝ) (w : V n) : V n →L[ℝ] V n :=
  ContinuousLinearMap.id ℝ (V n) - ((fderiv ℝ H w w)⁻¹ • fderiv ℝ H w).smulRight w -
    (liouvilleCLM w).smulRight (reeb H w)

lemma Pr_apply (H : V n → ℝ) (w v : V n) :
    Pr H w v = v - (fderiv ℝ H w v / fderiv ℝ H w w) • w - liouville w v • reeb H w := by
  simp [Pr, ka_liouvilleCLM_apply, div_eq_inv_mul]

lemma Pr_self (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (w : V n)
    (hw : w ∈ energySurface H) : Pr H w w = 0 := by
  have hD : 0 < fderiv ℝ H w w := hH.2.2 w hw
  rw [Pr_apply, div_self hD.ne', one_smul]
  unfold liouville; rw [ka_om_self]; simp

lemma Pr_reeb (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (w : V n)
    (hw : w ∈ energySurface H) : Pr H w (reeb H w) = 0 := by
  obtain ⟨_, h1, h2, _⟩ := ka_reeb_spec H hH w hw
  rw [Pr_apply, h1, h2]; simp

lemma Pr_xi (H : V n → ℝ) (w v : V n) (hv : IsInXi H w v) : Pr H w v = v := by
  rw [Pr_apply, hv.1, hv.2]; simp

lemma Pr_contDiffAt (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (w : V n)
    (hw : w ∈ energySurface H) : ContDiffAt ℝ ∞ (Pr H) w := by
  have hD : 0 < fderiv ℝ H w w := hH.2.2 w hw
  have hdH := ka_dH_contDiff H hH.1
  have h1 : ContDiffAt ℝ ∞ (fun w => fderiv ℝ H w w) w :=
    (hdH.clm_apply contDiff_id).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun w => (fderiv ℝ H w w)⁻¹) w := h1.inv hD.ne'
  have h3 : ContDiffAt ℝ ∞ (fun w => ((fderiv ℝ H w w)⁻¹ • fderiv ℝ H w).smulRight w) w :=
    (h2.smul hdH.contDiffAt).smulRight contDiffAt_id
  have h4 : ContDiffAt ℝ ∞ (fun w => (liouvilleCLM w).smulRight (reeb H w)) w :=
    ka_liouvilleCLM_contDiff.contDiffAt.smulRight (ka_reeb_contDiffAt H hH w hw)
  exact (contDiffAt_const.sub h3).sub h4

lemma proj_mem (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) :
    proj H y ∈ energySurface H := (ka_scale_spec H hH y hy).2

lemma proj_contDiffAt (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : y ≠ 0) : ContDiffAt ℝ ∞ (proj H) y :=
  (ka_scale_contDiffAt H hH y hy).smul contDiffAt_id

lemma proj_of_mem (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : x ∈ energySurface H) : proj H x = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx; simp at this
  have : scaleToS H x = 1 := ka_scale_unique H hH x hx0 1 one_pos (by rw [one_smul]; exact hx)
  simp [proj, this]

/-- `Dproj(x) v = v - (dH(x) v / dH(x) x) x` at `x ∈ S`. -/
lemma proj_hasFDerivAt_mem (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : x ∈ energySurface H) :
    HasFDerivAt (proj H) (ContinuousLinearMap.id ℝ (V n) -
      ((fderiv ℝ H x x)⁻¹ • fderiv ℝ H x).smulRight x) x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx; simp at this
  have hs := ka_scale_hasFDerivAt H hH x hx0
  have h1 : scaleToS H x = 1 := ka_scale_unique H hH x hx0 1 one_pos (by rw [one_smul]; exact hx)
  have hp : proj H x = x := proj_of_mem H hH hx
  rw [hp, h1] at hs
  have h := hs.smul (hasFDerivAt_id x)
  rw [h1] at h
  have hD : fderiv ℝ H x x ≠ 0 := (hH.2.2 x hx).ne'
  have heq : ContinuousLinearMap.id ℝ (V n) - ((fderiv ℝ H x x)⁻¹ • fderiv ℝ H x).smulRight x =
      (1 : ℝ) • ContinuousLinearMap.id ℝ (V n) +
        ((-((1 : ℝ) ^ 2 / fderiv ℝ H x x)) • fderiv ℝ H x).smulRight x := by
    ext1 v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, one_smul, smul_eq_mul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    field_simp
  rw [heq]; exact h

end FiniteEnergyPlane.N1

namespace FiniteEnergyPlane.N1
open FiniteEnergyPlane CauchyRiemannIndex

variable {n : ℕ}

/-- Parameters `(σ, Dτ, Dζ)`. -/
abbrev Q (n : ℕ) := ℝ × (ℝ × ℝ →L[ℝ] ℝ) × (ℝ × ℝ →L[ℝ] Vec n)

section
variable (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (P : ReebOrbit H)
  (Z : ℝ → Vec n →L[ℝ] V n)

/-- The tube map `(σ, a) ↦ proj(x(σ) + Z(σ/T) a)`. -/
noncomputable def Psi (σ : ℝ) (a : Vec n) : V n := proj H (P.x σ + Z (σ / P.T) a)

/-- The vector `Y(e) = Dτ(e) (R(x σ) + T⁻¹ Z'(σ/T) a) + Z(σ/T) (Dζ e)`. -/
noncomputable def Yv (q : Q n) (a : Vec n) (e : ℝ × ℝ) : V n :=
  q.2.1 e • (reeb H (P.x q.1) + (1 / P.T) • deriv Z (q.1 / P.T) a) + Z (q.1 / P.T) (q.2.2 e)

/-- The nonlinear remainder of the frame equation. -/
noncomputable def Gf (q : Q n) (a : Vec n) : Vec n :=
  Kinv (Z (q.1 / P.T)) (Pr H (Psi H P Z q.1 a) (Yv H P Z q a (1, 0)) +
    J (Psi H P Z q.1 a) (Pr H (Psi H P Z q.1 a) (Yv H P Z q a (0, 1)))) -
    (q.2.2 (1, 0) + mE (J₀ n) (q.2.2 (0, 1)))

end

lemma Tdiv {T σ : ℝ} (hT : 0 < T) : T * (σ / T) = σ := by field_simp

lemma frame_xi {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) (σ : ℝ) (b : Vec n) :
    IsInXi H (P.x σ) (Z (σ / P.T) b) := by
  have := ((hZ.2.2 (σ / P.T)).1 b); rwa [Tdiv P.T_pos] at this

lemma frame_J {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) (σ : ℝ) (b : Vec n) :
    J (P.x σ) (Z (σ / P.T) b) = Z (σ / P.T) (mE (J₀ n) b) := by
  have := ((hZ.2.2 (σ / P.T)).2.2.1 b); rwa [Tdiv P.T_pos] at this

lemma frame_K {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) (t : ℝ) (b : Vec n) :
    Kinv (Z t) (Z t b) = b := Kinv_left _ (hZ.2.2 t).2.2.2 b

lemma Psi_zero {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (Z : ℝ → Vec n →L[ℝ] V n) (σ : ℝ) : Psi H P Z σ 0 = P.x σ := by
  simp only [Psi, map_zero, add_zero]; exact proj_of_mem H hH (P.mem σ)

lemma Gf_zero {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V n → V n →L[ℝ] V n}
    {P : ReebOrbit H} {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) (q : Q n) :
    Gf H J P Z q 0 = 0 := by
  have hY : ∀ e, Pr H (P.x q.1) (Yv H P Z q 0 e) = Z (q.1 / P.T) (q.2.2 e) := by
    intro e
    simp only [Yv, map_zero, smul_zero, add_zero, map_add, map_smul,
      Pr_reeb H hH _ (P.mem q.1), Pr_xi H _ _ (frame_xi hZ q.1 _), zero_add]
  simp only [Gf, Psi_zero hH, hY, frame_J hZ, ← map_add, frame_K hZ, sub_self]

/-- `0 ∉ S`. -/
lemma exists_ball_avoid {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) :
    ∃ m > 0, ∀ x ∈ energySurface H, m ≤ ‖x‖ := by
  have h0 : H 0 ≠ 1 := by
    intro h; have := hH.2.2 0 h; simp at this
  have hc : ContinuousAt H 0 := hH.1.continuous.continuousAt
  obtain ⟨m, hm, hball⟩ := Metric.isOpen_iff.1 (isOpen_ne_fun hH.1.continuous continuous_const) 0 h0
  refine ⟨m, hm, fun x hx => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hball (by simpa using hlt) hx

lemma exists_r {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V n → V n →L[ℝ] V n}
    (P : ReebOrbit H) {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) :
    ∃ r > 0, ∀ σ : ℝ, ∀ a : Vec n, ‖a‖ < r → P.x σ + Z (σ / P.T) a ≠ 0 := by
  obtain ⟨m, hm, hmS⟩ := exists_ball_avoid hH
  obtain ⟨B, hB⟩ := (hZ.2.1.isBounded_of_continuous one_ne_zero hZ.1.continuous).exists_norm_le
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ ⟨0, rfl⟩)
  refine ⟨m / (B + 1), div_pos hm (by linarith), fun σ a ha h => ?_⟩
  have h1 : ‖Z (σ / P.T) a‖ ≤ B * ‖a‖ :=
    ((Z (σ / P.T)).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (hB _ ⟨_, rfl⟩) (norm_nonneg _))
  have h2 : P.x σ = -(Z (σ / P.T) a) := eq_neg_of_add_eq_zero_left h
  have h3 := hmS _ (P.mem σ)
  rw [h2, norm_neg] at h3
  have : B * ‖a‖ < m := by
    calc B * ‖a‖ ≤ (B + 1) * ‖a‖ := by nlinarith [norm_nonneg a]
      _ < (B + 1) * (m / (B + 1)) := by
          exact mul_lt_mul_of_pos_left ha (by linarith)
      _ = m := by field_simp
  linarith

lemma Gf_contDiffOn {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {J : V n → V n →L[ℝ] V n} (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    {Z : ℝ → Vec n →L[ℝ] V n} (hZc : ContDiff ℝ ∞ Z) {r : ℝ}
    (hr : ∀ σ : ℝ, ∀ a : Vec n, ‖a‖ < r → P.x σ + Z (σ / P.T) a ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : Q n × Vec n => Gf H J P Z p.1 p.2) {p | ‖p.2‖ < r} := by
  refine fun p hp => ContDiffAt.contDiffWithinAt ?_
  have hx : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  have hσ : ContDiff ℝ ∞ (fun p : Q n × Vec n => p.1.1) := contDiff_fst.fst
  have hσT : ContDiff ℝ ∞ (fun p : Q n × Vec n => p.1.1 / P.T) := hσ.div_const _
  have hZp : ContDiff ℝ ∞ (fun p : Q n × Vec n => Z (p.1.1 / P.T)) := hZc.comp hσT
  have hZd : ContDiff ℝ ∞ (fun p : Q n × Vec n => deriv Z (p.1.1 / P.T)) :=
    (contDiff_infty_iff_deriv.1 hZc).2.comp hσT
  have hy : ContDiff ℝ ∞ (fun p : Q n × Vec n => P.x p.1.1 + Z (p.1.1 / P.T) p.2) :=
    (hx.comp hσ).add (hZp.clm_apply contDiff_snd)
  have hy0 : P.x p.1.1 + Z (p.1.1 / P.T) p.2 ≠ 0 := hr _ _ hp
  have hw : ContDiffAt ℝ ∞ (fun p : Q n × Vec n => Psi H P Z p.1.1 p.2) p :=
    (proj_contDiffAt H hH hy0).comp p hy.contDiffAt
  have hwS : Psi H P Z p.1.1 p.2 ∈ energySurface H := proj_mem H hH hy0
  have hPr : ContDiffAt ℝ ∞ (fun p : Q n × Vec n => Pr H (Psi H P Z p.1.1 p.2)) p :=
    ContDiffAt.comp (g := Pr H) p (Pr_contDiffAt H hH _ hwS) hw
  have hJw : ContDiffAt ℝ ∞ (fun p : Q n × Vec n => J (Psi H P Z p.1.1 p.2)) p :=
    ContDiffAt.comp (g := J) p hJ.1.contDiffAt hw
  have hR : ContDiff ℝ ∞ (fun p : Q n × Vec n => reeb H (P.x p.1.1)) := by
    refine contDiff_iff_contDiffAt.2 (fun p => ?_)
    exact (ka_reeb_contDiffAt H hH _ (P.mem _)).comp p (hx.comp hσ).contDiffAt
  have hY : ∀ e : ℝ × ℝ, ContDiff ℝ ∞ (fun p : Q n × Vec n => Yv H P Z p.1 p.2 e) := by
    intro e
    have h1 : ContDiff ℝ ∞ (fun p : Q n × Vec n => p.1.2.1 e) :=
      contDiff_fst.snd.fst.clm_apply contDiff_const
    have h2 : ContDiff ℝ ∞ (fun p : Q n × Vec n => p.1.2.2 e) :=
      contDiff_fst.snd.snd.clm_apply contDiff_const
    exact (h1.smul (hR.add ((hZd.clm_apply contDiff_snd).const_smul _))).add
      (hZp.clm_apply h2)
  have hK : ContDiff ℝ ∞ (fun p : Q n × Vec n => Kinv (Z (p.1.1 / P.T))) :=
    Kinv_contDiff.comp hZp
  have hlast : ContDiff ℝ ∞ (fun p : Q n × Vec n =>
      p.1.2.2 (1, 0) + mE (J₀ n) (p.1.2.2 (0, 1))) :=
    (contDiff_fst.snd.snd.clm_apply contDiff_const).add
      (contDiff_const.clm_apply (contDiff_fst.snd.snd.clm_apply contDiff_const))
  exact (hK.contDiffAt.clm_apply ((hPr.clm_apply (hY _).contDiffAt).add
    (hJw.clm_apply (hPr.clm_apply (hY _).contDiffAt)))).sub hlast.contDiffAt

end FiniteEnergyPlane.N1

namespace FiniteEnergyPlane.N1
open FiniteEnergyPlane CauchyRiemannIndex

variable {n : ℕ}

lemma Gf_snd {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (P : ReebOrbit H) (Z : ℝ → Vec n →L[ℝ] V n) (c σ : ℝ) (a : Vec n)
    (hy : P.x σ + Z (σ / P.T) a ≠ 0) :
    Gf H J P Z (σ, c • ContinuousLinearMap.snd ℝ ℝ ℝ, 0) a =
      c • Kinv (Z (σ / P.T)) (J (Psi H P Z σ a) (Pr H (Psi H P Z σ a)
        (reeb H (P.x σ) + (1 / P.T) • deriv Z (σ / P.T) a - reeb H (Psi H P Z σ a)))) := by
  have hwS : Psi H P Z σ a ∈ energySurface H := proj_mem H hH hy
  simp only [Gf, Yv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.zero_apply, map_zero, add_zero, smul_eq_mul, mul_zero, zero_smul,
    mul_one, map_sub, Pr_reeb H hH _ hwS, sub_zero, map_smul, zero_add]

lemma hasFDerivAt_Psi {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H} {Z : ℝ → Vec n →L[ℝ] V n}
    (hZ : IsUnitaryXiFrame J P Z) (σ : ℝ) :
    HasFDerivAt (fun a => Psi H P Z σ a) (Z (σ / P.T)) 0 := by
  have h1 : HasFDerivAt (fun a : Vec n => P.x σ + Z (σ / P.T) a) (Z (σ / P.T)) 0 :=
    (Z (σ / P.T)).hasFDerivAt.const_add _
  have h2 := proj_hasFDerivAt_mem H hH (P.mem σ)
  have h0 : (fun a : Vec n => P.x σ + Z (σ / P.T) a) 0 = P.x σ := by simp
  rw [← h0] at h2
  have h3 := h2.comp (0 : Vec n) h1
  rw [h0] at h3
  have heq : (ContinuousLinearMap.id ℝ (V n) - ((fderiv ℝ H (P.x σ) (P.x σ))⁻¹ •
      fderiv ℝ H (P.x σ)).smulRight (P.x σ)).comp (Z (σ / P.T)) = Z (σ / P.T) := by
    ext1 b
    simp [(frame_xi hZ σ b).2]
  rw [heq] at h3
  exact h3

theorem hasFDerivAt_Gf_snd {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {J : V n → V n →L[ℝ] V n} (hJ : IsCompatibleXiStructure H J) {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) {r : ℝ} (hr0 : 0 < r)
    (hr : ∀ σ : ℝ, ∀ a : Vec n, ‖a‖ < r → P.x σ + Z (σ / P.T) a ≠ 0) (c σ : ℝ) :
    HasFDerivAt (fun a => Gf H J P Z (σ, c • ContinuousLinearMap.snd ℝ ℝ ℝ, 0) a)
      (c • (Kinv (Z (σ / P.T))).comp ((J (P.x σ)).comp ((Pr H (P.x σ)).comp
        ((1 / P.T) • deriv Z (σ / P.T) - (fderiv ℝ (reeb H) (P.x σ)).comp (Z (σ / P.T))))))
      0 := by
  set w : Vec n → V n := fun a => Psi H P Z σ a with hwdef
  have hw := hasFDerivAt_Psi hH hZ σ
  have hw0 : w 0 = P.x σ := Psi_zero hH P Z σ
  have hy0 : P.x σ + Z (σ / P.T) 0 ≠ 0 := hr σ 0 (by simpa using hr0)
  have hwc : ContDiffAt ℝ ∞ w 0 :=
    (proj_contDiffAt H hH hy0).comp (0 : Vec n)
      ((contDiff_const.add (Z (σ / P.T)).contDiff).contDiffAt)
  have hPrc : ContDiffAt ℝ ∞ (fun a => Pr H (w a)) 0 := by
    refine ContDiffAt.comp (g := Pr H) (0 : Vec n) ?_ hwc
    rw [hw0]; exact Pr_contDiffAt H hH _ (P.mem σ)
  have hJc : ContDiffAt ℝ ∞ (fun a => J (w a)) 0 :=
    ContDiffAt.comp (g := J) (0 : Vec n) hJ.1.contDiffAt hwc
  have hM : ContDiffAt ℝ ∞ (fun a => (J (w a)).comp (Pr H (w a))) 0 := hJc.clm_comp hPrc
  have hMd := (hM.differentiableAt (by simp)).hasFDerivAt
  have hR : HasFDerivAt (fun a => reeb H (w a)) ((fderiv ℝ (reeb H) (P.x σ)).comp (Z (σ / P.T)))
      0 := by
    have hRd : DifferentiableAt ℝ (reeb H) (w 0) := by
      rw [hw0]; exact (ka_reeb_contDiffAt H hH _ (P.mem σ)).differentiableAt (by simp)
    have := hRd.hasFDerivAt.comp (0 : Vec n) hw
    rwa [hw0] at this
  have hv : HasFDerivAt (fun a => reeb H (P.x σ) + (1 / P.T) • deriv Z (σ / P.T) a -
      reeb H (w a)) ((1 / P.T) • deriv Z (σ / P.T) -
        (fderiv ℝ (reeb H) (P.x σ)).comp (Z (σ / P.T))) 0 := by
    have h1 : HasFDerivAt (fun a : Vec n => (1 / P.T) • deriv Z (σ / P.T) a)
        ((1 / P.T) • deriv Z (σ / P.T)) 0 := ((1 / P.T) • deriv Z (σ / P.T)).hasFDerivAt
    exact (h1.const_add _).sub hR
  have hv0 : reeb H (P.x σ) + (1 / P.T) • deriv Z (σ / P.T) 0 - reeb H (w 0) = 0 := by
    rw [hw0]; simp
  have hMv := hMd.clm_apply hv
  rw [hv0, map_zero, add_zero] at hMv
  have hK := ((Kinv (Z (σ / P.T))).hasFDerivAt.comp (0 : Vec n) hMv).const_smul c
  have hfin : HasFDerivAt (fun a => c • Kinv (Z (σ / P.T)) ((J (w a)).comp (Pr H (w a))
      (reeb H (P.x σ) + (1 / P.T) • deriv Z (σ / P.T) a - reeb H (w a))))
      (c • (Kinv (Z (σ / P.T))).comp ((J (P.x σ)).comp ((Pr H (P.x σ)).comp
        ((1 / P.T) • deriv Z (σ / P.T) - (fderiv ℝ (reeb H) (P.x σ)).comp (Z (σ / P.T))))))
      0 := by
    rw [hw0] at hK
    exact hK
  refine hfin.congr_of_eventuallyEq ?_
  have hball : ball (0 : Vec n) r ∈ 𝓝 (0 : Vec n) := ball_mem_nhds _ hr0
  filter_upwards [hball] with a ha
  rw [Gf_snd hH J P Z c σ a (hr σ a (by simpa using ha))]
  rfl

/-- The derivative at `0` is the loop of the asymptotic operator, rescaled. -/
theorem fderiv_Gf_snd_apply {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hZS : ∀ η : ℝ → CauchyRiemannIndex.Vec n, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
        Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
    (c σ : ℝ) (b : Vec n) :
    (c • (Kinv (Z (σ / P.T))).comp ((J (P.x σ)).comp ((Pr H (P.x σ)).comp
        ((1 / P.T) • deriv Z (σ / P.T) - (fderiv ℝ (reeb H) (P.x σ)).comp (Z (σ / P.T)))))) b =
      (c / P.T) • mE (Sinf (σ / P.T)) b := by
  have hT := P.T_pos
  have hZd : Differentiable ℝ Z := hZ.1.differentiable (by simp)
  have hη : Differentiable ℝ (fun t => Z t b) := fun t =>
    ((hZd t).hasFDerivAt.clm_apply (hasFDerivAt_const b t)).differentiableAt
  have hder : ∀ t, deriv (fun t => Z t b) t = deriv Z t b := by
    intro t
    have := (hZd t).hasDerivAt.clm_apply (hasDerivAt_const t b)
    simpa using this.deriv
  have hxi := isInXi_linearizedReeb_deriv H hH P (fun t => Z t b) hη
    (fun t => (hZ.2.2 t).1 b) (σ / P.T)
  rw [Tdiv hT, hder] at hxi
  set v := -(deriv Z (σ / P.T) b) + P.T • fderiv ℝ (reeb H) (P.x σ) (Z (σ / P.T) b) with hvdef
  have hA := hZS (fun _ => b) contDiff_const (fun _ => rfl) (σ / P.T)
  simp only [asympOp, Tdiv hT, hder, deriv_const, map_zero, neg_zero, zero_sub] at hA
  -- hA : J (P.x σ) v = Z (σ/T) (-(S∞ b))
  have hlin : (1 / P.T) • deriv Z (σ / P.T) b - fderiv ℝ (reeb H) (P.x σ) (Z (σ / P.T) b) =
      (-(1 / P.T)) • v := by
    rw [hvdef, smul_add, smul_smul]
    field_simp
    module
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [hlin, map_smul, Pr_xi H _ _ hxi, map_smul, hA, map_smul, frame_K hZ, smul_smul,
    mE_apply, smul_neg, ← neg_smul]
  congr 1
  field_simp

end FiniteEnergyPlane.N1

namespace FiniteEnergyPlane.N1
open FiniteEnergyPlane CauchyRiemannIndex

variable {n : ℕ}

/-- The frame equation at a point of the end. -/
theorem frame_eq {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {J : V n → V n →L[ℝ] V n} (hJ : IsCompatibleXiStructure H J) {u : ℂ → V n}
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z)
    (τ : ℝ × ℝ → ℝ) (ζ : ℝ × ℝ → Vec n) (s t : ℝ) (hs : 0 < s)
    (hτd : DifferentiableAt ℝ τ (s, t)) (hζd : DifferentiableAt ℝ ζ (s, t))
    (hrep : ∀ᶠ q in 𝓝 (s, t), endW H u cylEnd q = proj H (P.x (τ q) + Z (τ q / P.T) (ζ q)))
    (hne : P.x (τ (s, t)) + Z (τ (s, t) / P.T) (ζ (s, t)) ≠ 0) :
    Pr H (Psi H P Z (τ (s, t)) (ζ (s, t)))
        (Yv H P Z (τ (s, t), fderiv ℝ τ (s, t), fderiv ℝ ζ (s, t)) (ζ (s, t)) (1, 0)) +
      J (Psi H P Z (τ (s, t)) (ζ (s, t))) (Pr H (Psi H P Z (τ (s, t)) (ζ (s, t)))
        (Yv H P Z (τ (s, t), fderiv ℝ τ (s, t), fderiv ℝ ζ (s, t)) (ζ (s, t)) (0, 1))) = 0 := by
  set p : ℝ × ℝ := (s, t) with hpdef
  set y : ℝ × ℝ → V n := fun q => P.x (τ q) + Z (τ q / P.T) (ζ q) with hydef
  have hZd : Differentiable ℝ Z := hZ.1.differentiable (by simp)
  -- derivative of y
  have hx := (P.hasDerivAt (τ p)).hasFDerivAt.comp p hτd.hasFDerivAt
  have hτT : HasFDerivAt (fun q => τ q / P.T) ((P.T)⁻¹ • fderiv ℝ τ p) p := by
    have := hτd.hasFDerivAt.const_smul (P.T)⁻¹
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    simp [div_eq_inv_mul]
  have hZτ := (hZd (τ p / P.T)).hasFDerivAt.comp p hτT
  obtain ⟨Dy, hy, hDyY⟩ : ∃ Dy, HasFDerivAt y Dy p ∧
      ∀ e, Dy e = Yv H P Z (τ p, fderiv ℝ τ p, fderiv ℝ ζ p) (ζ p) e := by
    refine ⟨_, hx.add (hZτ.clm_apply hζd.hasFDerivAt), fun e => ?_⟩
    have hZ' : fderiv ℝ Z (τ p / P.T) 1 = deriv Z (τ p / P.T) := rfl
    simp only [Yv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    have hl : fderiv ℝ Z (τ p / P.T) ((P.T)⁻¹ * fderiv ℝ τ p e) =
        ((P.T)⁻¹ * fderiv ℝ τ p e) • deriv Z (τ p / P.T) := by
      rw [← hZ', ← map_smul, smul_eq_mul, mul_one]
    rw [hl, smul_add, smul_smul, ContinuousLinearMap.smul_apply]
    simp only [one_div, smul_eq_mul]
    rw [mul_comm (fderiv ℝ τ p e)]; abel
  -- derivative of proj
  have hy0 : y p ≠ 0 := hne
  obtain ⟨hr, hHw⟩ := ka_scale_spec H hH (y p) hy0
  set r := scaleToS H (y p) with hrdef
  have hpr := (ka_scale_hasFDerivAt H hH (y p) hy0).smul (hasFDerivAt_id (y p))
  set Dr := (-(scaleToS H (y p) ^ 2 / fderiv ℝ H (proj H (y p)) (proj H (y p)))) •
    fderiv ℝ H (proj H (y p)) with hDr
  have hcomp : HasFDerivAt (proj H ∘ y)
      ((r • ContinuousLinearMap.id ℝ (V n) + Dr.smulRight (y p)).comp Dy) p := by
    have := hpr.comp p hy
    exact this
  have hW : fderiv ℝ (endW H u cylEnd) p =
      (r • ContinuousLinearMap.id ℝ (V n) + Dr.smulRight (y p)).comp Dy := by
    rw [Filter.EventuallyEq.fderiv_eq hrep]; exact hcomp.fderiv
  have hwp : endW H u cylEnd p = proj H (y p) := hrep.self_of_nhds
  set w := proj H (y p) with hwdef
  have hwS : w ∈ energySurface H := hHw
  have hPy : Pr H w (y p) = 0 := by
    have : y p = r⁻¹ • w := by
      rw [hwdef, proj, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    rw [this, map_smul, Pr_self H hH w hwS, smul_zero]
  have hPD : ∀ e, Pr H w (fderiv ℝ (endW H u cylEnd) p e) =
      r • Pr H w (Yv H P Z (τ p, fderiv ℝ τ p, fderiv ℝ ζ p) (ζ p) e) := by
    intro e
    rw [hW, ContinuousLinearMap.comp_apply, hDyY]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      hPy, smul_zero, add_zero]
  have hX := xiPart_dbar_endW_eq_zero H hH J hJ u hu hs t
  simp only [] at hX
  rw [← hpdef, hwp] at hX
  simp only [← Pr_apply] at hX
  rw [hPD, hPD, map_smul, ← smul_add] at hX
  have hPsi : Psi H P Z (τ p) (ζ p) = w := rfl
  rw [hPsi]
  exact (smul_eq_zero.1 hX).resolve_left hr.ne'

end FiniteEnergyPlane.N1

namespace FiniteEnergyPlane.N1
open FiniteEnergyPlane CauchyRiemannIndex

variable {n : ℕ}

/-- A smooth radial cutoff: the identity on `‖a‖ ≤ r/2`, with values in `ball 0 r`. -/
noncomputable def rho (r : ℝ) (a : Vec n) : Vec n :=
  Real.smoothTransition ((r ^ 2 - ‖a‖ ^ 2) / (r ^ 2 - (r / 2) ^ 2)) • a

lemma rho_contDiff (r : ℝ) : ContDiff ℝ ∞ (rho (n := n) r) :=
  (Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _)).smul contDiff_id

lemma rho_eq {r : ℝ} (hr : 0 < r) {a : Vec n} (ha : ‖a‖ ≤ r / 2) : rho r a = a := by
  unfold rho
  rw [Real.smoothTransition.one_of_one_le, one_smul]
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith [norm_nonneg a]

lemma rho_lt {r : ℝ} (hr : 0 < r) (a : Vec n) : ‖rho r a‖ < r := by
  unfold rho
  rw [norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  by_cases h : ‖a‖ < r
  · calc _ ≤ 1 * ‖a‖ :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) (norm_nonneg _)
      _ < r := by linarith
  · push_neg at h
    rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
    · exact hr
    · apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith

lemma rho_zero (r : ℝ) : rho (n := n) r 0 = 0 := by simp [rho]

/-- Entries of the matrix of a linear map. -/
noncomputable def entL (i j : Fin n ⊕ Fin n) : (Vec n →L[ℝ] Vec n) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)).symm L i j
      map_add' := fun L M => by simp
      map_smul' := fun c L => by simp }

lemma entL_apply (i j : Fin n ⊕ Fin n) (L : Vec n →L[ℝ] Vec n) :
    entL i j L = (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)).symm L i j := rfl

lemma deriv_per {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : Function.Periodic f 1) (x : ℝ) : deriv f (x + 1) = deriv f x := by
  rw [← deriv_comp_add_const]
  congr 1; funext y; exact hf y

lemma Gf_periodic {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) (q : Q n) (a : Vec n) :
    Gf H J P Z (q.1 + P.T, q.2) a = Gf H J P Z q a := by
  have h1 : (q.1 + P.T) / P.T = q.1 / P.T + 1 := by
    have := P.T_pos; field_simp
  simp only [Gf, Psi, Yv, h1, hZ.2.1 _, deriv_per hZ.2.1, P.periodic]

lemma Gf_periodic_eps {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (σ : ℝ) (D : (ℝ × ℝ →L[ℝ] ℝ) × (ℝ × ℝ →L[ℝ] Vec n)) (a : Vec n) :
    Gf H J P Z (σ + ε * P.T, D) a = Gf H J P Z (σ, D) a := by
  rcases hε with rfl | rfl
  · rw [one_mul]; exact Gf_periodic hZ (σ, D) a
  · have := Gf_periodic hZ (σ + -1 * P.T, D) a
    simp only [neg_mul, one_mul, neg_add_cancel_right] at this ⊢
    exact this.symm

lemma fderiv_periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {s₀ : ℝ} (hf : ∀ s > s₀, ∀ t : ℝ, f (s, t + 1) = f (s, t))
    {s : ℝ} (hs : s₀ < s) (t : ℝ) : fderiv ℝ f (s, t + 1) = fderiv ℝ f (s, t) := by
  have h1 : fderiv ℝ (fun q => f (q + (0, 1))) (s, t) = fderiv ℝ f ((s, t) + (0, 1)) :=
    fderiv_comp_add_right _
  have h2 : (fun q : ℝ × ℝ => f (q + (0, 1))) =ᶠ[𝓝 (s, t)] f := by
    have hU : {q : ℝ × ℝ | s₀ < q.1} ∈ 𝓝 (s, t) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hs
    filter_upwards [hU] with q hq
    obtain ⟨a, b⟩ := q
    simpa using hf a hq b
  rw [← h2.fderiv_eq, h1]; simp

section
variable (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (P : ReebOrbit H)
  (Z : ℝ → Vec n →L[ℝ] V n) (r : ℝ)

/-- The globalized remainder. -/
noncomputable def Ghat (p : Q n × Vec n) : Vec n := Gf H J P Z p.1 (rho r p.2)

/-- Its Hadamard factor. -/
noncomputable def gH (p : Q n × Vec n) : Vec n →L[ℝ] Vec n :=
  ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => Ghat H J P Z r (p.1, a)) (θ • p.2)

end

lemma Ghat_contDiff {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {J : V n → V n →L[ℝ] V n} (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    {Z : ℝ → Vec n →L[ℝ] V n} (hZc : ContDiff ℝ ∞ Z) {r : ℝ} (hr0 : 0 < r)
    (hr : ∀ σ : ℝ, ∀ a : Vec n, ‖a‖ < r → P.x σ + Z (σ / P.T) a ≠ 0) :
    ContDiff ℝ ∞ (Ghat H J P Z r) := by
  have hGon := Gf_contDiffOn hH hJ P hZc hr
  refine contDiff_iff_contDiffAt.2 (fun p => ?_)
  have hopen : IsOpen {q : Q n × Vec n | ‖q.2‖ < r} :=
    isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
  have hin : (p.1, rho r p.2) ∈ {q : Q n × Vec n | ‖q.2‖ < r} := by
    show ‖rho r p.2‖ < r
    exact rho_lt hr0 p.2
  have e : Ghat H J P Z r =
      (fun q : Q n × Vec n => Gf H J P Z q.1 q.2) ∘ (fun p : Q n × Vec n => (p.1, rho r p.2)) :=
    rfl
  have h1 : ContDiffAt ℝ ∞ (fun q : Q n × Vec n => Gf H J P Z q.1 q.2) (p.1, rho r p.2) :=
    hGon.contDiffAt (hopen.mem_nhds hin)
  have h2 : ContDiffAt ℝ ∞ (fun p : Q n × Vec n => (p.1, rho r p.2)) p :=
    (contDiff_fst.prodMk ((rho_contDiff r).comp contDiff_snd)).contDiffAt
  rw [e]
  exact h1.comp p h2

lemma gH_mul {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {J : V n → V n →L[ℝ] V n} (hJ : IsCompatibleXiStructure H J) {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) {r : ℝ} (hr0 : 0 < r)
    (hr : ∀ σ : ℝ, ∀ a : Vec n, ‖a‖ < r → P.x σ + Z (σ / P.T) a ≠ 0) (q : Q n) (a : Vec n) :
    gH H J P Z r (q, a) a = Gf H J P Z q (rho r a) := by
  have := (hadamard_integral_fderiv _ (Ghat_contDiff hH hJ P hZ.1 hr0 hr)).2 (q, a)
  have h0 : Ghat H J P Z r (q, 0) = 0 := by
    simp only [Ghat, rho_zero]; exact Gf_zero hH hZ q
  rw [h0, zero_add] at this
  exact this.symm

lemma gH_contDiff {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {J : V n → V n →L[ℝ] V n} (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    {Z : ℝ → Vec n →L[ℝ] V n} (hZc : ContDiff ℝ ∞ Z) {r : ℝ} (hr0 : 0 < r)
    (hr : ∀ σ : ℝ, ∀ a : Vec n, ‖a‖ < r → P.x σ + Z (σ / P.T) a ≠ 0) :
    ContDiff ℝ ∞ (gH H J P Z r) :=
  (hadamard_integral_fderiv _ (Ghat_contDiff hH hJ P hZc hr0 hr)).1

lemma gH_per {H : V n → ℝ} {J : V n → V n →L[ℝ] V n} {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) (r : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (σ : ℝ) (D : (ℝ × ℝ →L[ℝ] ℝ) × (ℝ × ℝ →L[ℝ] Vec n)) (a : Vec n) :
    gH H J P Z r ((σ + ε * P.T, D), a) = gH H J P Z r ((σ, D), a) := by
  simp only [gH, Ghat]
  congr 1; funext θ; congr 1; funext a'
  exact Gf_periodic_eps hZ hε σ D _

lemma gH_lim {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H)
    {J : V n → V n →L[ℝ] V n} (hJ : IsCompatibleXiStructure H J) {P : ReebOrbit H}
    {Z : ℝ → Vec n →L[ℝ] V n} (hZ : IsUnitaryXiFrame J P Z) {r : ℝ} (hr0 : 0 < r)
    (hr : ∀ σ : ℝ, ∀ a : Vec n, ‖a‖ < r → P.x σ + Z (σ / P.T) a ≠ 0)
    (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hZS : ∀ η : ℝ → CauchyRiemannIndex.Vec n, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
        Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
    (ε σ : ℝ) :
    gH H J P Z r ((σ, (ε * P.T) • ContinuousLinearMap.snd ℝ ℝ ℝ, 0), 0) =
      mE (ε • Sinf (σ / P.T)) := by
  have h1 : gH H J P Z r ((σ, (ε * P.T) • ContinuousLinearMap.snd ℝ ℝ ℝ, 0), 0) =
      fderiv ℝ (fun a => Ghat H J P Z r ((σ, (ε * P.T) • ContinuousLinearMap.snd ℝ ℝ ℝ, 0), a))
        0 := by
    simp only [gH, smul_zero, intervalIntegral.integral_const, sub_zero, one_smul]
  have h2 : (fun a => Ghat H J P Z r ((σ, (ε * P.T) • ContinuousLinearMap.snd ℝ ℝ ℝ, 0), a))
      =ᶠ[𝓝 0] (fun a => Gf H J P Z (σ, (ε * P.T) • ContinuousLinearMap.snd ℝ ℝ ℝ, 0) a) := by
    filter_upwards [ball_mem_nhds (0 : Vec n) (half_pos hr0)] with a ha
    simp only [Ghat]
    rw [rho_eq hr0 (by rw [mem_ball_zero_iff] at ha; linarith)]
  rw [h1, h2.fderiv_eq, (hasFDerivAt_Gf_snd hH hJ hZ hr0 hr (ε * P.T) σ).fderiv]
  ext1 b
  rw [fderiv_Gf_snd_apply hH hZ Sinf hZS (ε * P.T) σ b]
  have hT := P.T_pos
  have : ε * P.T / P.T = ε := by field_simp
  rw [this]
  simp [mE]

end FiniteEnergyPlane.N1

namespace FiniteEnergyPlane

open N1 CauchyRiemannIndex

/-- the derivative of a phase whose derivatives of order `≥ 1` tend to `0` tends to `0` -/
lemma n1d_fderiv_tendsto {θ : ℝ × ℝ → ℝ}
    (hθs : ∃ s₂ : ℝ, ContDiffOn ℝ ∞ θ (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m θ (s, t)‖ ≤ η) :
    TendstoZeroCInfty (fderiv ℝ θ) := by
  obtain ⟨s₂, hs₂⟩ := hθs
  refine ⟨⟨s₂, hs₂.fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) (by simp)⟩, fun m η hη => ?_⟩
  obtain ⟨s₃, hs₃⟩ := hθ (m + 1) (by omega) η hη
  exact ⟨s₃, fun s hs t => by rw [norm_iteratedFDeriv_fderiv]; exact hs₃ s hs t⟩

theorem exists_crEquation_tubeNormal_of_drift_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (Metric.ball 0 1 \ {0}) u) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hZS : ∀ η : ℝ → CauchyRiemannIndex.Vec n, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
        Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hθs : ∃ s₂ : ℝ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η)
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n) (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n),
      (∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ)) ∧
      (∀ i j, TendstoZeroCInfty (fun p : ℝ × ℝ => S p i j - (ε • Sinf (τ p / P.T)) i j)) ∧
      ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ) ∧ TendstoZeroUnif ζ ∧
      ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t) ∧
        CauchyRiemannIndex.crOp S ζ (s, t) = 0 ∧ h (s, t) = Z (τ (s, t) / P.T) (ζ (s, t)) := by
  have hT := P.T_pos
  obtain ⟨r, hr0, hr⟩ := exists_r hH P hZ
  have hgC := gH_contDiff hH hJ P hZ.1 hr0 hr
  set θ : ℝ × ℝ → ℝ := fun p => τ p - ε * P.T * p.2 with hθd
  have hθb : ∀ m : ℕ, 1 ≤ m → ∃ B s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖iteratedFDeriv ℝ m θ (s, t)‖ ≤ B :=
    fun m hm => by
      obtain ⟨s₂, hs₂⟩ := hθ m hm 1 one_pos
      exact ⟨1, s₂, hs₂⟩
  have hτθ : ∀ p : ℝ × ℝ, ε * P.T * p.2 + θ p = τ p := fun p => by simp only [hθd]; ring
  -- the frame coordinates
  set Φζ : ℝ × V n → Vec n := fun z => Kinv (Z (z.1 / P.T)) z.2 with hΦζ
  have hΦζc : ContDiff ℝ ∞ Φζ :=
    (Kinv_contDiff.comp (hZ.1.comp (contDiff_fst.div_const _))).clm_apply contDiff_snd
  have hΦζp : ∀ φ' v, Φζ (φ' + P.T, v) = Φζ (φ', v) := by
    intro φ' v
    simp only [hΦζ]
    rw [show (φ' + P.T) / P.T = φ' / P.T + 1 by field_simp, hZ.2.1]
  have hΦζpe : ∀ φ' v, Φζ (φ' + ε * P.T, v) = Φζ (φ', v) := by
    intro φ' v
    rcases hε with rfl | rfl
    · rw [one_mul]; exact hΦζp φ' v
    · have := hΦζp (φ' + -1 * P.T) v
      rw [show φ' + -1 * P.T + P.T = φ' by ring] at this
      exact this.symm
  have hΦζ0 : ∀ φ' : ℝ, Φζ (φ', 0) = 0 := by intro φ'; simp [hΦζ]
  set ζ : ℝ × ℝ → Vec n := fun p => Φζ (ε * P.T * p.2 + θ p, h p) with hζdef
  have hζC : TendstoZeroCInfty ζ :=
    tendstoZeroCInfty_comp_periodic_of_drift Φζ P.T 1 (ε * P.T) hT one_pos hΦζc.contDiffOn
      (fun φ' v _ => hΦζp φ' v) hΦζ0 θ hθs hθb h hh
  have hζval : ∀ p, ζ p = Kinv (Z (τ p / P.T)) (h p) := by
    intro p; simp only [hζdef, hΦζ, hτθ]
  have hhZ : ∀ s ≥ s₀, ∀ t : ℝ, h (s, t) = Z (τ (s, t) / P.T) (ζ (s, t)) := by
    intro s hs t
    obtain ⟨b, hb⟩ := (hZ.2.2 (τ (s, t) / P.T)).2.1 (h (s, t))
      (by rw [Tdiv hT]; exact (hrep s hs t).2.2.1)
    rw [hζval, ← hb, frame_K hZ]
  -- the coefficient
  have hDθ : TendstoZeroCInfty (fderiv ℝ θ) := n1d_fderiv_tendsto hθs hθ
  have hv : TendstoZeroCInfty (fun p => (ζ p, fderiv ℝ θ p, fderiv ℝ ζ p)) :=
    tendstoZeroCInfty_prodMk hζC
      (tendstoZeroCInfty_prodMk hDθ (tendstoZeroCInfty_fderiv hζC))
  set L0 : ℝ × ℝ →L[ℝ] ℝ := (ε * P.T) • ContinuousLinearMap.snd ℝ ℝ ℝ with hL0
  set Xf : ℝ × (Vec n × (ℝ × ℝ →L[ℝ] ℝ) × (ℝ × ℝ →L[ℝ] Vec n)) → Q n × Vec n :=
    fun z => ((z.1, L0 + z.2.2.1, z.2.2.2), z.2.1) with hXf
  have hXfc : ContDiff ℝ ∞ Xf :=
    ((contDiff_fst.prodMk ((contDiff_const.add contDiff_snd.snd.fst).prodMk
      contDiff_snd.snd.snd)).prodMk contDiff_snd.fst)
  set ME := (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)) with hME
  set S : ℝ × ℝ → Mat n := fun p =>
    ME.symm (gH H J P Z r (Xf (ε * P.T * p.2 + θ p, (ζ p, fderiv ℝ θ p, fderiv ℝ ζ p))))
    with hSdef
  have hlimE : ∀ (i j : Fin n ⊕ Fin n) (σ : ℝ),
      entL i j (gH H J P Z r ((σ, L0, 0), 0)) = (ε • Sinf (σ / P.T)) i j := by
    intro i j σ
    rw [entL_apply, hL0, gH_lim hH hJ hZ hr0 hr Sinf hZS ε]
    simp [mE, ← hME]
  have hSas : ∀ i j, TendstoZeroCInfty (fun p : ℝ × ℝ => S p i j - (ε • Sinf (τ p / P.T)) i j) := by
    intro i j
    set Φ : ℝ × (Vec n × (ℝ × ℝ →L[ℝ] ℝ) × (ℝ × ℝ →L[ℝ] Vec n)) → ℝ :=
      fun z => entL i j (gH H J P Z r (Xf z)) - entL i j (gH H J P Z r ((z.1, L0, 0), 0))
      with hΦ
    have hΦc : ContDiff ℝ ∞ Φ :=
      ((entL i j).contDiff.comp (hgC.comp hXfc)).sub ((entL i j).contDiff.comp (hgC.comp
        ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_const)))
    have hΦp : ∀ (φ' : ℝ) v, ‖v‖ < 1 → Φ (φ' + P.T, v) = Φ (φ', v) := by
      intro φ' v _
      simp only [hΦ, hXf]
      have e1 := gH_per hZ r (ε := 1) (Or.inl rfl) φ' (L0 + v.2.1, v.2.2) v.1
      have e2 := gH_per hZ r (ε := 1) (Or.inl rfl) φ' (L0, 0) 0
      rw [one_mul] at e1 e2
      rw [e1, e2]
    have hΦ0 : ∀ φ' : ℝ, Φ (φ', 0) = 0 := by intro φ'; simp [hΦ, hXf]
    have hC := tendstoZeroCInfty_comp_periodic_of_drift Φ P.T 1 (ε * P.T) hT one_pos
      hΦc.contDiffOn hΦp hΦ0 θ hθs hθb _ hv
    convert hC using 1
    funext p
    simp only [hΦ, hSdef, hτθ]
    rw [hlimE i j (τ p), entL_apply]
  -- thresholds
  obtain ⟨sθ, hθU0⟩ := hθs
  obtain ⟨sζ, hζs⟩ := hζC.1
  obtain ⟨sm, hsm⟩ := hζC.2 0 (r / 2) (half_pos hr0)
  set s₁ := max (max s₀ 0) (max (max sθ sζ) sm) with hs₁
  have hU : IsOpen (Set.Ioi s₁ ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hsub1 : Set.Ioi s₁ ×ˢ (Set.univ : Set ℝ) ⊆ Set.Ioi sθ ×ˢ Set.univ :=
    Set.prod_mono (Set.Ioi_subset_Ioi (by simp [hs₁])) le_rfl
  have hsub2 : Set.Ioi s₁ ×ˢ (Set.univ : Set ℝ) ⊆ Set.Ioi sζ ×ˢ Set.univ :=
    Set.prod_mono (Set.Ioi_subset_Ioi (by simp [hs₁])) le_rfl
  have hθU : ContDiffOn ℝ ∞ θ (Set.Ioi s₁ ×ˢ Set.univ) := hθU0.mono hsub1
  have hζU : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ) := hζs.mono hsub2
  have hvU : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      (ε * P.T * p.2 + θ p, (ζ p, fderiv ℝ θ p, fderiv ℝ ζ p))) (Set.Ioi s₁ ×ˢ Set.univ) :=
    ((contDiff_const.mul contDiff_snd).contDiffOn.add hθU).prodMk
      (hζU.prodMk ((hθU.fderiv_of_isOpen hU (by simp)).prodMk
        (hζU.fderiv_of_isOpen hU (by simp))))
  refine ⟨s₁, S, ζ, fun i j => ?_, hSas, hζU, ?_, ?_⟩
  · exact ((entL i j).contDiff.comp (hgC.comp hXfc)).comp_contDiffOn hvU
  · intro e he
    obtain ⟨s', hs'⟩ := hζC.2 0 e he
    exact ⟨s', fun s hs t => by simpa [norm_iteratedFDeriv_zero] using hs' s hs t⟩
  intro s hs t
  have hs0 : s₀ < s := lt_of_le_of_lt (by simp [hs₁]) hs
  have hspos : 0 < s := lt_of_le_of_lt (by simp [hs₁]) hs
  have hsm' : sm ≤ s := le_trans (by simp [hs₁]) hs.le
  have hθper : ∀ s > s₀, ∀ t : ℝ, θ (s, t + 1) = θ (s, t) := by
    intro s hs t
    simp only [hθd]; rw [(hrep s hs.le t).1]; ring
  have hζper : ∀ s > s₀, ∀ t : ℝ, ζ (s, t + 1) = ζ (s, t) := by
    intro s hs t
    simp only [hζdef]
    rw [hθper s hs t, (hrep s hs.le t).2.1, show ε * P.T * (t + 1) + θ (s, t) =
      ε * P.T * t + θ (s, t) + ε * P.T by ring, hΦζpe]
  refine ⟨?_, hζper s hs0 t, ?_, hhZ s hs0.le t⟩
  · simp only [hSdef, hXf]
    rw [hθper s hs0 t, hζper s hs0 t, fderiv_periodic hθper hs0 t, fderiv_periodic hζper hs0 t,
      show ε * P.T * (t + 1) + θ (s, t) = ε * P.T * t + θ (s, t) + ε * P.T by ring,
      gH_per hZ r hε]
  -- the equation
  set p : ℝ × ℝ := (s, t) with hpdef
  have hpU : p ∈ Set.Ioi s₁ ×ˢ (Set.univ : Set ℝ) := ⟨hs, trivial⟩
  have hθd' : DifferentiableAt ℝ θ p :=
    (hθU.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hζd : DifferentiableAt ℝ ζ p :=
    (hζU.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hτeq : τ = fun q => θ q + L0 q := by
    funext q; simp only [hθd, hL0, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_snd',
      smul_eq_mul]; ring
  have hτD : HasFDerivAt τ (fderiv ℝ θ p + L0) p := by
    rw [hτeq]; exact hθd'.hasFDerivAt.add L0.hasFDerivAt
  have hζsmall : ‖ζ p‖ ≤ r / 2 := by
    have := hsm s hsm' t; simpa [norm_iteratedFDeriv_zero] using this
  have hrep' : ∀ᶠ q in 𝓝 p, endW H u cylEnd q = proj H (P.x (τ q) + Z (τ q / P.T) (ζ q)) := by
    have hO : {q : ℝ × ℝ | s₀ < q.1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hs0
    filter_upwards [hO] with q hq
    obtain ⟨a, b⟩ := q
    rw [(hrep a hq.le b).2.2.2, hhZ a hq.le b]
  have hne : P.x (τ p) + Z (τ p / P.T) (ζ p) ≠ 0 := hr _ _ (by linarith)
  have hF := frame_eq hH hJ hu hZ τ ζ s t hspos (hτD.differentiableAt) hζd hrep' hne
  have hX : Xf (ε * P.T * p.2 + θ p, (ζ p, fderiv ℝ θ p, fderiv ℝ ζ p)) =
      ((τ p, fderiv ℝ τ p, fderiv ℝ ζ p), ζ p) := by
    simp only [hXf, hτD.fderiv, hτθ]
    congr 2
    rw [add_comm]
  have hGf : Gf H J P Z (τ p, fderiv ℝ τ p, fderiv ℝ ζ p) (ζ p) =
      -(partialS ζ p + mE (J₀ n) (partialT ζ p)) := by
    simp only [Gf]
    rw [hF, map_zero, zero_sub]
    rfl
  have hSz : Matrix.toEuclideanLin (S p) (ζ p) =
      Gf H J P Z (τ p, fderiv ℝ τ p, fderiv ℝ ζ p) (ζ p) := by
    rw [← mE_apply]
    simp only [hSdef, hME, mE_symm_apply]
    rw [hX, gH_mul hH hJ hZ hr0 hr, rho_eq hr0 hζsmall]
  show partialS ζ p + Matrix.toEuclideanLin (J₀ n) (partialT ζ p) +
    Matrix.toEuclideanLin (S p) (ζ p) = 0
  rw [hSz, hGf, ← mE_apply]
  abel

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hZS : ∀ η : ℝ → CauchyRiemannIndex.Vec n, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
        Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hθs : ∃ s₂ : ℝ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η)
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n) (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n),
      (∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ)) ∧
      (∀ i j, TendstoZeroCInfty (fun p : ℝ × ℝ => S p i j - (ε • Sinf (τ p / P.T)) i j)) ∧
      ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ) ∧ TendstoZeroUnif ζ ∧
      ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t) ∧
        CauchyRiemannIndex.crOp S ζ (s, t) = 0 ∧ h (s, t) = Z (τ (s, t) / P.T) (ζ (s, t)) :=
  exists_crEquation_tubeNormal_of_drift_aux H hH J hJ u hu P Z hZ Sinf hSinf hSinf' hZS ε hε τ h s₀ hθs hθ hh hrep
