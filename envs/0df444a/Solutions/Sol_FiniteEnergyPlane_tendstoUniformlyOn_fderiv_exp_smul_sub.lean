-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoUniformlyOn_fderiv_exp_smul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-22T19:11:41.878829+00:00
-- url     : https://prove2.me/submissions/0f273fd0-f827-4dfe-a7a8-666c6f4bb7e9

import Definitions.Def_FiniteEnergyPlane_Setting
import Definitions.Def_JHolomorphic_Setting
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Definitions.Def_FiniteEnergyPlane_OpenBook

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open FiniteEnergyPlane
open scoped ContDiff Topology in
open scoped ContDiff Topology
open Metric Filter Topology

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

namespace FiniteEnergyPlane

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

lemma norm_sub_lt_of_tendstoCInftyLocOn_aux {f : ℕ → X → Y} {g : X → Y} {O K : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) (hK : K ⊆ O) (hKc : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ K, ‖f k x - g x‖ < ε := by
  have h := (Metric.tendstoUniformlyOn_iff.1 (hc K hK hKc 0)) ε hε
  filter_upwards [h] with k hk x hx
  have h1 := hk x hx
  rw [dist_comm, dist_eq_norm] at h1
  have h2 := (iteratedFDeriv ℝ 0 (f k) x - iteratedFDeriv ℝ 0 g x).le_opNorm Fin.elim0
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_zero_apply, Finset.univ_eq_empty,
    Finset.prod_empty, mul_one] at h2
  exact lt_of_le_of_lt h2 h1

lemma norm_fderiv_sub_le_of_tendstoCInftyLocOn_aux {f : ℕ → X → Y} {g : X → Y} {O K : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) (hK : K ⊆ O) (hKc : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ K, ‖fderiv ℝ (f k) x - fderiv ℝ g x‖ ≤ ε := by
  have h := (Metric.tendstoUniformlyOn_iff.1 (hc K hK hKc 1)) ε hε
  filter_upwards [h] with k hk x hx
  have h1 := hk x hx
  rw [dist_comm, dist_eq_norm] at h1
  refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun a => ?_
  have h2 := (iteratedFDeriv ℝ 1 (f k) x - iteratedFDeriv ℝ 1 g x).le_opNorm (fun _ : Fin 1 => a)
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_one_apply, Fin.prod_univ_one]
    at h2
  rw [ContinuousLinearMap.sub_apply]
  exact h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))

end FiniteEnergyPlane

/-!
# (N), layer 1: the map `(s, z, t) ↦ e^{2s} u₀(z) - y(t)` has an invertible strict derivative

At `(0, 0, t₀)` with `u₀ 0 = y t₀ ∈ S`, its derivative `(δs, δz, δt) ↦ 2δs y₀ + Du₀(0) δz - δt R`
is injective when `D(proj ∘ u₀)(0)` is injective and transverse to the Reeb field.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The derivative, as a continuous linear map on `ℝ × ℂ × ℝ`. -/
noncomputable def lpfnL (y₀ R : V 1) (D : ℂ →L[ℝ] V 1) : ℝ × ℂ × ℝ →L[ℝ] V 1 :=
  (ContinuousLinearMap.fst ℝ ℝ (ℂ × ℝ)).smulRight ((2 : ℝ) • y₀) +
    D.comp ((ContinuousLinearMap.fst ℝ ℂ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℝ))) -
    ((ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℝ))).smulRight R

lemma lpfnL_apply (y₀ R : V 1) (D : ℂ →L[ℝ] V 1) (q : ℝ × ℂ × ℝ) :
    lpfnL y₀ R D q = (2 * q.1) • y₀ + D q.2.1 - q.2.2 • R := by
  simp [lpfnL, smul_smul, mul_comm]

lemma lpfnL_injective (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (u₀ : ℂ → V 1)
    (hu₀ : DifferentiableAt ℝ u₀ 0) (hS : u₀ 0 ∈ energySurface H)
    (htr : ∀ v : ℂ, v ≠ 0 → ∀ c : ℝ,
      fderiv ℝ (fun z => proj H (u₀ z)) 0 v ≠ c • reeb H (proj H (u₀ 0))) :
    Function.Injective (lpfnL (u₀ 0) (reeb H (u₀ 0)) (fderiv ℝ u₀ 0)) := by
  set y₀ := u₀ 0 with hy₀
  set R := reeb H y₀ with hR
  have hP := N1.proj_hasFDerivAt_mem H hH hS
  have hpy : proj H y₀ = y₀ := N1.proj_of_mem H hH hS
  obtain ⟨_, hlv, hdR, _⟩ := ka_reeb_spec H hH y₀ hS
  have hdy : 0 < fderiv ℝ H y₀ y₀ := hH.2.2 y₀ hS
  -- chain rule for `proj ∘ u₀`
  have hcomp : fderiv ℝ (fun z => proj H (u₀ z)) 0 =
      (ContinuousLinearMap.id ℝ (V 1) -
        ((fderiv ℝ H y₀ y₀)⁻¹ • fderiv ℝ H y₀).smulRight y₀).comp (fderiv ℝ u₀ 0) :=
    (hP.comp (0 : ℂ) hu₀.hasFDerivAt).fderiv
  intro q q' hqq
  rw [← sub_eq_zero, ← map_sub] at hqq
  rw [← sub_eq_zero]
  set d := q - q' with hd
  rw [lpfnL_apply] at hqq
  have hD : fderiv ℝ u₀ 0 d.2.1 = d.2.2 • R - (2 * d.1) • y₀ := by
    rw [sub_eq_zero] at hqq
    exact eq_sub_of_add_eq' hqq
  have hz : d.2.1 = 0 := by
    by_contra hne
    apply htr d.2.1 hne d.2.2
    rw [hcomp, hpy, ← hR]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hD]
    have hval : fderiv ℝ H y₀ (d.2.2 • R - (2 * d.1) • y₀) =
        -(2 * d.1) * fderiv ℝ H y₀ y₀ := by
      simp only [map_sub, map_smul, smul_eq_mul]; rw [hdR]; ring
    rw [hval]
    have hsc : (fderiv ℝ H y₀ y₀)⁻¹ * (-(2 * d.1) * fderiv ℝ H y₀ y₀) = -(2 * d.1) := by
      field_simp
    rw [hsc, neg_smul, sub_neg_eq_add, sub_add_cancel]
  rw [hz, map_zero, add_zero] at hqq
  -- apply `dH(y₀)`
  have hH' := congrArg (fderiv ℝ H y₀) hqq
  simp only [map_sub, map_smul, map_zero, smul_eq_mul] at hH'
  rw [hdR, mul_zero, sub_zero] at hH'
  have hs : d.1 = 0 := by
    have : 2 * d.1 = 0 := by
      rcases mul_eq_zero.1 hH' with h | h
      · exact h
      · exact absurd h hdy.ne'
    linarith
  rw [hs, mul_zero, zero_smul, zero_sub, neg_eq_zero] at hqq
  have hR0 : R ≠ 0 := by
    intro h0
    have h1 : liouville y₀ R = 0 := by rw [← ka_liouvilleCLM_apply, h0, map_zero]
    rw [h1] at hlv; exact zero_ne_one hlv
  have ht : d.2.2 = 0 := by
    rcases smul_eq_zero.1 hqq with h | h
    · exact h
    · exact absurd h hR0
  ext
  · exact hs
  · simpa using hz
  · exact ht

end FiniteEnergyPlane

/-!
# (N), layer 2: strict derivative of `(s, z, t) ↦ e^{2s} u₀(z) - y(t)` and the perturbation
`(s, z, t) ↦ e^{2s} (vₖ(z) - u₀(z))`
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The projections used below. -/
noncomputable def lpfnZ : ℝ × ℂ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℂ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℝ))

noncomputable def lpfnT : ℝ × ℂ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℝ))

noncomputable def lpfnS : ℝ × ℂ × ℝ →L[ℝ] ℝ := 2 • ContinuousLinearMap.fst ℝ ℝ (ℂ × ℝ)

lemma lpfn_exp_hasStrictFDerivAt (q : ℝ × ℂ × ℝ) :
    HasStrictFDerivAt (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1))
      (Real.exp (2 * q.1) • lpfnS) q := by
  have h1 : HasStrictFDerivAt (fun q : ℝ × ℂ × ℝ => 2 * q.1) lpfnS q := by
    have := lpfnS.hasStrictFDerivAt (x := q)
    convert this using 1
    funext q; simp [lpfnS]
  exact (Real.hasStrictDerivAt_exp (2 * q.1)).comp_hasStrictFDerivAt q h1

lemma lpfn_exp_hasFDerivAt (q : ℝ × ℂ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1))
      (Real.exp (2 * q.1) • lpfnS) q :=
  (lpfn_exp_hasStrictFDerivAt q).hasFDerivAt

theorem lpfn_hasStrictFDerivAt (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u₀ : ℂ → V 1) (hu₀ : ContDiff ℝ 1 u₀) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (t₀ : ℝ) (h0 : u₀ 0 = y t₀) :
    HasStrictFDerivAt (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • u₀ q.2.1 - y q.2.2)
      (lpfnL (u₀ 0) (reeb H (u₀ 0)) (fderiv ℝ u₀ 0)) ((0 : ℝ), (0 : ℂ), t₀) := by
  -- the trajectory is `C¹`
  have hyc : ContinuousAt (fun s => reeb H (y s)) t₀ :=
    (ka_reeb_contDiffAt H hH (y t₀) (hy.1 t₀)).continuousAt.comp (hy.2 t₀).continuousAt
  have hys : HasStrictDerivAt y (reeb H (y t₀)) t₀ :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt (Eventually.of_forall fun s => hy.2 s) hyc
  have hT : HasStrictFDerivAt (fun q : ℝ × ℂ × ℝ => y q.2.2)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (reeb H (y t₀))).comp lpfnT)
      ((0 : ℝ), (0 : ℂ), t₀) :=
    HasStrictFDerivAt.comp ((0 : ℝ), (0 : ℂ), t₀) (f := fun q : ℝ × ℂ × ℝ => q.2.2) hys
      lpfnT.hasStrictFDerivAt
  have hZ : HasStrictFDerivAt (fun q : ℝ × ℂ × ℝ => u₀ q.2.1)
      ((fderiv ℝ u₀ 0).comp lpfnZ) ((0 : ℝ), (0 : ℂ), t₀) :=
    HasStrictFDerivAt.comp ((0 : ℝ), (0 : ℂ), t₀) (f := fun q : ℝ × ℂ × ℝ => q.2.1)
      (hu₀.contDiffAt.hasStrictFDerivAt (by norm_num)) lpfnZ.hasStrictFDerivAt
  have hE := lpfn_exp_hasStrictFDerivAt ((0 : ℝ), (0 : ℂ), t₀)
  have h := (hE.smul hZ).sub hT
  refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
  rw [lpfnL_apply]
  simp [lpfnS, lpfnZ, lpfnT, h0, smul_smul]
  ring_nf

theorem lpfn_exists_equiv (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (u₀ : ℂ → V 1)
    (hu₀ : DifferentiableAt ℝ u₀ 0) (hS : u₀ 0 ∈ energySurface H)
    (htr : ∀ v : ℂ, v ≠ 0 → ∀ c : ℝ,
      fderiv ℝ (fun z => proj H (u₀ z)) 0 v ≠ c • reeb H (proj H (u₀ 0))) :
    ∃ L : (ℝ × ℂ × ℝ) ≃L[ℝ] V 1,
      (L : ℝ × ℂ × ℝ →L[ℝ] V 1) = lpfnL (u₀ 0) (reeb H (u₀ 0)) (fderiv ℝ u₀ 0) := by
  have hinj := lpfnL_injective H hH u₀ hu₀ hS htr
  have hdim : Module.finrank ℝ (ℝ × ℂ × ℝ) = Module.finrank ℝ (V 1) := by
    simp [Module.finrank_prod, Complex.finrank_real_complex]
  refine ⟨(LinearMap.linearEquivOfInjective
    (lpfnL (u₀ 0) (reeb H (u₀ 0)) (fderiv ℝ u₀ 0) : ℝ × ℂ × ℝ →ₗ[ℝ] V 1) hinj
      hdim).toContinuousLinearEquiv, ContinuousLinearMap.ext fun q => rfl⟩

/-- The perturbation is `C¹`-small near `(0, 0, t₀)`. -/
theorem lpfn_perturbation (u₀ : ℂ → V 1) (hu₀ : ContDiff ℝ 1 u₀) (v : ℕ → ℂ → V 1)
    (hv : ∀ k, ContDiff ℝ 1 (v k))
    (hlim : JHolomorphic.TendstoCInftyLocOn v u₀ Set.univ) (t₀ : ℝ) :
    (∀ k, ∀ q : ℝ × ℂ × ℝ, DifferentiableAt ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) ∧
    Tendsto (fun k => Real.exp (2 * (0 : ℝ)) • (v k (0 : ℂ) - u₀ 0)) atTop (𝓝 0) ∧
    TendstoUniformlyOn (fun k q => fderiv ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) 0 atTop
      (ball ((0 : ℝ), (0 : ℂ), t₀) 1) := by
  have hw : ∀ k, ContDiff ℝ 1 (fun z => v k z - u₀ z) := fun k => (hv k).sub hu₀
  have hD : ∀ k (q : ℝ × ℂ × ℝ), HasFDerivAt
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1))
      (Real.exp (2 * q.1) • ((fderiv ℝ (fun z => v k z - u₀ z) q.2.1).comp lpfnZ) +
        (Real.exp (2 * q.1) • lpfnS).smulRight (v k q.2.1 - u₀ q.2.1)) q := by
    intro k q
    have hz : HasFDerivAt (fun q : ℝ × ℂ × ℝ => v k q.2.1 - u₀ q.2.1)
        ((fderiv ℝ (fun z => v k z - u₀ z) q.2.1).comp lpfnZ) q :=
      HasFDerivAt.comp q (f := fun q : ℝ × ℂ × ℝ => q.2.1) (g := fun z => v k z - u₀ z)
        ((hw k).differentiable (by norm_num) q.2.1).hasFDerivAt lpfnZ.hasFDerivAt
    exact (lpfn_exp_hasFDerivAt q).smul hz
  refine ⟨fun k q => (hD k q).differentiableAt, ?_, ?_⟩
  · have := (Metric.tendstoUniformlyOn_iff.1 (hlim {0} (Set.subset_univ _) isCompact_singleton 0))
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [norm_sub_lt_of_tendstoCInftyLocOn_aux hlim (Set.subset_univ _)
      isCompact_singleton hε] with k hk
    simpa [dist_eq_norm] using hk 0 rfl
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set C : ℝ := 3 * Real.exp 2 with hC
    have hCpos : 0 < C := by positivity
    have hK : IsCompact (closedBall (0 : ℂ) 1) := isCompact_closedBall _ _
    have hε' : 0 < ε / (2 * C) := by positivity
    filter_upwards [norm_sub_lt_of_tendstoCInftyLocOn_aux hlim (Set.subset_univ _) hK hε',
      norm_fderiv_sub_le_of_tendstoCInftyLocOn_aux hlim (Set.subset_univ _) hK hε'] with k h0k h1k
    intro q hq
    rw [Pi.zero_apply, dist_zero_left, (hD k q).fderiv]
    have hq' : ‖q - ((0 : ℝ), (0 : ℂ), t₀)‖ < 1 := by rwa [mem_ball, dist_eq_norm] at hq
    have hs : |q.1| < 1 := by
      have := (norm_fst_le (q - ((0 : ℝ), (0 : ℂ), t₀))).trans_lt hq'
      simpa using this
    have hz : q.2.1 ∈ closedBall (0 : ℂ) 1 := by
      have := ((norm_fst_le _).trans (norm_snd_le (q - ((0 : ℝ), (0 : ℂ), t₀)))).trans_lt hq'
      rw [mem_closedBall, dist_zero_right]
      simpa using this.le
    have hexp : Real.exp (2 * q.1) ≤ Real.exp 2 := by
      apply Real.exp_le_exp.2
      have := (abs_lt.1 hs).2; linarith
    have hw0 := h0k q.2.1 hz
    have hw1 : ‖fderiv ℝ (fun z => v k z - u₀ z) q.2.1‖ ≤ ε / (2 * C) := by
      have he : fderiv ℝ (fun z => v k z - u₀ z) q.2.1 = fderiv ℝ (v k) q.2.1 - fderiv ℝ u₀ q.2.1 :=
        (((hv k).differentiable (by norm_num) _).hasFDerivAt.sub
          (hu₀.differentiable (by norm_num) _).hasFDerivAt).fderiv
      rw [he]
      exact h1k q.2.1 hz
    have hS : ‖lpfnS‖ ≤ 2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun q => ?_
      have : lpfnS q = 2 * q.1 := by simp [lpfnS]
      rw [this, norm_mul, Real.norm_two]
      gcongr
      exact norm_fst_le q
    have hZ : ‖lpfnZ‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun q => ?_
      have : lpfnZ q = q.2.1 := by simp [lpfnZ]
      rw [this, one_mul]
      exact (norm_fst_le q.2).trans (norm_snd_le q)
    have he0 : 0 ≤ Real.exp (2 * q.1) := (Real.exp_pos _).le
    calc ‖Real.exp (2 * q.1) • ((fderiv ℝ (fun z => v k z - u₀ z) q.2.1).comp lpfnZ) +
          (Real.exp (2 * q.1) • lpfnS).smulRight (v k q.2.1 - u₀ q.2.1)‖
        ≤ ‖Real.exp (2 * q.1) • ((fderiv ℝ (fun z => v k z - u₀ z) q.2.1).comp lpfnZ)‖ +
          ‖(Real.exp (2 * q.1) • lpfnS).smulRight (v k q.2.1 - u₀ q.2.1)‖ := norm_add_le _ _
      _ ≤ Real.exp 2 * (ε / (2 * C) * 1) + (Real.exp 2 * 2) * (ε / (2 * C)) := by
          gcongr
          · rw [norm_smul, Real.norm_of_nonneg he0]
            gcongr
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            gcongr
          · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_of_nonneg he0]
            gcongr
      _ = ε / 2 := by rw [hC]; field_simp; norm_num
      _ < ε := half_lt_self hε

end FiniteEnergyPlane

/-!
# (N), layer 3: a limit lemma for injective linear maps
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real NNReal

/-- If `Mₖ → M` with `M` injective and `Mₖ aₖ → M b`, then `aₖ → b`. -/
theorem lpfn_tendsto_of_tendsto_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : ℂ →L[ℝ] F) (hM : Function.Injective M) (Mk : ℕ → ℂ →L[ℝ] F)
    (hMk : Tendsto Mk atTop (𝓝 M)) (a : ℕ → ℂ) (b : ℂ)
    (hlim : Tendsto (fun k => Mk k (a k)) atTop (𝓝 (M b))) :
    Tendsto a atTop (𝓝 b) := by
  obtain ⟨K, hK, hKa⟩ := (M : ℂ →ₗ[ℝ] F).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hM)
  have hKr : (0 : ℝ) < K := hK
  -- `‖a - b‖ ≤ 2K (‖M - Mₖ‖ (1 + ‖b‖) + ‖Mₖ a - M b‖)` once `K ‖M - Mₖ‖ ≤ 1/2`
  have hev : ∀ᶠ k in atTop, (K : ℝ) * ‖M - Mk k‖ ≤ 1 / 2 := by
    have : Tendsto (fun k => (K : ℝ) * ‖M - Mk k‖) atTop (𝓝 ((K : ℝ) * 0)) := by
      apply Tendsto.const_mul
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hMk)
      simpa [norm_sub_rev] using this
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ k in atTop, ‖a k - b‖ ≤
      2 * K * (‖M - Mk k‖ * (1 + ‖b‖) + ‖Mk k (a k) - M b‖) := by
    filter_upwards [hev] with k hk
    have h1 : dist (a k) b ≤ K * dist (M (a k)) (M b) := hKa.le_mul_dist (a k) b
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 : ‖M (a k) - M b‖ ≤ ‖M - Mk k‖ * ‖a k‖ + ‖Mk k (a k) - M b‖ := by
      calc ‖M (a k) - M b‖ = ‖(M - Mk k) (a k) + (Mk k (a k) - M b)‖ := by
            congr 1; simp
        _ ≤ ‖(M - Mk k) (a k)‖ + ‖Mk k (a k) - M b‖ := norm_add_le _ _
        _ ≤ ‖M - Mk k‖ * ‖a k‖ + ‖Mk k (a k) - M b‖ := by
            gcongr; exact (M - Mk k).le_opNorm _
    have h3 : ‖a k‖ ≤ ‖a k - b‖ + ‖b‖ := by
      calc ‖a k‖ = ‖(a k - b) + b‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hn := norm_nonneg (M - Mk k)
    have hn2 := norm_nonneg (Mk k (a k) - M b)
    have hn3 := norm_nonneg b
    have hn4 := norm_nonneg (a k - b)
    nlinarith [mul_le_mul_of_nonneg_left h3 hn, mul_le_mul_of_nonneg_left h2 hKr.le]
  apply squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) hbound
  have hA : Tendsto (fun k => ‖M - Mk k‖) atTop (𝓝 0) := by
    simpa [norm_sub_rev] using (tendsto_iff_norm_sub_tendsto_zero.1 hMk)
  have hB : Tendsto (fun k => ‖Mk k (a k) - M b‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hlim
  have := ((hA.mul_const (1 + ‖b‖)).add hB).const_mul (2 * (K : ℝ))
  simpa using this

end FiniteEnergyPlane

/-! Wrappers publishing the (N) helper layers as standalone statements. -/

namespace FiniteEnergyPlane

open Metric Filter Topology

theorem tendsto_of_tendsto_apply_of_injective_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (M : ℂ →L[ℝ] F) (hM : Function.Injective M) (Mk : ℕ → ℂ →L[ℝ] F)
    (hMk : Tendsto Mk atTop (𝓝 M)) (a : ℕ → ℂ) (b : ℂ)
    (hlim : Tendsto (fun k => Mk k (a k)) atTop (𝓝 (M b))) :
    Tendsto a atTop (𝓝 b) :=
  lpfn_tendsto_of_tendsto_apply M hM Mk hMk a b hlim

theorem exists_equiv_hasStrictFDerivAt_exp_smul_sub_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (u₀ : ℂ → V 1) (hu₀ : ContDiff ℝ 1 u₀) (y : ℝ → V 1)
    (hy : IsReebTrajectory H y) (t₀ : ℝ) (h0 : u₀ 0 = y t₀)
    (htr : ∀ v : ℂ, v ≠ 0 → ∀ c : ℝ,
      fderiv ℝ (fun z => proj H (u₀ z)) 0 v ≠ c • reeb H (proj H (u₀ 0))) :
    ∃ L : (ℝ × ℂ × ℝ) ≃L[ℝ] V 1,
      (∀ q : ℝ × ℂ × ℝ, L q = (2 * q.1) • u₀ 0 + fderiv ℝ u₀ 0 q.2.1 - q.2.2 • reeb H (u₀ 0)) ∧
      HasStrictFDerivAt (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • u₀ q.2.1 - y q.2.2)
        (L : ℝ × ℂ × ℝ →L[ℝ] V 1) ((0 : ℝ), (0 : ℂ), t₀) := by
  have hS : u₀ 0 ∈ energySurface H := h0 ▸ hy.1 t₀
  obtain ⟨L, hL⟩ := lpfn_exists_equiv H hH u₀ (hu₀.differentiable (by norm_num) 0) hS htr
  refine ⟨L, fun q => ?_, ?_⟩
  · rw [← lpfnL_apply, ← hL]; rfl
  · rw [hL]; exact lpfn_hasStrictFDerivAt H hH u₀ hu₀ y hy t₀ h0

theorem tendstoUniformlyOn_fderiv_exp_smul_sub_aux (u₀ : ℂ → V 1) (hu₀ : ContDiff ℝ 1 u₀)
    (v : ℕ → ℂ → V 1) (hv : ∀ k, ContDiff ℝ 1 (v k))
    (hlim : JHolomorphic.TendstoCInftyLocOn v u₀ Set.univ) (t₀ : ℝ) :
    (∀ k, ∀ q : ℝ × ℂ × ℝ, DifferentiableAt ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) ∧
    Tendsto (fun k => Real.exp (2 * (0 : ℝ)) • (v k (0 : ℂ) - u₀ 0)) atTop (𝓝 0) ∧
    TendstoUniformlyOn (fun k q => fderiv ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) 0 atTop
      (ball ((0 : ℝ), (0 : ℂ), t₀) 1) :=
  lpfn_perturbation u₀ hu₀ v hv hlim t₀

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology

theorem solution (u₀ : ℂ → V 1) (hu₀ : ContDiff ℝ 1 u₀)
    (v : ℕ → ℂ → V 1) (hv : ∀ k, ContDiff ℝ 1 (v k))
    (hlim : JHolomorphic.TendstoCInftyLocOn v u₀ Set.univ) (t₀ : ℝ) :
    (∀ k, ∀ q : ℝ × ℂ × ℝ, DifferentiableAt ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) ∧
    Tendsto (fun k => Real.exp (2 * (0 : ℝ)) • (v k (0 : ℂ) - u₀ 0)) atTop (𝓝 0) ∧
    TendstoUniformlyOn (fun k q => fderiv ℝ
      (fun q : ℝ × ℂ × ℝ => Real.exp (2 * q.1) • (v k q.2.1 - u₀ q.2.1)) q) 0 atTop
      (ball ((0 : ℝ), (0 : ℂ), t₀) 1) :=
  tendstoUniformlyOn_fderiv_exp_smul_sub_aux u₀ hu₀ v hv hlim t₀
