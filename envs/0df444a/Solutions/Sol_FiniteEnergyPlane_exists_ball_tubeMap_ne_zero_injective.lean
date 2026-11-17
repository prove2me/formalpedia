-- Prove2me | solution 1 for FiniteEnergyPlane.exists_ball_tubeMap_ne_zero_injective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T11:01:50.1012+00:00
-- url     : https://prove2.me/submissions/01ff59d3-31de-45bd-b3c8-17b4cc63a85f

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_triangular_iff
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_isInXi_linearizedReeb_deriv
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_sub_model
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_fderiv_sub_model

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

/-! Linear algebra of Hryniewicz's global frame `Z₁, Z₂` of `ξ` (copied from the
`exists_prime_periodicOrbit_cover` solution, renamed `r26_*`). -/

namespace HryniewiczCriterion

open scoped ContDiff

lemma r26_clm_apply_eq_sum (L : R4 →L[ℝ] ℝ) (v : R4) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) +
      v 2 * L (Pi.single 2 1) + v 3 * L (Pi.single 3 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, Fin.sum_univ_four, smul_eq_mul]

lemma r26_omega0_X_right (H : R4 → ℝ) (y p : R4) :
    omega0 p (hamiltonianVectorField H y) = fderiv ℝ H y p := by
  rw [r26_clm_apply_eq_sum (fderiv ℝ H y) p]
  simp [omega0, hamiltonianVectorField, partialDeriv]

lemma r26_omega0_antisymm (u v : R4) : omega0 u v = -omega0 v u := by
  simp [omega0]; ring

lemma r26_omega0_self (u : R4) : omega0 u u = 0 := by
  simp [omega0]; ring

lemma r26_omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma r26_omega0_lin_left (u a b : R4) (p q : ℝ) :
    omega0 (p • a + q • b) u = p * omega0 a u + q * omega0 b u := by
  simp [omega0]; ring

lemma r26_omega0_lin_right2 (u a b : R4) (p q : ℝ) :
    omega0 u (p • a + q • b) = p * omega0 u a + q * omega0 u b := by
  simp [omega0]; ring

lemma r26_omega0_smul_left (u v : R4) (p : ℝ) : omega0 (p • u) v = p * omega0 u v := by
  simp [omega0]; ring

lemma r26_omega0_smul_right (u v : R4) (p : ℝ) : omega0 u (p • v) = p * omega0 u v := by
  simp [omega0]; ring

lemma r26_eq_frame_of_omega0 (Z₁ Z₂ a b v : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0) :
    v = omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set w : Fin 4 → R4 := ![Z₁, Z₂, a, b] with hw
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    replace hg : g 0 • Z₁ + g 1 • Z₂ + g 2 • a + g 3 • b = 0 := by
      simpa [Fin.sum_univ_four, hw] using hg
    have e1 := congrArg (omega0 Z₁) hg
    have e2 := congrArg (omega0 Z₂) hg
    have e3 := congrArg (omega0 a) hg
    have e4 := congrArg (omega0 b) hg
    rw [r26_omega0_lin_right] at e1 e2 e3 e4
    have z : ∀ u : R4, omega0 u 0 = 0 := fun u => by simp [omega0]
    rw [z] at e1 e2 e3 e4
    rw [r26_omega0_self, h12, h1a, h1b] at e1
    rw [r26_omega0_antisymm Z₂ Z₁, h12, r26_omega0_self, h2a, h2b] at e2
    rw [r26_omega0_antisymm a Z₁, r26_omega0_antisymm a Z₂, h1a, h2a, r26_omega0_self] at e3
    rw [r26_omega0_antisymm b Z₁, r26_omega0_antisymm b Z₂, r26_omega0_antisymm b a, h1b, h2b,
      r26_omega0_self] at e4
    have g1 : g 1 = 0 := by linarith
    have g0 : g 0 = 0 := by linarith
    have g3 : g 3 = 0 := by
      have : g 3 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    have g2 : g 2 = 0 := by
      have : g 2 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    intro i; fin_cases i <;> assumption
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℝ (Set.range w) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  replace hc : c 0 • Z₁ + c 1 • Z₂ + c 2 • a + c 3 • b = v := by
    simpa [Fin.sum_univ_four, hw] using hc
  have ea : omega0 v a = c 0 * omega0 Z₁ a + c 1 * omega0 Z₂ a + c 2 * omega0 a a +
      c 3 * omega0 b a := by
    rw [← hc, r26_omega0_antisymm, r26_omega0_lin_right]
    rw [r26_omega0_antisymm a Z₁, r26_omega0_antisymm a Z₂, r26_omega0_antisymm a b,
      r26_omega0_self]; ring
  have eb : omega0 v b = c 0 * omega0 Z₁ b + c 1 * omega0 Z₂ b + c 2 * omega0 a b +
      c 3 * omega0 b b := by
    rw [← hc, r26_omega0_antisymm, r26_omega0_lin_right]
    rw [r26_omega0_antisymm b Z₁, r26_omega0_antisymm b Z₂, r26_omega0_antisymm b a,
      r26_omega0_self]; ring
  rw [h1a, h2a, r26_omega0_self, r26_omega0_antisymm b a, hva] at ea
  rw [h1b, h2b, r26_omega0_self, hvb] at eb
  have c3 : c 3 = 0 := by
    have : c 3 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have c2 : c 2 = 0 := by
    have : c 2 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have hv2 : v = c 0 • Z₁ + c 1 • Z₂ := by rw [← hc, c2, c3]; simp
  have k0 : omega0 v Z₂ = c 0 := by
    rw [hv2, r26_omega0_lin_left, r26_omega0_self, h12]; ring
  have k1 : omega0 Z₁ v = c 1 := by
    rw [hv2, r26_omega0_antisymm, r26_omega0_lin_left, r26_omega0_self,
      r26_omega0_antisymm Z₂ Z₁, h12]; ring
  rw [k0, k1]; exact hv2

variable {H : R4 → ℝ}

lemma r26_ne_zero_of_dH_pos {y : R4} (hy : 0 < fderiv ℝ H y y) : y ≠ 0 := by
  rintro rfl; simp at hy

lemma r26_dot4_pos {y : R4} (hy : y ≠ 0) : 0 < dot4 y y := by
  by_contra h
  push_neg at h
  apply hy
  have hs : ∀ i, y i * y i = 0 := by
    intro i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ y j * y j := fun j _ => mul_self_nonneg _
    have hsum : ∑ j, y j * y j = 0 := le_antisymm h (Finset.sum_nonneg hnn)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  ext i; simpa using hs i

lemma r26_euclidNorm_sq (y : R4) : euclidNorm y * euclidNorm y = dot4 y y := by
  have : 0 ≤ dot4 y y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
  exact Real.mul_self_sqrt this

lemma r26_dH_xiFrameRaw {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    fderiv ℝ H y (xiFrameRaw H Q y) = 0 := by
  simp only [xiFrameRaw, map_sub, map_smul, smul_eq_mul]
  field_simp; ring

lemma r26_omega0_xiFrameRaw_self (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) (y : R4) :
    omega0 y (xiFrameRaw H Q y) = 0 := by
  have := hQ y
  simp only [xiFrameRaw, omega0] at this ⊢
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination this

lemma r26_omega0_quatQ1 (y : R4) : omega0 y (quatQ1 y) = 0 := by
  simp [omega0, quatQ1]; ring

lemma r26_omega0_quatQ2 (y : R4) : omega0 y (quatQ2 y) = 0 := by
  simp [omega0, quatQ2]; ring

lemma r26_omega0_raw21 (y : R4) :
    omega0 (xiFrameRaw H quatQ2 y) (xiFrameRaw H quatQ1 y) = dot4 y y := by
  simp [xiFrameRaw, omega0, quatQ1, quatQ2, dot4, Fin.sum_univ_four]; ring

lemma r26_omega0_xiFrame12 {y : R4} (hy : 0 < fderiv ℝ H y y) :
    omega0 (xiFrame1 H y) (xiFrame2 H y) = 1 := by
  have hpos := r26_dot4_pos (r26_ne_zero_of_dH_pos hy)
  have hn := r26_euclidNorm_sq y
  have hne : euclidNorm y ≠ 0 := by
    intro h; rw [h] at hn; linarith
  rw [xiFrame1, xiFrame2, r26_omega0_smul_left, r26_omega0_smul_right, r26_omega0_raw21, ← hn]
  field_simp

/-- `ω₀(y, Zᵢ) = 0`. -/
lemma r26_omega0_y_xiFrame (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) (y : R4) :
    omega0 y ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) = 0 := by
  rw [r26_omega0_smul_right, r26_omega0_xiFrameRaw_self Q hQ y, mul_zero]

/-- `dH(Zᵢ) = 0`. -/
lemma r26_dH_xiFrame {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    fderiv ℝ H y ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) = 0 := by
  rw [map_smul, r26_dH_xiFrameRaw hy, smul_zero]

lemma r26_cd_omega0 {p q : ℝ → R4} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun τ => omega0 (p τ) (q τ)) := by
  have h := fun i => contDiff_pi.1 hp i
  have k := fun i => contDiff_pi.1 hq i
  simp only [omega0]
  exact ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
    ((h 3).mul (k 2))

lemma r26_cd_dH (hH : ContDiff ℝ ∞ H) {c v : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (fun τ => fderiv ℝ H (c τ) (v τ)) :=
  ((hH.fderiv_right le_rfl).comp hc).clm_apply hv

lemma r26_cd_quatQ1 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ1 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ1] <;> first | exact h _ | exact (h _).neg

lemma r26_cd_quatQ2 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ2 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ2] <;> first | exact h _ | exact (h _).neg

lemma r26_cd_xiFrame (hH : ContDiff ℝ ∞ H) {c : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ τ, 0 < fderiv ℝ H (c τ) (c τ)) (Q : R4 → R4)
    (hQ : ContDiff ℝ ∞ (fun τ => Q (c τ))) :
    ContDiff ℝ ∞ (fun τ => (euclidNorm (c τ))⁻¹ • xiFrameRaw H Q (c τ)) := by
  have hraw : ContDiff ℝ ∞ (fun τ => xiFrameRaw H Q (c τ)) :=
    hQ.sub (((r26_cd_dH hH hc hQ).div (r26_cd_dH hH hc hc) fun τ => (hpos τ).ne').smul hc)
  have hdot : ContDiff ℝ ∞ (fun τ => dot4 (c τ) (c τ)) := by
    have h := fun i => contDiff_pi.1 hc i
    simp only [dot4, Fin.sum_univ_four]
    exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add
      ((h 3).mul (h 3))
  have hdne : ∀ τ, dot4 (c τ) (c τ) ≠ 0 := fun τ =>
    (r26_dot4_pos (r26_ne_zero_of_dH_pos (hpos τ))).ne'
  have hnorm : ContDiff ℝ ∞ (fun τ => euclidNorm (c τ)) := hdot.sqrt hdne
  have hnne : ∀ τ, euclidNorm (c τ) ≠ 0 := fun τ h => by
    have := r26_euclidNorm_sq (c τ); rw [h] at this; exact hdne τ (by linarith)
  exact (hnorm.inv hnne).smul hraw

end HryniewiczCriterion

namespace FiniteEnergyPlane

open scoped ContDiff

lemma r26_omega0_eq (u v : V 1) : omega0 u v = HryniewiczCriterion.omega0 u v := by
  simp [omega0, HryniewiczCriterion.omega0, dot, j0, Fin.sum_univ_four]; ring

lemma r26_omega0_bilin (a b c d : HryniewiczCriterion.R4) (p q r s : ℝ) :
    HryniewiczCriterion.omega0 (p • a + q • b) (r • c + s • d) =
      p * r * HryniewiczCriterion.omega0 a c + p * s * HryniewiczCriterion.omega0 a d +
      q * r * HryniewiczCriterion.omega0 b c + q * s * HryniewiczCriterion.omega0 b d := by
  simp [HryniewiczCriterion.omega0]; ring

lemma r26_J0_inl (a : CauchyRiemannIndex.Vec 1) :
    Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a (Sum.inl 0) = -a (Sum.inr 0) := by
  simp [Matrix.J, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Matrix.fromBlocks]

lemma r26_J0_inr (a : CauchyRiemannIndex.Vec 1) :
    Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a (Sum.inr 0) = a (Sum.inl 0) := by
  simp [Matrix.J, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Matrix.fromBlocks]

lemma r26_isInXi_comb {H : V 1 → ℝ} {x u v : V 1} (hu : IsInXi H x u) (hv : IsInXi H x v)
    (p q : ℝ) : IsInXi H x (p • u + q • v) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [liouville, r26_omega0_eq] at hu1 hv1 ⊢
    have e : HryniewiczCriterion.omega0 x (p • u + q • v) =
        p * HryniewiczCriterion.omega0 x u + q * HryniewiczCriterion.omega0 x v := by
      simp [HryniewiczCriterion.omega0]; ring
    rw [e]
    have h1 : HryniewiczCriterion.omega0 x u = 0 := by linarith
    have h2 : HryniewiczCriterion.omega0 x v = 0 := by linarith
    rw [h1, h2]; simp
  · rw [map_add, map_smul, map_smul, hu2, hv2]; simp

/-! ### The frame at a point of `S` -/

/-- `Z₁(x)`, the first vector of the global frame. -/
noncomputable def r26e (H : V 1 → ℝ) (x : V 1) : V 1 := HryniewiczCriterion.xiFrame1 H x

/-- `β(x) = ω₀(Z₁, J Z₁)`. -/
noncomputable def r26β (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) : ℝ :=
  HryniewiczCriterion.omega0 (r26e H x) (J x (r26e H x))

/-- `W = β^{-1/2} Z₁`. -/
noncomputable def r26W (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) : V 1 :=
  (Real.sqrt (r26β H J x))⁻¹ • r26e H x

/-- `Z(x) a = a₁ W + a₂ J W`. -/
noncomputable def r26ZAt (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) :
    CauchyRiemannIndex.Vec 1 →L[ℝ] V 1 :=
  (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).smulRight (r26W H J x) +
    (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).smulRight (J x (r26W H J x))

lemma r26ZAt_apply (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1)
    (a : CauchyRiemannIndex.Vec 1) :
    r26ZAt H J x a = a (Sum.inl 0) • r26W H J x + a (Sum.inr 0) • J x (r26W H J x) := by
  simp [r26ZAt]

section point

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J) {x : V 1} (hx : H x = 1)

include hH hx in
lemma r26_pos : 0 < fderiv ℝ H x x := hH.2.2 x hx

include hH hx in
lemma r26_e12 : HryniewiczCriterion.omega0 (r26e H x) (HryniewiczCriterion.xiFrame2 H x) = 1 :=
  HryniewiczCriterion.r26_omega0_xiFrame12 (r26_pos hH hx)

include hH hx in
lemma r26_e_xi : IsInXi H x (r26e H x) := by
  refine ⟨?_, ?_⟩
  · rw [liouville, r26_omega0_eq, r26e, HryniewiczCriterion.xiFrame1,
      HryniewiczCriterion.r26_omega0_y_xiFrame _ HryniewiczCriterion.r26_omega0_quatQ2]
    simp
  · exact HryniewiczCriterion.r26_dH_xiFrame (r26_pos hH hx) _

include hH hx in
lemma r26_e2_xi : IsInXi H x (HryniewiczCriterion.xiFrame2 H x) := by
  refine ⟨?_, ?_⟩
  · rw [liouville, r26_omega0_eq, HryniewiczCriterion.xiFrame2,
      HryniewiczCriterion.r26_omega0_y_xiFrame _ HryniewiczCriterion.r26_omega0_quatQ1]
    simp
  · exact HryniewiczCriterion.r26_dH_xiFrame (r26_pos hH hx) _

include hH hx in
/-- Every `w ∈ ξ_x` is `ω₀(w, Z₂) Z₁ + ω₀(Z₁, w) Z₂`. -/
lemma r26_decomp {w : V 1} (hw : IsInXi H x w) :
    w = HryniewiczCriterion.omega0 w (HryniewiczCriterion.xiFrame2 H x) • r26e H x +
      HryniewiczCriterion.omega0 (r26e H x) w • HryniewiczCriterion.xiFrame2 H x := by
  have hpos := r26_pos hH hx
  have xi_a : ∀ v, IsInXi H x v → HryniewiczCriterion.omega0 v x = 0 := by
    intro v hv
    have := hv.1
    rw [liouville, r26_omega0_eq] at this
    rw [HryniewiczCriterion.r26_omega0_antisymm]; linarith
  have xi_b : ∀ v, IsInXi H x v →
      HryniewiczCriterion.omega0 v (HryniewiczCriterion.hamiltonianVectorField H x) = 0 := by
    intro v hv
    rw [HryniewiczCriterion.r26_omega0_X_right]; exact hv.2
  have := HryniewiczCriterion.r26_eq_frame_of_omega0 (r26e H x) (HryniewiczCriterion.xiFrame2 H x)
    x (HryniewiczCriterion.hamiltonianVectorField H x) w (r26_e12 hH hx)
    (xi_a _ (r26_e_xi hH hx)) (xi_b _ (r26_e_xi hH hx)) (xi_a _ (r26_e2_xi hH hx))
    (xi_b _ (r26_e2_xi hH hx))
    (by rw [HryniewiczCriterion.r26_omega0_X_right]; exact hpos.ne') (xi_a _ hw) (xi_b _ hw)
  exact this

include hH hJ hx in
lemma r26_β_pos : 0 < r26β H J x := by
  have h := (hJ.2 x hx _ _ (r26_e_xi hH hx) (r26_e_xi hH hx)).2.2.1
  have hne : r26e H x ≠ 0 := by
    intro h0
    have := r26_e12 hH hx
    rw [h0] at this; simp [HryniewiczCriterion.omega0] at this
  have := h hne
  rw [r26_omega0_eq] at this
  exact this

include hH hJ hx in
lemma r26_W_xi : IsInXi H x (r26W H J x) := by
  have := r26_isInXi_comb (r26_e_xi hH hx) (r26_e_xi hH hx) (Real.sqrt (r26β H J x))⁻¹ 0
  simpa [r26W] using this

include hH hJ hx in
lemma r26_JW_xi : IsInXi H x (J x (r26W H J x)) :=
  (hJ.2 x hx _ _ (r26_W_xi hH hJ hx) (r26_W_xi hH hJ hx)).1

include hH hJ hx in
lemma r26_JJW : J x (J x (r26W H J x)) = -r26W H J x :=
  (hJ.2 x hx _ _ (r26_W_xi hH hJ hx) (r26_W_xi hH hJ hx)).2.1

include hH hJ hx in
lemma r26_sqrt_pos : 0 < Real.sqrt (r26β H J x) := Real.sqrt_pos.2 (r26_β_pos hH hJ hx)

include hH hJ hx in
lemma r26_W_JW : HryniewiczCriterion.omega0 (r26W H J x) (J x (r26W H J x)) = 1 := by
  have hs := r26_sqrt_pos hH hJ hx
  have hss : Real.sqrt (r26β H J x) * Real.sqrt (r26β H J x) = r26β H J x :=
    Real.mul_self_sqrt (r26_β_pos hH hJ hx).le
  rw [r26W, map_smul, HryniewiczCriterion.r26_omega0_smul_left,
    HryniewiczCriterion.r26_omega0_smul_right]
  change _ * (_ * r26β H J x) = 1
  rw [inv_mul_eq_div (Real.sqrt _) (r26β H J x), Real.div_sqrt]
  exact inv_mul_cancel₀ hs.ne'

include hH hJ hx in
lemma r26_unitary_xi (a : CauchyRiemannIndex.Vec 1) : IsInXi H x (r26ZAt H J x a) := by
  rw [r26ZAt_apply]; exact r26_isInXi_comb (r26_W_xi hH hJ hx) (r26_JW_xi hH hJ hx) _ _

include hH hJ hx in
lemma r26_unitary_surj (w : V 1) (hw : IsInXi H x w) :
    ∃ a, r26ZAt H J x a = w := by
  set e := r26e H x
  set e2 := HryniewiczCriterion.xiFrame2 H x
  set s := Real.sqrt (r26β H J x)
  set β := r26β H J x
  have hs := r26_sqrt_pos hH hJ hx
  have hβ := r26_β_pos hH hJ hx
  have hJe := r26_decomp hH hx ((hJ.2 x hx _ _ (r26_e_xi hH hx) (r26_e_xi hH hx)).1)
  have hβdef : HryniewiczCriterion.omega0 e (J x e) = β := rfl
  rw [hβdef] at hJe
  set α := HryniewiczCriterion.omega0 (J x e) e2
  set p := HryniewiczCriterion.omega0 w e2
  set q := HryniewiczCriterion.omega0 e w
  have hw' := r26_decomp hH hx hw
  have hβ0 : β ≠ 0 := hβ.ne'
  have hs0 : s ≠ 0 := hs.ne'
  refine ⟨(WithLp.equiv 2 (Fin 1 ⊕ Fin 1 → ℝ)).symm
    (Sum.elim (fun _ => s * (p - q * α / β)) (fun _ => s * q / β)), ?_⟩
  rw [r26ZAt_apply]
  simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, Sum.elim_inl, Sum.elim_inr]
  rw [r26W, map_smul, hJe]
  conv_rhs => rw [hw']
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

include hH hJ hx in
lemma r26_unitary_J (a : CauchyRiemannIndex.Vec 1) :
    J x (r26ZAt H J x a) =
      r26ZAt H J x (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) := by
  rw [r26ZAt_apply, r26ZAt_apply, r26_J0_inl, r26_J0_inr, map_add, map_smul, map_smul,
    r26_JJW hH hJ hx]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

include hH hJ hx in
lemma r26_unitary_omega (a b : CauchyRiemannIndex.Vec 1) :
    omega0 (r26ZAt H J x a) (r26ZAt H J x b) =
      inner ℝ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) b := by
  rw [r26_omega0_eq, r26ZAt_apply, r26ZAt_apply, r26_omega0_bilin,
    HryniewiczCriterion.r26_omega0_self, HryniewiczCriterion.r26_omega0_self,
    HryniewiczCriterion.r26_omega0_antisymm (J x _) (r26W H J x), r26_W_JW hH hJ hx]
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_one, r26_J0_inl, r26_J0_inr,
    RCLike.inner_apply, conj_trivial]
  ring

include hH hJ hx in
lemma r26_coord (a : CauchyRiemannIndex.Vec 1) :
    xiCoordC H x (r26ZAt H J x a) =
      ((((Real.sqrt (r26β H J x))⁻¹ * a (Sum.inl 0) +
        (Real.sqrt (r26β H J x))⁻¹ *
          HryniewiczCriterion.omega0 (J x (r26e H x)) (HryniewiczCriterion.xiFrame2 H x) *
            a (Sum.inr 0) : ℝ)) : ℂ) +
        ((Real.sqrt (r26β H J x) * a (Sum.inr 0) : ℝ) : ℂ) * Complex.I := by
  have hs := r26_sqrt_pos hH hJ hx
  have hss : Real.sqrt (r26β H J x) * Real.sqrt (r26β H J x) = r26β H J x :=
    Real.mul_self_sqrt (r26_β_pos hH hJ hx).le
  have h12 := r26_e12 hH hx
  have hc : xiCoordC H x (r26ZAt H J x a) =
      ⟨HryniewiczCriterion.omega0 (r26ZAt H J x a) (HryniewiczCriterion.xiFrame2 H x),
        HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H x) (r26ZAt H J x a)⟩ := rfl
  rw [hc]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    rw [r26ZAt_apply, HryniewiczCriterion.r26_omega0_lin_left, r26W, map_smul,
      HryniewiczCriterion.r26_omega0_smul_left, HryniewiczCriterion.r26_omega0_smul_left,
      h12]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    change HryniewiczCriterion.omega0 (r26e H x) _ = _
    rw [r26ZAt_apply, HryniewiczCriterion.r26_omega0_lin_right2, r26W, map_smul,
      HryniewiczCriterion.r26_omega0_smul_right, HryniewiczCriterion.r26_omega0_smul_right,
      HryniewiczCriterion.r26_omega0_self]
    change _ * (_ * 0) + _ * (_ * r26β H J x) = _
    rw [inv_mul_eq_div (Real.sqrt _) (r26β H J x), Real.div_sqrt]
    ring

end point

theorem exists_unitaryXiFrame_hasXiLoopWind_iff_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J P Z ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k) := by
  set c : ℝ → V 1 := fun t => P.x (P.T * t) with hcdef
  have hc : ContDiff ℝ ∞ c := (ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_id)
  have hcper : ∀ t, c (t + 1) = c t := fun t => by
    simp only [hcdef, mul_add, mul_one, P.periodic]
  have hcS : ∀ t, H (c t) = 1 := fun t => P.mem _
  have hpos : ∀ t, 0 < fderiv ℝ H (c t) (c t) := fun t => r26_pos hH (hcS t)
  have he : ContDiff ℝ ∞ (fun t => r26e H (c t)) :=
    HryniewiczCriterion.r26_cd_xiFrame hH.1 hc hpos HryniewiczCriterion.quatQ2
      (HryniewiczCriterion.r26_cd_quatQ2 hc)
  have he2 : ContDiff ℝ ∞ (fun t => HryniewiczCriterion.xiFrame2 H (c t)) :=
    HryniewiczCriterion.r26_cd_xiFrame hH.1 hc hpos HryniewiczCriterion.quatQ1
      (HryniewiczCriterion.r26_cd_quatQ1 hc)
  have hJc : ContDiff ℝ ∞ (fun t => J (c t)) := hJ.1.comp hc
  have hβ : ContDiff ℝ ∞ (fun t => r26β H J (c t)) :=
    HryniewiczCriterion.r26_cd_omega0 he (hJc.clm_apply he)
  have hs : ContDiff ℝ ∞ (fun t => Real.sqrt (r26β H J (c t))) :=
    hβ.sqrt (fun t => (r26_β_pos hH hJ (hcS t)).ne')
  have hsinv : ContDiff ℝ ∞ (fun t => (Real.sqrt (r26β H J (c t)))⁻¹) :=
    hs.inv (fun t => (r26_sqrt_pos hH hJ (hcS t)).ne')
  have hW : ContDiff ℝ ∞ (fun t => r26W H J (c t)) := hsinv.smul he
  have hJW : ContDiff ℝ ∞ (fun t => J (c t) (r26W H J (c t))) := hJc.clm_apply hW
  have hb : ContDiff ℝ ∞ (fun t => (Real.sqrt (r26β H J (c t)))⁻¹ *
      HryniewiczCriterion.omega0 (J (c t) (r26e H (c t))) (HryniewiczCriterion.xiFrame2 H (c t))) :=
    hsinv.mul (HryniewiczCriterion.r26_cd_omega0 (hJc.clm_apply he) he2)
  refine ⟨fun t => r26ZAt H J (c t), ⟨?_, ?_, fun t => ⟨r26_unitary_xi hH hJ (hcS t),
    r26_unitary_surj hH hJ (hcS t), r26_unitary_J hH hJ (hcS t),
    r26_unitary_omega hH hJ (hcS t)⟩⟩, ?_⟩
  · exact (contDiff_const.smulRight hW).add (contDiff_const.smulRight hJW)
  · intro t; simp only [hcper]
  · intro ζ hζ hζp hζ0 k
    have h1 : Continuous fun t => ζ t (Sum.inl 0) :=
      (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).continuous.comp hζ
    have h2 : Continuous fun t => ζ t (Sum.inr 0) :=
      (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).continuous.comp hζ
    have hzeq : (fun t => vecToC (ζ t)) = fun t => ((ζ t (Sum.inl 0) : ℝ) : ℂ) +
        ((ζ t (Sum.inr 0) : ℝ) : ℂ) * Complex.I :=
      funext fun t => Complex.ext (by simp [vecToC]) (by simp [vecToC])
    have hz : Continuous (fun t => vecToC (ζ t)) := by rw [hzeq]; fun_prop
    have hzp : Function.Periodic (fun t => vecToC (ζ t)) 1 := fun t => by
      simp only [hζp t]
    have hz0 : ∀ t, vecToC (ζ t) ≠ 0 := by
      intro t h
      apply hζ0 t
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [vecToC, Complex.zero_re, Complex.zero_im] at hre him
      ext i
      rcases i with i | i <;> fin_cases i
      · simpa using hre
      · simpa using him
    have hA := hasLoopWind_triangular_iff hsinv.continuous hb.continuous hs.continuous
      (fun t => by simp only [hcper]) (fun t => by simp only [hcper])
      (fun t => by simp only [hcper])
      (fun t => inv_pos.2 (r26_sqrt_pos hH hJ (hcS t))) (fun t => r26_sqrt_pos hH hJ (hcS t))
      hz hzp hz0 k
    have hfun : (fun t => xiCoordC H (P.x (P.T * t)) (r26ZAt H J (c t) (ζ t))) =
        fun t => (((Real.sqrt (r26β H J (c t)))⁻¹ * (vecToC (ζ t)).re +
          (Real.sqrt (r26β H J (c t)))⁻¹ *
            HryniewiczCriterion.omega0 (J (c t) (r26e H (c t)))
              (HryniewiczCriterion.xiFrame2 H (c t)) * (vecToC (ζ t)).im : ℝ) : ℂ) +
          ((Real.sqrt (r26β H J (c t)) * (vecToC (ζ t)).im : ℝ) : ℂ) * Complex.I := by
      funext t
      exact r26_coord hH hJ (hcS t) (ζ t)
    unfold HasXiLoopWind
    rw [hfun]
    exact hA

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

section
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- The linearized Cauchy–Riemann operator along `y` in the directions `e₁, e₂`:
`∂₁W + Jt(y) ∂₂W + (DJt(y) W) ∂₂y`. -/
noncomputable def linDbar (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (y W : D → E) (z : D) : E :=
  fderiv ℝ W z e₁ + Jt (y z) (fderiv ℝ W z e₂) + fderiv ℝ Jt (y z) (W z) (fderiv ℝ y z e₂)

lemma linDbar_add (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (y W₁ W₂ : D → E) (z : D)
    (h₁ : DifferentiableAt ℝ W₁ z) (h₂ : DifferentiableAt ℝ W₂ z) :
    linDbar Jt e₁ e₂ y (fun q => W₁ q + W₂ q) z =
      linDbar Jt e₁ e₂ y W₁ z + linDbar Jt e₁ e₂ y W₂ z := by
  unfold linDbar
  rw [fderiv_fun_add h₁ h₂]
  simp only [ContinuousLinearMap.add_apply, map_add]
  abel

lemma linDbar_smul (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (y W : D → E) (f : D → ℝ) (z : D)
    (hf : DifferentiableAt ℝ f z) (hW : DifferentiableAt ℝ W z) :
    linDbar Jt e₁ e₂ y (fun q => f q • W q) z =
      f z • linDbar Jt e₁ e₂ y W z + fderiv ℝ f z e₁ • W z +
        fderiv ℝ f z e₂ • Jt (y z) (W z) := by
  unfold linDbar
  rw [fderiv_fun_smul hf hW]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_add]
  abel

/-- Linearization of the Cauchy–Riemann equation along a `C²` family. -/
theorem linDbar_eq_zero_of_family (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (G : D × ℝ → E) (z₀ : D) (τ₀ : ℝ)
    (hG : ContDiffAt ℝ 2 G (z₀, τ₀)) (hJt : DifferentiableAt ℝ Jt (G (z₀, τ₀)))
    (hhol : ∀ᶠ q in 𝓝 (z₀, τ₀),
      fderiv ℝ G q (e₁, 0) + Jt (G q) (fderiv ℝ G q (e₂, 0)) = 0) :
    linDbar Jt e₁ e₂ (fun z => G (z, τ₀)) (fun z => fderiv ℝ G (z, τ₀) (0, 1)) z₀ = 0 := by
  set q₀ : D × ℝ := (z₀, τ₀) with hq₀
  have hGd : DifferentiableAt ℝ G q₀ := hG.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ G) q₀ :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : ∀ a b, fderiv ℝ (fderiv ℝ G) q₀ a b = fderiv ℝ (fderiv ℝ G) q₀ b a := by
    have := hG.isSymmSndFDerivAt (by simp)
    exact fun a b => this a b
  have hinc : ∀ z : D, HasFDerivAt (fun z => (z, τ₀)) (ContinuousLinearMap.inl ℝ D ℝ) z :=
    fun z => (hasFDerivAt_id z).prodMk (hasFDerivAt_const τ₀ z)
  -- the slice derivative of `G`
  have hy : fderiv ℝ (fun z => G (z, τ₀)) z₀ = (fderiv ℝ G q₀).comp (ContinuousLinearMap.inl ℝ D ℝ) :=
    (hGd.hasFDerivAt.comp z₀ (hinc z₀)).fderiv
  -- the slice derivative of `∂_τ G`
  have hW : HasFDerivAt (fun z => fderiv ℝ G (z, τ₀) ((0 : D), (1 : ℝ)))
      (((fderiv ℝ (fderiv ℝ G) q₀).comp (ContinuousLinearMap.inl ℝ D ℝ)).flip ((0 : D), (1 : ℝ))) z₀ := by
    have h1 : HasFDerivAt (fun z => fderiv ℝ G (z, τ₀))
        ((fderiv ℝ (fderiv ℝ G) q₀).comp (ContinuousLinearMap.inl ℝ D ℝ)) z₀ :=
      hD.hasFDerivAt.comp z₀ (hinc z₀)
    have := h1.clm_apply (hasFDerivAt_const (((0 : D), (1 : ℝ))) z₀)
    convert this using 1
    ext1 v
    simp
  -- differentiate the equation along `∂_τ`
  set A : D × ℝ → E := fun q => fderiv ℝ G q (e₁, 0) + Jt (G q) (fderiv ℝ G q (e₂, 0)) with hA
  have hA0 : A =ᶠ[𝓝 q₀] fun _ => 0 := hhol
  have hAd : HasFDerivAt A
      (((fderiv ℝ (fderiv ℝ G) q₀).flip (e₁, 0)) +
        ((fderiv ℝ Jt (G q₀)).comp (fderiv ℝ G q₀)).flip (fderiv ℝ G q₀ (e₂, 0)) +
          (Jt (G q₀)).comp ((fderiv ℝ (fderiv ℝ G) q₀).flip (e₂, 0))) q₀ := by
    have h1 := hD.hasFDerivAt.clm_apply (hasFDerivAt_const ((e₁, (0 : ℝ))) q₀)
    have h2 := hD.hasFDerivAt.clm_apply (hasFDerivAt_const ((e₂, (0 : ℝ))) q₀)
    have h3 : HasFDerivAt (fun q => Jt (G q)) ((fderiv ℝ Jt (G q₀)).comp (fderiv ℝ G q₀)) q₀ :=
      hJt.hasFDerivAt.comp q₀ hGd.hasFDerivAt
    have h4 := h3.clm_apply h2
    refine (h1.add h4).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [add_assoc, add_comm, add_left_comm]
  have h00 : (((fderiv ℝ (fderiv ℝ G) q₀).flip (e₁, 0)) +
        ((fderiv ℝ Jt (G q₀)).comp (fderiv ℝ G q₀)).flip (fderiv ℝ G q₀ (e₂, 0)) +
          (Jt (G q₀)).comp ((fderiv ℝ (fderiv ℝ G) q₀).flip (e₂, 0))) = 0 := by
    have h' : HasFDerivAt A (0 : D × ℝ →L[ℝ] E) q₀ :=
      (hasFDerivAt_const (0 : E) q₀).congr_of_eventuallyEq hA0
    exact hAd.unique h'
  have hval := DFunLike.congr_fun h00 ((0 : D), (1 : ℝ))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hval
  unfold linDbar
  rw [hW.fderiv, hy]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]
  rw [hsym (e₁, 0) (0, 1), hsym (e₂, 0) (0, 1)]
  rw [← hval]
  abel

/-- The coefficient identity of a solution of the linearized equation in a frame
`τ₁, τ₂ = J τ₁, F₁, F₂ = J F₁`. -/
theorem linDbar_frame_identity (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (y W τ₁ τ₂ F₁ F₂ : D → E)
    (f₁ f₂ n₁ n₂ : D → ℝ) (z : D)
    (hf₁ : DifferentiableAt ℝ f₁ z) (hf₂ : DifferentiableAt ℝ f₂ z)
    (hn₁ : DifferentiableAt ℝ n₁ z) (hn₂ : DifferentiableAt ℝ n₂ z)
    (hτ₁ : DifferentiableAt ℝ τ₁ z) (hτ₂ : DifferentiableAt ℝ τ₂ z)
    (hF₁ : DifferentiableAt ℝ F₁ z) (hF₂ : DifferentiableAt ℝ F₂ z)
    (hW : W =ᶠ[𝓝 z] fun q => f₁ q • τ₁ q + f₂ q • τ₂ q + n₁ q • F₁ q + n₂ q • F₂ q)
    (hL : linDbar Jt e₁ e₂ y W z = 0)
    (hLτ₁ : linDbar Jt e₁ e₂ y τ₁ z = 0) (hLτ₂ : linDbar Jt e₁ e₂ y τ₂ z = 0)
    (hJτ₁ : Jt (y z) (τ₁ z) = τ₂ z) (hJτ₂ : Jt (y z) (τ₂ z) = -τ₁ z)
    (hJF₁ : Jt (y z) (F₁ z) = F₂ z) (hJF₂ : Jt (y z) (F₂ z) = -F₁ z) :
    (fderiv ℝ f₁ z e₁ - fderiv ℝ f₂ z e₂) • τ₁ z + (fderiv ℝ f₁ z e₂ + fderiv ℝ f₂ z e₁) • τ₂ z +
      (fderiv ℝ n₁ z e₁ - fderiv ℝ n₂ z e₂) • F₁ z + (fderiv ℝ n₁ z e₂ + fderiv ℝ n₂ z e₁) • F₂ z +
      n₁ z • linDbar Jt e₁ e₂ y F₁ z + n₂ z • linDbar Jt e₁ e₂ y F₂ z = 0 := by
  have hcongr : linDbar Jt e₁ e₂ y W z = linDbar Jt e₁ e₂ y
      (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q + n₁ q • F₁ q + n₂ q • F₂ q) z := by
    unfold linDbar
    rw [hW.fderiv_eq, hW.self_of_nhds]
  rw [hcongr] at hL
  have d1 : DifferentiableAt ℝ (fun q => f₁ q • τ₁ q) z := hf₁.smul hτ₁
  have d2 : DifferentiableAt ℝ (fun q => f₂ q • τ₂ q) z := hf₂.smul hτ₂
  have d3 : DifferentiableAt ℝ (fun q => n₁ q • F₁ q) z := hn₁.smul hF₁
  have d4 : DifferentiableAt ℝ (fun q => n₂ q • F₂ q) z := hn₂.smul hF₂
  have d12 : DifferentiableAt ℝ (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q) z := d1.add d2
  have d123 : DifferentiableAt ℝ (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q + n₁ q • F₁ q) z := d12.add d3
  rw [linDbar_add Jt e₁ e₂ y (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q + n₁ q • F₁ q)
      (fun q => n₂ q • F₂ q) z d123 d4,
    linDbar_add Jt e₁ e₂ y (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q) (fun q => n₁ q • F₁ q) z d12 d3,
    linDbar_add Jt e₁ e₂ y (fun q => f₁ q • τ₁ q) (fun q => f₂ q • τ₂ q) z d1 d2,
    linDbar_smul Jt e₁ e₂ y _ _ z hf₁ hτ₁, linDbar_smul Jt e₁ e₂ y _ _ z hf₂ hτ₂,
    linDbar_smul Jt e₁ e₂ y _ _ z hn₁ hF₁, linDbar_smul Jt e₁ e₂ y _ _ z hn₂ hF₂,
    hLτ₁, hLτ₂, hJτ₁, hJτ₂, hJF₁, hJF₂] at hL
  refine Eq.trans ?_ hL
  simp only [smul_zero]
  module

end

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff

/-! ### A frame map on `V 1` and its inverse -/

/-- The four coordinate indices of `V 1`. -/
abbrev fi0 : Fin (2 * (1 + 1)) := ⟨0, by norm_num⟩
abbrev fi1 : Fin (2 * (1 + 1)) := ⟨1, by norm_num⟩
abbrev fi2 : Fin (2 * (1 + 1)) := ⟨2, by norm_num⟩
abbrev fi3 : Fin (2 * (1 + 1)) := ⟨3, by norm_num⟩

lemma fas_sum (f : Fin (2 * (1 + 1)) → ℝ) : ∑ k, f k = f fi0 + f fi1 + f fi2 + f fi3 :=
  Fin.sum_univ_four f

/-- `v ↦ v₀ a + v₁ b + v₂ c + v₃ d`. -/
noncomputable def fasB (a b c d : V 1) : V 1 →L[ℝ] V 1 :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ) fi0).smulRight a +
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ) fi1).smulRight b +
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ) fi2).smulRight c +
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ) fi3).smulRight d

lemma fasB_apply (a b c d v : V 1) :
    fasB a b c d v = v fi0 • a + v fi1 • b + v fi2 • c + v fi3 • d := by
  simp [fasB]

lemma fasB_contDiffAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {a b c d : X → V 1}
    {x : X} (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x)
    (hd : ContDiffAt ℝ ∞ d x) : ContDiffAt ℝ ∞ (fun y => fasB (a y) (b y) (c y) (d y)) x := by
  unfold fasB
  exact ((((contDiffAt_const.smulRight ha).add (contDiffAt_const.smulRight hb)).add
    (contDiffAt_const.smulRight hc)).add (contDiffAt_const.smulRight hd))

lemma fas_isUnit_of_injective (B : V 1 →L[ℝ] V 1) (h : Function.Injective B) : IsUnit B := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨h, (LinearMap.injective_iff_surjective (f := (B : V 1 →ₗ[ℝ] V 1))).1 h⟩

/-- The coordinates in an invertible frame. -/
noncomputable def fasC (a b c d : V 1) : V 1 →L[ℝ] V 1 := Ring.inverse (fasB a b c d)

section coords
variable {a b c d : V 1} (hB : IsUnit (fasB a b c d))
include hB

lemma fasC_expand (w : V 1) :
    (fasC a b c d w) fi0 • a + (fasC a b c d w) fi1 • b + (fasC a b c d w) fi2 • c +
      (fasC a b c d w) fi3 • d = w := by
  rw [← fasB_apply]
  have h : fasB a b c d * fasC a b c d = 1 := Ring.mul_inverse_cancel _ hB
  exact DFunLike.congr_fun h w

lemma fasC_comb (p q r s : ℝ) (i : Fin (2 * (1 + 1))) :
    fasC a b c d (p • a + q • b + r • c + s • d) i =
      (![p, q, r, s] : Fin 4 → ℝ) (Fin.cast (by norm_num) i) := by
  have hv : p • a + q • b + r • c + s • d =
      fasB a b c d (fun k => (![p, q, r, s] : Fin 4 → ℝ) (Fin.cast (by norm_num) k)) := by
    rw [fasB_apply]; simp [fi0, fi1, fi2, fi3]
  have h : fasC a b c d * fasB a b c d = 1 := Ring.inverse_mul_cancel _ hB
  rw [hv]
  exact congrFun (DFunLike.congr_fun h _) i

lemma fasC_comb2 (p q r s : ℝ) :
    fasC a b c d (p • a + q • b + r • c + s • d) fi2 = r := by
  rw [fasC_comb hB]; rfl

lemma fasC_comb3 (p q r s : ℝ) :
    fasC a b c d (p • a + q • b + r • c + s • d) fi3 = s := by
  rw [fasC_comb hB]; rfl

lemma fasC_comb0 (p q r s : ℝ) :
    fasC a b c d (p • a + q • b + r • c + s • d) fi0 = p := by
  rw [fasC_comb hB]; rfl

lemma fasC_comb1 (p q r s : ℝ) :
    fasC a b c d (p • a + q • b + r • c + s • d) fi1 = q := by
  rw [fasC_comb hB]; rfl

/-- Coordinates of `L w` for a map rotating the frame. -/
lemma fasC_rot (L : V 1 →L[ℝ] V 1) (hab : L a = b) (hba : L b = -a) (hcd : L c = d)
    (hdc : L d = -c) (w : V 1) :
    fasC a b c d (L w) fi2 = -(fasC a b c d w fi3) ∧
      fasC a b c d (L w) fi3 = fasC a b c d w fi2 := by
  have hexp := fasC_expand hB w
  set C := fasC a b c d with hC
  have hL : L w = (-(C w fi1)) • a + (C w fi0) • b + (-(C w fi3)) • c + (C w fi2) • d := by
    conv_lhs => rw [← hexp]
    simp only [map_add, map_smul, hab, hba, hcd, hdc]
    module
  rw [hL]
  exact ⟨fasC_comb2 hB _ _ _ _, fasC_comb3 hB _ _ _ _⟩

/-- A combination of the frame with coefficients `A, B, C', D'` and vectors `G₁, G₂` vanishing:
the two normal components. -/
lemma fasC_identity {A B' C' D' n₁ n₂ : ℝ} {G₁ G₂ : V 1}
    (h : A • a + B' • b + C' • c + D' • d + n₁ • G₁ + n₂ • G₂ = 0) :
    C' + n₁ * fasC a b c d G₁ fi2 + n₂ * fasC a b c d G₂ fi2 = 0 ∧
      D' + n₁ * fasC a b c d G₁ fi3 + n₂ * fasC a b c d G₂ fi3 = 0 := by
  have h0 := congrArg (fasC a b c d) h
  simp only [map_add, map_smul, map_zero] at h0
  have h1 : fasC a b c d (A • a + B' • b + C' • c + D' • d) =
      A • fasC a b c d a + B' • fasC a b c d b + C' • fasC a b c d c + D' • fasC a b c d d := by
    simp only [map_add, map_smul]
  rw [← h1] at h0
  have e2 := congrFun h0 fi2
  have e3 := congrFun h0 fi3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2 e3
  rw [fasC_comb2 hB] at e2
  rw [fasC_comb3 hB] at e3
  exact ⟨e2, e3⟩

end coords

/-! ### Point identities for `J̃` -/

section points
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

omit hH in
lemma fas_Jt_apply (y v : V 1) :
    Jtilde H J y v =
      (scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) * fderiv ℝ H (proj H y) v) •
        ((scaleToS H y)⁻¹ • reeb H (proj H y)) -
      (scaleToS H y * liouville (proj H y) v) • ((2 : ℝ) • y) +
      J (proj H y) (v -
        (scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) * fderiv ℝ H (proj H y) v) •
          ((2 : ℝ) • y) -
        (scaleToS H y * liouville (proj H y) v) • ((scaleToS H y)⁻¹ • reeb H (proj H y))) := by
  simp only [Jtilde, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ka_liouvilleCLM_apply, smul_eq_mul]

include hH in
lemma fas_y_eq {y : V 1} (hy : y ≠ 0) : y = (scaleToS H y)⁻¹ • proj H y := by
  have hr := (ka_scale_spec H hH y hy).1
  rw [proj, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

include hH in
/-- `J̃` sends the lifted Reeb field to `-∂ₐ`. -/
lemma fas_Jt_lift {y : V 1} (hy : y ≠ 0) :
    Jtilde H J y ((scaleToS H y)⁻¹ • reeb H (proj H y)) = -((2 : ℝ) • y) := by
  have hr := (ka_scale_spec H hH y hy).1
  have hx : proj H y ∈ energySurface H := (ka_scale_spec H hH y hy).2
  obtain ⟨-, h1, h2, -⟩ := ka_reeb_spec H hH _ hx
  have hl : liouville (proj H y) ((scaleToS H y)⁻¹ • reeb H (proj H y)) = (scaleToS H y)⁻¹ := by
    rw [← ka_liouvilleCLM_apply, map_smul, ka_liouvilleCLM_apply, h1, smul_eq_mul, mul_one]
  have hd : fderiv ℝ H (proj H y) ((scaleToS H y)⁻¹ • reeb H (proj H y)) = 0 := by
    rw [map_smul, h2, smul_zero]
  rw [fas_Jt_apply, hl, hd, mul_inv_cancel₀ hr.ne']
  simp

include hH in
/-- `J̃` sends `∂ₐ = 2y` to the lifted Reeb field. -/
lemma fas_Jt_two {y : V 1} (hy : y ≠ 0) :
    Jtilde H J y ((2 : ℝ) • y) = (scaleToS H y)⁻¹ • reeb H (proj H y) := by
  have hr := (ka_scale_spec H hH y hy).1
  have hx : proj H y ∈ energySurface H := (ka_scale_spec H hH y hy).2
  have hD : 0 < fderiv ℝ H (proj H y) (proj H y) := hH.2.2 _ hx
  have hye := fas_y_eq hH hy
  have hy2 : (2 : ℝ) • y = (2 * (scaleToS H y)⁻¹) • proj H y := by
    conv_lhs => rw [hye]
    rw [smul_smul]
  have hl : liouville (proj H y) ((2 : ℝ) • y) = 0 := by
    rw [hy2, ← ka_liouvilleCLM_apply, map_smul, ka_liouvilleCLM_apply]
    unfold liouville
    rw [ka_om_self]; simp
  have hd : scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) *
      fderiv ℝ H (proj H y) ((2 : ℝ) • y) = 1 := by
    rw [hy2, map_smul, smul_eq_mul]
    field_simp
  rw [fas_Jt_apply, hl, hd]
  simp

include hH in
/-- On `ξ`, `J̃` is `J`. -/
lemma fas_Jt_xi {y p : V 1} (hp : IsInXi H (proj H y) p) :
    Jtilde H J y p = J (proj H y) p := by
  rw [fas_Jt_apply, hp.1, hp.2]
  simp

include hH in
lemma fas_ne_zero_of_mem {x : V 1} (hx : x ∈ energySurface H) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

include hH in
lemma fas_scale_mem {x : V 1} (hx : x ∈ energySurface H) : scaleToS H x = 1 :=
  ka_scale_unique H hH x (fas_ne_zero_of_mem hH hx) 1 one_pos (by rw [one_smul]; exact hx)

include hH in
lemma fas_Jt_two_mem {x : V 1} (hx : x ∈ energySurface H) :
    Jtilde H J x ((2 : ℝ) • x) = reeb H x := by
  have h := fas_Jt_two (J := J) hH (fas_ne_zero_of_mem hH hx)
  rwa [fas_scale_mem hH hx, N1.proj_of_mem H hH hx, inv_one, one_smul] at h

include hH in
lemma fas_Jt_reeb_mem {x : V 1} (hx : x ∈ energySurface H) :
    Jtilde H J x (reeb H x) = -((2 : ℝ) • x) := by
  have h := fas_Jt_lift (J := J) hH (fas_ne_zero_of_mem hH hx)
  rwa [fas_scale_mem hH hx, N1.proj_of_mem H hH hx, inv_one, one_smul] at h

include hH in
lemma fas_Jt_xi_mem {x p : V 1} (hx : x ∈ energySurface H) (hp : IsInXi H x p) :
    Jtilde H J x p = J x p := by
  have h := fas_Jt_xi (J := J) hH (y := x) (p := p) (by rwa [N1.proj_of_mem H hH hx])
  rwa [N1.proj_of_mem H hH hx] at h

include hH hJ in
lemma fas_Jt_differentiableAt {y : V 1} (hy : y ≠ 0) : DifferentiableAt ℝ (Jtilde H J) y := by
  obtain ⟨hO, hC, -⟩ := (jtilde_isAlmostComplexOn H hH J hJ).1
  exact (hC.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)

include hH hJ in
lemma fas_Jt_contDiffAt {y : V 1} (hy : y ≠ 0) : ContDiffAt ℝ ∞ (Jtilde H J) y := by
  obtain ⟨hO, hC, -⟩ := (jtilde_isAlmostComplexOn H hH J hJ).1
  exact hC.contDiffAt (hO.mem_nhds hy)

include hH hJ in
lemma fas_Jt_sq {y : V 1} (hy : y ≠ 0) (v : V 1) :
    Jtilde H J y (Jtilde H J y v) = -v := by
  have h := (jtilde_isAlmostComplexOn H hH J hJ).1.2.2 y hy
  simpa using DFunLike.congr_fun h v

include hH hJ in
lemma fas_Jt_scale {y : V 1} (hy : y ≠ 0) {c : ℝ} (hc : 0 < c) :
    Jtilde H J (c • y) = Jtilde H J y :=
  (jtilde_isAlmostComplexOn H hH J hJ).2.2.2.2 y hy c hc

include hH hJ in
/-- `DJ̃(c y) = c⁻¹ DJ̃(y)`. -/
lemma fas_dJt_scale {y : V 1} (hy : y ≠ 0) {c : ℝ} (hc : 0 < c) (v : V 1) :
    fderiv ℝ (Jtilde H J) (c • y) v = c⁻¹ • fderiv ℝ (Jtilde H J) y v := by
  have hcy : c • y ≠ 0 := smul_ne_zero hc.ne' hy
  have hd := (fas_Jt_differentiableAt hH hJ hcy).hasFDerivAt
  have hl : HasFDerivAt (fun w : V 1 => c • w) (c • ContinuousLinearMap.id ℝ (V 1)) y :=
    (hasFDerivAt_id y).const_smul c
  have h1 := hd.comp y hl
  have hev : (Jtilde H J ∘ fun w : V 1 => c • w) =ᶠ[𝓝 y] Jtilde H J := by
    filter_upwards [isOpen_ne.mem_nhds hy] with w hw
    exact fas_Jt_scale hH hJ hw hc
  have h2 := (h1.congr_of_eventuallyEq hev.symm).fderiv
  have h3 := (fas_Jt_differentiableAt hH hJ hy).hasFDerivAt
  have h4 : fderiv ℝ (Jtilde H J) y = (fderiv ℝ (Jtilde H J) (c • y)).comp
      (c • ContinuousLinearMap.id ℝ (V 1)) := by
    have := (h1.congr_of_eventuallyEq hev.symm)
    exact h3.unique this
  rw [h4]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

include hH hJ in
/-- `DJ̃(x)[v] R(x) = -2v - J̃(x) DR(x)[v]` for `v ∈ ξ_x`. -/
lemma fas_dJt_reeb {x v : V 1} (hx : x ∈ energySurface H) (hv : IsInXi H x v) :
    fderiv ℝ (Jtilde H J) x v (reeb H x) =
      -((2 : ℝ) • v) - Jtilde H J x (fderiv ℝ (reeb H) x v) := by
  have hx0 := fas_ne_zero_of_mem hH hx
  have hr1 := fas_scale_mem hH hx
  have hpx := N1.proj_of_mem H hH hx
  have hs := ka_scale_hasFDerivAt H hH x hx0
  have hsi : HasFDerivAt (fun y => (scaleToS H y)⁻¹)
      (-(((scaleToS H x) ^ 2)⁻¹) • ((-(scaleToS H x ^ 2 / fderiv ℝ H (proj H x) (proj H x))) •
        fderiv ℝ H (proj H x))) x := by
    have := (hasDerivAt_inv (x := scaleToS H x) (by rw [hr1]; exact one_ne_zero)).comp_hasFDerivAt
      x hs
    exact this
  have hp := N1.proj_hasFDerivAt_mem H hH hx
  have hR : HasFDerivAt (reeb H) (fderiv ℝ (reeb H) x) (proj H x) := by
    rw [hpx]
    exact ((ka_reeb_contDiffAt H hH x hx).differentiableAt (by simp)).hasFDerivAt
  have hRp := hR.comp x hp
  have hL := hsi.smul hRp
  have hJd := (fas_Jt_differentiableAt hH hJ hx0).hasFDerivAt
  have hA := hJd.clm_apply hL
  have hev : (fun y => Jtilde H J y ((scaleToS H y)⁻¹ • (reeb H ∘ proj H) y)) =ᶠ[𝓝 x]
      fun y => -((2 : ℝ) • y) := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
    exact fas_Jt_lift hH hy
  have hB : HasFDerivAt (fun y : V 1 => -((2 : ℝ) • y)) (-((2 : ℝ) • ContinuousLinearMap.id ℝ (V 1))) x :=
    ((hasFDerivAt_id x).const_smul (2 : ℝ)).neg
  have hu := (hA.congr_of_eventuallyEq hev.symm).unique hB
  have hval := DFunLike.congr_fun hu v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply,
    Function.comp_apply, hpx, hr1, hv.2] at hval
  simp only [inv_one, one_smul, smul_eq_mul, mul_zero, zero_div, zero_smul, sub_zero, add_zero,
    zero_add, map_zero, smul_zero] at hval
  simp only [Pi.smul_apply', Function.comp_apply, hr1, hpx, inv_one, one_smul] at hval
  rw [eq_sub_iff_add_eq, add_comm]
  exact hval

end points

end FiniteEnergyPlane

/-!
# S model, layer A (local): the model map `Y(ζ, w) = e^{2T Re ζ} (x(T Im ζ) + M(Im ζ)(cToVec w))`
and its derivative.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace SM

/-- `cToVec` as a continuous real-linear map. -/
def cToVecL : ℂ →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := cToVec
      map_add' := fun a b => by ext i; rcases i with i | i <;> simp [cToVec]
      map_smul' := fun c a => by ext i; rcases i with i | i <;> simp [cToVec] }

@[simp] lemma cToVecL_apply (z : ℂ) : cToVecL z = cToVec z := rfl

lemma cToVec_vecToC (a : CauchyRiemannIndex.Vec 1) : cToVec (vecToC a) = a := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [cToVec, vecToC]

lemma vecToC_cToVec (z : ℂ) : vecToC (cToVec z) = z := by
  apply Complex.ext <;> simp [cToVec, vecToC]

lemma cToVec_I_mul (z : ℂ) :
    cToVec (Complex.I * z) = Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (cToVec z) := by
  have h : vecToC (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (cToVec z)) =
      Complex.I * vecToC (cToVec z) := by
    apply Complex.ext <;>
      simp [vecToC, CauchyRiemannIndex.J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec,
        dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]
  rw [vecToC_cToVec] at h
  rw [← h, cToVec_vecToC]

variable {H : V 1 → ℝ} (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)

/-- The model `m(t, w) = x(T t) + M(t)(cToVec w)`. -/
def mm (t : ℝ) (w : ℂ) : V 1 := P.x (P.T * t) + M t (cToVecL w)

/-- The model map `Y(ζ, w) = e^{2T Re ζ} m(Im ζ, w)`. -/
def Y (q : ℂ × ℂ) : V 1 := Real.exp (2 * P.T * q.1.re) • mm P M q.1.im q.2

/-- The explicit derivative of `Y` at `(it, w)`. -/
def Lx (H : V 1 → ℝ) (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (t : ℝ) (w : ℂ) : ℂ × ℂ →L[ℝ] V 1 :=
  ((2 * P.T) • (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ))).smulRight (mm P M t w) +
    (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).smulRight
      (P.T • reeb H (P.x (P.T * t)) + deriv M t (cToVecL w)) +
    (M t).comp (cToVecL.comp (ContinuousLinearMap.snd ℝ ℂ ℂ))

lemma Lx_apply (t : ℝ) (w : ℂ) (h : ℂ × ℂ) :
    Lx H P M t w h = (2 * P.T * h.1.re) • mm P M t w +
      h.1.im • (P.T • reeb H (P.x (P.T * t)) + deriv M t (cToVecL w)) + M t (cToVec h.2) := by
  simp [Lx, smul_eq_mul, mul_assoc]

variable (hH : IsStrictlyStarShapedLevel H)

include hH in
lemma contDiff_x : ContDiff ℝ ∞ (fun t : ℝ => P.x (P.T * t)) :=
  (ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_id)

include hH in
lemma hasDerivAt_x (t : ℝ) :
    HasDerivAt (fun s : ℝ => P.x (P.T * s)) (P.T • reeb H (P.x (P.T * t))) t := by
  have h0 : HasDerivAt (fun s => P.T * s) P.T t := by
    simpa using (hasDerivAt_id t).const_mul P.T
  exact (P.hasDerivAt (P.T * t)).scomp t h0

variable (hMc : ContDiff ℝ ∞ M)

include hMc in
lemma hasDerivAt_M (t : ℝ) : HasDerivAt M (deriv M t) t :=
  ((hMc.differentiable (by simp)) t).hasDerivAt

include hH hMc in
lemma contDiff_Y : ContDiff ℝ ∞ (Y P M) := by
  unfold Y mm
  have hx := contDiff_x P hH
  have him : ContDiff ℝ ∞ (fun q : ℂ × ℂ => q.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have hre : ContDiff ℝ ∞ (fun q : ℂ × ℂ => q.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst
  refine (Real.contDiff_exp.comp (contDiff_const.mul hre)).smul ((hx.comp him).add ?_)
  exact (hMc.comp him).clm_apply (cToVecL.contDiff.comp contDiff_snd)

include hH hMc in
/-- The derivative of `Y` at a general point. -/
lemma hasFDerivAt_Y_gen (q : ℂ × ℂ) :
    HasFDerivAt (Y P M) (Real.exp (2 * P.T * q.1.re) • Lx H P M q.1.im q.2) q := by
  have him : HasFDerivAt (fun q : ℂ × ℂ => q.1.im)
      (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) q :=
    (Complex.imCLM.hasFDerivAt).comp q (hasFDerivAt_fst)
  have hre : HasFDerivAt (fun q : ℂ × ℂ => q.1.re)
      (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) q :=
    (Complex.reCLM.hasFDerivAt).comp q (hasFDerivAt_fst)
  have hx : HasFDerivAt (fun q : ℂ × ℂ => P.x (P.T * q.1.im))
      ((Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).smulRight
        (P.T • reeb H (P.x (P.T * q.1.im)))) q := by
    have h0 := (hasDerivAt_x P hH q.1.im).hasFDerivAt
    have h1 := h0.comp q him
    exact h1.congr_fderiv (ContinuousLinearMap.ext fun h => by simp)
  have hM : HasFDerivAt (fun q : ℂ × ℂ => M q.1.im)
      ((Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).smulRight (deriv M q.1.im)) q :=
    (((hasDerivAt_M M hMc q.1.im).hasFDerivAt).comp q him).congr_fderiv
      (ContinuousLinearMap.ext fun h => by simp)
  have hc : HasFDerivAt (fun q : ℂ × ℂ => cToVecL q.2)
      (cToVecL.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)) q :=
    cToVecL.hasFDerivAt.comp q hasFDerivAt_snd
  have hm := hx.add (hM.clm_apply hc)
  have he : HasFDerivAt (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re))
      (Real.exp (2 * P.T * q.1.re) • ((2 * P.T) • (Complex.reCLM.comp
        (ContinuousLinearMap.fst ℝ ℂ ℂ)))) q :=
    (hre.const_mul (2 * P.T)).exp
  have hY := he.smul hm
  refine hY.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  rw [ContinuousLinearMap.smul_apply, Lx_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Complex.reCLM_apply,
    Complex.imCLM_apply, ContinuousLinearMap.flip_apply, mm, smul_eq_mul, Pi.add_apply,
    cToVecL_apply]
  module

include hH hMc in
lemma hasFDerivAt_Y (t : ℝ) (w : ℂ) :
    HasFDerivAt (Y P M) (Lx H P M t w) ((t : ℂ) * Complex.I, w) := by
  have h := hasFDerivAt_Y_gen P M hH hMc ((t : ℂ) * Complex.I, w)
  simpa using h

end SM

end

end FiniteEnergyPlane

/-!
# S model, layer B (local): invertibility of the model derivative near `w = 0`, a uniform
width, and the limit structure `Jinf = L⁻¹ ∘ J̃(m) ∘ L`.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace SM

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
  {M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hM : IsUnitaryXiFrame J P M)

lemma vecToC_J₀ (a : CauchyRiemannIndex.Vec 1) :
    vecToC (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) = Complex.I * vecToC a := by
  apply Complex.ext <;>
    simp [vecToC, CauchyRiemannIndex.J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec,
      dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]

lemma finrank_CC : Module.finrank ℝ (ℂ × ℂ) = 4 := by
  rw [Module.finrank_prod, Complex.finrank_real_complex]

lemma finrank_V1 : Module.finrank ℝ (V 1) = 4 := by
  simp [V]

/-- An injective map `ℂ × ℂ → V 1` is an isomorphism. -/
lemma exists_equiv_of_injective (L : ℂ × ℂ →L[ℝ] V 1) (hL : Function.Injective L) :
    ∃ e : (ℂ × ℂ) ≃L[ℝ] V 1, (e : ℂ × ℂ →L[ℝ] V 1) = L := by
  let e₀ := LinearMap.linearEquivOfInjective L.toLinearMap hL (by rw [finrank_CC, finrank_V1])
  refine ⟨e₀.toContinuousLinearEquiv, ?_⟩
  ext h <;> rfl

include hM in
lemma M_injective (t : ℝ) : Function.Injective (M t) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := (hM.2.2 t).2.2.2 a (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a)
  rw [ha] at h
  have h0 : omega0 (0 : V 1) (M t (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a)) = 0 := by
    simp [omega0, dot, j0]
  rw [h0, eq_comm, real_inner_self_eq_norm_sq] at h
  have hJa : Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    exact norm_eq_zero.1 this
  have hc := congrArg vecToC hJa
  rw [vecToC_J₀] at hc
  have : vecToC a = 0 := by
    have h0' : vecToC (0 : CauchyRiemannIndex.Vec 1) = 0 := by
      apply Complex.ext <;> simp [vecToC]
    rw [h0'] at hc
    simpa using hc
  rw [← cToVec_vecToC a, this]
  ext i; rcases i with i | i <;> simp [cToVec]


include hH hM in
/-- The model derivative along `w = 0` is injective. -/
lemma Lx_zero_injective (t : ℝ) : Function.Injective (Lx H P M t 0) := by
  have hT := P.T_pos
  set x := P.x (P.T * t) with hxdef
  have hx : x ∈ energySurface H := P.mem _
  have hD : 0 < fderiv ℝ H x x := hH.2.2 _ hx
  obtain ⟨-, hR1, hRH, -⟩ := ka_reeb_spec H hH _ hx
  rw [injective_iff_map_eq_zero]
  rintro ⟨ζ, μ⟩ hv
  rw [Lx_apply] at hv
  simp only [mm, map_zero, add_zero, ← hxdef, cToVecL_apply] at hv
  have hMξ := (hM.2.2 t).1 (cToVec μ)
  rw [← hxdef] at hMξ
  have h1 := congrArg (fderiv ℝ H x) hv
  simp only [map_add, map_smul, hRH, hMξ.2, map_zero, smul_zero, add_zero, smul_eq_mul] at h1
  have hre : ζ.re = 0 := by
    have : ζ.re * (2 * P.T * fderiv ℝ H x x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (by positivity)
  have h2 := congrArg (liouvilleCLM x) hv
  simp only [map_add, map_smul, ka_liouvilleCLM_apply, hR1, hMξ.1, map_zero, smul_zero,
    add_zero, smul_eq_mul, mul_one] at h2
  have hll : liouville x x = 0 := by
    unfold liouville; rw [ka_om_self]; simp
  rw [hll] at h2
  have him : ζ.im = 0 := by
    have h2' : ζ.im * P.T = 0 := by linarith
    rcases mul_eq_zero.1 h2' with h | h
    · exact h
    · exact absurd h hT.ne'
  rw [hre, him, mul_zero, zero_smul, zero_smul, zero_add, zero_add] at hv
  have hμ : cToVec μ = 0 := (injective_iff_map_eq_zero _).1 (M_injective P hM t) _ hv
  have hμ' : μ = 0 := by
    rw [← vecToC_cToVec μ, hμ]
    apply Complex.ext <;> simp [vecToC]
  simp [Prod.ext_iff, Complex.ext_iff, hre, him, hμ']


section tube
variable (M) (hMc : ContDiff ℝ ∞ M)

include hH hMc in
lemma Lx_eq_fderiv (t : ℝ) (w : ℂ) :
    fderiv ℝ (Y P M) ((t : ℂ) * Complex.I, w) = Lx H P M t w :=
  (hasFDerivAt_Y P M hH hMc t w).fderiv

lemma contDiff_embed : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ((p.1 : ℂ) * Complex.I, p.2)) :=
  ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const).prodMk contDiff_snd

include hH hMc in
lemma contDiff_Lx : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Lx H P M p.1 p.2) := by
  have h : (fun p : ℝ × ℂ => Lx H P M p.1 p.2) =
      fun p => fderiv ℝ (Y P M) ((p.1 : ℂ) * Complex.I, p.2) := by
    funext p; rw [Lx_eq_fderiv hH P M hMc]
  rw [h]
  exact ((contDiff_Y P M hH hMc).fderiv_right (m := ∞) (by simp)).comp contDiff_embed

include hH hMc in
lemma contDiff_mm : ContDiff ℝ ∞ (fun p : ℝ × ℂ => mm P M p.1 p.2) := by
  unfold mm
  exact ((contDiff_x P hH).comp contDiff_fst).add
    ((hMc.comp contDiff_fst).clm_apply (cToVecL.contDiff.comp contDiff_snd))

include hM in
lemma mm_periodic (t : ℝ) (w : ℂ) : mm P M (t + 1) w = mm P M t w := by
  simp only [mm, mul_add, mul_one, P.periodic, hM.2.1 t]

include hM in
lemma deriv_M_periodic (t : ℝ) : deriv M (t + 1) = deriv M t := by
  rw [← deriv_comp_add_const]
  congr 1
  funext s
  exact hM.2.1 s

include hM in
lemma Lx_periodic (t : ℝ) (w : ℂ) : Lx H P M (t + 1) w = Lx H P M t w := by
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [Lx_apply, mm_periodic P M hM, deriv_M_periodic P M hM, hM.2.1 t, mul_add, mul_one,
    P.periodic]

/-- Where the model derivative is an isomorphism and the model is nonzero. -/
def goodSet (H : V 1 → ℝ) (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) :
    Set (ℝ × ℂ) :=
  {p | mm P M p.1 p.2 ≠ 0 ∧
    Lx H P M p.1 p.2 ∈ Set.range ((↑) : ((ℂ × ℂ) ≃L[ℝ] V 1) → ℂ × ℂ →L[ℝ] V 1)}

include hH hMc in
lemma goodSet_isOpen : IsOpen (goodSet H P M) :=
  (isOpen_ne_fun (contDiff_mm hH P M hMc).continuous continuous_const).inter
    (ContinuousLinearEquiv.isOpen.preimage (contDiff_Lx hH P M hMc).continuous)

include hH hM in
lemma mem_goodSet_zero (t : ℝ) : (t, (0 : ℂ)) ∈ goodSet H P M := by
  refine ⟨?_, ?_⟩
  · simp only [mm, map_zero, add_zero]
    exact fas_ne_zero_of_mem hH (P.mem _)
  · obtain ⟨e, he⟩ := exists_equiv_of_injective _ (Lx_zero_injective hH P hM t)
    exact ⟨e, he⟩

include hH hM hMc in
lemma goodSet_tube : ∃ ρ > 0, ∀ (t : ℝ) (w : ℂ), ‖w‖ < ρ → (t, w) ∈ goodSet H P M := by
  have hsub : Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℂ) ⊆ goodSet H P M := by
    rintro ⟨t, w⟩ ⟨-, hw⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact mem_goodSet_zero hH P M hM t
  obtain ⟨U₁, U₂, -, hU₂, hs, ht, hprod⟩ := generalized_tube_lemma isCompact_Icc
    isCompact_singleton (goodSet_isOpen hH P M hMc) hsub
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU₂ 0 (ht rfl)
  refine ⟨ρ, hρ, fun t w hw => ?_⟩
  have hper : Function.Periodic (fun t : ℝ => (t, w) ∈ goodSet H P M) 1 := fun t => by
    simp only [goodSet, Set.mem_setOf_eq, mm_periodic P M hM, Lx_periodic P M hM]
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
  have : (y, w) ∈ goodSet H P M := hprod ⟨hs ⟨hy.1, hy.2.le⟩, hball (by simpa using hw)⟩
  have e : (t, w) ∈ goodSet H P M ↔ (y, w) ∈ goodSet H P M := by
    have := hty
    simpa using this
  exact e.2 this

end tube

end SM

end

end FiniteEnergyPlane

/-!
# S, child C5 (local proof), layer A: the tube map is nondegenerate far out.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SME

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  simp only [cylInf, ccwLoop]
  exact mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') (Complex.exp_ne_zero _)

lemma cylScale_cylScaleInv (s t : ℝ) (v : ℂ × ℂ) : cylScale s t (cylScaleInv s t v) = v := by
  have hc : (((2 * Real.pi : ℝ) : ℂ) * cylInf s t) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)) (cylInf_ne_zero s t)
  rcases v with ⟨a, b⟩
  have hz := cylInf_ne_zero s t
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [cylScale, cylScaleInv]
  field_simp

/-- If `c • (D ∘ cylScale)` is injective, so is `D`. -/
lemma injective_of_comp_cylScale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : ℂ × ℂ →L[ℝ] F) (s t c : ℝ) (h : Function.Injective (c • D.comp (cylScale s t))) :
    Function.Injective D := by
  rw [injective_iff_map_eq_zero] at h ⊢
  intro v hv
  have h1 : (c • D.comp (cylScale s t)) (cylScaleInv s t v) = 0 := by
    simp [cylScale_cylScaleInv, hv]
  have h2 := h _ h1
  rw [← cylScale_cylScaleInv s t v, h2, map_zero]

lemma eventually_const_mul_exp_lt (C b δ : ℝ) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ S : ℝ, ∀ s ≥ S, C * Real.exp (-(b * s)) < δ := by
  have h : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 (C * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)).const_mul C
  rw [mul_zero] at h
  exact eventually_atTop.1 (h.eventually_lt_const hδ)

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (P : ReebOrbit H) {M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hM : IsUnitaryXiFrame J P M)

/-- The model pair `(m, L)`. -/
def gm (H : V 1 → ℝ) (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (p : ℝ × ℂ) : V 1 × (ℂ × ℂ →L[ℝ] V 1) :=
  (SM.mm P M p.1 p.2, SM.Lx H P M p.1 p.2)

/-- The good set of pairs. -/
def Og : Set (V 1 × (ℂ × ℂ →L[ℝ] V 1)) :=
  {y : V 1 × (ℂ × ℂ →L[ℝ] V 1) | y.1 ≠ 0 ∧
    y.2 ∈ Set.range ((↑) : ((ℂ × ℂ) ≃L[ℝ] V 1) → ℂ × ℂ →L[ℝ] V 1)}

lemma Og_isOpen : IsOpen Og :=
  (isOpen_ne_fun continuous_fst continuous_const).inter
    (ContinuousLinearEquiv.isOpen.preimage continuous_snd)

include hH hM in
/-- A uniform neighbourhood of the model values inside the good set. -/
lemma exists_uniform_margin :
    ∃ ρ > 0, ∃ δ > 0, ∀ (t : ℝ) (w : ℂ), w ∈ ball (0 : ℂ) ρ →
      ∀ y, dist y (gm H P M (t, w)) < δ → y ∈ Og := by
  have hMc : ContDiff ℝ ∞ M := hM.1
  obtain ⟨ρ₁, hρ₁, hg⟩ := SM.goodSet_tube hH P M hM hMc
  set K0 := gm H P M '' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) (ρ₁ / 2)) with hK0
  have hcont : Continuous (gm H P M) :=
    (SM.contDiff_mm hH P M hMc).continuous.prodMk (SM.contDiff_Lx hH P M hMc).continuous
  have hK : IsCompact K0 :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image hcont
  have hsub : K0 ⊆ Og := by
    rintro _ ⟨⟨t, w⟩, ⟨-, hw⟩, rfl⟩
    have hw' : ‖w‖ < ρ₁ := by
      have := mem_closedBall_zero_iff.1 hw
      linarith
    obtain ⟨hm, e, he⟩ := hg t w hw'
    exact ⟨hm, e, he⟩
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open Og_isOpen hsub
  refine ⟨ρ₁ / 2, by positivity, δ, hδ, fun t w hw y hy => hth ?_⟩
  have hper : Function.Periodic (fun t : ℝ => gm H P M (t, w)) 1 := fun t => by
    simp only [gm, SM.mm_periodic P M hM, SM.Lx_periodic P M hM]
  obtain ⟨t', ht', hty⟩ := hper.exists_mem_Ico₀ one_pos t
  refine Metric.mem_thickening_iff.2 ⟨gm H P M (t, w), ?_, hy⟩
  have : gm H P M (t, w) = gm H P M (t', w) := hty
  rw [this]
  exact ⟨(t', w), ⟨⟨ht'.1, ht'.2.le⟩, ball_subset_closedBall hw⟩, rfl⟩

variable (u : ℂ → V 1) (N : ℂ → ℂ →L[ℝ] V 1)

include hH hM in
/-- Far part: nondegeneracy of `Φ` at `(e^{2π(s+it)}, w)` for large `s`. -/
lemma far_part (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (hN : ContDiff ℝ ∞ N)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∃ S : ℝ, ∀ s ≥ S, ∀ (t : ℝ) (w : ℂ), w ∈ ball (0 : ℂ) ρ →
      u (cylInf s t) + N (cylInf s t) w ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (cylInf s t, w)) := by
  have hMc : ContDiff ℝ ∞ M := hM.1
  obtain ⟨ρ, hρ, δ, hδ, hmargin⟩ := exists_uniform_margin hH P hM
  obtain ⟨-, h3⟩ := expDecayCInftyTube_rescaled_sub_model H hH P u hu0 d b hb ha hw N M hNM ρ hρ
  obtain ⟨-, h4⟩ := expDecayCInftyTube_rescaled_fderiv_sub_model H hH P u hu hu0 d b hb ha hw
    N hN M hMc hNM ρ hρ
  obtain ⟨C₁, s₁, hC₁⟩ := h3 0
  obtain ⟨C₂, s₂, hC₂⟩ := h4 0
  obtain ⟨S₁, hS₁⟩ := eventually_const_mul_exp_lt C₁ b δ hb hδ
  obtain ⟨S₂, hS₂⟩ := eventually_const_mul_exp_lt C₂ b δ hb hδ
  refine ⟨ρ, hρ, max (max s₁ s₂) (max S₁ S₂), fun s hs t w hw => ?_⟩
  have hs₁ : s ≥ s₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs₂ : s ≥ s₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hS₁' : s ≥ S₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hS₂' : s ≥ S₂ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have e1 := hC₁ s hs₁ t w hw
  have e2 := hC₂ s hs₂ t w hw
  rw [norm_iteratedFDeriv_zero] at e1 e2
  set c : ℝ := Real.exp (-(2 * (P.T * s + d)))
  set y : V 1 × (ℂ × ℂ →L[ℝ] V 1) :=
    (c • (u (cylInf s t) + N (cylInf s t) w),
      c • (fderiv ℝ (fun p : ℂ × ℂ => u p.1 + N p.1 p.2) (cylInf s t, w)).comp (cylScale s t))
  have hY : fderiv ℝ (fun p : ℂ × ℂ => Real.exp (2 * P.T * p.1.re) •
      (P.x (P.T * p.1.im) + M p.1.im (cToVec p.2))) ((t : ℂ) * Complex.I, w) =
      SM.Lx H P M t w := SM.Lx_eq_fderiv hH P M hMc t w
  rw [hY] at e2
  have hdist : dist y (gm H P M (t, w)) < δ := by
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
    exact ⟨lt_of_le_of_lt e1 (hS₁ s hS₁'), lt_of_le_of_lt e2 (hS₂ s hS₂')⟩
  obtain ⟨hy1, e, he⟩ := hmargin t w hw y hdist
  refine ⟨fun h0 => hy1 ?_, ?_⟩
  · show c • (u (cylInf s t) + N (cylInf s t) w) = 0
    rw [h0, smul_zero]
  · refine injective_of_comp_cylScale _ s t c ?_
    have : (c • (fderiv ℝ (fun p : ℂ × ℂ => u p.1 + N p.1 p.2) (cylInf s t, w)).comp
        (cylScale s t)) = (e : ℂ × ℂ →L[ℝ] V 1) := he.symm
    rw [this]
    exact e.injective

end SME

end

end FiniteEnergyPlane

/-!
# S, child C5 (local proof), layer B: compact part and assembly.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SME

/-- The derivative of `(z, w) ↦ u z + N z w` along `w = 0`. -/
lemma fderiv_tubeMap_zero (u : ℂ → V 1) (N : ℂ → ℂ →L[ℝ] V 1) (hu : Differentiable ℝ u)
    (hN : Differentiable ℝ N) (z Δ ν : ℂ) :
    fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (z, 0) (Δ, ν) = fderiv ℝ u z Δ + N z ν := by
  have h1 : HasFDerivAt (fun q : ℂ × ℂ => u q.1)
      ((fderiv ℝ u z).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) (z, 0) :=
    (hu z).hasFDerivAt.comp (z, (0 : ℂ)) hasFDerivAt_fst
  have hc : HasFDerivAt (fun q : ℂ × ℂ => N q.1)
      ((fderiv ℝ N z).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) (z, 0) :=
    (hN z).hasFDerivAt.comp (z, (0 : ℂ)) hasFDerivAt_fst
  have h2 := hc.clm_apply (hasFDerivAt_snd (p := ((z, 0) : ℂ × ℂ)))
  have h3 : HasFDerivAt (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) _ (z, 0) := h1.add h2
  rw [h3.fderiv]
  simp

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (P : ReebOrbit H) {M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hM : IsUnitaryXiFrame J P M)

/-- Polar form in cylindrical coordinates. -/
lemma exists_cylInf_of_lt (S : ℝ) (z : ℂ) (hz : Real.exp (2 * Real.pi * S) < ‖z‖) :
    ∃ s ≥ S, ∃ t : ℝ, cylInf s t = z := by
  have hpos : 0 < ‖z‖ := lt_trans (Real.exp_pos _) hz
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨Real.log ‖z‖ / (2 * Real.pi), ?_, Complex.arg z / (2 * Real.pi), ?_⟩
  · rw [ge_iff_le, le_div_iff₀ hpi, mul_comm S, Real.le_log_iff_exp_le hpos]
    exact hz.le
  · simp only [cylInf, ccwLoop]
    have e1 : 2 * Real.pi * (Real.log ‖z‖ / (2 * Real.pi)) = Real.log ‖z‖ := by
      field_simp
    have e2 : 2 * Real.pi * (Complex.arg z / (2 * Real.pi)) = Complex.arg z := by
      field_simp
    rw [e1, e2, Real.exp_log hpos]
    exact Complex.norm_mul_exp_arg_mul_I z

variable (u : ℂ → V 1) (N : ℂ → ℂ →L[ℝ] V 1)

include hH hM in
theorem main (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) := by
  obtain ⟨ρ₂, hρ₂, S, hfar⟩ := far_part hH P hM u N hu hu0 d b hb ha hw hN hNM
  set Φ : ℂ × ℂ → V 1 := fun q => u q.1 + N q.1 q.2 with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ :=
    (hu.comp contDiff_fst).add ((hN.comp contDiff_fst).clm_apply contDiff_snd)
  set G : Set (ℂ × ℂ) := {p | Φ p ≠ 0 ∧
    fderiv ℝ Φ p ∈ Set.range ((↑) : ((ℂ × ℂ) ≃L[ℝ] V 1) → ℂ × ℂ →L[ℝ] V 1)} with hG
  have hGo : IsOpen G :=
    (isOpen_ne_fun hΦ.continuous continuous_const).inter
      (ContinuousLinearEquiv.isOpen.preimage (hΦ.continuous_fderiv (by simp)))
  set R := Real.exp (2 * Real.pi * S)
  have hsub : closedBall (0 : ℂ) R ×ˢ ({0} : Set ℂ) ⊆ G := by
    rintro ⟨z, w⟩ ⟨-, hw0⟩
    rw [Set.mem_singleton_iff] at hw0
    subst hw0
    refine ⟨?_, ?_⟩
    · simpa [hΦdef] using hu0 z
    · have hinj : Function.Injective (fderiv ℝ Φ (z, 0)) := by
        rw [injective_iff_map_eq_zero]
        rintro ⟨Δ, ν⟩ h0
        rw [hΦdef, fderiv_tubeMap_zero u N (hu.differentiable (by simp))
          (hN.differentiable (by simp))] at h0
        obtain ⟨h1, h2⟩ := hNinj z Δ ν h0
        simp [h1, h2]
      obtain ⟨e, he⟩ := SM.exists_equiv_of_injective _ hinj
      exact ⟨e, he⟩
  obtain ⟨U₁, U₂, -, hU₂, hs, ht, hprod⟩ := generalized_tube_lemma (isCompact_closedBall _ _)
    isCompact_singleton hGo hsub
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU₂ 0 (ht rfl)
  refine ⟨min ρ₂ ε, lt_min hρ₂ hε, ?_⟩
  rintro ⟨z, w⟩ ⟨-, hw⟩
  have hw₂ : w ∈ ball (0 : ℂ) ρ₂ := ball_subset_ball (min_le_left _ _) hw
  have hwε : w ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_right _ _) hw
  by_cases hz : ‖z‖ ≤ R
  · have hmem : (z, w) ∈ G := hprod ⟨hs (mem_closedBall_zero_iff.2 hz), hball hwε⟩
    obtain ⟨h1, e, he⟩ := hmem
    refine ⟨h1, ?_⟩
    show Function.Injective (fderiv ℝ Φ (z, w))
    rw [← he]
    exact e.injective
  · obtain ⟨s, hs', t, rfl⟩ := exists_cylInf_of_lt S z (lt_of_not_ge hz)
    exact hfar s hs' t w hw₂

end SME

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) :=
  SME.main hH P hM u N hu hu0 d b hb ha hw hN hNinj hNM
