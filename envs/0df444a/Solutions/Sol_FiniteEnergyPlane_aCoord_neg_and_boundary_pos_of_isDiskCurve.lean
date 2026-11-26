-- Prove2me | solution 1 for FiniteEnergyPlane.aCoord_neg_and_boundary_pos_of_isDiskCurve
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T17:52:37.457336+00:00
-- url     : https://prove2.me/submissions/72dec387-a9ef-43ce-979a-458a40f015c6

import Definitions.Def_FiniteEnergyPlane_SpanningDisk
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_eq_of_isMaxOn_of_laplacian_nonneg
import Theorems.Thm_FiniteEnergyPlane_hopf_lemma_disk
import Theorems.Thm_FiniteEnergyPlane_laplacian_aCoord_eq_dlambdaDensity
import Theorems.Thm_FiniteEnergyPlane_fderiv_eq_zero_of_dlambdaDensity_eq_zero
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg_of_isJHolomorphicOn
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open FiniteEnergyPlane
open scoped ContDiff Topology in
open scoped ContDiff Topology
open MeasureTheory Metric Filter Topology Laplacian
open scoped ContDiff Real

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

namespace FiniteEnergyPlane

noncomputable section

/-- `ω₀` as a continuous bilinear map. -/
def ampmOm (n : ℕ) : V n →L[ℝ] V n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V n →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ omega0 ka_om_add_left ka_om_smul_left
        (fun m n₁ n₂ => ka_om_add_right n₁ n₂ m) (fun c m n => ka_om_smul_right c n m))

theorem ampmOm_apply {n : ℕ} (x v : V n) : ampmOm n x v = omega0 x v := by
  simp [ampmOm]

theorem ampm_contDiffAt_aCoord {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {y : V n} (hy : y ≠ 0) : ContDiffAt ℝ ∞ (aCoord H) y := by
  have hr := (ka_scale_spec H hH y hy).1
  have : aCoord H = fun y => (-1 / 2 : ℝ) * Real.log (scaleToS H y) := by
    funext y; unfold aCoord; ring
  rw [this]
  exact contDiffAt_const.mul ((ka_scale_contDiffAt H hH y hy).log hr.ne')

theorem ampm_contDiffAt_proj {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {y : V n} (hy : y ≠ 0) : ContDiffAt ℝ ∞ (proj H) y := by
  have : proj H = fun y => scaleToS H y • y := rfl
  rw [this]
  exact (ka_scale_contDiffAt H hH y hy).smul contDiffAt_id

theorem ampm_of_mem {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (x : V n) (hx : H x = 1) : x ≠ 0 ∧ proj H x = x ∧ aCoord H x = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx
    simp at this
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 x hx0
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := ⟨r, hr0, hr1⟩
  have h1 : scaleToS H x = 1 := by
    unfold scaleToS
    rw [dif_pos e1]
    have := hru _ (Classical.choose_spec e1)
    have h1' := hru 1 ⟨one_pos, by rw [one_smul]; exact hx⟩
    rw [this, h1']
  refine ⟨hx0, ?_, ?_⟩
  · unfold proj; rw [h1, one_smul]
  · unfold aCoord; rw [h1, Real.log_one]; simp

theorem ampm_exp_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) : Real.exp (2 * aCoord H y) • proj H y = y := by
  have hr := (ka_scale_spec H hH y hy).1
  have e : Real.exp (2 * aCoord H y) = (scaleToS H y)⁻¹ := by
    unfold aCoord
    rw [show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring,
      Real.exp_neg, Real.exp_log hr]
  rw [e]
  unfold proj
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- An open ball of `ℂ` minus a countable set is preconnected. -/
theorem ampm_isPreconnected_ball_diff {s : Set ℂ} (hs : s.Countable) :
    IsPreconnected (ball (0 : ℂ) 1 \ s) := by
  set g : ℂ → ℂ := fun z => ((Homeomorph.unitBall : ℂ ≃ₜ ball (0 : ℂ) 1) z : ℂ) with hg
  have hgc : Continuous g := continuous_subtype_val.comp Homeomorph.unitBall.continuous
  have hgi : Function.Injective g := Subtype.val_injective.comp Homeomorph.unitBall.injective
  have hpre : (g ⁻¹' s).Countable := hs.preimage hgi
  have hconn := hpre.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have himg : g '' (g ⁻¹' s)ᶜ = ball (0 : ℂ) 1 \ s := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(Homeomorph.unitBall x).2, hx⟩
    · rintro ⟨hz, hzs⟩
      refine ⟨Homeomorph.unitBall.symm ⟨z, hz⟩, ?_, ?_⟩
      · show g _ ∉ s
        simpa [hg] using hzs
      · simp [hg]
  rw [← himg]
  exact hconn.isPreconnected.image _ hgc.continuousOn

/-- Every point of the unit circle is on the loop `ccwLoop 1`. -/
theorem ampm_exists_ccwLoop {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) : ∃ t : ℝ, ccwLoop 1 t = ζ := by
  refine ⟨Complex.arg ζ / (2 * π), ?_⟩
  have hn : ‖ζ‖ = 1 := by simpa using hζ
  unfold ccwLoop
  have : ((2 * π * (Complex.arg ζ / (2 * π)) : ℝ) : ℂ) = (Complex.arg ζ : ℂ) := by
    congr 1; field_simp
  rw [this]
  have := Complex.norm_mul_exp_arg_mul_I ζ
  rw [hn] at this
  push_cast at this ⊢
  simpa using this

/-- Radial approach to a point of the unit circle avoiding a finite set. -/
theorem ampm_radial {Γ : Finset ℂ} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) (hζΓ : ζ ∉ (Γ : Set ℂ)) :
    Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * ζ) (𝓝[>] 0) (𝓝 ζ) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), ((1 - s : ℝ) : ℂ) * ζ ∈ ball (0 : ℂ) 1 \ (Γ : Set ℂ) := by
  have hn : ‖ζ‖ = 1 := by simpa using hζ
  have ht : Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * ζ) (𝓝 0) (𝓝 ζ) := by
    have : Continuous (fun s : ℝ => ((1 - s : ℝ) : ℂ) * ζ) := by fun_prop
    simpa using this.tendsto 0
  have ht' : Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * ζ) (𝓝[>] 0) (𝓝 ζ) :=
    ht.mono_left nhdsWithin_le_nhds
  refine ⟨ht', ?_⟩
  have hΓc : (Γ : Set ℂ)ᶜ ∈ 𝓝 ζ := Γ.finite_toSet.isClosed.isOpen_compl.mem_nhds hζΓ
  have h1 := ht'.eventually_mem hΓc
  have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [h1, h2] with s hs1 hs2
  refine ⟨?_, hs1⟩
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, hn,
    abs_of_pos (by linarith [hs2.2])]
  linarith [hs2.1]

/-- A function continuous on the closed disk minus `Γ` and constant on the open disk minus `Γ` has
the same value on the unit circle. -/
theorem ampm_eq_on_sphere {F : Type*} [TopologicalSpace F] [T2Space F] {Γ : Finset ℂ}
    (hΓ : (Γ : Set ℂ) ⊆ ball 0 1) {g : ℂ → F}
    (hg : ContinuousOn g (closedBall (0 : ℂ) 1 \ (Γ : Set ℂ))) {M : F}
    (hM : ∀ z ∈ ball (0 : ℂ) 1 \ (Γ : Set ℂ), g z = M) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    g ζ = M := by
  have hζΓ : ζ ∉ (Γ : Set ℂ) := by
    intro h; have := hΓ h; rw [mem_ball_zero_iff] at this
    rw [mem_sphere_zero_iff_norm] at hζ; linarith
  obtain ⟨ht, hev⟩ := ampm_radial hζ hζΓ
  have hζT : ζ ∈ closedBall (0 : ℂ) 1 \ (Γ : Set ℂ) :=
    ⟨sphere_subset_closedBall hζ, hζΓ⟩
  have hT : Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * ζ) (𝓝[>] 0)
      (𝓝[closedBall (0 : ℂ) 1 \ (Γ : Set ℂ)] ζ) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, hev.mono fun s hs => ⟨ball_subset_closedBall hs.1, hs.2⟩⟩
  have h1 := (hg ζ hζT).tendsto.comp hT
  have h2 : Tendsto (g ∘ fun s : ℝ => ((1 - s : ℝ) : ℂ) * ζ) (𝓝[>] 0) (𝓝 M) :=
    tendsto_const_nhds.congr' (hev.mono fun s hs => (hM _ hs).symm)
  exact tendsto_nhds_unique h1 h2

theorem ampm_ccwLoop_mem (t : ℝ) : ccwLoop 1 t ∈ sphere (0 : ℂ) 1 := by
  rw [ccwLoop, mem_sphere_zero_iff_norm, norm_mul, Complex.norm_exp_ofReal_mul_I]
  simp

/-- A constant loop has winding number `0`. -/
theorem ampm_hasLoopWind_const {f : ℝ → ℂ} (hc : Continuous f) (hp : Function.Periodic f 1)
    (h0 : ∀ t, f t ≠ 0) (hconst : ∀ t, f t = f 0) : HasLoopWind f 0 := by
  refine ⟨hc, hp, h0, fun _ => Complex.arg (f 0), continuous_const, fun t => ?_, by simp⟩
  rw [hconst t]
  exact (Complex.norm_mul_exp_arg_mul_I (f 0)).symm

theorem aCoord_neg_and_boundary_pos_of_isDiskCurve_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ)
    (z₀ : ℂ) (A : Set ℂ) (hA : A ⊆ ball 0 ρ) (Γ : Finset ℂ) (u : ℂ → V 1)
    (hu : IsDiskCurve H J e z₀ A Γ u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    (∀ z ∈ ball (0 : ℂ) 1 \ Γ, aCoord H (u z) < 0) ∧
      (∀ t : ℝ, 0 < liouville (u (ccwLoop 1 t)) (deriv (fun s => u (ccwLoop 1 s)) t)) ∧
      (Γ = ∅ → 0 < dlambdaEnergy H (ball 0 1) u) := by
  obtain ⟨hΓb, hsm, hne, hhol, -, c, ⟨hc, hwind⟩⟩ := hu
  set U : Set ℂ := ball (0 : ℂ) 1 \ (Γ : Set ℂ) with hUdef
  set T : Set ℂ := closedBall (0 : ℂ) 1 \ (Γ : Set ℂ) with hTdef
  have hΓcl : IsClosed (Γ : Set ℂ) := Γ.finite_toSet.isClosed
  have hUo : IsOpen U := isOpen_ball.sdiff hΓcl
  have hUT : U ⊆ T := Set.diff_subset_diff_left ball_subset_closedBall
  have hUc : IsPreconnected U := ampm_isPreconnected_ball_diff Γ.finite_toSet.countable
  set a : ℂ → ℝ := fun z => aCoord H (u z) with ha
  set w : ℂ → V 1 := fun z => proj H (u z) with hw
  have huU : ContDiffOn ℝ ∞ u U := hsm.mono hUT
  obtain ⟨haU, hΔ⟩ := laplacian_aCoord_eq_dlambdaDensity H hH J hJ U hUo u huU
    (fun z hz => hne z (hUT hz)) hhol
  have hadm : Admissible (fun _ : ℝ => (1 : ℝ)) :=
    ⟨contDiff_const, monotone_const, fun _ => ⟨zero_le_one, le_rfl⟩⟩
  have hdens : ∀ z ∈ U, 0 ≤ dlambdaDensity H u z := fun z hz =>
    (energyDensity_nonneg_of_isJHolomorphicOn H hH J hJ U u (fun z hz => hne z (hUT hz)) hhol
      _ hadm hz).2
  have hΔnn : ∀ z ∈ U, 0 ≤ Δ a z := fun z hz => by rw [hΔ z hz]; exact hdens z hz
  have haU2 : ContDiffOn ℝ 2 a U := haU.of_le (WithTop.coe_le_coe.2 le_top)
  -- smoothness up to the boundary
  have haT : ContDiffOn ℝ ∞ a T := fun z hz =>
    (ampm_contDiffAt_aCoord H hH (hne z hz)).comp_contDiffWithinAt z (hsm z hz)
  have hwT : ContDiffOn ℝ ∞ w T := fun z hz =>
    (ampm_contDiffAt_proj H hH (hne z hz)).comp_contDiffWithinAt z (hsm z hz)
  have hacT : ContinuousOn a T := haT.continuousOn
  -- boundary values
  have hbd : ∀ ζ ∈ sphere (0 : ℂ) 1, u ζ ≠ 0 ∧ w ζ = u ζ ∧ a ζ = 0 := by
    intro ζ hζ
    obtain ⟨t, rfl⟩ := ampm_exists_ccwLoop hζ
    rw [(hc t).2]
    have hS : H (e (c t)) = 1 := he.2.2.1 (hA (hc t).1)
    obtain ⟨h1, h2, h3⟩ := ampm_of_mem H hH _ hS
    exact ⟨h1, by simp only [hw, (hc t).2, h2], by simp only [ha, (hc t).2, h3]⟩
  have hsphereT : sphere (0 : ℂ) 1 ⊆ T := by
    intro ζ hζ
    refine ⟨sphere_subset_closedBall hζ, fun h => ?_⟩
    have := hΓb h; rw [mem_ball_zero_iff] at this
    rw [mem_sphere_zero_iff_norm] at hζ; linarith
  have h1sph : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  -- the case `a ≡ 0` without punctures is impossible
  have hnc : Γ = ∅ → ¬ ∀ z ∈ ball (0 : ℂ) 1, a z = 0 := by
    intro hΓe ha0
    have hU1 : U = ball (0 : ℂ) 1 := by simp [hUdef, hΓe]
    have hDa : ∀ z ∈ ball (0 : ℂ) 1, fderiv ℝ a z = 0 := by
      intro z hz
      have hev : a =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) ha0
      rw [hev.fderiv_eq]; simp
    have hDu : ∀ z ∈ ball (0 : ℂ) 1, fderiv ℝ u z = 0 := by
      intro z hz
      have hzU : z ∈ U := hU1 ▸ hz
      have hev : a =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) ha0
      have hΔ0 : Δ a z = 0 := by
        rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]; simp
      obtain ⟨hdu, hdb⟩ := hhol z hzU
      exact fderiv_eq_zero_of_dlambdaDensity_eq_zero H hH J hJ u z hdu (hne z (hUT hzU)) hdb
        (hDa z hz) (by rw [← hΔ z hzU, hΔ0])
    have hconst : ∀ z ∈ ball (0 : ℂ) 1, u z = u 0 := by
      intro z hz
      have hdiff : DifferentiableOn ℝ u (ball (0 : ℂ) 1) := fun y hy =>
        ((hhol y (hU1 ▸ hy)).1).differentiableWithinAt
      exact (convex_ball (0 : ℂ) 1).is_const_of_fderivWithin_eq_zero hdiff
        (fun y hy => by rw [fderivWithin_of_isOpen isOpen_ball hy]; exact hDu y hy) hz
        (mem_ball_self one_pos)
    have hsph : ∀ ζ ∈ sphere (0 : ℂ) 1, u ζ = u 0 :=
      fun ζ hζ => ampm_eq_on_sphere hΓb hsm.continuousOn (fun z hz => hconst z hz.1) hζ
    have hct : ∀ t, c t = c 0 := by
      intro t
      have e1 : e (c t) = e (c 0) := by
        rw [← (hc t).2, ← (hc 0).2, hsph _ (ampm_ccwLoop_mem t), hsph _ (ampm_ccwLoop_mem 0)]
      exact he.2.2.2.1 (hA (hc t).1) (hA (hc 0).1) e1
    have hw0 : HasLoopWind (fun t => c t - z₀) 0 :=
      ampm_hasLoopWind_const hwind.1 hwind.2.1 hwind.2.2.1 (fun t => by simp only [hct t])
    have := hasLoopWind_unique hwind hw0
    norm_num at this
  -- Part (1): `a < 0` in the interior
  have hneg : ∀ z ∈ U, a z < 0 := by
    -- near each puncture `a < 0`
    have hloc : ∀ p ∈ Γ, ∃ r > 0, ∀ z ∈ ball p r, z ≠ p → a z < 0 := by
      intro p hp
      have := (hΓ p hp).eventually (eventually_lt_atBot 0)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at this
      obtain ⟨r, hr, h⟩ := this
      exact ⟨r, hr, fun z hz hzp => h hz hzp⟩
    choose! r hr hrloc using hloc
    set K : Set ℂ := closedBall (0 : ℂ) 1 \ ⋃ p ∈ Γ, ball p (r p) with hK
    have hKc : IsCompact K := (isCompact_closedBall 0 1).diff
      (isOpen_biUnion fun p _ => isOpen_ball)
    have hKT : K ⊆ T := by
      intro z hz
      refine ⟨hz.1, fun hzΓ => hz.2 ?_⟩
      exact Set.mem_biUnion hzΓ (mem_ball_self (hr z hzΓ))
    have hle : ∀ z ∈ U, a z ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨z₁, hz₁, hpos⟩ := hcon
      have hz₁K : z₁ ∈ K := by
        refine ⟨ball_subset_closedBall hz₁.1, fun hmem => ?_⟩
        obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.1 hmem
        have := hrloc p hp z₁ hzp (fun h => hz₁.2 (h ▸ hp))
        linarith
      obtain ⟨p, hpK, hpmax⟩ := hKc.exists_isMaxOn ⟨z₁, hz₁K⟩ (hacT.mono hKT)
      have hap : 0 < a p := lt_of_lt_of_le hpos (hpmax hz₁K)
      have hpU : p ∈ U := by
        refine ⟨?_, (hKT hpK).2⟩
        rcases (mem_closedBall_zero_iff.1 hpK.1).lt_or_eq with h | h
        · exact mem_ball_zero_iff.2 h
        · have := (hbd p (by simpa using h)).2.2; linarith
      have hmaxU : ∀ z ∈ U, a z ≤ a p := by
        intro z hz
        by_cases hzK : z ∈ K
        · exact hpmax hzK
        · have : z ∈ ⋃ p ∈ Γ, ball p (r p) := by
            by_contra h; exact hzK ⟨ball_subset_closedBall hz.1, h⟩
          obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.1 this
          have := hrloc q hq z hzq (fun h => hz.2 (h ▸ hq))
          linarith
      have hc' := eq_of_isMaxOn_of_laplacian_nonneg hUo hUc haU2 hΔnn hpU hmaxU
      have := ampm_eq_on_sphere hΓb hacT hc' h1sph
      have h0 := (hbd 1 h1sph).2.2
      linarith
    intro z hz
    rcases (hle z hz).lt_or_eq with h | h
    · exact h
    exfalso
    have hc' := eq_of_isMaxOn_of_laplacian_nonneg hUo hUc haU2 hΔnn hz
      (fun y hy => by rw [h]; exact hle y hy)
    rw [h] at hc'
    by_cases hΓe : Γ = ∅
    · apply hnc hΓe
      intro y hy
      exact hc' y (by simp [hUdef, hΓe, hy])
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hΓe
      have h1 := (hΓ p hp).eventually (eventually_lt_atBot (-1))
      have hpb : ball (0 : ℂ) 1 ∈ 𝓝 p := isOpen_ball.mem_nhds (hΓb hp)
      have hfin : ((Γ : Set ℂ) \ {p})ᶜ ∈ 𝓝 p :=
        ((Γ.finite_toSet.diff).isClosed).isOpen_compl.mem_nhds (fun h => h.2 rfl)
      have h2 : ∀ᶠ y in 𝓝[≠] p, y ∈ U := by
        filter_upwards [nhdsWithin_le_nhds hpb, nhdsWithin_le_nhds hfin, self_mem_nhdsWithin]
          with y hy1 hy2 hy3
        refine ⟨hy1, fun hyΓ => hy2 ⟨hyΓ, hy3⟩⟩
      obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
      have := hc' y hy2
      simp only [ha] at this hy1
      linarith
  refine ⟨hneg, ?_, ?_⟩
  · -- Part (2): the boundary loop is positively transverse to `ξ`
    intro t
    set ζ := ccwLoop 1 t with hζdef
    have hζ : ζ ∈ sphere (0 : ℂ) 1 := ampm_ccwLoop_mem t
    have hζT : ζ ∈ T := hsphereT hζ
    obtain ⟨hu0ζ, hwζ, haζ⟩ := hbd ζ hζ
    have hζΓ : ζ ∉ (Γ : Set ℂ) := hζT.2
    have hζn : ‖ζ‖ = 1 := by simpa using hζ
    obtain ⟨r₀, hr₀, hr₀Γ⟩ := Metric.isOpen_iff.1 hΓcl.isOpen_compl ζ hζΓ
    -- unique differentiability on `T`
    have hUD : UniqueDiffOn ℝ T := by
      intro z hz
      have hzc : (Γ : Set ℂ)ᶜ ∈ 𝓝 z := hΓcl.isOpen_compl.mem_nhds hz.2
      have hcb : UniqueDiffOn ℝ (closedBall (0 : ℂ) 1) :=
        uniqueDiffOn_convex (convex_closedBall 0 1)
          ⟨0, by rw [interior_closedBall (0 : ℂ) one_ne_zero]; exact mem_ball_self one_pos⟩
      have := (hcb z hz.1).inter hzc
      rwa [← Set.diff_eq] at this
    set Fa : ℂ → ℂ →L[ℝ] ℝ := fun z => fderivWithin ℝ a T z with hFa
    set Fw : ℂ → ℂ →L[ℝ] V 1 := fun z => fderivWithin ℝ w T z with hFw
    have hFaC : ContinuousOn Fa T := haT.continuousOn_fderivWithin hUD (by simp)
    have hFwC : ContinuousOn Fw T := hwT.continuousOn_fderivWithin hUD (by simp)
    -- the Cauchy–Riemann identity at `ζ`
    have hCR : ∀ v : ℂ, liouville (w ζ) (Fw ζ (Complex.I * v)) = Fa ζ v := by
      intro v
      set E : ℂ → ℝ := fun z => liouville (w z) (Fw z (Complex.I * v)) - Fa z v with hE
      have hEc : ContinuousOn E T := by
        have h1 : ContinuousOn (fun z => liouville (w z) (Fw z (Complex.I * v))) T := by
          have : (fun z => liouville (w z) (Fw z (Complex.I * v))) =
              fun z => (1 / 2 : ℝ) * ampmOm 1 (w z) (Fw z (Complex.I * v)) := by
            funext z; rw [ampmOm_apply]; unfold liouville; ring
          rw [this]
          exact continuousOn_const.mul
            (((ampmOm 1).continuous.comp_continuousOn hwT.continuousOn).clm_apply
              (hFwC.clm_apply continuousOn_const))
        exact h1.sub (hFaC.clm_apply continuousOn_const)
      have hE0 : ∀ z ∈ U, E z = 0 := by
        intro z hz
        have hTz : T ∈ 𝓝 z := mem_of_superset (hUo.mem_nhds hz) hUT
        obtain ⟨hdu, hdb⟩ := hhol z hz
        obtain ⟨cr1, cr2⟩ := ka_cr H hH J hJ u z hdu (hne z (hUT hz)) hdb
        unfold ds dt at cr1 cr2
        simp only [hE, hFa, hFw, fderivWithin_of_mem_nhds hTz]
        have hIv : Complex.I * v = v.re • Complex.I + (-v.im) • (1 : ℂ) := by
          apply Complex.ext <;> simp
        have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
          apply Complex.ext <;> simp
        rw [hIv, map_add, map_smul, map_smul]
        conv_rhs => skip
        have hav : fderiv ℝ a z v = v.re * fderiv ℝ a z 1 + v.im * fderiv ℝ a z Complex.I := by
          conv_lhs => rw [hv]
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        rw [hav, cr1, cr2]
        unfold liouville
        simp only [ka_om_add_right, ka_om_smul_right]
        ring
      have := ampm_eq_on_sphere hΓb hEc hE0 hζ
      simp only [hE] at this
      linarith
    -- the derivative of `u` along the boundary loop
    have hda : HasFDerivWithinAt a (Fa ζ) T ζ :=
      ((haT ζ hζT).differentiableWithinAt (by simp)).hasFDerivWithinAt
    have hdw : HasFDerivWithinAt w (Fw ζ) T ζ :=
      ((hwT ζ hζT).differentiableWithinAt (by simp)).hasFDerivWithinAt
    have hexp := (hda.const_mul 2).exp
    have hprod := hexp.smul hdw
    have hu' := hprod.congr (f₁ := u) (fun z hz => (ampm_exp_smul H hH (u z) (hne z hz)).symm)
      (ampm_exp_smul H hH (u ζ) hu0ζ).symm
    have hloop : HasDerivAt (ccwLoop 1) (Complex.I * ((2 * π : ℝ) • ζ)) t := by
      have h1 : HasDerivAt (fun s : ℝ => (((2 * π * s : ℝ) : ℂ) * Complex.I))
          (((2 * π : ℝ) : ℂ) * Complex.I) t := by
        have := (((hasDerivAt_id t).const_mul (2 * π)).ofReal_comp).mul_const Complex.I
        simpa using this
      have h2 := (h1.cexp).const_mul ((1 : ℝ) : ℂ)
      have hfun : ccwLoop 1 = fun s : ℝ => ((1 : ℝ) : ℂ) *
          Complex.exp (((2 * π * s : ℝ) : ℂ) * Complex.I) := by
        funext s; rfl
      rw [hfun]
      refine h2.congr_deriv ?_
      rw [hζdef, Complex.real_smul]
      simp only [ccwLoop]
      push_cast
      ring
    have hcomp := hu'.comp_hasDerivWithinAt (s := Set.univ) t hloop.hasDerivWithinAt
      (fun s _ => hsphereT (ampm_ccwLoop_mem s))
    have hder : deriv (fun s => u (ccwLoop 1 s)) t =
        (Real.exp (2 * a ζ) • Fw ζ +
          (Real.exp (2 * a ζ) • (2 : ℝ) • Fa ζ).smulRight (w ζ))
          (Complex.I * ((2 * π : ℝ) • ζ)) :=
      (hasDerivWithinAt_univ.1 hcomp).deriv
    rw [hder]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, haζ, mul_zero, Real.exp_zero, one_smul]
    have hlin : liouville (u ζ) (Fw ζ (Complex.I * ((2 * π : ℝ) • ζ)) +
        ((2 : ℝ) • Fa ζ (Complex.I * ((2 * π : ℝ) • ζ))) • w ζ) =
        liouville (w ζ) (Fw ζ (Complex.I * ((2 * π : ℝ) • ζ))) := by
      rw [← hwζ]
      unfold liouville
      rw [ka_om_add_right, ka_om_smul_right, ka_om_self]
      ring
    rw [hlin, hCR, map_smul, smul_eq_mul]
    -- Hopf's lemma on a small disk inside the unit disk, tangent at `ζ`
    set R : ℝ := min (r₀ / 4) (1 / 2) with hRdef
    have hR : 0 < R := lt_min (by linarith) (by norm_num)
    have hR1 : R ≤ 1 / 2 := min_le_right _ _
    have hRr : R ≤ r₀ / 4 := min_le_left _ _
    set c₀ : ℂ := ((1 - R : ℝ) : ℂ) * ζ with hc₀
    have hc₀n : ‖c₀‖ = 1 - R := by
      rw [hc₀, norm_mul, Complex.norm_real, Real.norm_eq_abs, hζn, abs_of_pos (by linarith)]
      ring
    have hζc : ζ - c₀ = ((R : ℝ) : ℂ) * ζ := by rw [hc₀]; push_cast; ring
    have hζcn : ‖ζ - c₀‖ = R := by
      rw [hζc, norm_mul, Complex.norm_real, Real.norm_eq_abs, hζn, abs_of_pos hR]; ring
    have hcl : closedBall c₀ R ⊆ T := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      refine ⟨?_, fun hzΓ => ?_⟩
      · rw [mem_closedBall_zero_iff]
        calc ‖z‖ = ‖(z - c₀) + c₀‖ := by ring_nf
          _ ≤ ‖z - c₀‖ + ‖c₀‖ := norm_add_le _ _
          _ ≤ 1 := by rw [hc₀n]; linarith
      · have : z ∈ ball ζ r₀ := by
          rw [mem_ball, dist_eq_norm]
          calc ‖z - ζ‖ = ‖(z - c₀) - (ζ - c₀)‖ := by ring_nf
            _ ≤ ‖z - c₀‖ + ‖ζ - c₀‖ := norm_sub_le _ _
            _ < r₀ := by rw [hζcn]; linarith
        exact hr₀Γ this hzΓ
    have hball : ball c₀ R ⊆ U := by
      intro z hz
      refine ⟨?_, (hcl (ball_subset_closedBall hz)).2⟩
      rw [mem_ball, dist_eq_norm] at hz
      rw [mem_ball_zero_iff]
      calc ‖z‖ = ‖(z - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖z - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ < 1 := by rw [hc₀n]; linarith
    have hζs : ζ ∈ sphere c₀ R := by rw [mem_sphere, dist_eq_norm, hζcn]
    have hhopf := hopf_lemma_disk hR (hacT.mono hcl) (haU2.mono hball)
      (fun z hz => hΔnn z (hball hz)) (fun z hz => by rw [haζ]; exact hneg z (hball hz)) hζs
      (hda.mono hcl)
    rw [hζc, ← Complex.real_smul, map_smul, smul_eq_mul] at hhopf
    have hpos : 0 < Fa ζ ζ := pos_of_mul_pos_right hhopf hR.le
    have := Real.pi_pos
    positivity
  · -- Part (3): without punctures the `dλ`-energy is positive
    intro hΓe
    have hU1 : U = ball (0 : ℂ) 1 := by simp [hUdef, hΓe]
    by_contra hcon
    have hzero : dlambdaEnergy H (ball 0 1) u = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hcon)
    -- the density vanishes on the disk
    have hd0 : ∀ z ∈ ball (0 : ℂ) 1, dlambdaDensity H u z = 0 := by
      intro z₁ hz₁
      by_contra hne1
      have hpos : 0 < dlambdaDensity H u z₁ :=
        lt_of_le_of_ne (hdens z₁ (hU1 ▸ hz₁)) (Ne.symm hne1)
      have hcont : ContinuousOn (dlambdaDensity H u) (ball (0 : ℂ) 1) := by
        have hwU : ContDiffOn ℝ ∞ w (ball (0 : ℂ) 1) := hU1 ▸ (hwT.mono hUT)
        have hfw : ContinuousOn (fderiv ℝ w) (ball (0 : ℂ) 1) :=
          hwU.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
        have : dlambdaDensity H u =
            fun z => ampmOm 1 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) := by
          funext z; rw [ampmOm_apply]; rfl
        rw [this]
        exact ((ampmOm 1).continuous.comp_continuousOn (hfw.clm_apply continuousOn_const)).clm_apply
          (hfw.clm_apply continuousOn_const)
      have hev : ∀ᶠ z in 𝓝 z₁, z ∈ ball (0 : ℂ) 1 ∧
          dlambdaDensity H u z₁ / 2 < dlambdaDensity H u z :=
        Filter.Eventually.and (isOpen_ball.mem_nhds hz₁) ((hcont.continuousAt (isOpen_ball.mem_nhds hz₁)).eventually
          (lt_mem_nhds (half_lt_self hpos)))
      obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 hev
      have hlt : 0 < dlambdaEnergy H (ball 0 1) u := by
        unfold dlambdaEnergy
        calc (0 : ENNReal) < ENNReal.ofReal (dlambdaDensity H u z₁ / 2) * volume (ball z₁ r) :=
              ENNReal.mul_pos (by simpa using half_pos hpos) (measure_ball_pos volume z₁ hr).ne'
          _ = ∫⁻ _ in ball z₁ r, ENNReal.ofReal (dlambdaDensity H u z₁ / 2) :=
              (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ z in ball z₁ r, ENNReal.ofReal (dlambdaDensity H u z) :=
              setLIntegral_mono' measurableSet_ball
                (fun z hz => ENNReal.ofReal_le_ofReal (hsub hz).2.le)
          _ ≤ ∫⁻ z in ball 0 1, ENNReal.ofReal (dlambdaDensity H u z) :=
              lintegral_mono_set (fun z hz => (hsub hz).1)
      rw [hzero] at hlt
      exact lt_irrefl _ hlt
    -- `-a` is harmonic, positive inside and zero on the circle
    set b : ℂ → ℝ := fun z => -a z with hb
    have hbU : ∀ z ∈ U, 0 ≤ Δ b z := by
      intro z hz
      have : b = -a := rfl
      rw [this, InnerProductSpace.laplacian_neg, Pi.neg_apply, hΔ z hz, hd0 z (hU1 ▸ hz)]
      simp
    have hbcT : ContinuousOn b T := hacT.neg
    have h0U : (0 : ℂ) ∈ U := hU1 ▸ mem_ball_self one_pos
    have hTcb : closedBall (0 : ℂ) 1 ⊆ T := by
      intro z hz; exact ⟨hz, by simp [hΓe]⟩
    obtain ⟨p, hpK, hpmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
      ⟨0, mem_closedBall_self zero_le_one⟩ (hbcT.mono hTcb)
    have hbp : 0 < b p := by
      have := hpmax (mem_closedBall_self zero_le_one : (0 : ℂ) ∈ closedBall 0 1)
      have h0 := hneg 0 h0U
      simp only [Set.mem_setOf_eq, hb] at this ⊢; linarith
    have hpU : p ∈ U := by
      rw [hU1]
      rcases (mem_closedBall_zero_iff.1 hpK).lt_or_eq with h | h
      · exact mem_ball_zero_iff.2 h
      · have := (hbd p (by simpa using h)).2.2
        simp only [hb, this] at hbp; linarith
    have hc' := eq_of_isMaxOn_of_laplacian_nonneg hUo hUc haU2.neg hbU hpU
      (fun z hz => hpmax (ball_subset_closedBall (hU1 ▸ hz)))
    have := ampm_eq_on_sphere hΓb hbcT hc' h1sph
    have h0 := (hbd 1 h1sph).2.2
    simp only [hb, h0] at this
    linarith

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ)
    (z₀ : ℂ) (A : Set ℂ) (hA : A ⊆ ball 0 ρ) (Γ : Finset ℂ) (u : ℂ → V 1)
    (hu : IsDiskCurve H J e z₀ A Γ u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    (∀ z ∈ ball (0 : ℂ) 1 \ Γ, aCoord H (u z) < 0) ∧
      (∀ t : ℝ, 0 < liouville (u (ccwLoop 1 t)) (deriv (fun s => u (ccwLoop 1 s)) t)) ∧
      (Γ = ∅ → 0 < dlambdaEnergy H (ball 0 1) u) :=
  aCoord_neg_and_boundary_pos_of_isDiskCurve_aux H hH J hJ e ρ he z₀ A hA Γ u hu hΓ
