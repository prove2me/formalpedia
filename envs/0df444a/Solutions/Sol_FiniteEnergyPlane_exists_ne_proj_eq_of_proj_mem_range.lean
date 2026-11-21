-- Prove2me | solution 1 for FiniteEnergyPlane.exists_ne_proj_eq_of_proj_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T00:37:50.017144+00:00
-- url     : https://prove2.me/submissions/9a27f334-86e6-4fef-baed-5101f34a172e

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_immersion_transverse
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_reeb_spec

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

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Radial scaling in the symplectization: `proj` is invariant and `a` shifts by `log c / 2`. -/
theorem ff_proj_aCoord_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (c : ℝ) (hc : 0 < c) (y : V n) (hy : y ≠ 0) :
    proj H (c • y) = proj H y ∧ aCoord H (c • y) = aCoord H y + Real.log c / 2 := by
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 y hy
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := ⟨r, hr0, hr1⟩
  have e2 : ∃ r : ℝ, 0 < r ∧ H (r • (c • y)) = 1 :=
    ⟨r / c, div_pos hr0 hc, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']; exact hr1⟩
  have h1 : scaleToS H y = r := by
    unfold scaleToS
    rw [dif_pos e1]
    exact hru _ (Classical.choose_spec e1)
  have h2 : scaleToS H (c • y) = r / c := by
    unfold scaleToS
    rw [dif_pos e2]
    have hs2 := Classical.choose_spec e2
    have := hru (Classical.choose e2 * c) ⟨mul_pos hs2.1 hc, by rw [← smul_smul]; exact hs2.2⟩
    rw [← this, mul_div_cancel_right₀ _ hc.ne']
  refine ⟨?_, ?_⟩
  · unfold proj
    rw [h1, h2, smul_smul, div_mul_cancel₀ _ hc.ne']
  · unfold aCoord
    rw [h1, h2, Real.log_div hr0.ne' hc.ne']
    ring

theorem isNondegenerateEnd_shiftA_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u : ℂ → V n) (hu : ∀ z, u z ≠ 0) (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε : ℝ)
    (h : IsNondegenerateEnd H u e P ε) (c : ℝ) :
    IsNondegenerateEnd H (shiftA c u) e P ε := by
  obtain ⟨d, c', b, hb, h1, h2⟩ := h
  have hexp := Real.exp_pos (2 * c)
  have hs : ∀ z, proj H (shiftA c u z) = proj H (u z) ∧
      aCoord H (shiftA c u z) = aCoord H (u z) + c := by
    intro z
    have := ff_proj_aCoord_smul H hH _ hexp (u z) (hu z)
    refine ⟨this.1, ?_⟩
    have h3 := this.2
    rw [Real.log_exp] at h3
    simpa [shiftA, mul_div_assoc] using h3
  refine ⟨d + c, c', b, hb, ?_, ?_⟩
  · convert h1 using 2 with p
    simp only [endA, (hs _).2]
    ring
  · convert h2 using 3 with p
    simp only [endW, (hs _).1]

theorem isFastPlane_shiftA_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (c : ℝ) : IsFastPlane H J (shiftA c u) := by
  obtain ⟨hfe, ⟨P, hP, hnd⟩, hwind⟩ := hu
  have hexp := Real.exp_pos (2 * c)
  have h0 : ∀ z, u z ≠ 0 := fun z => hfe.2.1 z (Set.mem_univ z)
  refine ⟨?_, ⟨P, hP, isNondegenerateEnd_shiftA_aux H hH u h0 cylInf P 1 hnd c⟩, ?_⟩
  · have := (rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ u hfe 0 1 one_pos _ hexp).1
    have e : shiftA c u = fun w => Real.exp (2 * c) • u w := rfl
    rw [e]
    simpa using this
  · have hpi : piDs H (shiftA c u) = piDs H u := by
      have hw : (fun z => proj H (shiftA c u z)) = fun z => proj H (u z) := by
        funext z
        exact (ff_proj_aCoord_smul H hH _ hexp (u z) (h0 z)).1
      funext z
      have hw' : proj H (shiftA c u z) = proj H (u z) := congrFun hw z
      simp only [piDs, hw, hw']
    simpa only [HasWindPi, hpi] using hwind

end FiniteEnergyPlane

/-! Child B of Hryniewicz Lemma 6.24: meeting the asymptotic orbit forces a double point of
`proj ∘ u`. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

lemma mob_H_proj (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V 1) (hy : y ≠ 0) :
    H (proj H y) = 1 := (ka_scale_spec H hH y hy).2

lemma mob_ne_zero_of_mem (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V 1}
    (hx : H x = 1) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

lemma mob_proj_of_mem (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V 1}
    (hx : H x = 1) : proj H x = x := by
  have hx0 := mob_ne_zero_of_mem H hH hx
  obtain ⟨hs, hHs⟩ := ka_scale_spec H hH x hx0
  obtain ⟨r, -, hru⟩ := hH.2.1 x hx0
  have h1 : scaleToS H x = r := hru _ ⟨hs, hHs⟩
  have h2 : (1 : ℝ) = r := hru _ ⟨one_pos, by rw [one_smul]; exact hx⟩
  unfold proj
  rw [h1, ← h2, one_smul]

lemma mob_norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

lemma mob_continuous_cylInf (s : ℝ) : Continuous (fun t => cylInf s t) := by
  unfold cylInf ccwLoop
  fun_prop

theorem exists_ne_proj_eq_of_proj_mem_range_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (z₀ : ℂ)
    (hz₀ : proj H (u z₀) ∈ Set.range P.x) :
    ∃ z w : ℂ, z ≠ w ∧ proj H (u z) = proj H (u w) := by
  obtain ⟨τ₀, hτ₀⟩ := hz₀
  have hfu := hu.1
  have hsu : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfu.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfu.2.1 z trivial
  set wv : ℂ → V 1 := fun z => proj H (u z) with hwv
  have hwd : ContDiff ℝ ∞ wv := contDiff_iff_contDiffAt.2 fun z =>
    ((contDiffAt_aCoord_proj H hH (u z) (hu0 z)).2).comp z hsu.contDiffAt
  have hwS : ∀ z, H (wv z) = 1 := fun z => mob_H_proj H hH (u z) (hu0 z)
  set x₀ := P.x τ₀ with hx₀
  have hx₀S : H x₀ = 1 := P.mem τ₀
  have hwz₀ : wv z₀ = x₀ := hτ₀.symm
  set r₀ := reeb H x₀ with hr₀
  set Dw := fderiv ℝ wv z₀ with hDw
  have hxs : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  have hw1 : HasStrictFDerivAt wv Dw z₀ := hwd.contDiffAt.hasStrictFDerivAt (by simp)
  have hx1 : HasStrictDerivAt P.x r₀ τ₀ := by
    have := hxs.contDiffAt.hasStrictDerivAt (x := τ₀) (by simp)
    rwa [(P.hasDerivAt τ₀).deriv] at this
  -- the map `G` and its derivative
  set a : ℂ × ℝ × ℝ := (z₀, 0, 0) with ha
  set G : ℂ × ℝ × ℝ → V 1 := fun p => (1 + p.2.2) • (wv p.1 + (P.x (τ₀ + p.2.1) - x₀)) with hG
  set G' : ℂ × ℝ × ℝ →L[ℝ] V 1 :=
    Dw.comp (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)) +
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ))).smulRight r₀ +
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ))).smulRight x₀
    with hG'
  have hG'ap : ∀ p : ℂ × ℝ × ℝ, G' p = Dw p.1 + p.2.1 • r₀ + p.2.2 • x₀ := by
    intro p; simp [hG']
  have hGd : HasStrictFDerivAt G G' a := by
    have h1 : HasStrictFDerivAt (fun p : ℂ × ℝ × ℝ => wv p.1)
        (Dw.comp (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ))) a := hw1.comp a hasStrictFDerivAt_fst
    have hl : HasStrictFDerivAt (fun p : ℂ × ℝ × ℝ => τ₀ + p.2.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ))) a :=
      (hasStrictFDerivAt_snd.fst).const_add τ₀
    have hx1' : HasStrictFDerivAt P.x ((1 : ℝ →L[ℝ] ℝ).smulRight r₀) (τ₀ + a.2.1) := by
      rw [show τ₀ + a.2.1 = τ₀ by simp [ha]]; exact hx1.hasStrictFDerivAt
    have h2 := hx1'.comp a hl
    have h3 : HasStrictFDerivAt (fun p : ℂ × ℝ × ℝ => 1 + p.2.2)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ))) a :=
      (hasStrictFDerivAt_snd.snd).const_add 1
    have hF := h1.add (h2.sub_const x₀)
    have h4 := h3.smul hF
    refine h4.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    simp [hG'ap, ha, hwz₀, hx₀]
  -- injectivity of `G'`
  have hdHw : ∀ v, fderiv ℝ H x₀ (Dw v) = 0 := by
    intro v
    have hc : (fun z => H (wv z)) = fun _ => (1 : ℝ) := funext hwS
    have hHd : DifferentiableAt ℝ H (wv z₀) := (hH.1.differentiable (by simp)) _
    have := fderiv_comp z₀ hHd (hwd.differentiable (by simp) z₀)
    have h0 : fderiv ℝ (H ∘ wv) z₀ = 0 := by
      show fderiv ℝ (fun z => H (wv z)) z₀ = 0
      rw [hc]; exact fderiv_const_apply _
    rw [h0, hwz₀] at this
    have := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) this
    simpa using this.symm
  obtain ⟨-, hlR, hdR, -⟩ := reeb_spec H hH x₀ hx₀S
  have hr₀0 : r₀ ≠ 0 := by
    intro h; rw [← hr₀, h] at hlR; simp [liouville, omega0, dot] at hlR
  have hdx := hH.2.2 x₀ hx₀S
  have hinj : Function.Injective G' := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    rw [hG'ap] at hp
    have e1 : fderiv ℝ H x₀ (Dw p.1 + p.2.1 • r₀ + p.2.2 • x₀) = 0 := by rw [hp, map_zero]
    rw [map_add, map_add, map_smul, map_smul, hdHw, hdR, smul_eq_mul, smul_eq_mul] at e1
    have hρ : p.2.2 = 0 := by
      rcases mul_eq_zero.1 (by linarith : p.2.2 * fderiv ℝ H x₀ x₀ = 0) with h | h
      · exact h
      · linarith
    rw [hρ, zero_smul, add_zero] at hp
    have hv : p.1 = 0 := by
      by_contra hv
      apply isFastPlane_immersion_transverse H hH J hJ u hu z₀ p.1 hv (-p.2.1)
      show Dw p.1 = (-p.2.1) • reeb H (wv z₀)
      rw [hwz₀, neg_smul, ← hr₀]
      exact eq_neg_of_add_eq_zero_left hp
    rw [hv, map_zero, zero_add] at hp
    have hσ : p.2.1 = 0 := by
      rcases smul_eq_zero.1 hp with h | h
      · exact h
      · exact absurd h hr₀0
    exact Prod.ext hv (Prod.ext hσ hρ)
  have hdim : Module.finrank ℝ (ℂ × ℝ × ℝ) = Module.finrank ℝ (V 1) := by
    simp [Module.finrank_prod, Complex.finrank_real_complex]
  set eL := LinearMap.linearEquivOfInjective (G' : ℂ × ℝ × ℝ →ₗ[ℝ] V 1) hinj hdim
  set e' : (ℂ × ℝ × ℝ) ≃L[ℝ] V 1 := eL.toContinuousLinearEquiv
  have he' : (e' : ℂ × ℝ × ℝ →L[ℝ] V 1) = G' := ContinuousLinearMap.ext fun p => rfl
  have hGe : HasStrictFDerivAt G (e' : ℂ × ℝ × ℝ →L[ℝ] V 1) a := he' ▸ hGd
  set E := hGe.toOpenPartialHomeomorph G with hE
  have hEc : (E : ℂ × ℝ × ℝ → V 1) = G := hGe.toOpenPartialHomeomorph_coe
  have haE : a ∈ E.source := hGe.mem_toOpenPartialHomeomorph_source
  -- the open set `T'`
  set W : Set (ℂ × ℝ × ℝ) := {p | ‖p.1 - z₀‖ < 1 ∧ -1 < p.2.2} with hW
  have hWo : IsOpen W := by
    rw [hW, Set.setOf_and]
    exact (isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_const))
      continuous_const).inter (isOpen_lt continuous_const (continuous_snd.comp continuous_snd))
  set T' := E '' (E.source ∩ W) with hT'
  have hT'o : IsOpen T' := E.isOpen_image_source_inter hWo
  have hT'tgt : T' ⊆ E.target := by
    rintro _ ⟨p, hp, rfl⟩; exact E.map_source hp.1
  have hsymm : ∀ p ∈ E.source ∩ W, E.symm (G p) = p := by
    intro p hp; rw [← hEc]; exact E.left_inv hp.1
  -- the path `σ ↦ (z₀, σ, 0)`
  set γ : ℝ → ℂ × ℝ × ℝ := fun σ => (z₀, σ, 0) with hγ
  have hγc : Continuous γ := by fun_prop
  have hγ0 : γ 0 ∈ E.source ∩ W := ⟨haE, by simp [hW, hγ]⟩
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.1 ((E.open_source.inter hWo).preimage hγc) 0 hγ0
  set δ := δ₁ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hγmem : ∀ σ ∈ Icc (-δ) δ, γ σ ∈ E.source ∩ W := by
    intro σ hσ
    apply hball
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hσ.1, hσ.2]
  have hGγ : ∀ σ, G (γ σ) = P.x (τ₀ + σ) := by
    intro σ; simp [hG, hγ, hwz₀, hx₀]
  have hxT : ∀ σ ∈ Icc (-δ) δ, P.x (τ₀ + σ) ∈ T' := fun σ hσ =>
    ⟨γ σ, hγmem σ hσ, by rw [hEc, hGγ]⟩
  have hfx : ∀ σ ∈ Icc (-δ) δ, (E.symm (P.x (τ₀ + σ))).2.1 = σ := by
    intro σ hσ
    rw [← hGγ, hsymm _ (hγmem σ hσ)]
  set f : V 1 → ℝ := fun y => (E.symm y).2.1 with hf
  have hfc : ContinuousOn f T' :=
    (continuous_fst.comp continuous_snd).comp_continuousOn (E.continuousOn_symm.mono hT'tgt)
  -- compact arc and a uniform neighbourhood
  have hxc : Continuous P.x := hxs.continuous
  set K := (fun σ => P.x (τ₀ + σ)) '' Icc (-δ) δ with hK
  have hKc : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKT : K ⊆ T' := by rintro _ ⟨σ, hσ, rfl⟩; exact hxT σ hσ
  obtain ⟨η, hη, hthick⟩ := hKc.exists_thickening_subset_open hT'o hKT
  have hδm : δ ∈ Icc (-δ) δ := ⟨by linarith, le_rfl⟩
  have hδm' : -δ ∈ Icc (-δ) δ := ⟨le_rfl, by linarith⟩
  have hcp := (hfc.continuousAt (hT'o.mem_nhds (hxT δ hδm)))
  have hcm := (hfc.continuousAt (hT'o.mem_nhds (hxT (-δ) hδm')))
  obtain ⟨ηp, hηp, hp⟩ := Metric.continuousAt_iff.1 hcp δ hδpos
  obtain ⟨ηm, hηm, hm⟩ := Metric.continuousAt_iff.1 hcm δ hδpos
  set η' := min η (min ηp ηm) with hη'
  have hη'pos : 0 < η' := lt_min hη (lt_min hηp hηm)
  -- the end
  obtain ⟨d, c, b, hb, -, hWe⟩ := huP
  obtain ⟨s₁, hs₁⟩ := hWe (η' / 2) (by positivity)
  set s := max (max s₁ 0) (Real.log (‖z₀‖ + 2) / (2 * π)) with hs
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) (le_max_left _ _)
  have hss₁ : s₁ ≤ s := le_trans (le_max_left _ _) (le_max_left _ _)
  have hclose : ∀ t, dist (endW H u cylInf (s, t)) (P.x (P.T * t + c)) < η' := by
    intro t
    have h1 := hs₁ s hss₁ t
    simp only [one_mul] at h1
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    have hexp : 1 ≤ Real.exp (b * s) := Real.one_le_exp (mul_nonneg hb.le hs0)
    rw [dist_eq_norm]
    have : ‖endW H u cylInf (s, t) - P.x (P.T * t + c)‖ ≤ η' / 2 :=
      le_trans (le_mul_of_one_le_left (norm_nonneg _) hexp) h1
    linarith
  have hT := P.T_pos
  set tm := (τ₀ - δ - c) / P.T with htm
  set tp := (τ₀ + δ - c) / P.T with htp
  have hTt : ∀ t, P.T * t + c = τ₀ + (P.T * t + c - τ₀) := fun t => by ring
  have hTtm : P.T * tm + c = τ₀ + -δ := by rw [htm]; field_simp; ring
  have hTtp : P.T * tp + c = τ₀ + δ := by rw [htp]; field_simp; ring
  have htmp : tm ≤ tp := by
    rw [htm, htp]; exact div_le_div_of_nonneg_right (by linarith) hT.le
  have hinT : ∀ t ∈ Icc tm tp, endW H u cylInf (s, t) ∈ T' := by
    intro t ht
    apply hthick
    rw [mem_thickening_iff]
    refine ⟨P.x (P.T * t + c), ⟨P.T * t + c - τ₀, ⟨?_, ?_⟩, by
      show P.x (τ₀ + (P.T * t + c - τ₀)) = _; congr 1; ring⟩, ?_⟩
    · have := mul_le_mul_of_nonneg_left ht.1 hT.le
      rw [htm, mul_div_cancel₀ _ hT.ne'] at this; linarith
    · have := mul_le_mul_of_nonneg_left ht.2 hT.le
      rw [htp, mul_div_cancel₀ _ hT.ne'] at this; linarith
    · exact lt_of_lt_of_le (hclose t) (min_le_left _ _)
  set g : ℝ → ℝ := fun t => f (endW H u cylInf (s, t)) with hg
  have hendc : Continuous fun t => endW H u cylInf (s, t) :=
    hwd.continuous.comp (mob_continuous_cylInf s)
  have hgc : ContinuousOn g (Icc tm tp) :=
    hfc.comp hendc.continuousOn (fun t ht => hinT t ht)
  have hgp : 0 < g tp := by
    have h1 : dist (endW H u cylInf (s, tp)) (P.x (τ₀ + δ)) < ηp := by
      rw [← hTtp]; exact lt_of_lt_of_le (hclose tp)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have h2 := hp h1
    rw [show f (P.x (τ₀ + δ)) = δ from hfx δ hδm, Real.dist_eq, abs_lt] at h2
    simp only [hg]; linarith [h2.1]
  have hgm : g tm < 0 := by
    have h1 : dist (endW H u cylInf (s, tm)) (P.x (τ₀ + -δ)) < ηm := by
      rw [← hTtm]; exact lt_of_lt_of_le (hclose tm)
        (le_trans (min_le_right _ _) (min_le_right _ _))
    have h2 := hm h1
    rw [show f (P.x (τ₀ + -δ)) = -δ from hfx (-δ) hδm', Real.dist_eq, abs_lt] at h2
    simp only [hg]; linarith [h2.2]
  obtain ⟨tst, htst, hgt⟩ := intermediate_value_Icc htmp hgc ⟨hgm.le, hgp.le⟩
  obtain ⟨p, hpSW, hpG⟩ := hinT tst htst
  rw [hEc] at hpG
  have hp21 : p.2.1 = 0 := by
    have := hsymm p hpSW
    rw [hpG] at this
    have h2 : g tst = p.2.1 := by simp only [hg, hf]; rw [this]
    rw [← h2, hgt]
  have hρ : 0 < 1 + p.2.2 := by linarith [hpSW.2.2]
  have hyst : endW H u cylInf (s, tst) = (1 + p.2.2) • wv p.1 := by
    rw [← hpG]; simp [hG, hp21, hx₀]
  set w := cylInf s tst with hwdef
  have hpw : wv w = wv p.1 := by
    have h1 : proj H (wv w) = wv w := mob_proj_of_mem H hH (hwS w)
    have h2 : proj H ((1 + p.2.2) • wv p.1) = wv p.1 := by
      rw [(ff_proj_aCoord_smul H hH _ hρ _ (mob_ne_zero_of_mem H hH (hwS p.1))).1]
      exact mob_proj_of_mem H hH (hwS p.1)
    have : wv w = (1 + p.2.2) • wv p.1 := hyst
    rw [← h1, this, h2]
  refine ⟨p.1, w, ?_, hpw.symm⟩
  intro hzw
  have hn1 : ‖p.1‖ < ‖z₀‖ + 1 := by
    have := hpSW.2.1
    have h3 := norm_sub_norm_le p.1 z₀
    linarith
  have hn2 : ‖z₀‖ + 2 ≤ ‖w‖ := by
    rw [hwdef, mob_norm_cylInf]
    have hpos : 0 < ‖z₀‖ + 2 := by positivity
    have h1 : Real.log (‖z₀‖ + 2) / (2 * π) ≤ s := le_max_right _ _
    have h2 : Real.log (‖z₀‖ + 2) ≤ 2 * π * s := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    calc ‖z₀‖ + 2 = Real.exp (Real.log (‖z₀‖ + 2)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (2 * π * s) := Real.exp_le_exp.2 h2
  rw [hzw] at hn1
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (z₀ : ℂ)
    (hz₀ : proj H (u z₀) ∈ Set.range P.x) :
    ∃ z w : ℂ, z ≠ w ∧ proj H (u z) = proj H (u w) :=
  FiniteEnergyPlane.exists_ne_proj_eq_of_proj_mem_range_aux H hH J hJ P u hu huP z₀ hz₀
