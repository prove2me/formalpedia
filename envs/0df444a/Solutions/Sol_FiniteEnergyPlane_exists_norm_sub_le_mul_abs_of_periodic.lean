-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_sub_le_mul_abs_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T15:33:27.693181+00:00
-- url     : https://prove2.me/submissions/8b4d28ec-4fd0-444e-b108-f700541acdd8

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_isInXi_linearizedReeb_deriv
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open FiniteEnergyPlane
open scoped ContDiff Topology in
open scoped ContDiff Topology
open MeasureTheory Metric Filter Topology Set

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

/-!
# Helpers (published standalone) for `exists_page_direction_of_hasAsymptoticEigenvector` (87bebfe8)

Bounds for periodic maps, a uniform lower bound for a unitary frame, nonvanishing of an
asymptotic eigenvector (frame version, no compatibility hypothesis on `J`), Lipschitz bounds
from `C^∞` decay, and continuity of a solution of `F x (G x) = y x` with `F x` strictly monotone.
-/


namespace FiniteEnergyPlane

noncomputable section

theorem pd_periodic_bound {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} (hf : Continuous f)
    (hper : Function.Periodic f 1) : ∃ B, 0 ≤ B ∧ ∀ t, ‖f t‖ ≤ B := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
  obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico zero_lt_one t 0
  rw [hyt]
  exact (hK y ⟨hy.1, by linarith [hy.2]⟩).trans (le_max_left _ _)

theorem pd_periodic_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f 1) :
    ∃ L, 0 ≤ L ∧ ∀ x y, ‖f x - f y‖ ≤ L * |x - y| := by
  have hd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdper : Function.Periodic (deriv f) 1 := by
    intro t
    have h := deriv_comp_add_const (f := f) (a := (1 : ℝ)) (x := t)
    have hfun : (fun x => f (x + 1)) = f := funext hper
    rw [hfun] at h
    exact h.symm
  obtain ⟨B, hB0, hB⟩ := pd_periodic_bound hd hdper
  have hlip : LipschitzWith ⟨B, hB0⟩ f := by
    refine lipschitzWith_of_nnnorm_deriv_le (hf.differentiable one_ne_zero) (fun x => ?_)
    exact NNReal.coe_le_coe.1 (hB x)
  refine ⟨B, hB0, fun x y => ?_⟩
  have := hlip.dist_le_mul x y
  rw [dist_eq_norm, Real.dist_eq] at this
  exact this

theorem pd_abs_omega0_le (x y : V 1) : |omega0 x y| ≤ 4 * (‖x‖ * ‖y‖) := by
  unfold omega0 dot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hj : ∀ k, |j0 x k| ≤ ‖x‖ := by
    intro k
    unfold j0
    split_ifs
    · rw [abs_neg]; exact norm_le_pi_norm x _
    · exact norm_le_pi_norm x _
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (2 * (1 + 1)))),
      |j0 x k * y k| ≤ ‖x‖ * ‖y‖ := by
    intro k _
    rw [abs_mul]
    exact mul_le_mul (hj k) (norm_le_pi_norm y k) (abs_nonneg _) (norm_nonneg _)
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans (le_of_eq ?_)
  simp

/-- `J₀` as a continuous linear map. -/
def pdJ0L : CauchyRiemannIndex.Vec 1 →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1))

theorem pdJ0L_apply (a : CauchyRiemannIndex.Vec 1) :
    pdJ0L a = Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a := rfl

theorem pd_J0_J0 (a : CauchyRiemannIndex.Vec 1) :
    Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1)
      (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) = -a := by
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul, CauchyRiemannIndex.J₀, Matrix.J_squared,
    map_neg, Matrix.toLpLin_one]
  rfl

theorem pd_norm_J0_le (a : CauchyRiemannIndex.Vec 1) :
    ‖Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a‖ ≤ ‖pdJ0L‖ * ‖a‖ := by
  rw [← pdJ0L_apply]; exact pdJ0L.le_opNorm a

section Frame

variable {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
  {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1}

theorem pd_frame_bound (hZ : IsUnitaryXiFrame J P Z) : ∃ B, 0 ≤ B ∧ ∀ t, ‖Z t‖ ≤ B :=
  pd_periodic_bound hZ.1.continuous hZ.2.1

theorem pd_frame_lower (hZ : IsUnitaryXiFrame J P Z) :
    ∃ c > 0, ∀ t a, c * ‖a‖ ≤ ‖Z t a‖ := by
  obtain ⟨Zm, hZm0, hZm⟩ := pd_frame_bound hZ
  set j := ‖pdJ0L‖ with hj
  have hj0 : 0 ≤ j := norm_nonneg _
  refine ⟨(j * (4 * Zm) + 1)⁻¹, by positivity, fun t a => ?_⟩
  set b := Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a with hb
  have hin := (hZ.2.2 t).2.2.2 a b
  rw [← hb, real_inner_self_eq_norm_sq] at hin
  have hom := pd_abs_omega0_le (Z t a) (Z t b)
  rw [hin, abs_of_nonneg (by positivity)] at hom
  have hZb : ‖Z t b‖ ≤ Zm * ‖b‖ := ((Z t).le_opNorm b).trans
    (mul_le_mul_of_nonneg_right (hZm t) (norm_nonneg _))
  have hb' : ‖b‖ ≤ 4 * Zm * ‖Z t a‖ := by
    rcases (norm_nonneg b).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have h1 : ‖b‖ * ‖b‖ ≤ (4 * Zm * ‖Z t a‖) * ‖b‖ := by
        have := mul_le_mul_of_nonneg_left hZb (by positivity : (0 : ℝ) ≤ 4 * ‖Z t a‖)
        nlinarith
      exact le_of_mul_le_mul_right h1 hpos
  have ha : ‖a‖ ≤ j * ‖b‖ := by
    have h := pd_norm_J0_le b
    rw [hb, pd_J0_J0, norm_neg] at h
    rw [hb]; exact h
  rw [inv_mul_le_iff₀ (by positivity)]
  have : j * ‖b‖ ≤ j * (4 * Zm * ‖Z t a‖) := mul_le_mul_of_nonneg_left hb' hj0
  nlinarith [norm_nonneg (Z t a)]

theorem pd_J_on_xi (hZ : IsUnitaryXiFrame J P Z) (t : ℝ) (w : V 1)
    (hw : IsInXi H (P.x (P.T * t)) w) :
    J (P.x (P.T * t)) (J (P.x (P.T * t)) w) = -w := by
  obtain ⟨a, rfl⟩ := (hZ.2.2 t).2.1 w hw
  rw [(hZ.2.2 t).2.2.1 a, (hZ.2.2 t).2.2.1, pd_J0_J0, map_neg]

/-- An eigenvector of `A_P` vanishes nowhere (frame version). -/
theorem pd_eigen_ne_zero (hH : IsStrictlyStarShapedLevel H) (hZ : IsUnitaryXiFrame J P Z)
    {μ : ℝ} {v : ℝ → V 1} (hv : IsAsymptoticEigen J P μ v) (t : ℝ) : v t ≠ 0 := by
  obtain ⟨⟨hvs, hvper, hξ⟩, ⟨t₁, ht₁⟩, heig⟩ := hv
  have hvd : Differentiable ℝ v := hvs.differentiable (by simp)
  have hode : ∀ t, deriv v t = P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (v t) +
      μ • J (P.x (P.T * t)) (v t) := by
    intro t
    have hy := isInXi_linearizedReeb_deriv H hH P v hvd hξ t
    have hJJ := pd_J_on_xi hZ t _ hy
    have he := heig t
    simp only [asympOp] at he
    rw [he, map_smul] at hJJ
    rw [hJJ]
    abel
  have hxc : Continuous (fun t : ℝ => P.x (P.T * t)) :=
    (ReebOrbit.contDiff_x H hH P).continuous.comp (continuous_const.mul continuous_id)
  have h1 : Continuous (fun t => fderiv ℝ (reeb H) (P.x (P.T * t))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hr := ka_reeb_contDiffAt H hH (P.x (P.T * t)) (P.mem _)
    have hf : ContDiffAt ℝ 0 (fderiv ℝ (reeb H)) (P.x (P.T * t)) :=
      hr.fderiv_right (by simp)
    exact ContinuousAt.comp (g := fderiv ℝ (reeb H)) (f := fun t : ℝ => P.x (P.T * t))
      hf.continuousAt (hxc.continuousAt (x := t))
  have h1per : Function.Periodic (fun t => fderiv ℝ (reeb H) (P.x (P.T * t))) 1 := by
    intro t
    simp only [mul_add, mul_one, P.periodic]
  obtain ⟨Rm, hRm0, hRm⟩ := pd_periodic_bound h1 h1per
  obtain ⟨Zm, hZm0, hZm⟩ := pd_frame_bound hZ
  obtain ⟨c, hc, hcZ⟩ := pd_frame_lower hZ
  set K := P.T * Rm + |μ| * (Zm * ‖pdJ0L‖ / c) with hK
  have hbound : ∀ t, ‖deriv v t‖ ≤ K * ‖v t‖ := by
    intro t
    rw [hode t]
    refine (norm_add_le _ _).trans ?_
    have hA : ‖P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (v t)‖ ≤ P.T * Rm * ‖v t‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos P.T_pos, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ P.T_pos.le
      exact ((fderiv ℝ (reeb H) (P.x (P.T * t))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hRm t) (norm_nonneg _))
    have hB : ‖μ • J (P.x (P.T * t)) (v t)‖ ≤ |μ| * (Zm * ‖pdJ0L‖ / c) * ‖v t‖ := by
      obtain ⟨a, ha⟩ := (hZ.2.2 t).2.1 (v t) (hξ t)
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [← ha, (hZ.2.2 t).2.2.1 a]
      have h2 : ‖Z t (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a)‖ ≤
          Zm * (‖pdJ0L‖ * ‖a‖) :=
        ((Z t).le_opNorm _).trans (mul_le_mul (hZm t) (pd_norm_J0_le a) (norm_nonneg _) hZm0)
      have h3 : ‖a‖ ≤ ‖Z t a‖ / c := by rw [le_div_iff₀ hc]; linarith [hcZ t a]
      calc _ ≤ Zm * (‖pdJ0L‖ * ‖a‖) := h2
        _ ≤ Zm * (‖pdJ0L‖ * (‖Z t a‖ / c)) := by
          apply mul_le_mul_of_nonneg_left _ hZm0
          exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = Zm * ‖pdJ0L‖ / c * ‖Z t a‖ := by ring
    linarith
  intro h0
  have hzero : ∀ x, t ≤ x → v x = 0 := by
    intro x hx
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := v) (f' := deriv v) (δ := 0)
      (K := K) (ε := 0) (a := t) (b := x) hvs.continuous.continuousOn
      (fun y _ => (hvd y).hasDerivAt.hasDerivWithinAt) (by rw [h0, norm_zero])
      (fun y _ => by rw [add_zero]; exact hbound y) x ⟨hx, le_rfl⟩
    rw [gronwallBound_ε0_δ0] at this
    exact norm_le_zero_iff.1 this
  set k := ⌈t - t₁⌉₊ with hk
  have hk' : t ≤ t₁ + (k : ℝ) * 1 := by
    have := Nat.le_ceil (t - t₁); rw [← hk] at this; linarith
  have := (hvper.nat_mul k) t₁
  exact ht₁ (this ▸ hzero _ hk')

end Frame

/-- A solution `G` of `F x (G x) = y x`, with `F x` strictly increasing on an open set and
`F · s` continuous, is continuous. -/
theorem pd_continuousOn_of_strictMonoOn {X : Type*} [TopologicalSpace X] {S : Set X}
    {I : Set ℝ} (hI : IsOpen I) (F : X → ℝ → ℝ)
    (hF : ∀ s ∈ I, ContinuousOn (fun x => F x s) S) (hmono : ∀ x ∈ S, StrictMonoOn (F x) I)
    (G y : X → ℝ) (hG : ∀ x ∈ S, G x ∈ I) (hy : ContinuousOn y S)
    (hFG : ∀ x ∈ S, F x (G x) = y x) : ContinuousOn G S := by
  intro x₀ hx₀
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hI (G x₀) (hG x₀ hx₀)
  set e := min (ε / 2) (δ / 2) with he
  have he0 : 0 < e := by positivity
  have hea : G x₀ - e ∈ I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, show G x₀ - e - G x₀ = -e by ring, abs_neg,
      abs_of_pos he0]
    linarith [min_le_right (ε / 2) (δ / 2)])
  have heb : G x₀ + e ∈ I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, show G x₀ + e - G x₀ = e by ring, abs_of_pos he0]
    linarith [min_le_right (ε / 2) (δ / 2)])
  have hlo : F x₀ (G x₀ - e) < y x₀ := by
    rw [← hFG x₀ hx₀]
    exact hmono x₀ hx₀ hea (hG x₀ hx₀) (by linarith)
  have hhi : y x₀ < F x₀ (G x₀ + e) := by
    rw [← hFG x₀ hx₀]
    exact hmono x₀ hx₀ (hG x₀ hx₀) heb (by linarith)
  have h1 := (hF _ hea x₀ hx₀).eventually_lt (hy x₀ hx₀) hlo
  have h2 := (hy x₀ hx₀).eventually_lt (hF _ heb x₀ hx₀) hhi
  filter_upwards [h1, h2, self_mem_nhdsWithin] with x hx1 hx2 hxS
  rw [← hFG x hxS] at hx1 hx2
  have hl : G x₀ - e < G x := (hmono x hxS).lt_iff_lt hea (hG x hxS) |>.1 hx1
  have hr : G x < G x₀ + e := (hmono x hxS).lt_iff_lt (hG x hxS) heb |>.1 hx2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [min_le_left (ε / 2) (δ / 2)]

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f 1) :
    ∃ L, 0 ≤ L ∧ ∀ x y, ‖f x - f y‖ ≤ L * |x - y| :=
  pd_periodic_lip hf hper
