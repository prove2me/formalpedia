-- Prove2me | solution 1 for FiniteEnergyPlane.isFiniteEnergyCurve_orbitCylinder
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T22:22:35.004843+00:00
-- url     : https://prove2.me/submissions/0cab95d1-84c9-46e5-9e3e-c8bf4e3e8ce6

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x

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

/-! Child G of `proj_notMem_range_of_tendsto_disk`: the trivial cylinder over a periodic orbit in
logarithmic coordinates, `ζ ↦ e^{2 Re ζ} x(Im ζ)`, is a finite-energy `J̃`-holomorphic immersion on
every ball. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff ENNReal NNReal

section
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H)

include hH in
lemma pnrg_ne_zero_of_mem {x : V 1} (hx : x ∈ energySurface H) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

include hH in
lemma pnrg_scale (x : V 1) (hx : x ∈ energySurface H) (s : ℝ) :
    scaleToS H (Real.exp (2 * s) • x) = Real.exp (-(2 * s)) := by
  have hx0 := pnrg_ne_zero_of_mem hH hx
  have hy : Real.exp (2 * s) • x ≠ 0 := smul_ne_zero (Real.exp_pos _).ne' hx0
  refine ka_scale_unique H hH _ hy _ (Real.exp_pos _) ?_
  rw [smul_smul, ← Real.exp_add]
  have h0 : -(2 * s) + 2 * s = 0 := by ring
  rw [h0, Real.exp_zero, one_smul]
  exact hx

include hH in
lemma pnrg_proj (x : V 1) (hx : x ∈ energySurface H) (s : ℝ) :
    proj H (Real.exp (2 * s) • x) = x := by
  rw [proj, pnrg_scale hH x hx s, smul_smul, ← Real.exp_add]
  simp

include hH in
lemma pnrg_aCoord (x : V 1) (hx : x ∈ energySurface H) (s : ℝ) :
    aCoord H (Real.exp (2 * s) • x) = s := by
  rw [aCoord, pnrg_scale hH x hx s, Real.log_exp]
  ring

lemma pnrg_Jt_apply (J : V 1 → V 1 →L[ℝ] V 1) (y v : V 1) :
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
/-- `J̃` sends the lifted Reeb field to `-∂ₐ`. -/
lemma pnrg_Jt_lift (J : V 1 → V 1 →L[ℝ] V 1) {y : V 1} (hy : y ≠ 0) :
    Jtilde H J y ((scaleToS H y)⁻¹ • reeb H (proj H y)) = -((2 : ℝ) • y) := by
  have hr := (ka_scale_spec H hH y hy).1
  have hx : proj H y ∈ energySurface H := (ka_scale_spec H hH y hy).2
  obtain ⟨-, h1, h2, -⟩ := ka_reeb_spec H hH _ hx
  have hl : liouville (proj H y) ((scaleToS H y)⁻¹ • reeb H (proj H y)) = (scaleToS H y)⁻¹ := by
    rw [← ka_liouvilleCLM_apply, map_smul, ka_liouvilleCLM_apply, h1, smul_eq_mul, mul_one]
  have hd : fderiv ℝ H (proj H y) ((scaleToS H y)⁻¹ • reeb H (proj H y)) = 0 := by
    rw [map_smul, h2, smul_zero]
  rw [pnrg_Jt_apply, hl, hd, mul_inv_cancel₀ hr.ne']
  simp

end

/-- The map `ζ ↦ e^{2 Re ζ} x(Im ζ)`. -/
noncomputable def pnrgCyl {H : V 1 → ℝ} (P : ReebOrbit H) (ζ : ℂ) : V 1 :=
  Real.exp (2 * ζ.re) • P.x ζ.im

lemma pnrg_hasFDerivAt {H : V 1 → ℝ} (P : ReebOrbit H) (ζ : ℂ) :
    ∃ L : ℂ →L[ℝ] V 1, HasFDerivAt (pnrgCyl P) L ζ ∧ ∀ v : ℂ,
      L v = (Real.exp (2 * ζ.re) * 2 * v.re) • P.x ζ.im +
        (Real.exp (2 * ζ.re) * v.im) • reeb H (P.x ζ.im) := by
  have hre := ((Complex.reCLM.hasFDerivAt (x := ζ)).const_mul (2 : ℝ)).exp
  have him := (P.hasDerivAt ζ.im).hasFDerivAt.comp ζ (Complex.imCLM.hasFDerivAt (x := ζ))
  have h := hre.smul him
  refine ⟨_, h, fun v => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Function.comp_apply, smul_eq_mul, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_comp']
  module

lemma pnrg_fderiv {H : V 1 → ℝ} (P : ReebOrbit H) (ζ v : ℂ) :
    fderiv ℝ (pnrgCyl P) ζ v =
      (Real.exp (2 * ζ.re) * 2 * v.re) • P.x ζ.im + (Real.exp (2 * ζ.re) * v.im) • reeb H (P.x ζ.im) := by
  obtain ⟨L, hL, hv⟩ := pnrg_hasFDerivAt P ζ
  rw [hL.fderiv, hv]

lemma pnrg_contDiff {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) :
    ContDiff ℝ ∞ (pnrgCyl P) := by
  unfold pnrgCyl
  exact (Real.contDiff_exp.comp (contDiff_const.mul Complex.reCLM.contDiff)).smul
    ((ReebOrbit.contDiff_x H hH P).comp Complex.imCLM.contDiff)

lemma pnrg_proj_eq {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) :
    (fun ζ => proj H (pnrgCyl P ζ)) = fun ζ => P.x ζ.im := by
  funext ζ; exact pnrg_proj hH _ (P.mem _) _

lemma pnrg_aCoord_eq {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) :
    (fun ζ => aCoord H (pnrgCyl P ζ)) = fun ζ => ζ.re := by
  funext ζ; exact pnrg_aCoord hH _ (P.mem _) _

lemma pnrg_density {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (φ : ℝ → ℝ) (ζ : ℂ) : energyDensity H φ (pnrgCyl P) ζ = deriv φ ζ.re := by
  have hx := P.mem ζ.im
  obtain ⟨-, h1, -, -⟩ := ka_reeb_spec H hH _ hx
  have hreF : fderiv ℝ (fun ζ : ℂ => ζ.re) ζ = Complex.reCLM := Complex.reCLM.hasFDerivAt.fderiv
  have hdsa : ds (fun ζ : ℂ => ζ.re) ζ = 1 := by
    simp [ds, hreF]
  have hdta : dt (fun ζ : ℂ => ζ.re) ζ = 0 := by
    simp [dt, hreF]
  have him := (P.hasDerivAt ζ.im).hasFDerivAt.comp ζ (Complex.imCLM.hasFDerivAt (x := ζ))
  have hcomp : (fun ζ : ℂ => P.x ζ.im) = P.x ∘ Complex.im := rfl
  have hdsw : ds (fun ζ : ℂ => P.x ζ.im) ζ = 0 := by
    rw [ds, hcomp, him.fderiv]; simp
  have hdtw : dt (fun ζ : ℂ => P.x ζ.im) ζ = reeb H (P.x ζ.im) := by
    rw [dt, hcomp, him.fderiv]; simp
  have hpa : aCoord H (pnrgCyl P ζ) = ζ.re := pnrg_aCoord hH _ (P.mem _) _
  have hpp : proj H (pnrgCyl P ζ) = P.x ζ.im := pnrg_proj hH _ (P.mem _) _
  simp only [energyDensity, pnrg_proj_eq hH P, pnrg_aCoord_eq hH P, hpa, hpp]
  rw [hdsa, hdta, hdsw, hdtw, h1]
  have : omega0 (0 : V 1) (reeb H (P.x ζ.im)) = 0 := by
    have := ka_om_smul_left (n := 1) 0 (0 : V 1) (reeb H (P.x ζ.im)); simpa using this
  rw [this]; ring

/-- Tonelli on the plane, in the coordinates `p = τ + t i`, outer variable `t`. -/
theorem pnrg_lintegral_strip (g : ℂ → ℝ≥0∞) (hg : Measurable g) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ p in {p : ℂ | p.re ∈ A ∧ p.im ∈ B}, g p =
      ∫⁻ t in B, ∫⁻ τ in A, g (τ + t * Complex.I) := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hS : {p : ℂ | p.re ∈ A ∧ p.im ∈ B} = Complex.measurableEquivRealProd ⁻¹' (A ×ˢ B) := by
    ext p; simp [Complex.measurableEquivRealProd]
  have hg' : ∀ p, g p = (g ∘ Complex.measurableEquivRealProd.symm)
      (Complex.measurableEquivRealProd p) := fun p => by simp
  simp_rw [hS, hg']
  rw [hmp.setLIntegral_comp_preimage_emb Complex.measurableEquivRealProd.measurableEmbedding,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hm : Measurable (g ∘ Complex.measurableEquivRealProd.symm) :=
    hg.comp Complex.measurableEquivRealProd.symm.measurable
  rw [lintegral_prod_symm _ hm.aemeasurable]
  refine lintegral_congr fun t => lintegral_congr fun τ => ?_
  simp only [Function.comp_apply, Complex.measurableEquivRealProd_symm_apply]
  congr 1
  apply Complex.ext <;> simp

lemma pnrg_energy_lt_top {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (w₀ : ℂ) (r : ℝ) : energy H (ball w₀ r) (pnrgCyl P) < ⊤ := by
  set A : Set ℝ := Ioo (w₀.re - r) (w₀.re + r)
  set B : Set ℝ := Ioo (w₀.im - r) (w₀.im + r)
  have hsub : ball w₀ r ⊆ {p : ℂ | p.re ∈ A ∧ p.im ∈ B} := by
    intro p hp
    rw [mem_ball, dist_eq_norm] at hp
    have h1 := Complex.abs_re_le_norm (p - w₀)
    have h2 := Complex.abs_im_le_norm (p - w₀)
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      [linarith [neg_abs_le (p.re - w₀.re)]; linarith [le_abs_self (p.re - w₀.re)];
       linarith [neg_abs_le (p.im - w₀.im)]; linarith [le_abs_self (p.im - w₀.im)]]
  have hbound : ∀ φ : ℝ → ℝ, Admissible φ →
      ∫⁻ z in ball w₀ r, ENNReal.ofReal (energyDensity H φ (pnrgCyl P) z) ≤
        ENNReal.ofReal (2 * r) := by
    intro φ hφ
    obtain ⟨hφs, hφm, hφb⟩ := hφ
    have hd : Continuous (deriv φ) := hφs.continuous_deriv (by simp)
    simp_rw [pnrg_density hH P φ]
    have hmeas : Measurable (fun z : ℂ => ENNReal.ofReal (deriv φ z.re)) :=
      ENNReal.measurable_ofReal.comp (hd.measurable.comp Complex.measurable_re)
    calc ∫⁻ z in ball w₀ r, ENNReal.ofReal (deriv φ z.re)
        ≤ ∫⁻ z in {p : ℂ | p.re ∈ A ∧ p.im ∈ B}, ENNReal.ofReal (deriv φ z.re) :=
          lintegral_mono_set hsub
      _ = ∫⁻ t in B, ∫⁻ τ in A, ENNReal.ofReal (deriv φ (τ + t * Complex.I).re) :=
          pnrg_lintegral_strip _ hmeas A B measurableSet_Ioo measurableSet_Ioo
      _ = ∫⁻ t in B, ∫⁻ τ in A, ENNReal.ofReal (deriv φ τ) := by simp
      _ ≤ ∫⁻ t in B, 1 := by
          refine lintegral_mono fun t => ?_
          rcases le_or_gt r 0 with hr | hr
          · have : A = ∅ := Ioo_eq_empty (by linarith)
            rw [this]; simp
          have hle : w₀.re - r ≤ w₀.re + r := by linarith
          have hint : Integrable (deriv φ) (volume.restrict A) :=
            (hd.integrableOn_Icc (a := w₀.re - r) (b := w₀.re + r)).mono_set Ioo_subset_Icc_self
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun τ => hφm.deriv_nonneg)]
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle,
            intervalIntegral.integral_deriv_eq_sub (fun x _ => (hφs.differentiable (by simp)) x)
              (hd.intervalIntegrable _ _)]
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          linarith [(hφb (w₀.re + r)).2, (hφb (w₀.re - r)).1]
      _ = ENNReal.ofReal (2 * r) := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioo]
          congr 1; ring
  have : energy H (ball w₀ r) (pnrgCyl P) ≤ ENNReal.ofReal (2 * r) := by
    unfold energy
    exact iSup₂_le hbound
  exact lt_of_le_of_lt this ENNReal.ofReal_lt_top

/-- The trivial cylinder over a periodic Reeb orbit in logarithmic coordinates. -/
theorem isFiniteEnergyCurve_orbitCylinder_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (w₀ : ℂ) (r : ℝ) :
    IsFiniteEnergyCurve H J (ball w₀ r) (fun ζ : ℂ => Real.exp (2 * ζ.re) • P.x ζ.im) ∧
      (∀ ζ : ℂ, Function.Injective (fderiv ℝ (fun ζ : ℂ => Real.exp (2 * ζ.re) • P.x ζ.im) ζ)) ∧
      ∀ ζ : ℂ, proj H (Real.exp (2 * ζ.re) • P.x ζ.im) = P.x ζ.im := by
  have heq : (fun ζ : ℂ => Real.exp (2 * ζ.re) • P.x ζ.im) = pnrgCyl P := rfl
  rw [heq]
  have hne : ∀ ζ, pnrgCyl P ζ ≠ 0 := fun ζ =>
    smul_ne_zero (Real.exp_pos _).ne' (pnrg_ne_zero_of_mem hH (P.mem _))
  refine ⟨⟨(pnrg_contDiff hH P).contDiffOn, fun ζ _ => hne ζ, ?_, pnrg_energy_lt_top hH P w₀ r⟩,
    ?_, fun ζ => pnrg_proj hH _ (P.mem _) _⟩
  · intro ζ _
    refine ⟨(pnrg_hasFDerivAt P ζ).choose_spec.1.differentiableAt, ?_⟩
    unfold JHolomorphic.dbarJ
    rw [pnrg_fderiv, pnrg_fderiv]
    have hsc := pnrg_scale hH _ (P.mem ζ.im) ζ.re
    have hpr := pnrg_proj hH _ (P.mem ζ.im) ζ.re
    have hlift := pnrg_Jt_lift hH J (hne ζ)
    unfold pnrgCyl at hlift ⊢
    rw [hsc, hpr, ← Real.exp_neg, neg_neg] at hlift
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_smul, add_zero, zero_add]
    rw [hlift, smul_smul]
    simp only [mul_comm]
    abel_nf
  · intro ζ v w hvw
    have hx := P.mem ζ.im
    obtain ⟨-, h1, -, -⟩ := ka_reeb_spec H hH _ hx
    have hx0 := pnrg_ne_zero_of_mem hH hx
    have hlx : liouville (P.x ζ.im) (P.x ζ.im) = 0 := by
      unfold liouville; rw [ka_om_self]; simp
    rw [← sub_eq_zero, ← map_sub, pnrg_fderiv] at hvw
    set d := v - w
    have hl := congrArg (liouvilleCLM (P.x ζ.im)) hvw
    simp only [map_add, map_smul, map_zero, ka_liouvilleCLM_apply, hlx, h1, smul_eq_mul,
      mul_zero, mul_one, zero_add] at hl
    have him : d.im = 0 := by
      rcases mul_eq_zero.1 hl with h | h
      · exact absurd h (Real.exp_pos _).ne'
      · exact h
    rw [him, mul_zero, zero_smul, add_zero] at hvw
    have hre : d.re = 0 := by
      rcases smul_eq_zero.1 hvw with h | h
      · have := Real.exp_pos (2 * ζ.re)
        have h2 : Real.exp (2 * ζ.re) * 2 ≠ 0 := by positivity
        exact (mul_eq_zero.1 h).resolve_left h2
      · exact absurd h hx0
    have : d = 0 := Complex.ext hre him
    exact sub_eq_zero.1 this

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (w₀ : ℂ) (r : ℝ) :
    IsFiniteEnergyCurve H J (ball w₀ r) (fun ζ : ℂ => Real.exp (2 * ζ.re) • P.x ζ.im) ∧
      (∀ ζ : ℂ, Function.Injective (fderiv ℝ (fun ζ : ℂ => Real.exp (2 * ζ.re) • P.x ζ.im) ζ)) ∧
      ∀ ζ : ℂ, proj H (Real.exp (2 * ζ.re) • P.x ζ.im) = P.x ζ.im :=
  isFiniteEnergyCurve_orbitCylinder_aux H hH J P w₀ r
