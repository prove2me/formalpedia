-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInftyTube_rescaled_sub_model
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-15T17:48:08.973301+00:00
-- url     : https://prove2.me/submissions/7cce9bfd-412f-4d02-98ae-8ad966df2aac

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_comp_sub
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

/-!
# Tube decay algebra (local): lifting decay on the end to the tube, pairs, zero.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SMD

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The projection `(s, t, w) ↦ (s, t)`. -/
def pr : ℝ × ℝ × ℂ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)))

@[simp] lemma pr_apply (q : ℝ × ℝ × ℂ) : pr q = (q.1, q.2.1) := rfl

lemma norm_pr_le : ‖pr‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
    simp only [pr_apply, one_mul]
    refine max_le (norm_fst_le q) ((norm_fst_le q.2).trans (norm_snd_le q))

/-- Decay on the end lifts to the tube (constant in `w`). -/
lemma expDecayCInftyTube_of_expDecayCInfty {h : ℝ × ℝ → F} {b : ℝ} (hh : ExpDecayCInfty h b)
    (ρ : ℝ) : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => h (q.1, q.2.1)) ρ b := by
  obtain ⟨⟨s₀, hs⟩, hl⟩ := hh
  set O : Set (ℝ × ℝ) := Ioi s₀ ×ˢ univ with hO
  have hOo : IsOpen O := isOpen_Ioi.prod isOpen_univ
  have hpre : IsOpen (pr ⁻¹' O) := hOo.preimage pr.continuous
  refine ⟨⟨s₀, (hs.comp pr.contDiff.contDiffOn ?_)⟩, fun m => ?_⟩
  · rintro ⟨s, t, w⟩ ⟨hs', -, -⟩
    exact ⟨hs', trivial⟩
  obtain ⟨C, s₁, hC⟩ := hl m
  refine ⟨|C|, max s₁ (s₀ + 1), fun s hs1 t w _ => ?_⟩
  have hsO : pr (s, t, w) ∈ O := ⟨by simp; linarith [le_max_right s₁ (s₀ + 1)], trivial⟩
  have e := ContinuousLinearMap.iteratedFDerivWithin_comp_right pr hs hOo.uniqueDiffOn
    hpre.uniqueDiffOn hsO (i := m) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen m hpre hsO, iteratedFDerivWithin_of_isOpen m hOo hsO] at e
  have e' : (fun q : ℝ × ℝ × ℂ => h (q.1, q.2.1)) = h ∘ pr := rfl
  rw [e', e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin m, ‖pr‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_pr_le
  have h1 := hC s (le_trans (le_max_left _ _) hs1) t
  simp only [pr_apply] at h1 ⊢
  calc ‖iteratedFDeriv ℝ m h (s, t)‖ * ∏ _i : Fin m, ‖pr‖ ≤ (|C| * Real.exp (-(b * s))) * 1 :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
          hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    _ = |C| * Real.exp (-(b * s)) := mul_one _

/-- The zero function decays. -/
lemma expDecayCInftyTube_zero (ρ b : ℝ) :
    ExpDecayCInftyTube (fun _ : ℝ × ℝ × ℂ => (0 : F)) ρ b :=
  ⟨⟨0, contDiffOn_const⟩, fun m => ⟨0, 0, fun s _ t w _ => by
    rw [show (fun _ : ℝ × ℝ × ℂ => (0 : F)) = fun _ => (0 : F) from rfl]
    simp [iteratedFDeriv_const_of_ne, iteratedFDeriv_zero_fun]⟩⟩

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pairs of decaying maps decay. -/
lemma expDecayCInftyTube_prod {f₁ : ℝ × ℝ × ℂ → F} {f₂ : ℝ × ℝ × ℂ → G} {ρ b : ℝ}
    (h₁ : ExpDecayCInftyTube f₁ ρ b) (h₂ : ExpDecayCInftyTube f₂ ρ b) :
    ExpDecayCInftyTube (fun q => (f₁ q, f₂ q)) ρ b := by
  obtain ⟨⟨s₁, hs₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨s₂, hs₂⟩, hl₂⟩ := h₂
  set S : ℝ := max s₁ s₂
  have hsub₁ : (Ioi S ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℝ × ℂ)) ⊆
      Ioi s₁ ×ˢ univ ×ˢ ball (0 : ℂ) ρ :=
    prod_mono (Ioi_subset_Ioi (le_max_left _ _)) subset_rfl
  have hsub₂ : (Ioi S ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℝ × ℂ)) ⊆
      Ioi s₂ ×ˢ univ ×ˢ ball (0 : ℂ) ρ :=
    prod_mono (Ioi_subset_Ioi (le_max_right _ _)) subset_rfl
  refine ⟨⟨S, (hs₁.mono hsub₁).prodMk (hs₂.mono hsub₂)⟩, fun m => ?_⟩
  obtain ⟨C₁, t₁, hC₁⟩ := hl₁ m
  obtain ⟨C₂, t₂, hC₂⟩ := hl₂ m
  refine ⟨|C₁| + |C₂|, max (max t₁ t₂) (S + 1), fun s hs t w hw => ?_⟩
  have hsS : S < s := by linarith [le_max_right (max t₁ t₂) (S + 1)]
  have hq : ((s, t, w) : ℝ × ℝ × ℂ) ∈ Ioi S ×ˢ univ ×ˢ ball (0 : ℂ) ρ := ⟨hsS, trivial, hw⟩
  have ho : IsOpen (Ioi S ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℝ × ℂ)) := isOpen_Ioi.prod (isOpen_univ.prod isOpen_ball)
  have ha₁ : ContDiffAt ℝ ∞ f₁ (s, t, w) := (hs₁.mono hsub₁).contDiffAt (ho.mem_nhds hq)
  have ha₂ : ContDiffAt ℝ ∞ f₂ (s, t, w) := (hs₂.mono hsub₂).contDiffAt (ho.mem_nhds hq)
  rw [iteratedFDeriv_prodMk ha₁ ha₂ (by exact_mod_cast le_top),
    ContinuousMultilinearMap.opNorm_prod]
  have e := (Real.exp_pos (-(b * s))).le
  have b₁ := hC₁ s (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs) t w hw
  have b₂ := hC₂ s (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs) t w hw
  have c₁ : C₁ * Real.exp (-(b * s)) ≤ |C₁| * Real.exp (-(b * s)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) e
  have c₂ : C₂ * Real.exp (-(b * s)) ≤ |C₂| * Real.exp (-(b * s)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) e
  have d₁ := mul_nonneg (abs_nonneg C₁) e
  have d₂ := mul_nonneg (abs_nonneg C₂) e
  refine max_le ?_ ?_ <;> nlinarith

end SMD

end

end FiniteEnergyPlane

/-!
# S, child (a) (local proof): the rescaled tube map converges to the model on the tube.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SMD

lemma exp_aCoord_smul_proj {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H)
    (y : V 1) (hy : y ≠ 0) : Real.exp (2 * aCoord H y) • proj H y = y := by
  have hr := (ka_scale_spec H hH y hy).1
  have e : Real.exp (2 * aCoord H y) = (scaleToS H y)⁻¹ := by
    unfold aCoord
    rw [show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring,
      Real.exp_neg, Real.exp_log hr]
  rw [e]
  unfold proj
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

lemma clm_apply_complex {X : Type*} [AddCommGroup X] [Module ℝ X] (L : ℂ →ₗ[ℝ] X) (w : ℂ) :
    L w = w.re • L 1 + w.im • L Complex.I := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [map_add, show (w.re : ℂ) = w.re • (1 : ℂ) by simp,
    show (w.im : ℂ) * Complex.I = w.im • Complex.I by simp, map_smul, map_smul]

lemma cToVec_decomp (w : ℂ) :
    cToVec w = w.re • cToVec 1 + w.im • cToVec Complex.I := by
  ext i; rcases i with i | i <;> simp [cToVec]

end SMD

theorem expDecayCInftyTube_rescaled_sub_model_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      Real.exp (-(2 * (P.T * q.1 + d))) •
          (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) -
        (P.x (P.T * q.2.1) + M q.2.1 (cToVec q.2.2))) ρ b := by
  -- the data
  set α : ℝ × ℝ → ℝ := fun p => endA H u cylInf p - P.T * p.1 - d with hα
  set A : ℂ → ℝ × ℝ → V 1 := fun ν p =>
    Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν) with hA
  set f : ℝ × ℝ × ℂ → ℝ × V 1 × V 1 × V 1 × ℂ := fun q =>
    (α (q.1, q.2.1), endW H u cylInf (q.1, q.2.1), A 1 (q.1, q.2.1), A Complex.I (q.1, q.2.1),
      q.2.2) with hf
  set g : ℝ × ℂ → ℝ × V 1 × V 1 × V 1 × ℂ := fun p =>
    (0, P.x (P.T * p.1), 0, 0, p.2) with hg
  set G : ℝ × V 1 × V 1 × V 1 × ℂ → V 1 := fun y =>
    Real.exp (2 * y.1) • y.2.1 + y.2.2.2.2.re • y.2.2.1 + y.2.2.2.2.im • y.2.2.2.1 with hG
  have hGc : ContDiff ℝ ∞ G := by
    have hre : ContDiff ℝ ∞ (fun y : ℝ × V 1 × V 1 × V 1 × ℂ => y.2.2.2.2.re) :=
      Complex.reCLM.contDiff.comp (by fun_prop)
    have him : ContDiff ℝ ∞ (fun y : ℝ × V 1 × V 1 × V 1 × ℂ => y.2.2.2.2.im) :=
      Complex.imCLM.contDiff.comp (by fun_prop)
    have h1 : ContDiff ℝ ∞ (fun y : ℝ × V 1 × V 1 × V 1 × ℂ => Real.exp (2 * y.1) • y.2.1) :=
      (Real.contDiff_exp.comp (by fun_prop)).smul (by fun_prop)
    exact (h1.add (hre.smul (by fun_prop))).add (him.smul (by fun_prop))
  have hgc : ContDiffOn ℝ ∞ g (univ ×ˢ ball (0 : ℂ) (2 * ρ)) := by
    refine ContDiff.contDiffOn ?_
    exact contDiff_const.prodMk ((((ReebOrbit.contDiff_x H hH P).comp
      (contDiff_const.mul contDiff_fst))).prodMk (contDiff_const.prodMk
        (contDiff_const.prodMk contDiff_snd)))
  have hgper : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w) := by
    intro t w
    simp only [hg, mul_add, mul_one, P.periodic]
  -- the difference decays
  have hdiff : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => f q - g (q.2.1, q.2.2)) ρ b := by
    have e : (fun q : ℝ × ℝ × ℂ => f q - g (q.2.1, q.2.2)) = fun q =>
        (α (q.1, q.2.1), (endW H u cylInf (q.1, q.2.1) - P.x (P.T * q.2.1)),
          A 1 (q.1, q.2.1), A Complex.I (q.1, q.2.1), (0 : ℂ)) := by
      funext q
      simp [hf, hg, Prod.ext_iff]
    rw [e]
    exact SMD.expDecayCInftyTube_prod (SMD.expDecayCInftyTube_of_expDecayCInfty ha ρ)
      (SMD.expDecayCInftyTube_prod (SMD.expDecayCInftyTube_of_expDecayCInfty hw ρ)
        (SMD.expDecayCInftyTube_prod (SMD.expDecayCInftyTube_of_expDecayCInfty (hNM 1) ρ)
          (SMD.expDecayCInftyTube_prod (SMD.expDecayCInftyTube_of_expDecayCInfty
            (hNM Complex.I) ρ) (SMD.expDecayCInftyTube_zero ρ b))))
  have key := expDecayCInftyTube_comp_sub G univ isOpen_univ hGc.contDiffOn ρ b hρ hb g hgc
    hgper (fun _ _ _ => mem_univ _) f hdiff
  -- identify
  have e : (fun q : ℝ × ℝ × ℂ => G (f q) - G (g (q.2.1, q.2.2))) = fun q =>
      Real.exp (-(2 * (P.T * q.1 + d))) •
          (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) -
        (P.x (P.T * q.2.1) + M q.2.1 (cToVec q.2.2)) := by
    funext q
    obtain ⟨s, t, w⟩ := q
    have hu := SMD.exp_aCoord_smul_proj hH (u (cylInf s t)) (hu0 _)
    have hN := SMD.clm_apply_complex (N (cylInf s t)).toLinearMap w
    have hc := SMD.cToVec_decomp w
    simp only [ContinuousLinearMap.coe_coe] at hN
    simp only [hG, hf, hg, hα, hA, endA, endW, mul_zero, Real.exp_zero, one_smul, smul_zero,
      add_zero]
    rw [hN, hc, map_add, map_smul, map_smul]
    have e2 : Real.exp (2 * (aCoord H (u (cylInf s t)) - P.T * s - d)) =
        Real.exp (-(2 * (P.T * s + d))) * Real.exp (2 * aCoord H (u (cylInf s t))) := by
      rw [← Real.exp_add]; ring_nf
    rw [e2, mul_smul, hu]
    simp only [smul_sub, smul_add, smul_smul]
    module
  rw [e] at key
  exact key

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      Real.exp (-(2 * (P.T * q.1 + d))) •
          (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) -
        (P.x (P.T * q.2.1) + M q.2.1 (cToVec q.2.2))) ρ b :=
  expDecayCInftyTube_rescaled_sub_model_aux H hH P u hu0 d b hb ha hw N M hNM ρ hρ
