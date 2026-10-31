-- Prove2me | solution 1 for FiniteEnergyPlane.xiPart_partialS_ne_zero_of_eigenTube
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T17:18:28.068076+00:00
-- url     : https://prove2.me/submissions/941dc09b-c7d8-467a-b0e1-fd5d1be6b242

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_mul_norm_of_periodic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open FiniteEnergyPlane
open scoped ContDiff Topology in
open scoped ContDiff Topology
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

namespace FiniteEnergyPlane.DLPD

open FiniteEnergyPlane N1

variable {n : ℕ}

theorem bdd_of_periodic {F : Type*} [NormedAddCommGroup F] (f : ℝ → F) (hf : Continuous f)
    {T : ℝ} (hT : 0 < T) (hp : Function.Periodic f T) : ∃ K, 0 ≤ K ∧ ∀ t, ‖f t‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  have hall : ∀ t, ‖f t‖ ≤ K := by
    intro t
    obtain ⟨y, hy, hyt⟩ := hp.exists_mem_Ico hT t 0
    rw [hyt]
    exact hK y ⟨hy.1, by linarith [hy.2]⟩
  exact ⟨K, (norm_nonneg _).trans (hall 0), hall⟩

theorem lower_of_periodic {F : Type*} [NormedAddCommGroup F] (f : ℝ → F) (hf : Continuous f)
    {T : ℝ} (hT : 0 < T) (hp : Function.Periodic f T) (hne : ∀ t, f t ≠ 0) :
    ∃ m > 0, ∀ t, m ≤ ‖f t‖ := by
  obtain ⟨y₀, -, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
    (Set.nonempty_Icc.2 hT.le) hf.norm.continuousOn
  refine ⟨‖f y₀‖, norm_pos_iff.2 (hne y₀), fun t => ?_⟩
  obtain ⟨y, hy, hyt⟩ := hp.exists_mem_Ico hT t 0
  rw [hyt]
  exact hmin ⟨hy.1, by linarith [hy.2]⟩

theorem x_ne_zero {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (φ : ℝ) :
    P.x φ ≠ 0 := by
  intro h
  have hm := P.mem φ
  rw [h] at hm
  have := hH.2.2 0 hm
  simp at this

/-- `π_{proj(x(φ) + k)} R(x(φ))`. -/
noncomputable def Phi1 (H : V n → ℝ) (P : ReebOrbit H) (q : ℝ × V n) : V n :=
  Pr H (proj H (P.x q.1 + q.2)) (reeb H (P.x q.1))

/-- `π_{proj(x(φ) + k)} - π_{x(φ)}`. -/
noncomputable def Phi2 (H : V n → ℝ) (P : ReebOrbit H) (q : ℝ × V n) : V n →L[ℝ] V n :=
  Pr H (proj H (P.x q.1 + q.2)) - Pr H (P.x q.1)

theorem Pr_comp_contDiffAt {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (q : ℝ × V n) (hq : P.x q.1 + q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × V n => Pr H (proj H (P.x q.1 + q.2))) q := by
  have hxs : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  have hY : ContDiff ℝ ∞ (fun q : ℝ × V n => P.x q.1 + q.2) := (hxs.comp contDiff_fst).add contDiff_snd
  have hpr : ContDiffAt ℝ ∞ (fun q : ℝ × V n => proj H (P.x q.1 + q.2)) q :=
    ContDiffAt.comp (g := proj H) q (proj_contDiffAt H hH hq) hY.contDiffAt
  exact ContDiffAt.comp (g := Pr H) q (Pr_contDiffAt H hH _ (proj_mem H hH hq)) hpr

theorem Prx_contDiffAt {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (q : ℝ × V n) : ContDiffAt ℝ ∞ (fun q : ℝ × V n => Pr H (P.x q.1)) q := by
  have hxs : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  exact ContDiffAt.comp (g := Pr H) q (Pr_contDiffAt H hH _ (P.mem _))
    (hxs.comp contDiff_fst).contDiffAt

theorem ball_ne {H : V n → ℝ} (P : ReebOrbit H) {m₀ : ℝ} (hm₀ : ∀ φ, m₀ ≤ ‖P.x φ‖) (φ : ℝ)
    {k : V n} (hk : ‖k‖ < m₀) : P.x φ + k ≠ 0 := by
  intro h
  have : k = -P.x φ := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h
  rw [this, norm_neg] at hk
  linarith [hm₀ φ]

theorem lip_Phi1 {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) {m₀ : ℝ}
    (hm₀p : 0 < m₀) (hm₀ : ∀ φ, m₀ ≤ ‖P.x φ‖) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (φ : ℝ) (k : V n), ‖k‖ ≤ m₀ / 2 → ‖Phi1 H P (φ, k)‖ ≤ L * ‖k‖ := by
  have hxs : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  refine exists_norm_le_mul_norm_of_periodic (Phi1 H P) P.T m₀ P.T_pos hm₀p ?_ ?_ ?_
  · intro q hq
    have hk : ‖q.2‖ < m₀ := by simpa using hq.2
    have hne := ball_ne P hm₀ q.1 hk
    have hR : ContDiffAt ℝ ∞ (fun q : ℝ × V n => reeb H (P.x q.1)) q :=
      ContDiffAt.comp (g := reeb H) q (ka_reeb_contDiffAt H hH _ (P.mem _))
        (hxs.comp contDiff_fst).contDiffAt
    exact ((Pr_comp_contDiffAt hH P q hne).clm_apply hR).contDiffWithinAt.of_le (by simp)
  · intro φ k _
    simp [Phi1, P.periodic]
  · intro φ
    simp only [Phi1, add_zero]
    rw [proj_of_mem H hH (P.mem φ)]
    exact Pr_reeb H hH _ (P.mem φ)

theorem lip_Phi2 {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) {m₀ : ℝ}
    (hm₀p : 0 < m₀) (hm₀ : ∀ φ, m₀ ≤ ‖P.x φ‖) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (φ : ℝ) (k : V n), ‖k‖ ≤ m₀ / 2 → ‖Phi2 H P (φ, k)‖ ≤ L * ‖k‖ := by
  refine exists_norm_le_mul_norm_of_periodic (Phi2 H P) P.T m₀ P.T_pos hm₀p ?_ ?_ ?_
  · intro q hq
    have hk : ‖q.2‖ < m₀ := by simpa using hq.2
    have hne := ball_ne P hm₀ q.1 hk
    exact ((Pr_comp_contDiffAt hH P q hne).sub (Prx_contDiffAt hH P q)).contDiffWithinAt.of_le
      (by simp)
  · intro φ k _
    simp [Phi2, P.periodic]
  · intro φ
    simp only [Phi2, add_zero]
    rw [proj_of_mem H hH (P.mem φ), sub_self]

end FiniteEnergyPlane.DLPD

namespace FiniteEnergyPlane.DLPD

open FiniteEnergyPlane N1

variable {n : ℕ}

/-- The pointwise estimate: the leading term `E κ v₀` dominates. -/
theorem core {Pw Φ₂ : V n →L[ℝ] V n} {R v0 rr g' Φ1v : V n}
    {E κ τs η L₁ L₂ M₁ B1 Vb G m : ℝ}
    (hE : 0 < E) (hκ : κ < 0) (hPwR : Pw R = Φ1v) (hPwv : Pw v0 = v0 + Φ₂ v0)
    (hτs : |τs| ≤ η) (hΦ1 : ‖Φ1v‖ ≤ L₁ * (E * B1)) (hΦ2 : ‖Φ₂‖ ≤ L₂ * η)
    (hPw : ‖Pw‖ ≤ M₁ + L₂) (hm : m ≤ ‖v0‖) (hVb : ‖v0‖ ≤ Vb) (hrr : ‖rr‖ ≤ η)
    (hg' : ‖g'‖ ≤ η * G) (hη : 0 ≤ η) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hM₁ : 0 ≤ M₁)
    (hB1 : 0 ≤ B1) (hG : 0 ≤ G)
    (hQ : η * (L₁ * B1 + (-κ) * L₂ * Vb + (-κ) * (M₁ + L₂) + (M₁ + L₂) * G) < (-κ) * m) :
    Pw (τs • R + (E • g' + (E * κ) • (v0 + rr))) ≠ 0 := by
  intro h0
  have hexp : Pw (τs • R + (E • g' + (E * κ) • (v0 + rr))) =
      (E * κ) • v0 + (τs • Φ1v + E • (κ • Φ₂ v0 + κ • Pw rr + Pw g')) := by
    simp only [map_add, map_smul, hPwR, hPwv]
    module
  rw [hexp] at h0
  have h1 : ‖(E * κ) • v0‖ = ‖τs • Φ1v + E • (κ • Φ₂ v0 + κ • Pw rr + Pw g')‖ := by
    rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
  have hκa : |κ| = -κ := abs_of_neg hκ
  have hl : ‖(E * κ) • v0‖ = E * (-κ) * ‖v0‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hE, hκa]
  have hA : ‖τs • Φ1v‖ ≤ η * (L₁ * (E * B1)) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hτs hΦ1 (norm_nonneg _) hη
  have hB : ‖Φ₂ v0‖ ≤ L₂ * η * Vb :=
    (Φ₂.le_opNorm v0).trans (mul_le_mul hΦ2 hVb (norm_nonneg _) (by positivity))
  have hC : ‖Pw rr‖ ≤ (M₁ + L₂) * η :=
    (Pw.le_opNorm rr).trans (mul_le_mul hPw hrr (norm_nonneg _) (by positivity))
  have hD : ‖Pw g'‖ ≤ (M₁ + L₂) * (η * G) :=
    (Pw.le_opNorm g').trans (mul_le_mul hPw hg' (norm_nonneg _) (by positivity))
  have hin : ‖κ • Φ₂ v0 + κ • Pw rr + Pw g'‖ ≤
      (-κ) * (L₂ * η * Vb) + (-κ) * ((M₁ + L₂) * η) + (M₁ + L₂) * (η * G) := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hD)
    · rw [norm_smul, Real.norm_eq_abs, hκa]
      exact mul_le_mul_of_nonneg_left hB (by linarith)
    · rw [norm_smul, Real.norm_eq_abs, hκa]
      exact mul_le_mul_of_nonneg_left hC (by linarith)
  have hR : ‖τs • Φ1v + E • (κ • Φ₂ v0 + κ • Pw rr + Pw g')‖ ≤
      η * (L₁ * (E * B1)) +
        E * ((-κ) * (L₂ * η * Vb) + (-κ) * ((M₁ + L₂) * η) + (M₁ + L₂) * (η * G)) := by
    refine (norm_add_le _ _).trans (add_le_add hA ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hE]
    exact mul_le_mul_of_nonneg_left hin hE.le
  have key : E * ((-κ) * m) ≤
      E * (η * (L₁ * B1 + (-κ) * L₂ * Vb + (-κ) * (M₁ + L₂) + (M₁ + L₂) * G)) := by
    calc E * ((-κ) * m) ≤ E * ((-κ) * ‖v0‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (by linarith)) hE.le
      _ = ‖(E * κ) • v0‖ := by rw [hl]; ring
      _ ≤ _ := h1.le.trans hR
      _ = _ := by ring
  have := mul_lt_mul_of_pos_left hQ hE
  linarith

theorem gbound {τs T η V'b G : ℝ} {a rs : V n} (hT : 0 < T) (hτ : |τs| ≤ η) (ha : ‖a‖ ≤ V'b)
    (hrs : ‖rs‖ ≤ η) (hη : 0 ≤ η) (hG : G = V'b / T + 1) : ‖(τs / T) • a + rs‖ ≤ η * G := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hT]
  have hd : |τs| / T ≤ η / T := div_le_div_of_nonneg_right hτ hT.le
  have h1 : |τs| / T * ‖a‖ ≤ η / T * V'b :=
    mul_le_mul hd ha (norm_nonneg _) (div_nonneg hη hT.le)
  have h2 : η / T * V'b + η = η * G := by rw [hG]; field_simp
  linarith

theorem main {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (κ ε c s₀ : ℝ)
    (hκ : κ < 0) (v : ℝ → V n) (hv : IsXiLoop P v) (hv0 : ∀ t : ℝ, v t ≠ 0)
    (τ : ℝ × ℝ → ℝ) (r : ℝ × ℝ → V n) (W : ℝ × ℝ → V n)
    (hτ : TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c))
    (hr : TendstoZeroCInfty r)
    (hW : ∀ s ≥ s₀, ∀ t : ℝ, W (s, t) =
      proj H (P.x (τ (s, t)) + Real.exp (κ * s) • (v (τ (s, t) / P.T) + r (s, t)))) :
    ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      Pr H (W (s, t)) (fderiv ℝ W (s, t) (1, 0)) ≠ 0 := by
  obtain ⟨hvs, hvper, hvξ⟩ := hv
  have hvd : Differentiable ℝ v := hvs.differentiable (by simp)
  have hv'c : Continuous (deriv v) := hvs.continuous_deriv (by simp)
  have hv'per : Function.Periodic (deriv v) 1 := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun f => deriv f x) (funext fun y => hvper y)
  obtain ⟨m, hm, hmv⟩ := lower_of_periodic v hvs.continuous one_pos hvper hv0
  obtain ⟨Vb, hVb0, hVb⟩ := bdd_of_periodic v hvs.continuous one_pos hvper
  obtain ⟨V'b, hV'b0, hV'b⟩ := bdd_of_periodic (deriv v) hv'c one_pos hv'per
  have hxs : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  have hT := P.T_pos
  obtain ⟨m₀, hm₀, hm₀x⟩ := lower_of_periodic P.x hxs.continuous hT P.periodic (x_ne_zero hH P)
  have hPrc : Continuous (fun φ => Pr H (P.x φ)) := continuous_iff_continuousAt.2 fun φ =>
    (ContDiffAt.comp (g := Pr H) φ (Pr_contDiffAt H hH _ (P.mem φ)) hxs.contDiffAt).continuousAt
  obtain ⟨M₁, hM₁0, hM₁⟩ := bdd_of_periodic _ hPrc hT (fun φ => by simp only [P.periodic])
  obtain ⟨L₁, hL₁0, hL₁⟩ := lip_Phi1 hH P hm₀ hm₀x
  obtain ⟨L₂, hL₂0, hL₂⟩ := lip_Phi2 hH P hm₀ hm₀x
  set B1 := Vb + 1 with hB1
  set G := V'b / P.T + 1 with hG
  have hG0 : 0 ≤ G := by positivity
  set Q := L₁ * B1 + (-κ) * L₂ * Vb + (-κ) * (M₁ + L₂) + (M₁ + L₂) * G with hQdef
  have hK : 0 < -κ := by linarith
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ (-κ) := hK.le
    positivity
  set η := min 1 ((-κ) * m / (2 * (Q + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηQ : η * Q < (-κ) * m := by
    have h1 : η ≤ (-κ) * m / (2 * (Q + 1)) := min_le_right _ _
    have h2 : η * Q ≤ (-κ) * m / (2 * (Q + 1)) * Q := mul_le_mul_of_nonneg_right h1 hQ0
    have h3 : (-κ) * m / (2 * (Q + 1)) * Q < (-κ) * m := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hK hm]
    linarith
  set δ := min (m₀ / 2) η with hδdef
  have hδ : 0 < δ := lt_min (by positivity) hη
  obtain ⟨sθ, hθs⟩ := hτ.1
  obtain ⟨sr, hrs⟩ := hr.1
  obtain ⟨s1, hs1⟩ := hτ.2 1 η hη
  obtain ⟨s2, hs2⟩ := hr.2 0 η hη
  obtain ⟨s3, hs3⟩ := hr.2 1 η hη
  set s4 := Real.log (δ / B1) / κ
  have hB1p : 0 < B1 := by positivity
  refine ⟨max (max (max s₀ sθ) (max sr s1)) (max (max s2 s3) s4) + 1, fun s hs t => ?_⟩
  have hs₀ : s₀ < s := by
    have := le_max_left s₀ sθ; have := le_max_left (max s₀ sθ) (max sr s1)
    have := le_max_left (max (max s₀ sθ) (max sr s1)) (max (max s2 s3) s4); linarith
  have hsθ : sθ < s := by
    have := le_max_right s₀ sθ; have := le_max_left (max s₀ sθ) (max sr s1)
    have := le_max_left (max (max s₀ sθ) (max sr s1)) (max (max s2 s3) s4); linarith
  have hsr : sr < s := by
    have := le_max_left sr s1; have := le_max_right (max s₀ sθ) (max sr s1)
    have := le_max_left (max (max s₀ sθ) (max sr s1)) (max (max s2 s3) s4); linarith
  have hs1' : s1 ≤ s := by
    have := le_max_right sr s1; have := le_max_right (max s₀ sθ) (max sr s1)
    have := le_max_left (max (max s₀ sθ) (max sr s1)) (max (max s2 s3) s4); linarith
  have hs2' : s2 ≤ s := by
    have := le_max_left s2 s3; have := le_max_left (max s2 s3) s4
    have := le_max_right (max (max s₀ sθ) (max sr s1)) (max (max s2 s3) s4); linarith
  have hs3' : s3 ≤ s := by
    have := le_max_right s2 s3; have := le_max_left (max s2 s3) s4
    have := le_max_right (max (max s₀ sθ) (max sr s1)) (max (max s2 s3) s4); linarith
  have hs4 : s4 ≤ s := by
    have := le_max_right (max s2 s3) s4
    have := le_max_right (max (max s₀ sθ) (max sr s1)) (max (max s2 s3) s4); linarith
  set p : ℝ × ℝ := (s, t) with hp
  set θ : ℝ × ℝ → ℝ := fun p => τ p - ε * P.T * p.2 - c with hθdef
  have hopen : ∀ a : ℝ, IsOpen (Set.Ioi a ×ˢ (Set.univ : Set ℝ)) :=
    fun a => isOpen_Ioi.prod isOpen_univ
  have hθd : DifferentiableAt ℝ θ p :=
    (hθs.contDiffAt ((hopen sθ).mem_nhds (Set.mk_mem_prod (Set.mem_Ioi.2 hsθ) (Set.mem_univ t)))).differentiableAt (by simp)
  have hrd : DifferentiableAt ℝ r p :=
    (hrs.contDiffAt ((hopen sr).mem_nhds (Set.mk_mem_prod (Set.mem_Ioi.2 hsr) (Set.mem_univ t)))).differentiableAt (by simp)
  have hτeq : τ = fun q => θ q + (ε * P.T * q.2 + c) := by
    funext q; simp only [hθdef]; ring
  have hτd : DifferentiableAt ℝ τ p := by
    rw [hτeq]; exact hθd.add (by fun_prop)
  set Y : ℝ × ℝ → V n := fun q =>
    P.x (τ q) + Real.exp (κ * q.1) • (v (τ q / P.T) + r q) with hYdef
  have hτT : DifferentiableAt ℝ (fun q => τ q / P.T) p := by
    simpa [div_eq_mul_inv] using hτd.mul_const P.T⁻¹
  have hvT : DifferentiableAt ℝ (fun q => v (τ q / P.T)) p := (hvd _).comp p hτT
  have hxτ : DifferentiableAt ℝ (fun q => P.x (τ q)) p :=
    ((hxs.differentiable (by simp)) _).comp p hτd
  have hYd : DifferentiableAt ℝ Y p :=
    hxτ.add ((by fun_prop : DifferentiableAt ℝ (fun q : ℝ × ℝ => Real.exp (κ * q.1)) p).smul
      (hvT.add hrd))
  -- derivatives along the line `σ ↦ (σ, t)`
  have hline : HasDerivAt (fun σ : ℝ => (σ, t)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  set τs := fderiv ℝ θ p (1, 0) with hτsdef
  set rs := fderiv ℝ r p (1, 0) with hrsdef
  have hθl : HasDerivAt (fun σ => θ (σ, t)) τs s := by
    have := hθd.hasFDerivAt.comp_hasDerivAt s hline; exact this
  have hτl : HasDerivAt (fun σ => τ (σ, t)) τs s := by
    refine (hθl.add_const (ε * P.T * t + c)).congr_of_eventuallyEq
      (Eventually.of_forall fun σ => ?_)
    simp only [hθdef]; ring
  have hxl : HasDerivAt (fun σ => P.x (τ (σ, t))) (τs • reeb H (P.x (τ p))) s :=
    (P.hasDerivAt (τ p)).scomp s hτl
  have hvl : HasDerivAt (fun σ => v (τ (σ, t) / P.T)) ((τs / P.T) • deriv v (τ p / P.T)) s :=
    ((hvd _).hasDerivAt).scomp s (hτl.div_const P.T)
  have hrl : HasDerivAt (fun σ => r (σ, t)) rs s := by
    have := hrd.hasFDerivAt.comp_hasDerivAt s hline; exact this
  have hel : HasDerivAt (fun σ => Real.exp (κ * σ)) (Real.exp (κ * s) * κ) s := by
    simpa using ((hasDerivAt_id s).const_mul κ).exp
  have hYl := hxl.add (hel.smul (hvl.add hrl))
  have hdY : fderiv ℝ Y p (1, 0) = τs • reeb H (P.x (τ p)) +
      (Real.exp (κ * s) • ((τs / P.T) • deriv v (τ p / P.T) + rs) +
        (Real.exp (κ * s) * κ) • (v (τ p / P.T) + r p)) := by
    have h1 : HasDerivAt (fun σ => Y (σ, t)) (fderiv ℝ Y p (1, 0)) s := by
      have := hYd.hasFDerivAt.comp_hasDerivAt s hline; exact this
    have h2 : HasDerivAt (fun σ => Y (σ, t)) (τs • reeb H (P.x (τ p)) +
      (Real.exp (κ * s) • ((τs / P.T) • deriv v (τ p / P.T) + rs) +
        (Real.exp (κ * s) * κ) • (v (τ p / P.T) + r p))) s := by exact hYl
    exact h1.unique h2
  -- the point
  set φ := τ p with hφ
  set E := Real.exp (κ * s) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set k : V n := E • (v (φ / P.T) + r p) with hk
  have hrp : ‖r p‖ ≤ η := by
    have := hs2 s hs2' t; rwa [norm_iteratedFDeriv_zero] at this
  have hgn : ‖v (φ / P.T) + r p‖ ≤ B1 :=
    (norm_add_le _ _).trans (by linarith [hVb (φ / P.T)])
  have hEB : E * B1 ≤ δ := by
    have h1 : κ * s ≤ Real.log (δ / B1) := by
      have : κ * s ≤ κ * s4 := mul_le_mul_of_nonpos_left hs4 hκ.le
      have h2 : κ * s4 = Real.log (δ / B1) := by
        simp only [s4]; rw [mul_comm]; exact div_mul_cancel₀ _ hκ.ne
      linarith
    have := Real.exp_le_exp.2 h1
    rw [Real.exp_log (by positivity)] at this
    rw [le_div_iff₀ hB1p] at this
    exact this
  have hkn : ‖k‖ ≤ E * B1 := by
    rw [hk, norm_smul, Real.norm_eq_abs, abs_of_pos hEpos]
    exact mul_le_mul_of_nonneg_left hgn hEpos.le
  have hkδ : ‖k‖ ≤ δ := hkn.trans hEB
  have hkm : ‖k‖ ≤ m₀ / 2 := hkδ.trans (min_le_left _ _)
  have hkη : ‖k‖ ≤ η := hkδ.trans (min_le_right _ _)
  have hYp : Y p = P.x φ + k := rfl
  have hY0 : Y p ≠ 0 := by
    rw [hYp]; exact ball_ne P hm₀x φ (by linarith)
  -- `W = proj ∘ Y` near `p`
  have heq : W =ᶠ[𝓝 p] fun q => proj H (Y q) := by
    filter_upwards [(hopen s₀).mem_nhds (Set.mk_mem_prod (Set.mem_Ioi.2 hs₀) (Set.mem_univ t))] with q hq
    obtain ⟨a, b⟩ := q
    exact hW a (le_of_lt hq.1) b
  have hσ := ka_scale_spec H hH (Y p) hY0
  set σ := scaleToS H (Y p) with hσdef
  set Lsc : V n →L[ℝ] ℝ := (-(scaleToS H (Y p) ^ 2 / fderiv ℝ H (proj H (Y p)) (proj H (Y p)))) •
          fderiv ℝ H (proj H (Y p)) with hLsc
  have hproj : HasFDerivAt (proj H)
      (σ • ContinuousLinearMap.id ℝ (V n) + Lsc.smulRight (Y p)) (Y p) :=
    (ka_scale_hasFDerivAt H hH (Y p) hY0).smul (hasFDerivAt_id (Y p))
  have hWd := (hproj.comp p hYd.hasFDerivAt).congr_of_eventuallyEq heq
  have hWp : W p = proj H (Y p) := heq.eq_of_nhds
  set Pw := Pr H (proj H (Y p)) with hPwdef
  have hPwY : Pw (Y p) = 0 := by
    have h := Pr_self H hH (proj H (Y p)) (proj_mem H hH hY0)
    have h2 : proj H (Y p) = σ • Y p := rfl
    rw [← hPwdef] at h
    rw [h2, map_smul] at h
    exact (smul_eq_zero.1 h).resolve_left hσ.1.ne'
  show Pr H (W p) (fderiv ℝ W p (1, 0)) ≠ 0
  have hred : ∀ d : V n, Pw ((σ • ContinuousLinearMap.id ℝ (V n) + Lsc.smulRight (Y p)) d) =
      σ • Pw d := by
    intro d
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      map_smul, hPwY, smul_zero, add_zero]
  rw [hWd.fderiv, hWp, ← hPwdef, ContinuousLinearMap.comp_apply, hred, hdY]
  refine smul_ne_zero hσ.1.ne' ?_
  -- apply the core estimate
  have hPwx : Pw = Pr H (P.x φ) + Phi2 H P (φ, k) := by
    simp only [hPwdef, Phi2, hYp]; abel
  have hΦ2 : ‖Phi2 H P (φ, k)‖ ≤ L₂ * η :=
    (hL₂ φ k hkm).trans (mul_le_mul_of_nonneg_left hkη hL₂0)
  refine core (Φ₂ := Phi2 H P (φ, k)) (Φ1v := Phi1 H P (φ, k)) (L₁ := L₁) (L₂ := L₂)
    (M₁ := M₁) (B1 := B1) (Vb := Vb) (G := G) (m := m) (η := η)
    hEpos hκ ?_ ?_ ?_ ?_ hΦ2 ?_ (hmv _) (hVb _) hrp ?_ hη.le hL₁0 hL₂0 hM₁0 hB1p.le hG0 hηQ
  · simp only [hPwdef, Phi1, hYp]
  · rw [hPwx, ContinuousLinearMap.add_apply]
    congr 1
    have hξ := hvξ (φ / P.T)
    rw [mul_div_cancel₀ φ hT.ne'] at hξ
    exact Pr_xi H _ _ hξ
  · have h := hs1 s hs1' t
    rw [norm_iteratedFDeriv_one] at h
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ θ p).le_opNorm _).trans ?_
    have : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
    rw [this, mul_one]; exact h
  · exact (hL₁ φ k hkm).trans (mul_le_mul_of_nonneg_left hkn hL₁0)
  · rw [hPwx]
    refine (norm_add_le _ _).trans (add_le_add (hM₁ φ) (hΦ2.trans ?_))
    nlinarith
  · have hrs1 : ‖rs‖ ≤ η := by
      have h := hs3 s hs3' t
      rw [norm_iteratedFDeriv_one] at h
      refine ((fderiv ℝ r p).le_opNorm _).trans ?_
      have : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
      rw [this, mul_one]; exact h
    have hτs' : |τs| ≤ η := by
      have h := hs1 s hs1' t
      rw [norm_iteratedFDeriv_one] at h
      rw [← Real.norm_eq_abs]
      refine ((fderiv ℝ θ p).le_opNorm _).trans ?_
      have : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
      rw [this, mul_one]; exact h
    exact gbound hT hτs' (hV'b _) hrs1 hη.le hG

end FiniteEnergyPlane.DLPD

namespace FiniteEnergyPlane

theorem xiPart_partialS_ne_zero_of_eigenTube_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (κ ε c s₀ : ℝ) (hκ : κ < 0)
    (v : ℝ → V n) (hv : IsXiLoop P v) (hv0 : ∀ t : ℝ, v t ≠ 0)
    (τ : ℝ × ℝ → ℝ) (r : ℝ × ℝ → V n) (W : ℝ × ℝ → V n)
    (hτ : TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c))
    (hr : TendstoZeroCInfty r)
    (hW : ∀ s ≥ s₀, ∀ t : ℝ, W (s, t) =
      proj H (P.x (τ (s, t)) + Real.exp (κ * s) • (v (τ (s, t) / P.T) + r (s, t)))) :
    ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      let w := W (s, t)
      let d := fderiv ℝ W (s, t) (1, 0)
      d - (fderiv ℝ H w d / fderiv ℝ H w w) • w - liouville w d • reeb H w ≠ 0 := by
  obtain ⟨s₁, hs₁⟩ := DLPD.main hH P κ ε c s₀ hκ v hv hv0 τ r W hτ hr hW
  refine ⟨s₁, fun s hs t => ?_⟩
  have := hs₁ s hs t
  rwa [N1.Pr_apply] at this

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (κ ε c s₀ : ℝ) (hκ : κ < 0)
    (v : ℝ → V n) (hv : IsXiLoop P v) (hv0 : ∀ t : ℝ, v t ≠ 0)
    (τ : ℝ × ℝ → ℝ) (r : ℝ × ℝ → V n) (W : ℝ × ℝ → V n)
    (hτ : TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c))
    (hr : TendstoZeroCInfty r)
    (hW : ∀ s ≥ s₀, ∀ t : ℝ, W (s, t) =
      proj H (P.x (τ (s, t)) + Real.exp (κ * s) • (v (τ (s, t) / P.T) + r (s, t)))) :
    ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      let w := W (s, t)
      let d := fderiv ℝ W (s, t) (1, 0)
      d - (fderiv ℝ H w d / fderiv ℝ H w w) • w - liouville w d • reeb H w ≠ 0 :=
  xiPart_partialS_ne_zero_of_eigenTube_aux H hH P κ ε c s₀ hκ v hv hv0 τ r W hτ hr hW
