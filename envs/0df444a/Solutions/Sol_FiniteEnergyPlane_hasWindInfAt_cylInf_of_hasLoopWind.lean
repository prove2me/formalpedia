-- Prove2me | solution 1 for FiniteEnergyPlane.hasWindInfAt_cylInf_of_hasLoopWind
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T11:34:52.083576+00:00
-- url     : https://prove2.me/submissions/118e8612-c219-4f04-b0ff-cec3f8f89c82

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_zero_of_forall_ne_ray
import Theorems.Thm_FiniteEnergyPlane_continuousAt_xiCoordC
import Theorems.Thm_FiniteEnergyPlane_im_conj_xiCoordC_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_re_mul_add_im_mul

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

theorem ka_aCoord_differentiableAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {y : V n} (hy : y ≠ 0) : DifferentiableAt ℝ (aCoord H) y := by
  have hr := (ka_scale_spec H hH y hy).1
  have hd : DifferentiableAt ℝ (scaleToS H) y :=
    (ka_scale_contDiffAt H hH y hy).differentiableAt (by simp)
  have : aCoord H = fun y => (-1 / 2 : ℝ) * Real.log (scaleToS H y) := by
    funext y; unfold aCoord; ring
  rw [this]
  exact (hd.log hr.ne').const_mul _

theorem ka_proj_differentiableAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {y : V n} (hy : y ≠ 0) : DifferentiableAt ℝ (proj H) y := by
  have hd : DifferentiableAt ℝ (scaleToS H) y :=
    (ka_scale_contDiffAt H hH y hy).differentiableAt (by simp)
  have : proj H = fun y => scaleToS H y • y := rfl
  rw [this]
  exact hd.smul differentiableAt_id

/-- The real-linear map `(s, t) ↦ -2π (s + i t)`. -/
noncomputable def kaL : ℝ × ℝ →L[ℝ] ℂ :=
  (-(2 * π) : ℝ) • (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I)

theorem kaL_apply (p : ℝ × ℝ) : kaL p = (-(2 * π) : ℝ) • ((p.1 : ℂ) + p.2 • Complex.I) := by
  simp [kaL]

theorem ka_cylEnd_eq (p : ℝ × ℝ) : cylEnd p.1 p.2 = Complex.exp (kaL p) := by
  rw [kaL_apply]
  simp only [cylEnd, cwLoop, zero_add]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
  push_cast
  ring

theorem ka_cylEnd_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => cylEnd p.1 p.2) (Complex.exp (kaL p) • kaL) p := by
  have : (fun p : ℝ × ℝ => cylEnd p.1 p.2) = fun p => Complex.exp (kaL p) := by
    funext p; exact ka_cylEnd_eq p
  rw [this]
  exact kaL.hasFDerivAt.cexp

theorem ka_cylEnd_mem {s : ℝ} (hs : 0 < s) (t : ℝ) : cylEnd s t ∈ ball (0 : ℂ) 1 \ {0} := by
  have hn : ‖cylEnd s t‖ = Real.exp (-(2 * π * s)) := by
    rw [show cylEnd s t = cylEnd (s, t).1 (s, t).2 from rfl, ka_cylEnd_eq, Complex.norm_exp,
      kaL_apply]
    simp
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, hn, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  · intro h0
    rw [Set.mem_singleton_iff] at h0
    rw [h0, norm_zero] at hn
    exact (Real.exp_pos _).ne' hn.symm

theorem fderiv_endA_eq_liouville_endW_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : JHolomorphic.IsJHolomorphicOn (Jtilde H J) (ball 0 1 \ {0}) u)
    (hu0 : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, u z ≠ 0) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    DifferentiableAt ℝ (endA H u cylEnd) (s, t) ∧ DifferentiableAt ℝ (endW H u cylEnd) (s, t) ∧
      fderiv ℝ (endA H u cylEnd) (s, t) (1, 0) =
        liouville (endW H u cylEnd (s, t)) (fderiv ℝ (endW H u cylEnd) (s, t) (0, 1)) ∧
      fderiv ℝ (endA H u cylEnd) (s, t) (0, 1) =
        -liouville (endW H u cylEnd (s, t)) (fderiv ℝ (endW H u cylEnd) (s, t) (1, 0)) := by
  set p : ℝ × ℝ := (s, t)
  set ζ := cylEnd s t with hζ
  have hmem := ka_cylEnd_mem hs t
  have hy : u ζ ≠ 0 := hu0 ζ hmem
  obtain ⟨hdu, hhol⟩ := hu ζ hmem
  set a : ℂ → ℝ := fun z => aCoord H (u z) with ha
  set w : ℂ → V n := fun z => proj H (u z) with hw
  have hda : DifferentiableAt ℝ a ζ :=
    (ka_aCoord_differentiableAt H hH hy).comp ζ hdu
  have hdw : DifferentiableAt ℝ w ζ :=
    (ka_proj_differentiableAt H hH hy).comp ζ hdu
  have hE := ka_cylEnd_hasFDerivAt p
  have hEp : (fun p : ℝ × ℝ => cylEnd p.1 p.2) p = ζ := rfl
  have hA : HasFDerivAt (endA H u cylEnd) ((fderiv ℝ a ζ).comp (Complex.exp (kaL p) • kaL)) p := by
    have := (hEp ▸ hda.hasFDerivAt).comp p hE
    exact this
  have hW : HasFDerivAt (endW H u cylEnd) ((fderiv ℝ w ζ).comp (Complex.exp (kaL p) • kaL)) p := by
    have := (hEp ▸ hdw.hasFDerivAt).comp p hE
    exact this
  obtain ⟨cr1, cr2⟩ := ka_cr H hH J hJ u ζ hdu hy hhol
  set c : ℂ := Complex.exp (kaL p) * (-(2 * π) : ℝ) with hc
  have e10 : (Complex.exp (kaL p) • kaL) (1, 0) = c := by
    simp [kaL_apply, hc]
  have e01 : (Complex.exp (kaL p) • kaL) (0, 1) = Complex.I * c := by
    simp [kaL_apply, hc]; ring
  have dec : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : ℂ →L[ℝ] F) (z : ℂ),
      L z = z.re • L 1 + z.im • L Complex.I := by
    intro F _ _ L z
    conv_lhs => rw [show z = z.re • (1 : ℂ) + z.im • Complex.I by apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul]
  have hre : (Complex.I * c).re = -c.im := by simp
  have him : (Complex.I * c).im = c.re := by simp
  unfold ds dt at cr1 cr2
  have hwz : endW H u cylEnd p = w ζ := rfl
  refine ⟨hA.differentiableAt, hW.differentiableAt, ?_, ?_⟩
  · rw [hA.fderiv, hW.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      e10, e01, dec (fderiv ℝ a ζ) c, dec (fderiv ℝ w ζ) (Complex.I * c), hre, him, hwz]
    simp only [smul_eq_mul]
    rw [cr1, cr2]
    unfold liouville
    simp only [ka_om_add_right, ka_om_smul_right]
    ring
  · rw [hA.fderiv, hW.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      e10, e01, dec (fderiv ℝ a ζ) (Complex.I * c), dec (fderiv ℝ w ζ) c, hre, him, hwz]
    simp only [smul_eq_mul]
    rw [cr1, cr2]
    unfold liouville
    simp only [ka_om_add_right, ka_om_smul_right]
    ring

end FiniteEnergyPlane

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

open N1

/-- At a point of `u`, the `ξ`-part of `∂ₛ(proj ∘ u)` is `-J` of the `ξ`-part of `∂ₜ(proj ∘ u)`. -/
theorem nx_xi_parts {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0) :
    Pr H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z 1) =
      -J (proj H (u z)) (Pr H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z Complex.I)) ∧
    IsInXi H (proj H (u z)) (Pr H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z Complex.I)) := by
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
  have hS' := ka_scale_hasFDerivAt H hH y hz
  have hp' : HasFDerivAt (proj H) (r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A)) y := by
    have h1 := hS'.smul (hasFDerivAt_id y)
    have heq : r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A) =
        scaleToS H y • ContinuousLinearMap.id ℝ (V n) +
        ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) •
          fderiv ℝ H (proj H y)).smulRight y := by
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
  have hdw : ∀ v : ℂ, fderiv ℝ (fun z => proj H (u z)) z v =
      r • (fderiv ℝ u z v - α (fderiv ℝ u z v) • A) := by
    intro v
    rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]
    rfl
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
  have hPA : Pr H x A = 0 := by
    show Pr H x ((2:ℝ) • y) = 0
    rw [hyx, map_smul, map_smul, Pr_self H hH x hx, smul_zero, smul_zero]
  have hPB : Pr H x B = 0 := by
    show Pr H x (r⁻¹ • reeb H x) = 0
    rw [map_smul, Pr_reeb H hH x hx, smul_zero]
  set Wt := ut - α ut • A - β ut • B with hWt
  have hPWt : IsInXi H x Wt := hWgen ut
  have hJWt : IsInXi H x (J x Wt) := (hJ.2 x hx Wt Wt hPWt hPWt).1
  have hholx : us + (α ut • B - β ut • A + J x Wt) = 0 := hhol
  clear_value A B
  have hPus : Pr H x us = -J x Wt := by
    have hs : us = -(α ut • B - β ut • A + J x Wt) := eq_neg_of_add_eq_zero_left hholx
    rw [hs, map_neg, map_add, map_sub, map_smul, map_smul, hPA, hPB, Pr_xi H x _ hJWt]
    simp
  have hPut : Pr H x ut = Wt := by
    have : ut = Wt + α ut • A + β ut • B := by rw [hWt]; abel
    rw [this, map_add, map_add, map_smul, map_smul, hPA, hPB, Pr_xi H x _ hPWt]
    simp
  have ha : Pr H x (fderiv ℝ (fun z => proj H (u z)) z 1) = r • -J x Wt := by
    rw [hdw, map_smul, map_sub, map_smul, hPA, smul_zero, sub_zero]
    exact congrArg (r • ·) hPus
  have hb : Pr H x (fderiv ℝ (fun z => proj H (u z)) z Complex.I) = r • Wt := by
    rw [hdw, map_smul, map_sub, map_smul, hPA, smul_zero, sub_zero]
    exact congrArg (r • ·) hPut
  refine ⟨?_, ?_⟩
  · rw [ha, hb, map_smul, smul_neg]
  · rw [hb]
    exact ⟨by rw [← ka_liouvilleCLM_apply, map_smul, ka_liouvilleCLM_apply, hPWt.1, smul_zero],
      by rw [map_smul, hPWt.2, smul_zero]⟩

theorem xiPart_dbar_endW_eq_zero_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    let w := endW H u cylEnd (s, t)
    let πw : V n → V n := fun v =>
      v - (fderiv ℝ H w v / fderiv ℝ H w w) • w - liouville w v • reeb H w
    πw (fderiv ℝ (endW H u cylEnd) (s, t) (1, 0)) +
      J w (πw (fderiv ℝ (endW H u cylEnd) (s, t) (0, 1))) = 0 := by
  intro w πw
  have hπ : ∀ v, πw v = Pr H w v := fun v => (Pr_apply H w v).symm
  simp only [hπ]
  set p : ℝ × ℝ := (s, t)
  set ζ := cylEnd s t with hζ
  have hmem := ka_cylEnd_mem hs t
  obtain ⟨_, hu0, hhol, _⟩ := hu
  have hy : u ζ ≠ 0 := hu0 ζ hmem
  obtain ⟨hdu, hdbar⟩ := hhol ζ hmem
  set wf : ℂ → V n := fun z => proj H (u z) with hwf
  have hdw : DifferentiableAt ℝ wf ζ := (ka_proj_differentiableAt H hH hy).comp ζ hdu
  have hE := ka_cylEnd_hasFDerivAt p
  have hEp : (fun p : ℝ × ℝ => cylEnd p.1 p.2) p = ζ := rfl
  have hW : HasFDerivAt (endW H u cylEnd) ((fderiv ℝ wf ζ).comp (Complex.exp (kaL p) • kaL)) p := by
    have := (hEp ▸ hdw.hasFDerivAt).comp p hE
    exact this
  set c : ℂ := Complex.exp (kaL p) * (-(2 * π) : ℝ) with hc
  have e10 : (Complex.exp (kaL p) • kaL) (1, 0) = c := by simp [kaL_apply, hc]
  have e01 : (Complex.exp (kaL p) • kaL) (0, 1) = Complex.I * c := by
    simp [kaL_apply, hc]; ring
  have dec : ∀ (L : ℂ →L[ℝ] V n) (z : ℂ), L z = z.re • L 1 + z.im • L Complex.I := by
    intro L z
    conv_lhs => rw [show z = z.re • (1 : ℂ) + z.im • Complex.I by apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul]
  have hre : (Complex.I * c).re = -c.im := by simp
  have him : (Complex.I * c).im = c.re := by simp
  have hwz : w = wf ζ := rfl
  obtain ⟨hab, hbξ⟩ := nx_xi_parts H hH J hJ u ζ hdu hy hdbar
  have hwS : wf ζ ∈ energySurface H := proj_mem H hH hy
  have hJJ : J (wf ζ) (J (wf ζ) (Pr H (wf ζ) (fderiv ℝ wf ζ Complex.I))) =
      -Pr H (wf ζ) (fderiv ℝ wf ζ Complex.I) := (hJ.2 _ hwS _ _ hbξ hbξ).2.1
  rw [hW.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, e10, e01,
    dec (fderiv ℝ wf ζ) c, dec (fderiv ℝ wf ζ) (Complex.I * c), hre, him, hwz]
  simp only [map_add, map_smul]
  rw [show (fderiv ℝ wf ζ) 1 = fderiv ℝ (fun z => proj H (u z)) ζ 1 from rfl, hab, map_neg, hJJ]
  module

end FiniteEnergyPlane

namespace FiniteEnergyPlane

lemma c1x_xiCoordC_eq (H : V 1 → ℝ) (x v : V 1) :
    xiCoordC H x v =
      ((HryniewiczCriterion.omega0 v (HryniewiczCriterion.xiFrame2 H x) : ℝ) : ℂ) +
        ((HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H x) v : ℝ) : ℂ) *
          Complex.I := by
  have hc : xiCoordC H x v =
      ⟨HryniewiczCriterion.omega0 v (HryniewiczCriterion.xiFrame2 H x),
        HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H x) v⟩ := rfl
  rw [hc]
  apply Complex.ext <;> simp

/-- `xiCoordC H x` is real-linear. -/
lemma c1x_xiCoordC_add_smul (H : V 1 → ℝ) (x v v' : V 1) (a b : ℝ) :
    xiCoordC H x (a • v + b • v') = a * xiCoordC H x v + b * xiCoordC H x v' := by
  simp only [c1x_xiCoordC_eq, HryniewiczCriterion.omega0, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  ring

lemma c1x_xiCoordC_zero (H : V 1 → ℝ) (x : V 1) : xiCoordC H x 0 = 0 := by
  simp [c1x_xiCoordC_eq, HryniewiczCriterion.omega0]

lemma c1x_omega0_continuous :
    Continuous (fun p : HryniewiczCriterion.R4 × HryniewiczCriterion.R4 =>
      HryniewiczCriterion.omega0 p.1 p.2) := by
  unfold HryniewiczCriterion.omega0
  fun_prop

lemma c1x_omega0_eq (u v : V 1) : omega0 u v = HryniewiczCriterion.omega0 u v := by
  simp [omega0, HryniewiczCriterion.omega0, dot, j0, Fin.sum_univ_four]; ring

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

lemma c1w_ccwLoop_periodic (R : ℝ) : Function.Periodic (ccwLoop R) 1 := by
  intro t
  simp only [ccwLoop]
  congr 1
  rw [show (((2 * π * (t + 1) : ℝ)) : ℂ) * Complex.I =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma c1w_ccwLoop_continuous (R : ℝ) : Continuous (ccwLoop R) := by
  unfold ccwLoop
  fun_prop

lemma c1w_norm_ccwLoop (R t : ℝ) (hR : 0 ≤ R) : ‖ccwLoop R t‖ = R := by
  simp only [ccwLoop, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]

lemma c1w_ccwLoop_pow (R t : ℝ) (m : ℕ) :
    ccwLoop R t ^ m = ((R ^ m : ℝ) : ℂ) * Complex.exp (((2 * π * m * t : ℝ) : ℂ) * Complex.I) := by
  simp only [ccwLoop, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- The loop `t ↦ a ρ^m e^{2πimt}` (`a ≠ 0`, `ρ > 0`) has winding number `m`. -/
lemma c1w_hasLoopWind_const_mul_pow (a : ℂ) (ha : a ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) :
    HasLoopWind (fun t => a * ccwLoop ρ t ^ m) m := by
  have hc : Continuous (fun t => a * ccwLoop ρ t ^ m) :=
    continuous_const.mul ((c1w_ccwLoop_continuous ρ).pow m)
  refine ⟨hc, fun t => by simp only [c1w_ccwLoop_periodic ρ t], fun t => ?_, ?_⟩
  · refine mul_ne_zero ha (pow_ne_zero _ ?_)
    intro h
    have := c1w_norm_ccwLoop ρ t hρ.le
    rw [h, norm_zero] at this
    linarith
  · refine ⟨fun t => Complex.arg a + 2 * π * m * t, by fun_prop, fun t => ?_, by push_cast; ring⟩
    have hn : ‖a * ccwLoop ρ t ^ m‖ = ‖a‖ * ρ ^ m := by
      rw [norm_mul, norm_pow, c1w_norm_ccwLoop ρ t hρ.le]
    dsimp only
    rw [hn, c1w_ccwLoop_pow]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a]
    push_cast
    rw [show ((Complex.arg a : ℂ) + 2 * π * m * t) * Complex.I =
        (Complex.arg a : ℂ) * Complex.I + 2 * π * m * t * Complex.I by ring, Complex.exp_add]
    ring

lemma c1w_alg (w p q : ℂ) : (w.re : ℂ) * p + (w.im : ℂ) * q =
    (p - Complex.I * q) / 2 * w + (p + Complex.I * q) / 2 * starRingEnd ℂ w := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have h2 : starRingEnd ℂ w = (w.re : ℂ) - (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(p - Complex.I * q) / 2) * hw + (-(p + Complex.I * q) / 2) * h2 +
    (q * (w.im : ℂ)) * Complex.I_sq

/-- Let `p, q` be continuous on `B(z₀, R)` with `Im(conj p(z₀) · q(z₀)) > 0` (so that
`w ↦ Re(w) p(z₀) + Im(w) q(z₀)` is an orientation-preserving real-linear isomorphism of `ℂ`), and let
`F(z) = Re((z - z₀)^m) p(z) + Im((z - z₀)^m) q(z)` on `B(z₀, R)`. Then on some smaller disc
`B(z₀, r)`, `F` has no zero other than `z₀`, and `F` has winding number `m` along every
counterclockwise circle `t ↦ z₀ + ρ e^{2πit}`, `0 < ρ < r`. -/
theorem exists_ball_hasLoopWind_re_mul_add_im_mul_aux (F p q : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hp : ContinuousOn p (ball z₀ R)) (hq : ContinuousOn q (ball z₀ R))
    (hpq : 0 < (starRingEnd ℂ (p z₀) * q z₀).im)
    (hF : ∀ z ∈ ball z₀ R,
      F z = (((z - z₀) ^ m).re : ℂ) * p z + (((z - z₀) ^ m).im : ℂ) * q z) :
    ∃ r > (0 : ℝ), r ≤ R ∧ (∀ z ∈ ball z₀ r, z ≠ z₀ → F z ≠ 0) ∧
      ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => F (z₀ + ccwLoop ρ t)) m := by
  set A : ℂ → ℂ := fun z => (p z - Complex.I * q z) / 2 with hA
  set B : ℂ → ℂ := fun z => (p z + Complex.I * q z) / 2 with hB
  have hFAB : ∀ z ∈ ball z₀ R, F z = A z * (z - z₀) ^ m + B z * starRingEnd ℂ ((z - z₀) ^ m) := by
    intro z hz
    rw [hF z hz]
    exact c1w_alg _ _ _
  -- `‖B z₀‖ < ‖A z₀‖`
  have hAB : ‖B z₀‖ < ‖A z₀‖ := by
    have key : Complex.normSq (A z₀) - Complex.normSq (B z₀) =
        (starRingEnd ℂ (p z₀) * q z₀).im := by
      simp only [hA, hB, Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.sub_re,
        Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
      norm_num
      ring
    have h2 : ‖B z₀‖ ^ 2 < ‖A z₀‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2
  set κ := ‖A z₀‖ - ‖B z₀‖ with hκ
  have hκ0 : 0 < κ := by linarith
  have hA0 : A z₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hAB; exact absurd hAB (not_lt.2 (norm_nonneg _))
  have hzR : ball z₀ R ∈ 𝓝 z₀ := isOpen_ball.mem_nhds (mem_ball_self hR)
  have hAc : ContinuousAt A z₀ :=
    ((hp.continuousAt hzR).sub (continuousAt_const.mul (hq.continuousAt hzR))).div_const _
  have hBc : ContinuousAt B z₀ :=
    ((hp.continuousAt hzR).add (continuousAt_const.mul (hq.continuousAt hzR))).div_const _
  have hev : ∀ᶠ z in 𝓝 z₀, ‖A z - A z₀‖ < κ / 2 ∧ ‖B z - B z₀‖ < κ / 2 ∧ z ∈ ball z₀ R := by
    refine ((hAc.sub continuousAt_const).norm.eventually (gt_mem_nhds ?_)).and
      (((hBc.sub continuousAt_const).norm.eventually (gt_mem_nhds ?_)).and hzR)
    · simp only [Pi.sub_apply, hA, sub_self, norm_zero]; exact half_pos hκ0
    · simp only [Pi.sub_apply, hB, sub_self, norm_zero]; exact half_pos hκ0
  obtain ⟨r, hr, hrs⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set r' := min r R
  have hr' : 0 < r' := lt_min hr hR
  -- the key estimate `‖F z - A z₀ w‖ < ‖A z₀‖ ‖w‖` for `w = (z - z₀)^m ≠ 0`
  have hest : ∀ z ∈ ball z₀ r', z ≠ z₀ →
      ‖F z - A z₀ * (z - z₀) ^ m‖ < ‖A z₀ * (z - z₀) ^ m‖ := by
    intro z hz hne
    obtain ⟨h1, h2, h3⟩ := hrs z (ball_subset_ball (min_le_left _ _) hz)
    have hw : 0 < ‖(z - z₀) ^ m‖ := norm_pos_iff.2 (pow_ne_zero _ (sub_ne_zero.2 hne))
    rw [hFAB z h3, show A z * (z - z₀) ^ m + B z * starRingEnd ℂ ((z - z₀) ^ m) -
        A z₀ * (z - z₀) ^ m = (A z - A z₀) * (z - z₀) ^ m +
          B z * starRingEnd ℂ ((z - z₀) ^ m) by ring]
    have hBz : ‖B z‖ < ‖B z₀‖ + κ / 2 := by
      have := norm_sub_norm_le (B z) (B z₀)
      linarith
    calc _ ≤ ‖(A z - A z₀) * (z - z₀) ^ m‖ + ‖B z * starRingEnd ℂ ((z - z₀) ^ m)‖ :=
          norm_add_le _ _
      _ = (‖A z - A z₀‖ + ‖B z‖) * ‖(z - z₀) ^ m‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]; ring
      _ < ‖A z₀‖ * ‖(z - z₀) ^ m‖ := by
          refine mul_lt_mul_of_pos_right ?_ hw; linarith
      _ = _ := (norm_mul _ _).symm
  refine ⟨r', hr', min_le_right _ _, fun z hz hne h0 => ?_, fun ρ hρ => ?_⟩
  · have := hest z hz hne
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  · obtain ⟨hρ0, hρr⟩ := hρ
    set γ : ℝ → ℂ := fun t => z₀ + ccwLoop ρ t with hγ
    have hγb : ∀ t, γ t ∈ ball z₀ r' := fun t => by
      rw [mem_ball, dist_eq_norm, hγ, add_sub_cancel_left, c1w_norm_ccwLoop ρ t hρ0.le]
      exact hρr
    have hγne : ∀ t, γ t ≠ z₀ := fun t h => by
      have := c1w_norm_ccwLoop ρ t hρ0.le
      rw [show ccwLoop ρ t = γ t - z₀ by simp [hγ], h, sub_self, norm_zero] at this
      linarith
    have hγR : ∀ t, γ t ∈ ball z₀ R := fun t => ball_subset_ball (min_le_right _ _) (hγb t)
    have hγc : Continuous γ := continuous_const.add (c1w_ccwLoop_continuous ρ)
    have hFγ : (fun t => F (γ t)) = fun t => (((γ t - z₀) ^ m).re : ℂ) * p (γ t) +
        (((γ t - z₀) ^ m).im : ℂ) * q (γ t) := funext fun t => hF _ (hγR t)
    have hFc : Continuous (fun t => F (γ t)) := by
      rw [hFγ]
      have hpc : Continuous (fun t => p (γ t)) := hp.comp_continuous hγc hγR
      have hqc : Continuous (fun t => q (γ t)) := hq.comp_continuous hγc hγR
      have hw : Continuous (fun t => (γ t - z₀) ^ m) := (hγc.sub continuous_const).pow m
      exact ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp hw)).mul hpc).add
        ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp hw)).mul hqc)
    set L : ℝ → ℂ := fun t => A z₀ * ccwLoop ρ t ^ m with hL
    have hLw : HasLoopWind L m := c1w_hasLoopWind_const_mul_pow _ hA0 ρ hρ0 m
    have hL0 : ∀ t, L t ≠ 0 := hLw.2.2.1
    have hLγ : ∀ t, L t = A z₀ * (γ t - z₀) ^ m := fun t => by simp [hL, hγ]
    set Q : ℝ → ℂ := fun t => F (γ t) / L t with hQ
    have hQre : ∀ t, 0 < (Q t).re := by
      intro t
      have he := hest (γ t) (hγb t) (hγne t)
      rw [← hLγ] at he
      have hd : ‖Q t - 1‖ < 1 := by
        rw [hQ, show F (γ t) / L t - 1 = (F (γ t) - L t) / L t by field_simp [hL0 t],
          norm_div, div_lt_one (norm_pos_iff.2 (hL0 t))]
        exact he
      have := Complex.abs_re_le_norm (Q t - 1)
      rw [Complex.sub_re, Complex.one_re] at this
      have := abs_le.1 this
      linarith [this.1]
    have hQw : HasLoopWind Q 0 := by
      refine hasLoopWind_zero_of_forall_ne_ray Q (hFc.div (continuous_const.mul
        ((c1w_ccwLoop_continuous ρ).pow m)) hL0) ?_ (-1) (by norm_num) ?_
      · intro t
        simp only [hQ, hL, hγ, c1w_ccwLoop_periodic ρ t]
      · intro t s hs h
        have := hQre t
        rw [h] at this
        simp at this
        linarith
    have hprod := hasLoopWind_mul hLw hQw
    rw [add_zero] at hprod
    have heq : (fun t => L t * Q t) = fun t => F (z₀ + ccwLoop ρ t) := funext fun t => by
      simp only [hQ]
      field_simp [hL0 t]
      try rfl
    rw [heq] at hprod
    exact hprod

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open N1

/-- On a domain where `u` is `J̃`-holomorphic, the `ξ`-part of the derivative of `w = proj ∘ u` in
any direction `c` is `Re(c) ζ + Im(c) J ζ` with `ζ = π ∂ₛw`; in the global frame this reads
`Re(c) · piDs + Im(c) · q`, with `q` continuous and `Im(conj piDs · q) > 0` where `piDs ≠ 0`. -/
lemma wpb_core (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) :
    ∃ q : ℂ → ℂ, (∀ z ∈ U, ContinuousAt q z) ∧ (∀ z ∈ U, ContinuousAt (piDs H u) z) ∧
      ∀ z ∈ U, (∀ c : ℂ, xiCoordC H (proj H (u z))
          (piXi H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z c)) =
            (c.re : ℂ) * piDs H u z + (c.im : ℂ) * q z) ∧
        (piDs H u z ≠ 0 → 0 < (starRingEnd ℂ (piDs H u z) * q z).im) := by
  set W : ℂ → V 1 := fun z => proj H (u z) with hWdef
  set ζ : ℂ → V 1 := fun z => Pr H (W z) (fderiv ℝ W z 1) with hζdef
  set q : ℂ → ℂ := fun z => xiCoordC H (W z) (J (W z) (ζ z)) with hqdef
  have hWS : ∀ z ∈ U, W z ∈ energySurface H := fun z hz => proj_mem H hH (hu0 z hz)
  have hus : ∀ z ∈ U, ContDiffAt ℝ ∞ u z := fun z hz => hu.contDiffAt (hU.mem_nhds hz)
  have hWs : ∀ z ∈ U, ContDiffAt ℝ ∞ W z := fun z hz =>
    (proj_contDiffAt H hH (hu0 z hz)).comp z (hus z hz)
  have hζc : ∀ z ∈ U, ContinuousAt ζ z := by
    intro z hz
    have h1 : ContDiffAt ℝ ∞ (fun y => Pr H (W y)) z :=
      (Pr_contDiffAt H hH _ (hWS z hz)).comp z (hWs z hz)
    have h2 : ContDiffAt ℝ ∞ (fun y => fderiv ℝ W y 1) z :=
      ((hWs z hz).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    exact (h1.clm_apply h2).continuousAt
  have hdH : ∀ z ∈ U, ∀ d, fderiv ℝ H (W z) (fderiv ℝ W z d) = 0 := by
    intro z hz d
    have hc : (H ∘ W) =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun y hy => hWS y hy
    have h1 : HasFDerivAt (H ∘ W) ((fderiv ℝ H (W z)).comp (fderiv ℝ W z)) z :=
      ((hH.1.differentiable (by simp)) (W z)).hasFDerivAt.comp z
        ((hWs z hz).differentiableAt (by simp)).hasFDerivAt
    have h2 : HasFDerivAt (H ∘ W) (0 : ℂ →L[ℝ] ℝ) z :=
      (hasFDerivAt_const (1 : ℝ) z).congr_of_eventuallyEq hc
    have := congrArg (fun L => L d) (h1.unique h2)
    simpa using this
  have hPr : ∀ z ∈ U, ∀ d, piXi H (W z) (fderiv ℝ W z d) = Pr H (W z) (fderiv ℝ W z d) := by
    intro z hz d
    rw [Pr_apply, hdH z hz d, zero_div, zero_smul, sub_zero]
    rfl
  have hpiDs : ∀ z ∈ U, piDs H u z = xiCoordC H (W z) (ζ z) := by
    intro z hz
    simp only [piDs, ds, hζdef]
    rw [← hPr z hz 1]
  have hpiDsc : ∀ z ∈ U, ContinuousAt (piDs H u) z := by
    intro z hz
    have h1 : ContinuousAt (fun y => xiCoordC H (W y) (ζ y)) z :=
      continuousAt_xiCoordC H hH (hWs z hz).continuousAt (hζc z hz) (hWS z hz)
    refine h1.congr ?_
    filter_upwards [hU.mem_nhds hz] with y hy
    exact (hpiDs y hy).symm
  have hqc : ∀ z ∈ U, ContinuousAt q z := by
    intro z hz
    have hJc : ContinuousAt (fun y => J (W y)) z :=
      hJ.1.continuous.continuousAt.comp (hWs z hz).continuousAt
    exact continuousAt_xiCoordC H hH (hWs z hz).continuousAt (hJc.clm_apply (hζc z hz))
      (hWS z hz)
  refine ⟨q, hqc, hpiDsc, fun z hz => ?_⟩
  obtain ⟨hdu, hd0⟩ := hhol z hz
  obtain ⟨h1, hb⟩ := nx_xi_parts H hH J hJ u z hdu (hu0 z hz) hd0
  set b := Pr H (W z) (fderiv ℝ W z Complex.I) with hbdef
  have hS := hWS z hz
  obtain ⟨hJbxi, hJJb, -, -⟩ := hJ.2 (W z) hS b b hb hb
  have hζb : ζ z = -J (W z) b := h1
  have hJζ : J (W z) (ζ z) = b := by rw [hζb, map_neg, hJJb, neg_neg]
  have hζxi : IsInXi H (W z) (ζ z) := by
    rw [hζb]
    refine ⟨?_, ?_⟩
    · rw [← ka_liouvilleCLM_apply, map_neg, ka_liouvilleCLM_apply, hJbxi.1, neg_zero]
    · rw [map_neg, hJbxi.2, neg_zero]
  refine ⟨fun c => ?_, fun hne => ?_⟩
  · have hc : c = c.re • (1 : ℂ) + c.im • Complex.I := by
      apply Complex.ext <;> simp
    have : fderiv ℝ W z c = c.re • fderiv ℝ W z 1 + c.im • fderiv ℝ W z Complex.I := by
      conv_lhs => rw [hc]
      rw [map_add, map_smul, map_smul]
    change xiCoordC H (W z) (piXi H (W z) (fderiv ℝ W z c)) = _
    rw [hPr z hz c, this, map_add, map_smul, map_smul]
    change xiCoordC H (W z) (c.re • ζ z + c.im • b) = _
    rw [← hJζ, c1x_xiCoordC_add_smul, hpiDs z hz]
  · obtain ⟨hJζxi, -, hpos, -⟩ := hJ.2 (W z) hS (ζ z) (ζ z) hζxi hζxi
    have hζ0 : ζ z ≠ 0 := by
      intro h0
      apply hne
      rw [hpiDs z hz, h0, c1x_xiCoordC_zero]
    rw [hpiDs z hz, hqdef]
    simp only
    rw [im_conj_xiCoordC_mul H hH hS hζxi hJζxi]
    exact hpos hζ0

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open N1

/-- The `s`-derivative of `W ∘ E` at `(s, t)`, by the chain rule along the line `x ↦ (x, t)`. -/
lemma wpc_fderiv_line {W : ℂ → V 1} {E : ℝ × ℝ → ℂ} {s t : ℝ} {d : ℂ}
    (hW : DifferentiableAt ℝ W (E (s, t))) (hE : DifferentiableAt ℝ E (s, t))
    (hd : HasDerivAt (fun x => E (x, t)) d s) :
    fderiv ℝ (fun q => W (E q)) (s, t) (1, 0) = fderiv ℝ W (E (s, t)) d := by
  have hγ : HasDerivAt (fun x : ℝ => ((x, t) : ℝ × ℝ)) (1, 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  have h1 : DifferentiableAt ℝ (fun q => W (E q)) (s, t) := hW.comp (s, t) hE
  have h2 := h1.hasFDerivAt.comp_hasDerivAt s hγ
  have h3 := hW.hasFDerivAt.comp_hasDerivAt s hd
  exact h2.unique h3

lemma wpc_hasDerivAt_cylInf (s t : ℝ) :
    HasDerivAt (fun x => cylInf x t) ((2 * π : ℝ) * cylInf s t) s := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (2 * π * x)) (Real.exp (2 * π * s) * (2 * π * 1)) s :=
    ((hasDerivAt_id s).const_mul (2 * π)).exp
  have h2 := (h1.ofReal_comp).mul_const (Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I))
  have h3 : (fun x => cylInf x t) =
      fun x => ((Real.exp (2 * π * x) : ℝ) : ℂ) * Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) :=
    rfl
  rw [h3]
  refine h2.congr_deriv ?_
  rw [show cylInf s t = ((Real.exp (2 * π * s) : ℝ) : ℂ) *
    Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) from rfl]
  push_cast
  ring

lemma wpc_hasDerivAt_cylEndAt (z₀ : ℂ) (s t : ℝ) :
    HasDerivAt (fun x => cylEndAt z₀ x t) ((-(2 * π) : ℝ) * (cylEndAt z₀ s t - z₀)) s := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(2 * π * x)))
      (Real.exp (-(2 * π * s)) * (-(2 * π * 1))) s :=
    (((hasDerivAt_id s).const_mul (2 * π)).neg).exp
  have h2 := ((h1.ofReal_comp).mul_const
    (Complex.exp (-((2 * π * t : ℝ) : ℂ) * Complex.I))).const_add z₀
  have h3 : (fun x => cylEndAt z₀ x t) = fun x => z₀ +
      ((Real.exp (-(2 * π * x)) : ℝ) : ℂ) * Complex.exp (-((2 * π * t : ℝ) : ℂ) * Complex.I) :=
    rfl
  rw [h3]
  refine h2.congr_deriv ?_
  rw [show cylEndAt z₀ s t = z₀ + ((Real.exp (-(2 * π * s)) : ℝ) : ℂ) *
    Complex.exp (-((2 * π * t : ℝ) : ℂ) * Complex.I) from rfl, add_sub_cancel_left]
  push_cast
  ring

lemma wpc_cylEndAt_neg (z₀ : ℂ) (s t : ℝ) :
    cylEndAt z₀ s (-1 * t) = z₀ + ccwLoop (Real.exp (-(2 * π * s))) t := by
  simp only [cylEndAt, cwLoop, ccwLoop]
  congr 3
  push_cast
  ring

lemma wpc_cylInf_one (s t : ℝ) : cylInf s (1 * t) = ccwLoop (Real.exp (2 * π * s)) t := by
  simp [cylInf]

/-- The loop of `HasWindInfAt` along an end `E` at `(s, t')`, rewritten in the frame form. -/
lemma wpc_loop_eq (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) (q : ℂ → ℂ)
    (hcore : ∀ z ∈ U, ∀ c : ℂ, xiCoordC H (proj H (u z))
          (piXi H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z c)) =
            (c.re : ℂ) * piDs H u z + (c.im : ℂ) * q z)
    (e : ℝ → ℝ → ℂ) (s t' : ℝ) (d : ℂ) (he : DifferentiableAt ℝ (fun q : ℝ × ℝ => e q.1 q.2) (s, t'))
    (hd : HasDerivAt (fun x => e x t') d s) (hU' : e s t' ∈ U) :
    xiCoordC H (endW H u e (s, t'))
        (piXi H (endW H u e (s, t')) (fderiv ℝ (endW H u e) (s, t') (1, 0))) =
      (d.re : ℂ) * piDs H u (e s t') + (d.im : ℂ) * q (e s t') := by
  have hW : DifferentiableAt ℝ (fun z => proj H (u z)) (e s t') :=
    ((proj_contDiffAt H hH (hu0 _ hU')).comp _ (hu.contDiffAt (hU.mem_nhds hU'))).differentiableAt
      (by simp)
  have hf := wpc_fderiv_line (W := fun z => proj H (u z)) (E := fun q : ℝ × ℝ => e q.1 q.2) hW he hd
  have hend : endW H u e = fun q : ℝ × ℝ => proj H (u (e q.1 q.2)) := rfl
  rw [hend]
  simp only at hf ⊢
  rw [hf]
  exact hcore _ hU' d

theorem hasWindInfAt_cylInf_of_hasLoopWind_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (R : ℝ)
    (hRU : ∀ z : ℂ, R < ‖z‖ → z ∈ U) (k : ℤ)
    (hk : ∀ ρ > R, HasLoopWind (fun t => piDs H u (ccwLoop ρ t)) k) :
    HasWindInfAt H u cylInf 1 (k + 1) := by
  obtain ⟨q, hqc, -, hcore⟩ := wpb_core H hH J hJ U hU u hu hu0 hhol
  have hpi := Real.pi_pos
  refine ⟨Real.log (|R| + 1) / (2 * π), fun s hs => ?_⟩
  set ρ := Real.exp (2 * π * s) with hρ
  have hρR : R < ρ := by
    have h1 : Real.log (|R| + 1) ≤ 2 * π * s := by
      rw [ge_iff_le, div_le_iff₀ (by positivity)] at hs; linarith
    have h2 : |R| + 1 ≤ ρ := by
      rw [hρ, ← Real.exp_log (by positivity : (0 : ℝ) < |R| + 1)]
      exact Real.exp_le_exp.2 h1
    linarith [le_abs_self R]
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hmem : ∀ t, ccwLoop ρ t ∈ U := fun t =>
    hRU _ (by rw [c1w_norm_ccwLoop ρ t hρ0.le]; exact hρR)
  have heq : (fun t => xiCoordC H (endW H u cylInf (s, 1 * t))
      (piXi H (endW H u cylInf (s, 1 * t)) (fderiv ℝ (endW H u cylInf) (s, 1 * t) (1, 0)))) =
      fun t => ((((2 * π : ℝ) : ℂ) * ccwLoop ρ t).re : ℂ) * piDs H u (ccwLoop ρ t) +
        ((((2 * π : ℝ) : ℂ) * ccwLoop ρ t).im : ℂ) * q (ccwLoop ρ t) := by
    funext t
    have h := wpc_loop_eq H hH U hU u hu hu0 q (fun z hz => (hcore z hz).1) cylInf s (1 * t)
      _ (by unfold cylInf ccwLoop; fun_prop) (wpc_hasDerivAt_cylInf s (1 * t))
      (by rw [wpc_cylInf_one]; exact hmem t)
    rw [h, wpc_cylInf_one]
  rw [heq]
  have hc : HasLoopWind (fun t => ((2 * π : ℝ) : ℂ) * ccwLoop ρ t) 1 := by
    have := c1w_hasLoopWind_const_mul_pow ((2 * π : ℝ) : ℂ) (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)) ρ hρ0 1
    simpa using this
  have hp := hk ρ hρR
  have hqcont : Continuous (fun t => q (ccwLoop ρ t)) :=
    continuous_iff_continuousAt.2 fun t =>
      (hqc _ (hmem t)).comp (c1w_ccwLoop_continuous ρ).continuousAt
  have hw := hasLoopWind_re_mul_add_im_mul hc hp hqcont
    (fun t => by simp only [c1w_ccwLoop_periodic ρ t])
    (fun t => (hcore _ (hmem t)).2 (hp.2.2.1 t))
  rw [add_comm] at hw
  exact hw

theorem hasWindInfAt_cylEndAt_of_hasLoopWind_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (z₀ : ℂ) (r : ℝ) (hr : 0 < r)
    (hrU : ball z₀ r \ {z₀} ⊆ U) (k : ℤ)
    (hk : ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => piDs H u (z₀ + ccwLoop ρ t)) k) :
    HasWindInfAt H u (cylEndAt z₀) (-1) (k + 1) := by
  obtain ⟨q, hqc, -, hcore⟩ := wpb_core H hH J hJ U hU u hu hu0 hhol
  have hpi := Real.pi_pos
  refine ⟨-Real.log (r / 2) / (2 * π), fun s hs => ?_⟩
  set ρ := Real.exp (-(2 * π * s)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρr : ρ < r := by
    have h1 : -(2 * π * s) ≤ Real.log (r / 2) := by
      rw [ge_iff_le, div_le_iff₀ (by positivity)] at hs; linarith
    have h2 : ρ ≤ r / 2 := by
      rw [hρ, ← Real.exp_log (by positivity : (0 : ℝ) < r / 2)]
      exact Real.exp_le_exp.2 h1
    linarith
  have hmem : ∀ t, z₀ + ccwLoop ρ t ∈ U := fun t => hrU ⟨by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, c1w_norm_ccwLoop ρ t hρ0.le]; exact hρr,
    fun h => by
      have := c1w_norm_ccwLoop ρ t hρ0.le
      rw [Set.mem_singleton_iff, add_eq_left] at h
      rw [h, norm_zero] at this; linarith⟩
  have heq : (fun t => xiCoordC H (endW H u (cylEndAt z₀) (s, -1 * t))
      (piXi H (endW H u (cylEndAt z₀) (s, -1 * t))
        (fderiv ℝ (endW H u (cylEndAt z₀)) (s, -1 * t) (1, 0)))) =
      fun t => ((((-(2 * π) : ℝ) : ℂ) * ccwLoop ρ t).re : ℂ) * piDs H u (z₀ + ccwLoop ρ t) +
        ((((-(2 * π) : ℝ) : ℂ) * ccwLoop ρ t).im : ℂ) * q (z₀ + ccwLoop ρ t) := by
    funext t
    have h := wpc_loop_eq H hH U hU u hu hu0 q (fun z hz => (hcore z hz).1) (cylEndAt z₀) s
      (-1 * t) _ (by unfold cylEndAt cwLoop; fun_prop) (wpc_hasDerivAt_cylEndAt z₀ s (-1 * t))
      (by rw [wpc_cylEndAt_neg]; exact hmem t)
    rw [h, wpc_cylEndAt_neg, add_sub_cancel_left]
  rw [heq]
  have hc : HasLoopWind (fun t => ((-(2 * π) : ℝ) : ℂ) * ccwLoop ρ t) 1 := by
    have := c1w_hasLoopWind_const_mul_pow ((-(2 * π) : ℝ) : ℂ)
      (by exact_mod_cast (by linarith : (-(2 * π) : ℝ) ≠ 0)) ρ hρ0 1
    simpa using this
  have hp := hk ρ ⟨hρ0, hρr⟩
  have hqcont : Continuous (fun t => q (z₀ + ccwLoop ρ t)) :=
    continuous_iff_continuousAt.2 fun t =>
      ContinuousAt.comp (g := q) (f := fun t => z₀ + ccwLoop ρ t) (hqc _ (hmem t))
        ((continuous_const.add (c1w_ccwLoop_continuous ρ)).continuousAt)
  have hw := hasLoopWind_re_mul_add_im_mul hc hp hqcont
    (fun t => by simp only [c1w_ccwLoop_periodic ρ t])
    (fun t => (hcore _ (hmem t)).2 (hp.2.2.1 t))
  rw [add_comm] at hw
  exact hw

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (R : ℝ)
    (hRU : ∀ z : ℂ, R < ‖z‖ → z ∈ U) (k : ℤ)
    (hk : ∀ ρ > R, HasLoopWind (fun t => piDs H u (ccwLoop ρ t)) k) :
    HasWindInfAt H u cylInf 1 (k + 1) :=
  hasWindInfAt_cylInf_of_hasLoopWind_aux H hH J hJ U hU u hu hu0 hhol R hRU k hk
