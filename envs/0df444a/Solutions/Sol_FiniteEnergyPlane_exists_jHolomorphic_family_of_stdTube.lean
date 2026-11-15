-- Prove2me | solution 1 for FiniteEnergyPlane.exists_jHolomorphic_family_of_stdTube
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T18:41:53.848126+00:00
-- url     : https://prove2.me/submissions/ebee725e-6e3d-4b63-9fdf-d1b9f044ebff

import Definitions.Def_FiniteEnergyPlane_Tube
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_of_aCoord_proj_sub_le
import Theorems.Thm_FiniteEnergyPlane_exists_cylindrical_bounds_of_expDecayCInftyTube
import Theorems.Thm_FiniteEnergyPlane_infDist_proj_le_of_isFastPlane

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

open Metric Filter Topology
open scoped ContDiff Real

/-- Away from `0`, the symplectization coordinates `aCoord H` and `proj H` are smooth. -/
theorem contDiffAt_aCoord_proj_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) : ContDiffAt ℝ ∞ (aCoord H) y ∧ ContDiffAt ℝ ∞ (proj H) y := by
  have hr := (ka_scale_spec H hH y hy).1
  have hd : ContDiffAt ℝ ∞ (scaleToS H) y := ka_scale_contDiffAt H hH y hy
  constructor
  · have : aCoord H = fun y => (-1 / 2 : ℝ) * Real.log (scaleToS H y) := by
      funext y; unfold aCoord; ring
    rw [this]
    exact contDiffAt_const.mul (hd.log hr.ne')
  · have : proj H = fun y => scaleToS H y • y := rfl
    rw [this]
    exact hd.smul contDiffAt_id

theorem emb_exp_aCoord_smul_proj {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) : Real.exp (2 * aCoord H y) • proj H y = y := by
  have hr := (ka_scale_spec H hH y hy).1
  have e : Real.exp (2 * aCoord H y) = (scaleToS H y)⁻¹ := by
    unfold aCoord
    rw [show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring,
      Real.exp_neg, Real.exp_log hr]
  rw [e]
  unfold proj
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- If `u : E → V n` is differentiable at `z`, `u z ≠ 0`, then the derivative of `u` at `z` is
injective if and only if the derivative at `z` of the symplectization coordinates
`w ↦ (aCoord H (u w), proj H (u w))` is. -/
theorem injective_fderiv_aCoord_proj_comp_iff_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (u : E → V n) (z : E)
    (hu : DifferentiableAt ℝ u z) (h0 : u z ≠ 0) :
    Function.Injective (fderiv ℝ (fun w => (aCoord H (u w), proj H (u w))) z) ↔
      Function.Injective (fderiv ℝ u z) := by
  obtain ⟨ha, hp⟩ := contDiffAt_aCoord_proj_aux H hH (u z) h0
  have hda : DifferentiableAt ℝ (aCoord H) (u z) := ha.differentiableAt (by simp)
  have hdp : DifferentiableAt ℝ (proj H) (u z) := hp.differentiableAt (by simp)
  have hA : HasFDerivAt (fun w => aCoord H (u w)) ((fderiv ℝ (aCoord H) (u z)).comp (fderiv ℝ u z)) z :=
    hda.hasFDerivAt.comp z hu.hasFDerivAt
  have hB : HasFDerivAt (fun w => proj H (u w)) ((fderiv ℝ (proj H) (u z)).comp (fderiv ℝ u z)) z :=
    hdp.hasFDerivAt.comp z hu.hasFDerivAt
  have hG := hA.prodMk hB
  rw [hG.fderiv]
  -- the formula expressing `u` through its coordinates
  have hev : (fun w => Real.exp (2 * aCoord H (u w)) • proj H (u w)) =ᶠ[𝓝 z] u := by
    filter_upwards [hu.continuousAt.eventually_ne h0] with w hw
    exact emb_exp_aCoord_smul_proj H hH (u w) hw
  have hexp := (hA.const_mul 2).exp
  have hsm := (hexp.smul hB).congr_of_eventuallyEq hev.symm
  have hdu := hsm.unique hu.hasFDerivAt
  constructor
  · intro hinj
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply (injective_iff_map_eq_zero _).1 hinj
    simp [hv]
  · intro hinj
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply (injective_iff_map_eq_zero _).1 hinj
    have hv1 : ((fderiv ℝ (aCoord H) (u z)).comp (fderiv ℝ u z)) v = 0 := congrArg Prod.fst hv
    have hv2 : ((fderiv ℝ (proj H) (u z)).comp (fderiv ℝ u z)) v = 0 := congrArg Prod.snd hv
    rw [← hdu]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply']
    simp [hv1, hv2]

end FiniteEnergyPlane

/-!
# X transfer: cylindrical `C²` bounds of a map on `ℂ × ℂ` and their consequences

`CylBound F ρ' C`: on `ℂ × closedBall 0 ρ'`, the first two derivatives of `F` are bounded by `C`
in the cylindrical scale (base directions weighted by `1 / (1 + ‖ζ‖)`).
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cylindrical `C²` bound. -/
def CylBound (F : ℂ × ℂ → E) (ρ' C : ℝ) : Prop :=
  ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' →
    (∀ h : ℂ × ℂ, ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) ∧
    ∀ h k : ℂ × ℂ, ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
      C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖)

lemma CylBound.nonneg {F : ℂ × ℂ → E} {ρ' C : ℝ} (hρ' : 0 ≤ ρ') (hC : CylBound F ρ' C) :
    0 ≤ C := by
  have h := (hC 0 0 (by simpa using hρ')).1 (0, 1)
  simp only [norm_zero, zero_div, zero_add, norm_one, mul_one] at h
  exact le_trans (norm_nonneg _) h

/-- Mean value estimate along a segment, centred at `ζ₀`. -/
lemma seg_core {Ψ : ℂ × ℂ → E} {ρ' B : ℝ} {ζ₀ ζ₁ w₀ w₁ : ℂ}
    (hw₀ : w₀ ∈ closedBall (0 : ℂ) ρ') (hw₁ : w₁ ∈ closedBall (0 : ℂ) ρ')
    (hζ : ‖ζ₁ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2)
    (hd : ∀ ζ w, w ∈ closedBall (0 : ℂ) ρ' → DifferentiableAt ℝ Ψ (ζ, w))
    (hb : ∀ ζ w (h : ℂ × ℂ), w ∈ closedBall (0 : ℂ) ρ' → ‖ζ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2 →
      ‖fderiv ℝ Ψ (ζ, w) h‖ ≤ B * (2 * ‖h.1‖ / (1 + ‖ζ₀‖) + ‖h.2‖)) :
    ‖Ψ (ζ₁, w₁) - Ψ (ζ₀, w₀)‖ ≤ B * (2 * ‖ζ₁ - ζ₀‖ / (1 + ‖ζ₀‖) + ‖w₁ - w₀‖) := by
  set Δ : ℂ × ℂ := (ζ₁ - ζ₀, w₁ - w₀) with hΔ
  set γ : ℝ → ℂ × ℂ := fun θ => (ζ₀, w₀) + θ • Δ with hγ
  have hγd : ∀ θ : ℝ, HasDerivAt γ Δ θ := fun θ => by
    have h0 : HasDerivAt (fun x : ℝ => x • Δ) ((1 : ℝ) • Δ) θ := (hasDerivAt_id θ).smul_const Δ
    rw [one_smul] at h0
    exact h0.const_add (ζ₀, w₀)
  have hmem : ∀ θ ∈ Set.Icc (0 : ℝ) 1, (γ θ).2 ∈ closedBall (0 : ℂ) ρ' ∧
      ‖(γ θ).1 - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2 := by
    intro θ hθ
    constructor
    · have := (convex_closedBall (0 : ℂ) ρ').add_smul_sub_mem hw₀ hw₁ hθ
      simpa [hγ, hΔ] using this
    · have e : (γ θ).1 - ζ₀ = θ • (ζ₁ - ζ₀) := by simp [hγ, hΔ]
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      calc θ * ‖ζ₁ - ζ₀‖ ≤ 1 * ‖ζ₁ - ζ₀‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
        _ ≤ (1 + ‖ζ₀‖) / 2 := by rw [one_mul]; exact hζ
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun θ => Ψ (γ θ))
    (f' := fun θ => fderiv ℝ Ψ (γ θ) Δ)
    (C := B * (2 * ‖ζ₁ - ζ₀‖ / (1 + ‖ζ₀‖) + ‖w₁ - w₀‖))
    (fun θ hθ => by
      have hdθ : DifferentiableAt ℝ Ψ (γ θ) := hd (γ θ).1 (γ θ).2 (hmem θ hθ).1
      exact (hdθ.hasFDerivAt.comp_hasDerivAt θ (hγd θ)).hasDerivWithinAt)
    (fun θ hθ => by
      have hθ' : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hθ.1, hθ.2.le⟩
      exact hb (γ θ).1 (γ θ).2 Δ (hmem θ hθ').1 (hmem θ hθ').2)
  have e1 : γ 1 = (ζ₁, w₁) := by simp [hγ, hΔ]
  have e0 : γ 0 = (ζ₀, w₀) := by simp [hγ]
  simpa [e1, e0] using key

lemma differentiableAt_of_mem {F : ℂ × ℂ → E} {ρ ρ' : ℝ} (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) {ζ w : ℂ}
    (hw : w ∈ closedBall (0 : ℂ) ρ') :
    ContDiffAt ℝ ∞ F (ζ, w) := by
  have hopen : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) := isOpen_univ.prod isOpen_ball
  have hin : (ζ, w) ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) :=
    ⟨Set.mem_univ _, lt_of_le_of_lt (mem_closedBall.1 hw) hρ⟩
  exact hF.contDiffAt (hopen.mem_nhds hin)

lemma weight_le {ζ ζ₀ : ℂ} (h : ‖ζ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2) (a : ℝ) (ha : 0 ≤ a) :
    a / (1 + ‖ζ‖) ≤ 2 * a / (1 + ‖ζ₀‖) := by
  have h1 : ‖ζ₀‖ ≤ ‖ζ‖ + ‖ζ - ζ₀‖ := by
    have := norm_sub_norm_le ζ₀ ζ
    rw [norm_sub_rev] at this
    linarith
  have h2 : (1 + ‖ζ₀‖) / 2 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ, norm_nonneg ζ₀]
  have hp : 0 < 1 + ‖ζ₀‖ := by linarith [norm_nonneg ζ₀]
  have hq : 0 < 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  rw [div_le_div_iff₀ hq hp]
  nlinarith

lemma CylBound.seg {F : ℂ × ℂ → E} {ρ ρ' C : ℝ} (hρ' : 0 ≤ ρ') (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (hC : CylBound F ρ' C)
    {ζ₀ ζ₁ w₀ w₁ : ℂ} (hw₀ : w₀ ∈ closedBall (0 : ℂ) ρ') (hw₁ : w₁ ∈ closedBall (0 : ℂ) ρ')
    (hζ : ‖ζ₁ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2) :
    ‖F (ζ₁, w₁) - F (ζ₀, w₀)‖ ≤ C * (2 * ‖ζ₁ - ζ₀‖ / (1 + ‖ζ₀‖) + ‖w₁ - w₀‖) := by
  have hC0 := hC.nonneg hρ'
  refine seg_core hw₀ hw₁ hζ
    (fun ζ w hw => (differentiableAt_of_mem hρ hF hw).differentiableAt (by simp)) ?_
  intro ζ w h hw hζ'
  refine le_trans ((hC ζ w hw).1 h) (mul_le_mul_of_nonneg_left ?_ hC0)
  have := weight_le hζ' ‖h.1‖ (norm_nonneg _)
  linarith

lemma CylBound.seg_fderiv {F : ℂ × ℂ → E} {ρ ρ' C : ℝ} (hρ' : 0 ≤ ρ') (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (hC : CylBound F ρ' C)
    {ζ₀ ζ₁ w₀ w₁ : ℂ} (hw₀ : w₀ ∈ closedBall (0 : ℂ) ρ') (hw₁ : w₁ ∈ closedBall (0 : ℂ) ρ')
    (hζ : ‖ζ₁ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2) (k : ℂ × ℂ) :
    ‖fderiv ℝ F (ζ₁, w₁) k - fderiv ℝ F (ζ₀, w₀) k‖ ≤
      C * (2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖) * (2 * ‖ζ₁ - ζ₀‖ / (1 + ‖ζ₀‖) + ‖w₁ - w₀‖) := by
  have hC0 := hC.nonneg hρ'
  have hp : 0 < 1 + ‖ζ₀‖ := by linarith [norm_nonneg ζ₀]
  have hdd : ∀ ζ w, w ∈ closedBall (0 : ℂ) ρ' → DifferentiableAt ℝ (fderiv ℝ F) (ζ, w) := by
    intro ζ w hw
    have h1 : ContDiffAt ℝ ∞ (fderiv ℝ F) (ζ, w) :=
      (differentiableAt_of_mem hρ hF hw).fderiv_right (m := ∞) (by simp)
    exact h1.differentiableAt (by simp)
  refine seg_core (Ψ := fun p => fderiv ℝ F p k) hw₀ hw₁ hζ
    (fun ζ w hw => (hdd ζ w hw).clm_apply (differentiableAt_const k)) ?_
  intro ζ w h hw hζ'
  have e : fderiv ℝ (fun p => fderiv ℝ F p k) (ζ, w) h = fderiv ℝ (fderiv ℝ F) (ζ, w) h k := by
    rw [fderiv_clm_apply (hdd ζ w hw) (differentiableAt_const k)]
    simp
  rw [e]
  refine le_trans ((hC ζ w hw).2 h k) ?_
  have a1 := weight_le hζ' ‖h.1‖ (norm_nonneg _)
  have a2 := weight_le hζ' ‖k.1‖ (norm_nonneg _)
  have n1 : 0 ≤ ‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖ := by positivity
  have n2 : 0 ≤ 2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖ := by positivity
  calc C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖)
      ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0 n1); linarith
    _ ≤ C * (2 * ‖h.1‖ / (1 + ‖ζ₀‖) + ‖h.2‖) * (2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖) := by
        apply mul_le_mul_of_nonneg_right _ n2
        apply mul_le_mul_of_nonneg_left _ hC0; linarith
    _ = C * (2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖) * (2 * ‖h.1‖ / (1 + ‖ζ₀‖) + ‖h.2‖) := by ring

/-- Closeness of `F ∘ (ψ, v)` to `F(·, 0)` in cylindrical `C¹` scale, pointwise at `z`. -/
lemma CylBound.close {F : ℂ × ℂ → E} {ρ ρ' C : ℝ} (hρ' : 0 ≤ ρ') (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (hC : CylBound F ρ' C)
    {ψ v : ℂ → ℂ} {z : ℂ} (hψ : DifferentiableAt ℝ ψ z) (hv : DifferentiableAt ℝ v z)
    {ε : ℝ} (hε1 : ε ≤ 1 / 2) (hερ : ε ≤ ρ')
    (h1 : ‖ψ z - z‖ ≤ ε * (1 + ‖z‖)) (h2 : ‖v z‖ ≤ ε)
    (h3 : ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε)
    (h4 : (1 + ‖z‖) * ‖fderiv ℝ v z‖ ≤ ε) :
    ‖F (ψ z, v z) - F (z, 0)‖ ≤ 3 * C * ε ∧
      (1 + ‖z‖) * ‖fderiv ℝ (fun x => F (ψ x, v x)) z - fderiv ℝ (fun x => F (x, 0)) z‖ ≤
        9 * C * ε := by
  have hC0 := hC.nonneg hρ'
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) h2
  have hp : 0 < 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hw0 : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ' := by simpa using hρ'
  have hw1 : v z ∈ closedBall (0 : ℂ) ρ' := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hζ : ‖ψ z - z‖ ≤ (1 + ‖z‖) / 2 := by nlinarith
  have hq : 2 * ‖ψ z - z‖ / (1 + ‖z‖) ≤ 2 * ε := by
    rw [div_le_iff₀ hp]; nlinarith
  have hseg : 2 * ‖ψ z - z‖ / (1 + ‖z‖) + ‖v z - 0‖ ≤ 3 * ε := by
    rw [sub_zero]; linarith
  constructor
  · refine le_trans (hC.seg hρ' hρ hF hw0 hw1 hζ) ?_
    calc C * (2 * ‖ψ z - z‖ / (1 + ‖z‖) + ‖v z - 0‖) ≤ C * (3 * ε) :=
          mul_le_mul_of_nonneg_left hseg hC0
      _ = 3 * C * ε := by ring
  · have hFd : DifferentiableAt ℝ F (ψ z, v z) :=
      (differentiableAt_of_mem hρ hF hw1).differentiableAt (by simp)
    have hFd0 : DifferentiableAt ℝ F (z, 0) :=
      (differentiableAt_of_mem hρ hF hw0).differentiableAt (by simp)
    have hA : HasFDerivAt (fun x => F (ψ x, v x))
        ((fderiv ℝ F (ψ z, v z)).comp ((fderiv ℝ ψ z).prod (fderiv ℝ v z))) z :=
      hFd.hasFDerivAt.comp z (hψ.hasFDerivAt.prodMk hv.hasFDerivAt)
    have hB : HasFDerivAt (fun x : ℂ => F (x, 0))
        ((fderiv ℝ F (z, 0)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ))) z :=
      hFd0.hasFDerivAt.comp z ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (0 : ℂ) z))
    rw [hA.fderiv, hB.fderiv]
    have hop : ‖(fderiv ℝ F (ψ z, v z)).comp ((fderiv ℝ ψ z).prod (fderiv ℝ v z)) -
        (fderiv ℝ F (z, 0)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ))‖ ≤
        9 * C * ε / (1 + ‖z‖) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
      intro h
      have hsplit : ((fderiv ℝ F (ψ z, v z)).comp ((fderiv ℝ ψ z).prod (fderiv ℝ v z)) -
          (fderiv ℝ F (z, 0)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ))) h =
          fderiv ℝ F (ψ z, v z) (fderiv ℝ ψ z h - h, fderiv ℝ v z h) +
            (fderiv ℝ F (ψ z, v z) (h, 0) - fderiv ℝ F (z, 0) (h, 0)) := by
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.zero_apply]
        have : (fderiv ℝ ψ z h, fderiv ℝ v z h) =
            (fderiv ℝ ψ z h - h, fderiv ℝ v z h) + (h, (0 : ℂ)) := by simp
        rw [this, map_add]
        abel
      rw [hsplit]
      have t1 : ‖fderiv ℝ F (ψ z, v z) (fderiv ℝ ψ z h - h, fderiv ℝ v z h)‖ ≤
          C * (3 * ε * ‖h‖ / (1 + ‖z‖)) := by
        refine le_trans ((hC (ψ z) (v z) hw1).1 _) (mul_le_mul_of_nonneg_left ?_ hC0)
        have a1 : ‖fderiv ℝ ψ z h - h‖ ≤ ε * ‖h‖ := by
          have := (fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ).le_opNorm h
          simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at this
          exact le_trans this (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
        have a2 : ‖fderiv ℝ v z h‖ ≤ ε * ‖h‖ / (1 + ‖z‖) := by
          rw [le_div_iff₀ hp]
          have := (fderiv ℝ v z).le_opNorm h
          calc ‖fderiv ℝ v z h‖ * (1 + ‖z‖) ≤ ‖fderiv ℝ v z‖ * ‖h‖ * (1 + ‖z‖) :=
                mul_le_mul_of_nonneg_right this hp.le
            _ = (1 + ‖z‖) * ‖fderiv ℝ v z‖ * ‖h‖ := by ring
            _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
        have a3 := weight_le (ζ := ψ z) (ζ₀ := z) hζ ‖fderiv ℝ ψ z h - h‖ (norm_nonneg _)
        have a4 : 2 * ‖fderiv ℝ ψ z h - h‖ / (1 + ‖z‖) ≤ 2 * (ε * ‖h‖) / (1 + ‖z‖) := by
          apply div_le_div_of_nonneg_right _ hp.le; linarith
        have e : 3 * ε * ‖h‖ / (1 + ‖z‖) = 2 * (ε * ‖h‖) / (1 + ‖z‖) + ε * ‖h‖ / (1 + ‖z‖) := by
          ring
        simp only
        rw [e]
        linarith
      have t2 := hC.seg_fderiv hρ' hρ hF hw0 hw1 hζ (h, (0 : ℂ))
      simp only [norm_zero, add_zero] at t2
      have t2' : ‖fderiv ℝ F (ψ z, v z) (h, 0) - fderiv ℝ F (z, 0) (h, 0)‖ ≤
          C * (2 * ‖h‖ / (1 + ‖z‖)) * (3 * ε) :=
        le_trans t2 (mul_le_mul_of_nonneg_left hseg (by positivity))
      calc ‖fderiv ℝ F (ψ z, v z) (fderiv ℝ ψ z h - h, fderiv ℝ v z h) +
            (fderiv ℝ F (ψ z, v z) (h, 0) - fderiv ℝ F (z, 0) (h, 0))‖
          ≤ C * (3 * ε * ‖h‖ / (1 + ‖z‖)) + C * (2 * ‖h‖ / (1 + ‖z‖)) * (3 * ε) :=
            le_trans (norm_add_le _ _) (add_le_add t1 t2')
        _ = 9 * C * ε / (1 + ‖z‖) * ‖h‖ := by ring
    calc (1 + ‖z‖) * ‖_‖ ≤ (1 + ‖z‖) * (9 * C * ε / (1 + ‖z‖)) :=
          mul_le_mul_of_nonneg_left hop hp.le
      _ = 9 * C * ε := by field_simp

end XT

end FiniteEnergyPlane

/-!
# X transfer: clause lemmas for `z ↦ Φ (ψ z, v z)` from cylindrical bounds of
`aCoord H ∘ Φ` and `proj H ∘ Φ`.
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The far region: where the weighted bounds on `(ψ, v)` put the segment from `(z, 0)` to
`(ψ z, v z)` inside the domain of the cylindrical bounds. -/
lemma far {ρ' : ℝ} (C₁ β C₂ δ' : ℝ) (hρ' : 0 < ρ') (hβ : 0 < β) (hδ' : δ' < 0) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R ≤ x →
      C₁ * (1 + x) ^ (-β) ≤ 1 / 2 ∧ C₂ * (1 + x) ^ δ' ≤ ρ' := by
  have h1 : Tendsto (fun x : ℝ => C₁ * x ^ (-β)) atTop (𝓝 (C₁ * 0)) :=
    (tendsto_rpow_neg_atTop hβ).const_mul C₁
  have h2 : Tendsto (fun x : ℝ => C₂ * x ^ (-(-δ'))) atTop (𝓝 (C₂ * 0)) :=
    (tendsto_rpow_neg_atTop (neg_pos.2 hδ')).const_mul C₂
  rw [mul_zero] at h1 h2
  simp only [neg_neg] at h2
  have ev := (h1.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
    (h2.eventually (eventually_le_nhds hρ'))
  obtain ⟨a, ha⟩ := eventually_atTop.1 ev
  refine ⟨max a 0, le_max_right _ _, fun x hx => ?_⟩
  exact ha (1 + x) (by linarith [le_max_left a 0])

lemma far_pt {ρ' C₁ β C₂ δ' : ℝ} (hβ : 0 < β) (hδ' : δ' < 0) {ψz vz z : ℂ}
    (f1 : C₁ * (1 + ‖z‖) ^ (-β) ≤ 1 / 2) (f2 : C₂ * (1 + ‖z‖) ^ δ' ≤ ρ')
    (hψ : ‖ψz - z‖ ≤ C₁ * (1 + ‖z‖) ^ (1 - β)) (hv : ‖vz‖ ≤ C₂ * (1 + ‖z‖) ^ δ') :
    vz ∈ closedBall (0 : ℂ) ρ' ∧ ‖ψz - z‖ ≤ (1 + ‖z‖) / 2 ∧
      2 * ‖ψz - z‖ / (1 + ‖z‖) + ‖vz - 0‖ ≤
        (2 * |C₁| + |C₂|) * (1 + ‖z‖) ^ (-(min β (-δ'))) := by
  have hx : 0 < 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hx1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have e : (1 + ‖z‖) ^ (1 - β) = (1 + ‖z‖) * (1 + ‖z‖) ^ (-β) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [e] at hψ
  have k1 : (1 + ‖z‖) ^ (-β) ≤ (1 + ‖z‖) ^ (-(min β (-δ'))) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg (min_le_left _ _))
  have k2 : (1 + ‖z‖) ^ δ' ≤ (1 + ‖z‖) ^ (-(min β (-δ'))) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [min_le_right β (-δ')])
  have p1 : 0 ≤ (1 + ‖z‖) ^ (-β) := by positivity
  have p2 : 0 ≤ (1 + ‖z‖) ^ δ' := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right]; linarith
  · nlinarith
  · rw [sub_zero]
    have q1 : 2 * ‖ψz - z‖ / (1 + ‖z‖) ≤ 2 * (C₁ * (1 + ‖z‖) ^ (-β)) := by
      rw [div_le_iff₀ hx]; nlinarith
    have q2 : C₁ * (1 + ‖z‖) ^ (-β) ≤ |C₁| * (1 + ‖z‖) ^ (-(min β (-δ'))) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C₁) p1).trans
        (mul_le_mul_of_nonneg_left k1 (abs_nonneg _))
    have q3 : C₂ * (1 + ‖z‖) ^ δ' ≤ |C₂| * (1 + ‖z‖) ^ (-(min β (-δ'))) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C₂) p2).trans
        (mul_le_mul_of_nonneg_left k2 (abs_nonneg _))
    nlinarith

section tube

variable {H : V 1 → ℝ} {Φ : ℂ × ℂ → V 1} {ρ ρ' : ℝ}

lemma contDiffOn_coords (hH : IsStrictlyStarShapedLevel H) (hΦ : ContDiff ℝ ∞ Φ)
    (hΦ0 : ∀ p ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)), Φ p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => aCoord H (Φ p)) (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      ContDiffOn ℝ ∞ (fun p => proj H (Φ p)) (Set.univ ×ˢ ball (0 : ℂ) ρ) := by
  constructor
  · intro p hp
    exact (((contDiffAt_aCoord_proj_aux H hH (Φ p) (hΦ0 p hp)).1).comp p
      hΦ.contDiffAt).contDiffWithinAt
  · intro p hp
    exact (((contDiffAt_aCoord_proj_aux H hH (Φ p) (hΦ0 p hp)).2).comp p
      hΦ.contDiffAt).contDiffWithinAt

lemma member_end (hρ' : 0 < ρ') (hρ : ρ' < ρ) {Ca Cp : ℝ}
    (hFa : ContDiffOn ℝ ∞ (fun p => aCoord H (Φ p)) (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hFp : ContDiffOn ℝ ∞ (fun p => proj H (Φ p)) (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hCa : CylBound (fun p => aCoord H (Φ p)) ρ' Ca)
    (hCp : CylBound (fun p => proj H (Φ p)) ρ' Cp)
    {P : ReebOrbit H} {u : ℂ → V 1} (hΦu : ∀ z, Φ (z, 0) = u z)
    (huP : IsNondegenerateEnd H u cylInf P 1) {ψ v : ℂ → ℂ} {C₁ β C₂ δ' : ℝ}
    (hβ : 0 < β) (hδ' : δ' < 0)
    (hψ : ∀ z, ‖ψ z - z‖ ≤ C₁ * (1 + ‖z‖) ^ (1 - β))
    (hv : ∀ z, ‖v z‖ ≤ C₂ * (1 + ‖z‖) ^ δ') :
    IsNondegenerateEnd H (fun z => Φ (ψ z, v z)) cylInf P 1 := by
  obtain ⟨R, -, hR⟩ := far (ρ' := ρ') C₁ β C₂ δ' hρ' hβ hδ'
  have hCa0 := hCa.nonneg hρ'.le
  have hCp0 := hCp.nonneg hρ'.le
  have hw0 : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ' := by simpa using hρ'.le
  refine isNondegenerateEnd_of_aCoord_proj_sub_le H P u _ huP R
    ((Ca + Cp) * (2 * |C₁| + |C₂|)) (min β (-δ')) (lt_min hβ (neg_pos.2 hδ')) ?_
  intro z hz
  obtain ⟨f1, f2⟩ := hR ‖z‖ hz
  obtain ⟨g1, g2, g3⟩ := far_pt hβ hδ' f1 f2 (hψ z) (hv z)
  have pp : 0 ≤ (2 * |C₁| + |C₂|) * (1 + ‖z‖) ^ (-(min β (-δ'))) := by positivity
  rw [← hΦu z]
  constructor
  · have := hCa.seg hρ'.le hρ hFa hw0 g1 g2
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    calc Ca * (2 * ‖ψ z - z‖ / (1 + ‖z‖) + ‖v z - 0‖)
        ≤ Ca * ((2 * |C₁| + |C₂|) * (1 + ‖z‖) ^ (-(min β (-δ')))) :=
          mul_le_mul_of_nonneg_left g3 hCa0
      _ ≤ (Ca + Cp) * (2 * |C₁| + |C₂|) * (1 + ‖z‖) ^ (-(min β (-δ'))) := by nlinarith
  · have := hCp.seg hρ'.le hρ hFp hw0 g1 g2
    refine this.trans ?_
    calc Cp * (2 * ‖ψ z - z‖ / (1 + ‖z‖) + ‖v z - 0‖)
        ≤ Cp * ((2 * |C₁| + |C₂|) * (1 + ‖z‖) ^ (-(min β (-δ')))) :=
          mul_le_mul_of_nonneg_left g3 hCp0
      _ ≤ (Ca + Cp) * (2 * |C₁| + |C₂|) * (1 + ‖z‖) ^ (-(min β (-δ'))) := by nlinarith

lemma member_dist (hH : IsStrictlyStarShapedLevel H) (hΦ : ContDiff ℝ ∞ Φ)
    (hΦ0 : ∀ p ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)), Φ p ≠ 0)
    (hρ' : 0 < ρ') (hρ : ρ' < ρ) {Cp : ℝ}
    (hFp : ContDiffOn ℝ ∞ (fun p => proj H (Φ p)) (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hCp : CylBound (fun p => proj H (Φ p)) ρ' Cp)
    {S : Set (V 1)} {u : ℂ → V 1} (hΦu : ∀ z, Φ (z, 0) = u z)
    {ψ v : ℂ → ℂ} {C₁ β C₂ δ' CU : ℝ} (hβ : 0 < β) (hδ' : δ' < 0)
    (hψc : Continuous ψ) (hvc : Continuous v) (hvρ : ∀ z, v z ∈ ball (0 : ℂ) ρ)
    (hψ : ∀ z, ‖ψ z - z‖ ≤ C₁ * (1 + ‖z‖) ^ (1 - β))
    (hv : ∀ z, ‖v z‖ ≤ C₂ * (1 + ‖z‖) ^ δ')
    (hU : ∀ z, infDist (proj H (u z)) S ≤ CU * (1 + ‖z‖) ^ δ') :
    ∃ C : ℝ, ∀ z, infDist (proj H (Φ (ψ z, v z))) S ≤ C * (1 + ‖z‖) ^ δ' := by
  obtain ⟨R, hR0, hR⟩ := far (ρ' := ρ') C₁ β C₂ δ' hρ' hβ hδ'
  have hCp0 := hCp.nonneg hρ'.le
  have hw0 : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ' := by simpa using hρ'.le
  -- compact part
  have hcont : Continuous (fun z => infDist (proj H (Φ (ψ z, v z))) S) := by
    refine (Metric.continuous_infDist_pt S).comp ?_
    rw [continuous_iff_continuousAt]
    intro z
    have h0 : Φ (ψ z, v z) ≠ 0 := hΦ0 _ ⟨Set.mem_univ _, hvρ z⟩
    have h1 : ContinuousAt (proj H) (Φ (ψ z, v z)) :=
      (contDiffAt_aCoord_proj_aux H hH _ h0).2.continuousAt
    have h2 : ContinuousAt (fun z => Φ (ψ z, v z)) z :=
      (hΦ.continuous.comp (hψc.prodMk hvc)).continuousAt
    exact ContinuousAt.comp (f := fun z => Φ (ψ z, v z)) h1 h2
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hcont.continuousOn
  have hR1 : 0 < 1 + R := by linarith
  have hRp : 0 < (1 + R) ^ δ' := Real.rpow_pos_of_pos hR1 _
  have h2p : 0 < (2 : ℝ) ^ δ' := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨max (|CU| / 2 ^ δ' + Cp * |C₂|) (|M| / (1 + R) ^ δ'), fun z => ?_⟩
  have hx : 0 < 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hxp : 0 ≤ (1 + ‖z‖) ^ δ' := by positivity
  rcases le_or_gt R ‖z‖ with hz | hz
  · obtain ⟨f1, f2⟩ := hR ‖z‖ hz
    obtain ⟨g1, g2, -⟩ := far_pt hβ hδ' f1 f2 (hψ z) (hv z)
    have d1 : infDist (proj H (Φ (ψ z, v z))) S ≤
        infDist (proj H (Φ (ψ z, 0))) S + dist (proj H (Φ (ψ z, v z))) (proj H (Φ (ψ z, 0))) :=
      Metric.infDist_le_infDist_add_dist
    have d2 : dist (proj H (Φ (ψ z, v z))) (proj H (Φ (ψ z, 0))) ≤ Cp * ‖v z‖ := by
      have := hCp.seg hρ'.le hρ hFp (ζ₀ := ψ z) (ζ₁ := ψ z) hw0 g1
        (by rw [sub_self, norm_zero]; positivity)
      rw [sub_self, norm_zero, mul_zero, zero_div, zero_add, sub_zero] at this
      rw [dist_eq_norm]; exact this
    have d3 : infDist (proj H (Φ (ψ z, 0))) S ≤ |CU| / 2 ^ δ' * (1 + ‖z‖) ^ δ' := by
      rw [hΦu]
      refine (hU (ψ z)).trans ?_
      have hψn : (1 + ‖z‖) / 2 ≤ 1 + ‖ψ z‖ := by
        have := norm_sub_norm_le z (ψ z)
        rw [norm_sub_rev] at this
        linarith
      have r1 : (1 + ‖ψ z‖) ^ δ' ≤ ((1 + ‖z‖) / 2) ^ δ' :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hψn hδ'.le
      rw [Real.div_rpow hx.le (by norm_num)] at r1
      calc CU * (1 + ‖ψ z‖) ^ δ' ≤ |CU| * (1 + ‖ψ z‖) ^ δ' :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |CU| * ((1 + ‖z‖) ^ δ' / 2 ^ δ') := mul_le_mul_of_nonneg_left r1 (abs_nonneg _)
        _ = |CU| / 2 ^ δ' * (1 + ‖z‖) ^ δ' := by ring
    have d4 : Cp * ‖v z‖ ≤ Cp * |C₂| * (1 + ‖z‖) ^ δ' := by
      have : ‖v z‖ ≤ |C₂| * (1 + ‖z‖) ^ δ' :=
        (hv z).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hxp)
      calc Cp * ‖v z‖ ≤ Cp * (|C₂| * (1 + ‖z‖) ^ δ') := mul_le_mul_of_nonneg_left this hCp0
        _ = _ := by ring
    calc infDist (proj H (Φ (ψ z, v z))) S
        ≤ (|CU| / 2 ^ δ' + Cp * |C₂|) * (1 + ‖z‖) ^ δ' := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hxp
  · have hm := hM z (by rw [mem_closedBall, dist_zero_right]; exact hz.le)
    rw [Real.norm_eq_abs] at hm
    have r1 : (1 + R) ^ δ' ≤ (1 + ‖z‖) ^ δ' :=
      Real.rpow_le_rpow_of_nonpos hx (by linarith) hδ'.le
    have hMabs : M ≤ |M| := le_abs_self M
    have r2 : |M| ≤ |M| / (1 + R) ^ δ' * (1 + ‖z‖) ^ δ' := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hRp]
      exact mul_le_mul_of_nonneg_left r1 (abs_nonneg _)
    calc infDist (proj H (Φ (ψ z, v z))) S ≤ |M| := (le_abs_self _).trans (hm.trans hMabs)
      _ ≤ |M| / (1 + R) ^ δ' * (1 + ‖z‖) ^ δ' := r2
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hxp

lemma ne_zero_of_mem (hH : IsStrictlyStarShapedLevel H) {x : V 1} (hx : x ∈ energySurface H) :
    x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

/-- Fibre derivative of `Φ` bounded by `‖Φ‖`. -/
lemma der_bound (hH : IsStrictlyStarShapedLevel H) (hΦ : ContDiff ℝ ∞ Φ)
    (hΦ0 : ∀ p ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)), Φ p ≠ 0)
    (hρ' : 0 < ρ') (hρ : ρ' < ρ) {Ca Cp : ℝ}
    (hCa : CylBound (fun p => aCoord H (Φ p)) ρ' Ca)
    (hCp : CylBound (fun p => proj H (Φ p)) ρ' Cp) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ζ w o : ℂ), w ∈ closedBall (0 : ℂ) ρ' →
      ‖fderiv ℝ Φ (ζ, w) (0, o)‖ ≤ K * ‖o‖ * ‖Φ (ζ, w)‖ := by
  have hCa0 := hCa.nonneg hρ'.le
  have hCp0 := hCp.nonneg hρ'.le
  have hS := isCompact_energySurface H hH
  obtain ⟨M, hM⟩ := hS.isBounded.exists_norm_le
  rcases (energySurface H).eq_empty_or_nonempty with hemp | hne
  · refine ⟨0, le_rfl, fun ζ w o hw => ?_⟩
    exfalso
    have h0 : Φ (ζ, w) ≠ 0 := hΦ0 _ ⟨Set.mem_univ _, mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ)⟩
    have : proj H (Φ (ζ, w)) ∈ energySurface H := (ka_scale_spec H hH _ h0).2
    rw [hemp] at this
    exact this
  obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne continuous_norm.continuousOn
  have hm : 0 < ‖x₀‖ := norm_pos_iff.2 (ne_zero_of_mem hH hx₀)
  have hM0 : 0 ≤ M := (norm_nonneg x₀).trans (hM x₀ hx₀)
  refine ⟨(Cp + 2 * Ca * M) / ‖x₀‖, by positivity, fun ζ w o hw => ?_⟩
  set p : ℂ × ℂ := (ζ, w) with hp
  have hpin : p ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) :=
    ⟨Set.mem_univ _, mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ)⟩
  have h0 : Φ p ≠ 0 := hΦ0 _ hpin
  obtain ⟨hca, hcp⟩ := contDiffAt_aCoord_proj_aux H hH (Φ p) h0
  have hΦd : DifferentiableAt ℝ Φ p := (hΦ.differentiable (by simp)) p
  have hA : HasFDerivAt (fun q => aCoord H (Φ q)) (fderiv ℝ (fun q => aCoord H (Φ q)) p) p :=
    ((hca.comp p hΦ.contDiffAt).differentiableAt (by simp)).hasFDerivAt
  have hB : HasFDerivAt (fun q => proj H (Φ q)) (fderiv ℝ (fun q => proj H (Φ q)) p) p :=
    ((hcp.comp p hΦ.contDiffAt).differentiableAt (by simp)).hasFDerivAt
  have hev : (fun q => Real.exp (2 * aCoord H (Φ q)) • proj H (Φ q)) =ᶠ[𝓝 p] Φ := by
    filter_upwards [hΦd.continuousAt.eventually_ne h0] with q hq
    exact emb_exp_aCoord_smul_proj H hH (Φ q) hq
  have hsm := (((hA.const_mul 2).exp).smul hB).congr_of_eventuallyEq hev.symm
  have hdu := hΦd.hasFDerivAt.unique hsm
  have hval : fderiv ℝ Φ p (0, o) = Real.exp (2 * aCoord H (Φ p)) •
      (fderiv ℝ (fun q => proj H (Φ q)) p (0, o) +
        (2 * fderiv ℝ (fun q => aCoord H (Φ q)) p (0, o)) • proj H (Φ p)) := by
    rw [hdu]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, smul_add, smul_smul, mul_assoc]
  have b1 := (hCa ζ w hw).1 (0, o)
  have b2 := (hCp ζ w hw).1 (0, o)
  simp only [norm_zero, zero_div, zero_add] at b1 b2
  rw [Real.norm_eq_abs] at b1
  have hpS : proj H (Φ p) ∈ energySurface H := (ka_scale_spec H hH _ h0).2
  have n1 : ‖proj H (Φ p)‖ ≤ M := hM _ hpS
  have n2 : ‖x₀‖ ≤ ‖proj H (Φ p)‖ := hmin hpS
  have hΦn : ‖Φ p‖ = Real.exp (2 * aCoord H (Φ p)) * ‖proj H (Φ p)‖ := by
    conv_lhs => rw [← emb_exp_aCoord_smul_proj H hH (Φ p) h0]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he := Real.exp_pos (2 * aCoord H (Φ p))
  have hin : ‖fderiv ℝ (fun q => proj H (Φ q)) p (0, o) +
      (2 * fderiv ℝ (fun q => aCoord H (Φ q)) p (0, o)) • proj H (Φ p)‖ ≤
      (Cp + 2 * Ca * M) * ‖o‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    have : 2 * |fderiv ℝ (fun q => aCoord H (Φ q)) p (0, o)| * ‖proj H (Φ p)‖ ≤
        2 * (Ca * ‖o‖) * M :=
      mul_le_mul (by linarith) n1 (norm_nonneg _) (by positivity)
    nlinarith
  rw [hval, norm_smul, Real.norm_eq_abs, abs_of_pos he, hΦn]
  have hK : (Cp + 2 * Ca * M) * ‖o‖ ≤ (Cp + 2 * Ca * M) / ‖x₀‖ * ‖o‖ * ‖proj H (Φ p)‖ := by
    have hc : 0 ≤ (Cp + 2 * Ca * M) * ‖o‖ := by positivity
    calc (Cp + 2 * Ca * M) * ‖o‖ = (Cp + 2 * Ca * M) * ‖o‖ / ‖x₀‖ * ‖x₀‖ := by
          field_simp
      _ ≤ (Cp + 2 * Ca * M) * ‖o‖ / ‖x₀‖ * ‖proj H (Φ p)‖ :=
          mul_le_mul_of_nonneg_left n2 (by positivity)
      _ = _ := by ring
  calc Real.exp (2 * aCoord H (Φ p)) * ‖_‖
      ≤ Real.exp (2 * aCoord H (Φ p)) * ((Cp + 2 * Ca * M) / ‖x₀‖ * ‖o‖ * ‖proj H (Φ p)‖) :=
        mul_le_mul_of_nonneg_left (hin.trans hK) he.le
    _ = _ := by ring

lemma member_close (hρ' : 0 < ρ') (hρ : ρ' < ρ) {Ca Cp : ℝ}
    (hFa : ContDiffOn ℝ ∞ (fun p => aCoord H (Φ p)) (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hFp : ContDiffOn ℝ ∞ (fun p => proj H (Φ p)) (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hCa : CylBound (fun p => aCoord H (Φ p)) ρ' Ca)
    (hCp : CylBound (fun p => proj H (Φ p)) ρ' Cp)
    {u : ℂ → V 1} (hΦu : ∀ z, Φ (z, 0) = u z) {ψ v : ℂ → ℂ}
    (hψd : Differentiable ℝ ψ) (hvd : Differentiable ℝ v) {ε : ℝ} (hε1 : ε ≤ 1 / 2)
    (hερ : ε ≤ ρ')
    (h : ∀ z, ‖ψ z - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖v z‖ ≤ ε ∧
      ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧ (1 + ‖z‖) * ‖fderiv ℝ v z‖ ≤ ε) :
    IsCylCloseTo H (9 * (Ca + Cp) * ε) (fun z => Φ (ψ z, v z)) u := by
  have hCa0 := hCa.nonneg hρ'.le
  have hCp0 := hCp.nonneg hρ'.le
  have hu : u = fun z => Φ (z, 0) := funext fun z => (hΦu z).symm
  subst hu
  intro z
  obtain ⟨h1, h2, h3, h4⟩ := h z
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans h2
  have A := hCa.close hρ'.le hρ hFa (hψd z) (hvd z) hε1 hερ h1 h2 h3 h4
  have B := hCp.close hρ'.le hρ hFp (hψd z) (hvd z) hε1 hερ h1 h2 h3 h4
  have A1 : |aCoord H (Φ (ψ z, v z)) - aCoord H (Φ (z, 0))| ≤ 3 * Ca * ε := A.1
  have B1 : ‖proj H (Φ (ψ z, v z)) - proj H (Φ (z, 0))‖ ≤ 3 * Cp * ε := B.1
  have A2 : (1 + ‖z‖) * ‖fderiv ℝ (fun x => aCoord H (Φ (ψ x, v x))) z -
      fderiv ℝ (fun x : ℂ => aCoord H (Φ (x, 0))) z‖ ≤ 9 * Ca * ε := A.2
  have B2 : (1 + ‖z‖) * ‖fderiv ℝ (fun x => proj H (Φ (ψ x, v x))) z -
      fderiv ℝ (fun x : ℂ => proj H (Φ (x, 0))) z‖ ≤ 9 * Cp * ε := B.2
  have q1 : 0 ≤ Ca * ε := mul_nonneg hCa0 hε0
  have q2 : 0 ≤ Cp * ε := mul_nonneg hCp0 hε0
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · rw [mul_add]; linarith

end tube

end XT

end FiniteEnergyPlane

/-!
# X transfer: glue for `exists_jHolomorphic_family_of_stdTube` (c301cb05)

`g(z, t) = Φ(G(z, t))`. The symplectization coordinates of `Φ` have cylindrical `C²` bounds
(child A); every analytic clause follows from them, the weighted bounds on `G` and, for the
distance clause, the window rate of `u` (U 1c2ff730).
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real

lemma member_hol {Jb : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Jt : V 1 → V 1 →L[ℝ] V 1}
    {Φ : ℂ × ℂ → V 1} {ρ : ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hint : ∀ p ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)),
      (fderiv ℝ Φ p).comp (Jb p) = (Jt (Φ p)).comp (fderiv ℝ Φ p))
    {γ : ℂ → ℂ × ℂ} (hγ : JHolomorphic.IsJHolomorphicOn Jb Set.univ γ)
    (hγρ : ∀ z, (γ z).2 ∈ ball (0 : ℂ) ρ) :
    JHolomorphic.IsJHolomorphicOn Jt Set.univ (fun z => Φ (γ z)) := by
  intro z _
  obtain ⟨hd, he⟩ := hγ z (Set.mem_univ _)
  have hΦd : DifferentiableAt ℝ Φ (γ z) := hΦ.differentiable (by simp) _
  have hc : HasFDerivAt (fun z => Φ (γ z)) ((fderiv ℝ Φ (γ z)).comp (fderiv ℝ γ z)) z :=
    hΦd.hasFDerivAt.comp z hd.hasFDerivAt
  refine ⟨hc.differentiableAt, ?_⟩
  unfold JHolomorphic.dbarJ at he ⊢
  rw [hc.fderiv]
  have hi := hint (γ z) ⟨Set.mem_univ _, hγρ z⟩
  have := congrArg (fun L => L (fderiv ℝ γ z Complex.I)) hi
  simp only [ContinuousLinearMap.comp_apply] at this ⊢
  rw [← this, ← map_add, he, map_zero]

lemma trans_zero {Φ : ℂ × ℂ → V 1} {G : ℂ × ℝ → ℂ × ℂ} {u : ℂ → V 1}
    (hΦd : DifferentiableAt ℝ Φ (0, 0)) (hinj : Function.Injective (fderiv ℝ Φ (0, 0)))
    (hGd : DifferentiableAt ℝ G (0, 0)) (hG0 : ∀ z, G (z, 0) = (z, 0))
    (hGw : (fderiv ℝ G (0, 0) (0, 1)).2 = Complex.I)
    (hτ : ∃ τ : ℂ, fderiv ℝ Φ (0, 0) (τ, 1) = u 0) (hΦu : Φ (0, 0) = u 0) :
    ∀ (Δ : ℂ) (δt lam : ℝ),
      fderiv ℝ (fun q => Φ (G q)) (0, 0) (Δ, δt) + lam • Φ (G (0, 0)) = 0 →
        Δ = 0 ∧ δt = 0 ∧ lam = 0 := by
  intro Δ δt lam h
  have hG00 : G (0, 0) = (0, 0) := hG0 0
  have hc : HasFDerivAt (fun q => Φ (G q))
      ((fderiv ℝ Φ (0, 0)).comp (fderiv ℝ G (0, 0))) (0, 0) := by
    have hd : DifferentiableAt ℝ Φ (G (0, 0)) := by rw [hG00]; exact hΦd
    have h1 := hd.hasFDerivAt.comp (0, 0) hGd.hasFDerivAt
    rwa [hG00] at h1
  have hbase : ∀ Δ : ℂ, fderiv ℝ G (0, 0) (Δ, 0) = (Δ, 0) := by
    intro Δ
    have h1 : HasFDerivAt (fun z : ℂ => G (z, 0))
        ((fderiv ℝ G (0, 0)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℝ))) 0 :=
      hGd.hasFDerivAt.comp (0 : ℂ)
        ((hasFDerivAt_id (0 : ℂ)).prodMk (hasFDerivAt_const (0 : ℝ) (0 : ℂ)))
    have h2 : HasFDerivAt (fun z : ℂ => G (z, 0))
        ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ)) 0 := by
      have : (fun z : ℂ => G (z, 0)) = fun z => (z, (0 : ℂ)) := funext hG0
      rw [this]
      exact (hasFDerivAt_id (0 : ℂ)).prodMk (hasFDerivAt_const (0 : ℂ) (0 : ℂ))
    have := congrArg (fun L => L Δ) (h1.unique h2)
    simpa using this
  obtain ⟨τ, hτ⟩ := hτ
  have hsplit : fderiv ℝ G (0, 0) (Δ, δt) = (Δ, 0) + δt • fderiv ℝ G (0, 0) (0, 1) := by
    have : ((Δ, δt) : ℂ × ℝ) = (Δ, 0) + δt • ((0 : ℂ), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul, hbase]
  rw [hc.fderiv, ContinuousLinearMap.comp_apply, hsplit, hG00, hΦu, ← hτ,
    ← (fderiv ℝ Φ (0, 0)).map_smul lam, ← (fderiv ℝ Φ (0, 0)).map_add] at h
  have hz := hinj (h.trans (map_zero _).symm)
  have h2 := congrArg Prod.snd hz
  have h1 := congrArg Prod.fst hz
  simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_zero, hGw, Prod.fst_add, Prod.smul_fst,
    Prod.fst_zero, zero_add] at h1 h2
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp at hre him
  subst hre
  subst him
  simp at h1
  exact ⟨h1, rfl, rfl⟩

lemma member_der {Φ : ℂ × ℂ → V 1} {ρ ρ' : ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hΦ0 : ∀ p ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)), Φ p ≠ 0)
    (hρ' : 0 < ρ') {K : ℝ}
    (hK : ∀ (ζ w o : ℂ), w ∈ closedBall (0 : ℂ) ρ' →
      ‖fderiv ℝ Φ (ζ, w) (0, o)‖ ≤ K * ‖o‖ * ‖Φ (ζ, w)‖)
    {ψ v : ℂ → ℂ} (hψc : Continuous ψ) (hvc : Continuous v)
    (hvρ : ∀ z, v z ∈ ball (0 : ℂ) ρ) {C₂ δ' : ℝ} (hδ' : δ' < 0)
    (hv : ∀ z, ‖v z‖ ≤ C₂ * (1 + ‖z‖) ^ δ') :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ z o,
      ‖fderiv ℝ Φ (ψ z, v z) (0, o)‖ ≤ K' * ‖o‖ * ‖Φ (ψ z, v z)‖ := by
  obtain ⟨R, -, hR⟩ := far (ρ' := ρ') 0 1 C₂ δ' hρ' one_pos hδ'
  have hne : ∀ z, Φ (ψ z, v z) ≠ 0 := fun z => hΦ0 _ ⟨Set.mem_univ _, hvρ z⟩
  have hcont : Continuous (fun z => ‖fderiv ℝ Φ (ψ z, v z)‖ / ‖Φ (ψ z, v z)‖) := by
    have h1 : Continuous (fun z => fderiv ℝ Φ (ψ z, v z)) :=
      (hΦ.continuous_fderiv (by simp)).comp (hψc.prodMk hvc)
    have h2 : Continuous (fun z => Φ (ψ z, v z)) := hΦ.continuous.comp (hψc.prodMk hvc)
    exact h1.norm.div h2.norm (fun z => norm_ne_zero_iff.2 (hne z))
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max K |M|, le_max_of_le_right (abs_nonneg _), fun z o => ?_⟩
  have hn : 0 < ‖Φ (ψ z, v z)‖ := norm_pos_iff.2 (hne z)
  rcases le_or_gt R ‖z‖ with hz | hz
  · have hw : v z ∈ closedBall (0 : ℂ) ρ' := by
      rw [mem_closedBall, dist_zero_right]
      exact (hv z).trans (hR ‖z‖ hz).2
    refine (hK (ψ z) (v z) o hw).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (norm_nonneg _)
  · have hm := hM z (by rw [mem_closedBall, dist_zero_right]; exact hz.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hn] at hm
    have ho : ‖((0 : ℂ), o)‖ = ‖o‖ := by simp [Prod.norm_def]
    calc ‖fderiv ℝ Φ (ψ z, v z) (0, o)‖ ≤ ‖fderiv ℝ Φ (ψ z, v z)‖ * ‖((0 : ℂ), o)‖ :=
          (fderiv ℝ Φ (ψ z, v z)).le_opNorm _
      _ ≤ (|M| * ‖Φ (ψ z, v z)‖) * ‖o‖ := by
          rw [ho]
          exact mul_le_mul_of_nonneg_right
            (hm.trans (mul_le_mul_of_nonneg_right (le_abs_self M) hn.le)) (norm_nonneg _)
      _ = |M| * ‖o‖ * ‖Φ (ψ z, v z)‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) (norm_nonneg _)

end XT

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_jHolomorphic_family_of_stdTube_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (l : ℕ) (hl : 1 ≤ l)
    (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) (Φ : ℂ × ℂ → V 1) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦu : ∀ z, Φ (z, 0) = u z)
    (hΦp : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, Φ p ≠ 0 ∧ Function.Injective (fderiv ℝ Φ p) ∧
        (fderiv ℝ Φ p).comp (Jbar p) = (Jtilde H J (Φ p)).comp (fderiv ℝ Φ p))
    (hτ : ∃ τ : ℂ, fderiv ℝ Φ (0, 0) (τ, 1) = u 0)
    (hmodel : ∃ (d c : ℝ) (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
        ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
        (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t + c)) ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          aCoord H (Φ (cylInf q.1 q.2.1, q.2.2)) - P.T * q.1 - d - α (q.2.1, q.2.2)) ρ b ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          proj H (Φ (cylInf q.1 q.2.1, q.2.2)) - X (q.2.1, q.2.2)) ρ b)
    (r : ℝ) (hr : 0 < r) (G : ℂ × ℝ → ℂ × ℂ)
    (hG : ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r))
    (hG0 : ∀ z, G (z, 0) = (z, 0)) (hGω : (fderiv ℝ G (0, 0) (0, 1)).2 = Complex.I)
    (hGt : ∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => G (z, t)) ∧ (∀ z, (G (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
        JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => G (z, t)) ∧
        (∃ C β : ℝ, 0 < β ∧ ∀ z, ‖(G (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β)) ∧
        (∃ C : ℝ, ∀ z, ‖(G (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ G (z, t) (Δ, 1)).1 = 0 ∧
          ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π)))
    (hGc : ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ z,
        ‖(G (z, t)).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(G (z, t)).2‖ ≤ ε ∧
        ‖fderiv ℝ (fun z => (G (z, t)).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
        (1 + ‖z‖) * ‖fderiv ℝ (fun z => (G (z, t)).2) z‖ ≤ ε) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
        JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
        (∃ C : ℝ, ∀ z, infDist (proj H (g (z, t))) (Set.range P.x) ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, ‖fderiv ℝ g (z, t) (Δ, 1)‖ ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π)) * ‖g (z, t)‖) ∧
      (∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, 0) (Δ, δt) + lam • g (0, 0) = 0 →
        Δ = 0 ∧ δt = 0 ∧ lam = 0) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
        IsCylCloseTo H ε (fun z => g (z, t)) u := by
  obtain ⟨d, c, α, X, hα, hX, hper, -, hEa, hEp⟩ := hmodel
  have hΦ0 : ∀ p ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)), Φ p ≠ 0 :=
    fun p hp => (hΦp p hp).1
  obtain ⟨hFa, hFp⟩ := XT.contDiffOn_coords (H := H) hH hΦ hΦ0
  have hρ2 : 0 < ρ / 2 := by positivity
  have hρlt : ρ / 2 < ρ := by linarith
  have hδ' : δ / (2 * π) < 0 := div_neg_of_neg_of_pos hδ (by positivity)
  have hEa' : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      aCoord H (Φ (cylInf q.1 q.2.1, q.2.2)) - q.1 • P.T - (d + α (q.2.1, q.2.2))) ρ b := by
    have e : (fun q : ℝ × ℝ × ℂ =>
        aCoord H (Φ (cylInf q.1 q.2.1, q.2.2)) - q.1 • P.T - (d + α (q.2.1, q.2.2))) =
        fun q : ℝ × ℝ × ℂ =>
          aCoord H (Φ (cylInf q.1 q.2.1, q.2.2)) - P.T * q.1 - d - α (q.2.1, q.2.2) := by
      funext q; simp only [smul_eq_mul]; ring
    rw [e]; exact hEa
  have hEp' : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      proj H (Φ (cylInf q.1 q.2.1, q.2.2)) - q.1 • (0 : V 1) - X (q.2.1, q.2.2)) ρ b := by
    have e : (fun q : ℝ × ℝ × ℂ =>
        proj H (Φ (cylInf q.1 q.2.1, q.2.2)) - q.1 • (0 : V 1) - X (q.2.1, q.2.2)) =
        fun q : ℝ × ℝ × ℂ => proj H (Φ (cylInf q.1 q.2.1, q.2.2)) - X (q.2.1, q.2.2) := by
      funext q; simp
    rw [e]; exact hEp
  obtain ⟨Ca, hCa⟩ := exists_cylindrical_bounds_of_expDecayCInftyTube ρ b (ρ / 2) hb hρ2 hρlt (fun p => aCoord H (Φ p)) hFa
    P.T (fun q => d + α q) (contDiffOn_const.add hα)
    (fun t w => by simp only [(hper t w).1]) hEa'
  obtain ⟨Cp, hCp⟩ := exists_cylindrical_bounds_of_expDecayCInftyTube ρ b (ρ / 2) hb hρ2 hρlt (fun p => proj H (Φ p)) hFp
    0 X hX (fun t w => (hper t w).2) hEp'
  have hCa : XT.CylBound (fun p => aCoord H (Φ p)) (ρ / 2) Ca := hCa
  have hCp : XT.CylBound (fun p => proj H (Φ p)) (ρ / 2) Cp := hCp
  obtain ⟨CU, hU⟩ := infDist_proj_le_of_isFastPlane H hH J hJ P u hu huP δ hδ hwin
  obtain ⟨K, -, hK⟩ := XT.der_bound hH hΦ hΦ0 hρ2 hρlt hCa hCp
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo (-r) r : Set (ℂ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hGdiff : ∀ z : ℂ, ∀ t ∈ Set.Ioo (-r) r, DifferentiableAt ℝ G (z, t) := fun z t ht =>
    (hG.contDiffAt (hopen.mem_nhds ⟨Set.mem_univ _, ht⟩)).differentiableAt (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hl))
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have h0r : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  refine ⟨r, hr, fun q => Φ (G q), (hΦ.of_le (by exact_mod_cast le_top)).comp_contDiffOn hG,
    fun z => by show Φ (G (z, 0)) = u z; rw [hG0]; exact hΦu z, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨hsm, hball, hhol, ⟨C₁, β, hβ, hψ⟩, ⟨C₂, hv⟩, ⟨C₃, hder⟩⟩ := hGt t ht
    have hψc : Continuous (fun z => (G (z, t)).1) := hsm.fst.continuous
    have hvc : Continuous (fun z => (G (z, t)).2) := hsm.snd.continuous
    refine ⟨hΦ.comp hsm, fun z => hΦ0 _ ⟨Set.mem_univ _, hball z⟩,
      XT.member_hol hΦ (fun p hp => (hΦp p hp).2.2) hhol hball, ?_, ?_, ?_⟩
    · exact XT.member_end hρ2 hρlt hFa hFp hCa hCp hΦu huP (ψ := fun z => (G (z, t)).1)
        (v := fun z => (G (z, t)).2) hβ hδ' hψ hv
    · exact XT.member_dist hH hΦ hΦ0 hρ2 hρlt hFp hCp hΦu (ψ := fun z => (G (z, t)).1)
        (v := fun z => (G (z, t)).2) hβ hδ' hψc hvc hball hψ hv hU
    · obtain ⟨K', hK'0, hK'⟩ := XT.member_der hΦ hΦ0 hρ2 hK (ψ := fun z => (G (z, t)).1)
        (v := fun z => (G (z, t)).2) hψc hvc hball hδ' hv
      refine ⟨K' * C₃, fun z => ?_⟩
      obtain ⟨Δ, hΔ1, hΔ2⟩ := hder z
      refine ⟨Δ, ?_⟩
      have hc : fderiv ℝ (fun q => Φ (G q)) (z, t) =
          (fderiv ℝ Φ (G (z, t))).comp (fderiv ℝ G (z, t)) :=
        ((hΦd (G (z, t))).hasFDerivAt.comp (z, t) (hGdiff z t ht).hasFDerivAt).fderiv
      have e : fderiv ℝ G (z, t) (Δ, 1) = (0, (fderiv ℝ G (z, t) (Δ, 1)).2) :=
        Prod.ext hΔ1 rfl
      rw [hc, ContinuousLinearMap.comp_apply, e]
      refine (hK' z _).trans ?_
      calc K' * ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ * ‖Φ (G (z, t))‖
          ≤ K' * (C₃ * (1 + ‖z‖) ^ (δ / (2 * π))) * ‖Φ (G (z, t))‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ2 hK'0) (norm_nonneg _)
        _ = _ := by ring
  · have hinj := (hΦp (0, 0) ⟨Set.mem_univ _, mem_ball_self hρ⟩).2.1
    exact XT.trans_zero (hΦd (0, 0)) hinj (hGdiff 0 0 h0r) hG0 hGω hτ (hΦu 0)
  · intro ε hε
    have hCa0 := hCa.nonneg hρ2.le
    have hCp0 := hCp.nonneg hρ2.le
    have hA : 0 ≤ 9 * (Ca + Cp) := by positivity
    have hε' : 0 < min (ε / (9 * (Ca + Cp) + 1)) (min (1 / 2) (ρ / 2)) :=
      lt_min (by positivity) (lt_min (by norm_num) hρ2)
    obtain ⟨r', hr', hcl⟩ := hGc _ hε'
    refine ⟨r', hr', fun t ht => ?_⟩
    have ht' : t ∈ Set.Ioo (-r) r := ⟨by linarith [ht.1, hr'.2], by linarith [ht.2, hr'.2]⟩
    obtain ⟨hsm, -⟩ := hGt t ht'
    have key := XT.member_close hρ2 hρlt hFa hFp hCa hCp hΦu (ψ := fun z => (G (z, t)).1)
      (v := fun z => (G (z, t)).2) (hsm.fst.differentiable (by simp))
      (hsm.snd.differentiable (by simp)) ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) (hcl t ht)
    have hle : 9 * (Ca + Cp) * min (ε / (9 * (Ca + Cp) + 1)) (min (1 / 2) (ρ / 2)) ≤ ε := by
      calc 9 * (Ca + Cp) * min (ε / (9 * (Ca + Cp) + 1)) (min (1 / 2) (ρ / 2))
          ≤ 9 * (Ca + Cp) * (ε / (9 * (Ca + Cp) + 1)) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hA
        _ = ε * (9 * (Ca + Cp) / (9 * (Ca + Cp) + 1)) := by ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
            ((div_le_one (by positivity)).2 (by linarith)) hε.le
        _ = ε := mul_one ε
    intro z
    obtain ⟨k1, k2, k3⟩ := key z
    exact ⟨k1.trans hle, k2.trans hle, k3.trans hle⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (l : ℕ) (hl : 1 ≤ l)
    (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) (Φ : ℂ × ℂ → V 1) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦu : ∀ z, Φ (z, 0) = u z)
    (hΦp : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, Φ p ≠ 0 ∧ Function.Injective (fderiv ℝ Φ p) ∧
        (fderiv ℝ Φ p).comp (Jbar p) = (Jtilde H J (Φ p)).comp (fderiv ℝ Φ p))
    (hτ : ∃ τ : ℂ, fderiv ℝ Φ (0, 0) (τ, 1) = u 0)
    (hmodel : ∃ (d c : ℝ) (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
        ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
        (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t + c)) ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          aCoord H (Φ (cylInf q.1 q.2.1, q.2.2)) - P.T * q.1 - d - α (q.2.1, q.2.2)) ρ b ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          proj H (Φ (cylInf q.1 q.2.1, q.2.2)) - X (q.2.1, q.2.2)) ρ b)
    (r : ℝ) (hr : 0 < r) (G : ℂ × ℝ → ℂ × ℂ)
    (hG : ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r))
    (hG0 : ∀ z, G (z, 0) = (z, 0)) (hGω : (fderiv ℝ G (0, 0) (0, 1)).2 = Complex.I)
    (hGt : ∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => G (z, t)) ∧ (∀ z, (G (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
        JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => G (z, t)) ∧
        (∃ C β : ℝ, 0 < β ∧ ∀ z, ‖(G (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β)) ∧
        (∃ C : ℝ, ∀ z, ‖(G (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ G (z, t) (Δ, 1)).1 = 0 ∧
          ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π)))
    (hGc : ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ z,
        ‖(G (z, t)).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(G (z, t)).2‖ ≤ ε ∧
        ‖fderiv ℝ (fun z => (G (z, t)).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
        (1 + ‖z‖) * ‖fderiv ℝ (fun z => (G (z, t)).2) z‖ ≤ ε) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
        JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
        (∃ C : ℝ, ∀ z, infDist (proj H (g (z, t))) (Set.range P.x) ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, ‖fderiv ℝ g (z, t) (Δ, 1)‖ ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π)) * ‖g (z, t)‖) ∧
      (∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, 0) (Δ, δt) + lam • g (0, 0) = 0 →
        Δ = 0 ∧ δt = 0 ∧ lam = 0) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
        IsCylCloseTo H ε (fun z => g (z, t)) u :=
  exists_jHolomorphic_family_of_stdTube_aux H hH J hJ P u hu huP δ hδ hwin l hl ρ b hρ hb Φ Jbar hΦ hΦu hΦp hτ hmodel r hr G hG hG0 hGω hGt hGc
