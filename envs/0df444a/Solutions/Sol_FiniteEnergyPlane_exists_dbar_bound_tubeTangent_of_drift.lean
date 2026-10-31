-- Prove2me | solution 1 for FiniteEnergyPlane.exists_dbar_bound_tubeTangent_of_drift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T12:05:55.998173+00:00
-- url     : https://prove2.me/submissions/fbe0fd2d-0edc-4c3e-b187-dfaf5d698a8b

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_fderiv_endA_eq_liouville_endW
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact

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

theorem kad_abs_omega0_le {n : ℕ} (u v : V n) :
    |omega0 u v| ≤ ‖(KAo.omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)‖ * ‖u‖ * ‖v‖ := by
  rw [← KAo.omegaL_apply, ← Real.norm_eq_abs]
  exact KAo.omegaL.le_opNorm₂ u v

set_option maxHeartbeats 1000000 in
theorem exists_dbar_bound_tubeTangent_of_drift_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hθs : ∃ s₂ : ℝ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η)
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ K s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1) (s, t) (1, 0) -
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t) (0, 1)| +
        |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1) (s, t) (0, 1) +
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t) (1, 0)| ≤
        K * (‖h (s, t)‖ + ‖fderiv ℝ h (s, t)‖) := by
  have hT := P.T_pos
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
  -- the orbit: compact, away from `0`, bounded Reeb field
  have hxc : Continuous P.x :=
    continuous_iff_continuousAt.2 fun τ => (P.hasDerivAt τ).continuousAt
  have hKc : IsCompact (Set.range P.x) :=
    Function.Periodic.compact_of_continuous (fun τ => P.periodic τ) hT.ne' hxc
  have hx0 : ∀ τ, P.x τ ≠ 0 := by
    intro τ h0
    have := hH.2.2 _ (P.mem τ)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  have hKO : Set.range P.x ⊆ {y : V n | y ≠ 0} := by
    rintro _ ⟨τ, rfl⟩; exact hx0 τ
  have hsc : ContDiffOn ℝ 1 (scaleToS H) {y : V n | y ≠ 0} := fun y hy =>
    ((ka_scale_contDiffAt H hH y hy).of_le (by simp)).contDiffWithinAt
  obtain ⟨δ, hδ, D, hD0, hL⟩ := exists_lipschitz_near_compact isOpen_ne hsc hKc hKO
  have hRc : Continuous fun τ => reeb H (P.x τ) :=
    continuous_iff_continuousAt.2 fun τ =>
      (ka_reeb_contDiffAt H hH _ (P.mem τ)).continuousAt.comp hxc.continuousAt
  have hRK : IsCompact (Set.range fun τ => reeb H (P.x τ)) :=
    Function.Periodic.compact_of_continuous (fun τ => by simp only [P.periodic τ]) hT.ne' hRc
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hRK.isBounded
  have hR : ∀ τ, ‖reeb H (P.x τ)‖ ≤ M := fun τ => hM _ ⟨τ, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hR 0)
  set W0 := ‖(KAo.omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)‖ with hW0
  have hW00 : 0 ≤ W0 := norm_nonneg (KAo.omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)
  -- thresholds
  obtain ⟨a₀, hGs⟩ := hθs
  obtain ⟨⟨b₀, hhs⟩, hhd⟩ := hh
  obtain ⟨s₂, hs₂⟩ := hhd 0 δ hδ
  obtain ⟨s₃, hs₃⟩ := hθ 1 le_rfl 1 one_pos
  obtain ⟨s₄, hs₄⟩ := hhd 1 1 one_pos
  set K₀ := (1 + P.T) * D * (D + 1) + D ^ 2 * ((1 + P.T) * W0 * M + W0 / 2) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨2 * K₀, max (max (max (s₀ + 1) (a₀ + 1)) (max (b₀ + 1) 1)) (max s₂ (max s₃ s₄)),
    fun s hs t => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hs
  obtain ⟨⟨⟨hs0, hsa⟩, hsb, hs1⟩, hs2, hs3, hs4⟩ := hs
  set p : ℝ × ℝ := (s, t) with hp
  -- smoothness at `p`
  have hopen : ∀ e : ℝ, IsOpen (Set.Ioi e ×ˢ (Set.univ : Set ℝ)) := fun e =>
    isOpen_Ioi.prod isOpen_univ
  have hGd : DifferentiableAt ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) p :=
    (hGs.differentiableOn (by simp)).differentiableAt
      ((hopen a₀).mem_nhds ⟨show a₀ < s by linarith, trivial⟩)
  have hhd' : DifferentiableAt ℝ h p :=
    (hhs.differentiableOn (by simp)).differentiableAt
      ((hopen b₀).mem_nhds ⟨show b₀ < s by linarith, trivial⟩)
  have hτfun : τ = fun q : ℝ × ℝ => (τ q - ε * P.T * q.2) + ε * P.T * q.2 := by
    funext q; ring
  have hτd : DifferentiableAt ℝ τ p := by
    rw [hτfun]
    exact hGd.add ((differentiableAt_snd).const_mul _)
  have hGder : ∀ v : ℝ × ℝ, fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) p v =
      fderiv ℝ τ p v - ε * P.T * v.2 := by
    intro v
    have hd : HasFDerivAt (fun p : ℝ × ℝ => τ p - ε * P.T * p.2)
        (fderiv ℝ τ p - (ε * P.T) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      hτd.hasFDerivAt.sub ((hasFDerivAt_snd).const_mul (ε * P.T))
    rw [hd.fderiv]; simp
  -- bounds at `p`
  have hhδ : ‖h p‖ ≤ δ := by
    have := hs₂ s hs2 t; rwa [norm_iteratedFDeriv_zero] at this
  have hDG : ‖fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) p‖ ≤ 1 := by
    have := hs₃ s hs3 t; rwa [norm_iteratedFDeriv_one] at this
  have hDh : ‖fderiv ℝ h p‖ ≤ 1 := by
    have := hs₄ s hs4 t; rwa [norm_iteratedFDeriv_one] at this
  have hσ : ∀ v : ℝ × ℝ, ‖v‖ ≤ 1 → |fderiv ℝ τ p v| ≤ 1 + P.T := by
    intro v hv
    have e : fderiv ℝ τ p v =
        fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) p v + ε * P.T * v.2 := by
      rw [hGder]; ring
    have h1 : |fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) p v| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [norm_nonneg v])
    have h2 : |v.2| ≤ 1 := (norm_snd_le v).trans hv
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 1 + P.T := by
        rw [abs_mul, abs_mul, hεa, abs_of_pos hT]; nlinarith [abs_nonneg v.2]
  -- the tube point
  set x := P.x (τ p) with hxdef
  set Y : ℝ × ℝ → V n := fun q => P.x (τ q) + h q with hYdef
  have hYp : Y p = x + h p := rfl
  have hball : Y p ∈ closedBall x δ := by
    rw [mem_closedBall, dist_eq_norm, hYp, add_sub_cancel_left]; exact hhδ
  obtain ⟨hBO, hLx⟩ := hL x ⟨τ p, rfl⟩
  have hY0 : Y p ≠ 0 := hBO hball
  have hrx : scaleToS H x = 1 :=
    ka_scale_unique H hH x (hx0 _) 1 one_pos (by rw [one_smul]; exact P.mem _)
  set r := scaleToS H (Y p) with hr
  have hrD : |r| ≤ D := by rw [← Real.norm_eq_abs]; exact (hLx _ hball).1
  have hr1 : |r - 1| ≤ D * ‖h p‖ := by
    have := (hLx _ hball).2 x (mem_closedBall_self hδ.le)
    rw [hrx, Real.norm_eq_abs, hYp, add_sub_cancel_left] at this
    exact this
  -- derivative of the tube map
  have hxτ : HasFDerivAt (fun q => P.x (τ q)) ((fderiv ℝ τ p).smulRight (reeb H x)) p :=
    by
      have := (P.hasDerivAt (τ p)).hasFDerivAt.comp p hτd.hasFDerivAt
      exact this.congr_fderiv (ContinuousLinearMap.ext fun v => by simp [hxdef])
  have hY : HasFDerivAt Y ((fderiv ℝ τ p).smulRight (reeb H x) + fderiv ℝ h p) p :=
    hxτ.add hhd'.hasFDerivAt
  have hsd : DifferentiableAt ℝ (scaleToS H) (Y p) :=
    (ka_scale_contDiffAt H hH _ hY0).differentiableAt (by simp)
  have hrY := hsd.hasFDerivAt.comp p hY
  have hPY := hrY.smul hY
  have hnear : {q : ℝ × ℝ | s₀ < q.1} ∈ 𝓝 p :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (show s₀ < s by linarith)
  -- `w = proj (x(τ) + h)` near `p`
  have hev : endW H u cylEnd =ᶠ[𝓝 p] fun q => scaleToS H (Y q) • Y q := by
    filter_upwards [hnear] with q hq
    exact (hrep q.1 hq.le q.2).2.2.2
  have hWder : ∀ v, fderiv ℝ (endW H u cylEnd) p v =
      r • (fderiv ℝ τ p v • reeb H x + fderiv ℝ h p v) +
        (fderiv ℝ (scaleToS H) (Y p) ((fderiv ℝ τ p).smulRight (reeb H x) v +
          fderiv ℝ h p v)) • Y p := by
    intro v
    have hW' := hPY.congr_of_eventuallyEq hev
    rw [hW'.fderiv]
    simp [hr]
  have hWp : endW H u cylEnd p = r • Y p := (hrep s (by linarith) t).2.2.2
  -- tangency: `ω₀(x(τ), h) ≡ 0`
  have hz := KAo.omegaL.hasFDerivAt_of_bilinear hxτ hhd'.hasFDerivAt
  have hz0 : HasFDerivAt (fun q => KAo.omegaL (P.x (τ q)) (h q)) (0 : ℝ × ℝ →L[ℝ] ℝ) p := by
    refine (hasFDerivAt_const (0 : ℝ) p).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with q hq
    have := (hrep q.1 hq.le q.2).2.2.1.1
    rw [KAo.omegaL_apply]; unfold liouville at this; linarith
  have htan : ∀ v, omega0 x (fderiv ℝ h p v) + fderiv ℝ τ p v * omega0 (reeb H x) (h p) = 0 := by
    intro v
    have := congrArg (fun L => L v) (hz.unique hz0)
    simpa [KAo.omegaL_apply, ka_om_smul_left] using this
  obtain ⟨-, hR1, -, -⟩ := ka_reeb_spec H hH x (P.mem _)
  have hxR : omega0 x (reeb H x) = 2 := by unfold liouville at hR1; linarith
  -- the key estimate
  have key : ∀ v : ℝ × ℝ, ‖v‖ ≤ 1 →
      |liouville (endW H u cylEnd p) (fderiv ℝ (endW H u cylEnd) p v) - fderiv ℝ τ p v| ≤
        K₀ * ‖h p‖ := by
    intro v hv
    have hk : ‖fderiv ℝ h p v‖ ≤ 1 :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [norm_nonneg v])
    have hexp : liouville (endW H u cylEnd p) (fderiv ℝ (endW H u cylEnd) p v) -
          fderiv ℝ τ p v =
        (r ^ 2 - 1) * fderiv ℝ τ p v + r ^ 2 * fderiv ℝ τ p v * omega0 (h p) (reeb H x) +
          r ^ 2 * omega0 (h p) (fderiv ℝ h p v) / 2 := by
      rw [hWder, hWp, hYp]
      unfold liouville
      have ht := htan v
      rw [ka_om_anti (reeb H x) (h p)] at ht
      simp only [ka_om_add_left, ka_om_add_right, ka_om_smul_left, ka_om_smul_right,
        ka_om_self, hxR]
      rw [ka_om_anti (h p) x]
      linear_combination (r ^ 2 / 2) * ht
    rw [hexp]
    have hσv := hσ v hv
    have b1 : |omega0 (h p) (reeb H x)| ≤ W0 * ‖h p‖ * M :=
      (kad_abs_omega0_le _ _).trans (mul_le_mul_of_nonneg_left (hR _) (by positivity))
    have b2 : |omega0 (h p) (fderiv ℝ h p v)| ≤ W0 * ‖h p‖ * 1 :=
      (kad_abs_omega0_le _ _).trans (mul_le_mul_of_nonneg_left hk (by positivity))
    have hr2 : r ^ 2 ≤ D ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg r) hrD 2
    have hr1' : |r + 1| ≤ D + 1 := (abs_add_le r 1).trans (by simp; linarith)
    have hnh := norm_nonneg (h p)
    calc _ ≤ |(r ^ 2 - 1) * fderiv ℝ τ p v| +
          |r ^ 2 * fderiv ℝ τ p v * omega0 (h p) (reeb H x)| +
          |r ^ 2 * omega0 (h p) (fderiv ℝ h p v) / 2| := abs_add_three _ _ _
      _ = |r - 1| * |r + 1| * |fderiv ℝ τ p v| +
          r ^ 2 * |fderiv ℝ τ p v| * |omega0 (h p) (reeb H x)| +
          r ^ 2 * |omega0 (h p) (fderiv ℝ h p v)| / 2 := by
        rw [show r ^ 2 - 1 = (r - 1) * (r + 1) by ring]
        simp only [abs_mul, abs_div, abs_pow, sq_abs, abs_two]
      _ ≤ (D * ‖h p‖) * (D + 1) * (1 + P.T) + D ^ 2 * (1 + P.T) * (W0 * ‖h p‖ * M) +
          D ^ 2 * (W0 * ‖h p‖ * 1) / 2 := by
        gcongr
      _ = K₀ * ‖h p‖ := by rw [hK₀]; ring
  -- assemble
  obtain ⟨hAd, -, hA10, hA01⟩ := fderiv_endA_eq_liouville_endW H hH J hJ u hu.2.2.1 hu.2.1
    (show 0 < s by linarith) t
  have hFder : ∀ v : ℝ × ℝ,
      fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1) p v =
        fderiv ℝ (endA H u cylEnd) p v - ε * P.T * v.1 := by
    intro v
    have hd : HasFDerivAt (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1)
        (fderiv ℝ (endA H u cylEnd) p - (ε * P.T) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
      hAd.hasFDerivAt.sub ((hasFDerivAt_fst).const_mul (ε * P.T))
    rw [hd.fderiv]; simp
  have n10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp
  have n01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp
  have k1 := key (0, 1) n01
  have k2 := key (1, 0) n10
  rw [hFder, hFder, hGder, hGder, hA10, hA01]
  have e2 : -liouville (endW H u cylEnd p) (fderiv ℝ (endW H u cylEnd) p (1, 0)) -
      ε * P.T * (0 : ℝ) + (fderiv ℝ τ p (1, 0) - ε * P.T * (0 : ℝ)) =
      -(liouville (endW H u cylEnd p) (fderiv ℝ (endW H u cylEnd) p (1, 0)) -
        fderiv ℝ τ p (1, 0)) := by ring
  have e1 : liouville (endW H u cylEnd p) (fderiv ℝ (endW H u cylEnd) p (0, 1)) -
      ε * P.T * (1 : ℝ) - (fderiv ℝ τ p (0, 1) - ε * P.T * (1 : ℝ)) =
      liouville (endW H u cylEnd p) (fderiv ℝ (endW H u cylEnd) p (0, 1)) -
        fderiv ℝ τ p (0, 1) := by ring
  rw [e1, e2, abs_neg]
  have := norm_nonneg (fderiv ℝ h p)
  nlinarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₀ : ℝ)
    (hθs : ∃ s₂ : ℝ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t)‖ ≤ η)
    (hh : TendstoZeroCInfty h)
    (hrep : ∀ s ≥ s₀, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t))) :
    ∃ K s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1) (s, t) (1, 0) -
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t) (0, 1)| +
        |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1) (s, t) (0, 1) +
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2) (s, t) (1, 0)| ≤
        K * (‖h (s, t)‖ + ‖fderiv ℝ h (s, t)‖) :=
  FiniteEnergyPlane.exists_dbar_bound_tubeTangent_of_drift_aux H hH J hJ u hu P ε hε τ h s₀ hθs hθ hh hrep
