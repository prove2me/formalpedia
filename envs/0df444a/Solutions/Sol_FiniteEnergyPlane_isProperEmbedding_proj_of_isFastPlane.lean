-- Prove2me | solution 1 for FiniteEnergyPlane.isProperEmbedding_proj_of_isFastPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T19:51:45.934438+00:00
-- url     : https://prove2.me/submissions/e41ceee2-2cb2-4df2-aea6-c027eb2482ac

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Topology.DerivedSet
import Theorems.Thm_FiniteEnergyPlane_exists_holomorphic_eqOn_of_accPt_intersection
import Theorems.Thm_FiniteEnergyPlane_exists_intersection_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_immersion_transverse
import Theorems.Thm_FiniteEnergyPlane_exists_eq_of_proj_eq_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_isBounded_preimage_proj_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_shiftA

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

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem proj_aCoord_exp_smul_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (c : ℝ) (y : V n) (hy : y ≠ 0) :
    proj H (Real.exp (2 * c) • y) = proj H y ∧ aCoord H (Real.exp (2 * c) • y) = aCoord H y + c := by
  have hc := Real.exp_pos (2 * c)
  obtain ⟨hr, hr1⟩ := ka_scale_spec H hH y hy
  have h2 : scaleToS H (Real.exp (2 * c) • y) = scaleToS H y / Real.exp (2 * c) := by
    apply ka_scale_unique H hH _ (smul_ne_zero hc.ne' hy) _ (div_pos hr hc)
    rw [smul_smul, div_mul_cancel₀ _ hc.ne']
    exact hr1
  refine ⟨?_, ?_⟩
  · unfold proj
    rw [h2, smul_smul, div_mul_cancel₀ _ hc.ne']
  · unfold aCoord
    rw [h2, Real.log_div hr.ne' hc.ne', Real.log_exp]
    ring

theorem eq_of_aCoord_eq_of_proj_eq_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {x y : V n} (hx : x ≠ 0) (hy : y ≠ 0) (ha : aCoord H x = aCoord H y)
    (hp : proj H x = proj H y) : x = y := by
  have hrx := (ka_scale_spec H hH x hx).1
  have hry := (ka_scale_spec H hH y hy).1
  have hlog : Real.log (scaleToS H x) = Real.log (scaleToS H y) := by
    unfold aCoord at ha
    linarith
  have hs : scaleToS H x = scaleToS H y := Real.log_injOn_pos hrx hry hlog
  unfold proj at hp
  rw [hs] at hp
  exact smul_right_injective _ hry.ne' hp

theorem continuous_aCoord_proj_comp_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u : ℂ → V n) (hu0 : ∀ z, u z ≠ 0) (huc : Continuous u) :
    Continuous (fun z => aCoord H (u z)) ∧ Continuous (fun z => proj H (u z)) := by
  have hs : Continuous (fun z => scaleToS H (u z)) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact ContinuousAt.comp (f := u) (ka_scale_contDiffAt H hH (u z) (hu0 z)).continuousAt
      huc.continuousAt
  constructor
  · unfold aCoord
    exact ((hs.log (fun z => (ka_scale_spec H hH _ (hu0 z)).1.ne')).neg).div_const 2
  · unfold proj
    exact hs.smul huc

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem injOn_ball_of_hasStrictFDerivAt_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F}
    {x : E} (hf : HasStrictFDerivAt f f' x) (hi : Function.Injective f') :
    ∃ δ > 0, Set.InjOn f (Metric.ball x δ) := by
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith (𝕜 := ℝ) (f' : E →ₗ[ℝ] F)
    (LinearMap.ker_eq_bot.mpr hi)
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hlow : ∀ v : E, ‖v‖ ≤ K * ‖f' v‖ := by
    intro v
    have := hanti.le_mul_dist v 0
    simpa [dist_zero_right] using this
  have hc : (0 : ℝ) < 1 / (2 * K) := by positivity
  have hev := (hasStrictFDerivAt_iff_isLittleO.mp hf).def hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨δ, hδ, fun a ha b hb hab => ?_⟩
  have hmem : ((a, b) : E × E) ∈ Metric.ball ((x, x) : E × E) δ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp ha) (Metric.mem_ball.mp hb)
  have h1 := hball _ hmem
  simp only [hab, sub_self, zero_sub, norm_neg] at h1
  have h2 := hlow (a - b)
  have h3 : K * ‖f' (a - b)‖ ≤ K * (1 / (2 * K) * ‖a - b‖) :=
    mul_le_mul_of_nonneg_left h1 hK'.le
  have h4 : K * (1 / (2 * K) * ‖a - b‖) = ‖a - b‖ / 2 := by
    field_simp
  have h5 : ‖a - b‖ ≤ 0 := by
    have := norm_nonneg (a - b)
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h5)

end FiniteEnergyPlane

/-!
# Lemma 6.22 glue, part 1: a bounded, closed intersection set has only isolated points

`u, v` are immersed finite-energy curves on `ℂ`. If the intersection pairs inside an open set `O`
form a bounded closed set `A`, then every pair in `A` is isolated: the first projection of the
derived set of `A` is open (McDuff, Lemma 2.7: near a non-isolated pair, `u = v ∘ φ`), closed
(compact), bounded, hence empty.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem pe_isolated (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u v : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hv : IsFiniteEnergyCurve H J Set.univ v)
    (hui : ∀ z, Function.Injective (fderiv ℝ u z)) (hvi : ∀ w, Function.Injective (fderiv ℝ v w))
    (O : Set (ℂ × ℂ)) (hO : IsOpen O)
    (hcl : IsClosed {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2})
    (hbd : Bornology.IsBounded {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2})
    (p : ℂ × ℂ) (hp : p ∈ O) (hpe : u p.1 = v p.2) :
    ∃ ε > 0, ∀ z ∈ ball p.1 ε, ∀ w ∈ ball p.2 ε, u z = v w → z = p.1 ∧ w = p.2 := by
  set A : Set (ℂ × ℂ) := {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2} with hAdef
  have hDsub : derivedSet A ⊆ A := (derivedSet_subset_closure A).trans hcl.closure_subset
  have hDc : IsCompact (derivedSet A) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_derivedSet A) (hbd.subset hDsub)
  set D : Set ℂ := Prod.fst '' derivedSet A with hDdef
  have hDcomp : IsCompact D := hDc.image continuous_fst
  -- `D` is open
  have hDopen : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨q, hq, rfl⟩
    have hqA : q ∈ A := hDsub hq
    -- a sequence of other intersection pairs converging to `q`
    have hcl' : q ∈ closure (A \ {q}) := by
      have := (accPt_principal_iff_clusterPt.1 hq)
      exact mem_closure_iff_clusterPt.2 this
    obtain ⟨s, hsA, hs⟩ := mem_closure_iff_seq_limit.1 hcl'
    have hs1 : Tendsto (fun k => (s k).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hs
    have hs2 : Tendsto (fun k => (s k).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hs
    have hne : ∀ k, ((s k).1, (s k).2) ≠ (q.1, q.2) := fun k h => (hsA k).2 (by
      simpa using h)
    have heq : ∀ k, u (s k).1 = v (s k).2 := fun k => (hsA k).1.2
    obtain ⟨ε, hε, φ, hφd, hφ0, -, -, hEq⟩ :=
      exists_holomorphic_eqOn_of_accPt_intersection H hH J hJ Set.univ Set.univ isOpen_univ
        isOpen_univ u v hu hv (fun z _ => hui z) (fun w _ => hvi w) q.1 q.2 trivial trivial
        (fun k => (s k).1) (fun k => (s k).2) hs1 hs2 hne heq
    set g : ℂ → ℂ × ℂ := fun z => (z, φ z) with hg
    have hφc : ∀ z ∈ ball q.1 ε, ContinuousAt φ z := fun z hz =>
      (hφd.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
    have hgc : ∀ z ∈ ball q.1 ε, ContinuousAt g z := fun z hz =>
      continuousAt_id.prodMk (hφc z hz)
    have hgq : g q.1 = q := by simp [hg, hφ0]
    have hev : ∀ᶠ z in 𝓝 q.1, z ∈ ball q.1 ε ∧ g z ∈ O := by
      refine Filter.Eventually.and (isOpen_ball.mem_nhds (mem_ball_self hε) :
        ∀ᶠ z in 𝓝 q.1, z ∈ ball q.1 ε) ?_
      have : O ∈ 𝓝 (g q.1) := by rw [hgq]; exact hO.mem_nhds hqA.1
      exact (hgc q.1 (mem_ball_self hε)) this
    have hev2 := eventually_eventually_nhds.2 hev
    filter_upwards [hev2, hev] with z hz hz0
    refine ⟨g z, ?_, rfl⟩
    rw [derivedSet, Set.mem_setOf_eq, accPt_iff_nhds]
    intro U hU
    have h1 : ∀ᶠ z' in 𝓝 z, g z' ∈ U := (hgc z hz0.1) hU
    obtain ⟨z', ⟨hz'U, hz'b, hz'O⟩, hz'ne⟩ :=
      (((h1.and hz).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists
        (f := 𝓝[≠] z)
    refine ⟨g z', ⟨hz'U, hz'O, ?_⟩, ?_⟩
    · exact hEq hz'b
    · intro h
      exact hz'ne (congrArg Prod.fst h)
  have hDempty : D = ∅ := by
    rcases isClopen_iff.1 ⟨hDcomp.isClosed, hDopen⟩ with h | h
    · exact h
    · exact absurd (h ▸ hDcomp) (noncompact_univ ℂ)
  have hpA : p ∈ A := ⟨hp, hpe⟩
  have hnacc : ¬ AccPt p (𝓟 A) := fun h => by
    have : p.1 ∈ D := ⟨p, h, rfl⟩
    rw [hDempty] at this
    exact this
  rw [accPt_iff_nhds] at hnacc
  push_neg at hnacc
  obtain ⟨U, hU, hUA⟩ := hnacc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU (hO.mem_nhds hp))
  refine ⟨ε, hε, fun z hz w hw hzw => ?_⟩
  have hmem : (z, w) ∈ ball p ε := by
    rw [← ball_prod_same]; exact ⟨hz, hw⟩
  have h2 := hball hmem
  have := hUA (z, w) ⟨h2.1, h2.2, hzw⟩
  rw [← this]
  exact ⟨rfl, rfl⟩

end FiniteEnergyPlane

/-!
# Hryniewicz Lemma 6.22 (`isProperEmbedding_proj_of_isFastPlane`): glue

HWZ95 Theorem 2.3 route with the translations `shiftA τ u`:
* far from `0`, `proj ∘ u` takes no value twice (child `exists_eq_of_proj_eq_of_isFastPlane`), so
  every intersection of `u` with `shiftA τ u`, `τ ≠ 0`, lies in a fixed compact set;
* such intersections are isolated (`pe_isolated`, via McDuff Lemma 2.7);
* the set of `τ > 0` with an intersection is bounded, contains its supremum (compactness) and is
  open to the right of it (persistence of isolated intersections), hence empty;
* a self-intersection `u z = u w`, `z ≠ w`, is isolated as well, and persists to small `τ ≠ 0`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem pe_shiftA_zero {n : ℕ} (u : ℂ → V n) : shiftA 0 u = u := by
  funext z; simp [shiftA]

theorem pe_fderiv_shiftA_inj {n : ℕ} (u : ℂ → V n) (hu : ContDiff ℝ ∞ u) (c : ℝ) (z : ℂ)
    (h : Function.Injective (fderiv ℝ u z)) : Function.Injective (fderiv ℝ (shiftA c u) z) := by
  have e : shiftA c u = Real.exp (2 * c) • u := rfl
  rw [e, fderiv_const_smul (hu.differentiable (by simp) z)]
  intro a b hab
  simp only [ContinuousLinearMap.smul_apply] at hab
  exact h ((smul_right_injective _ (Real.exp_pos _).ne') hab)

theorem pe_main (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hmiss : ∀ z, proj H (u z) ∉ Set.range P.x) :
    Function.Injective (proj H ∘ u) ∧
      (∀ z, Function.Injective (fderiv ℝ (proj H ∘ u) z)) ∧
      ∀ K : Set (V 1), IsCompact K → Disjoint K (Set.range P.x) →
        Bornology.IsBounded ((proj H ∘ u) ⁻¹' K) := by
  have hfc := hu.1
  have hsm : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfc.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfc.2.1 z trivial
  have hcont : Continuous u := hsm.continuous
  have hsh : ∀ c, IsFiniteEnergyCurve H J Set.univ (shiftA c u) := fun c =>
    (isFastPlane_shiftA H hH J hJ u hu c).1
  -- immersions
  have himm : ∀ z, Function.Injective (fderiv ℝ (proj H ∘ u) z) := by
    intro z a b hab
    by_contra hne
    have := isFastPlane_immersion_transverse H hH J hJ u hu z (a - b) (sub_ne_zero.2 hne) 0
    apply this
    rw [zero_smul, map_sub]
    exact sub_eq_zero.2 hab
  have hui : ∀ z, Function.Injective (fderiv ℝ u z) := by
    intro z
    have hd : DifferentiableAt ℝ u z := hsm.differentiable (by simp) z
    have hc : fderiv ℝ (proj H ∘ u) z = (fderiv ℝ (proj H) (u z)).comp (fderiv ℝ u z) :=
      fderiv_comp z (ka_proj_differentiableAt H hH (hu0 z)) hd
    have := himm z
    rw [hc, ContinuousLinearMap.coe_comp'] at this
    exact this.of_comp
  have hshi : ∀ c z, Function.Injective (fderiv ℝ (shiftA c u) z) := fun c z =>
    pe_fderiv_shiftA_inj u hsm c z (hui z)
  -- two points on one ray
  have hray : ∀ z w, proj H (u z) = proj H (u w) →
      u z = shiftA (aCoord H (u z) - aCoord H (u w)) u w := by
    intro z w h
    have e1 := emb_exp_aCoord_smul_proj H hH (u z) (hu0 z)
    have e2 := emb_exp_aCoord_smul_proj H hH (u w) (hu0 w)
    have : Real.exp (2 * (aCoord H (u z) - aCoord H (u w))) • u w =
        Real.exp (2 * (aCoord H (u z) - aCoord H (u w))) •
          (Real.exp (2 * aCoord H (u w)) • proj H (u w)) := by rw [e2]
    rw [smul_smul, ← Real.exp_add, ← h,
      show 2 * (aCoord H (u z) - aCoord H (u w)) + 2 * aCoord H (u w) = 2 * aCoord H (u z) by ring,
      e1] at this
    exact this.symm
  -- far from `0`, no repeated values of `proj ∘ u`
  obtain ⟨R, hR⟩ := exists_eq_of_proj_eq_of_isFastPlane H hH J hJ P u hu huP hmiss
  have hB : ∀ z w, z ≠ w → proj H (u z) = proj H (u w) → ‖z‖ < R ∧ ‖w‖ < R := by
    intro z w hne h
    constructor
    · by_contra hc; push_neg at hc; exact hne (hR z w hc h)
    · by_contra hc; push_neg at hc; exact hne (hR w z hc h.symm).symm
  set KK : Set (ℂ × ℂ) := closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R with hKK
  have hKc : IsCompact KK := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  set A : ℝ → Set (ℂ × ℂ) := fun τ => {p : ℂ × ℂ | u p.1 = shiftA τ u p.2} with hA
  have hAsub : ∀ τ ≠ (0 : ℝ), ∀ p ∈ A τ, p ∈ KK := by
    intro τ hτ p hp
    have hp' : u p.1 = Real.exp (2 * τ) • u p.2 := hp
    have hne : p.1 ≠ p.2 := by
      intro h
      rw [h] at hp'
      have h1 : (Real.exp (2 * τ) - 1) • u p.2 = 0 := by
        rw [sub_smul, one_smul, ← hp', sub_self]
      rcases smul_eq_zero.1 h1 with h2 | h2
      · have : Real.exp (2 * τ) = 1 := by linarith
        rw [Real.exp_eq_one_iff] at this
        exact hτ (by linarith)
      · exact hu0 _ h2
    have hpp : proj H (u p.1) = proj H (u p.2) := by
      rw [hp']; exact (proj_aCoord_exp_smul_aux H hH τ (u p.2) (hu0 _)).1
    have := hB p.1 p.2 hne hpp
    exact ⟨mem_closedBall_zero_iff.2 this.1.le, mem_closedBall_zero_iff.2 this.2.le⟩
  have hAcl : ∀ τ, IsClosed (A τ) := fun τ =>
    isClosed_eq (hcont.comp continuous_fst) ((hcont.const_smul (Real.exp (2 * τ))).comp continuous_snd)
  -- isolated intersections for `τ ≠ 0`
  have hiso : ∀ τ ≠ (0 : ℝ), ∀ p ∈ A τ, ∃ ε > 0, ∀ z ∈ ball p.1 ε, ∀ w ∈ ball p.2 ε,
      u z = shiftA τ u w → z = p.1 ∧ w = p.2 := by
    intro τ hτ p hp
    have hset : {q : ℂ × ℂ | q ∈ (Set.univ : Set (ℂ × ℂ)) ∧ u q.1 = shiftA τ u q.2} = A τ := by
      ext q; simp [hA]
    exact pe_isolated H hH J hJ u (shiftA τ u) hfc (hsh τ) hui (hshi τ) Set.univ isOpen_univ
      (hset ▸ hAcl τ) (hset ▸ hKc.isBounded.subset (hAsub τ hτ)) p trivial hp
  -- persistence of an isolated intersection under `shiftA cₖ u → shiftA σ u`
  have hpers : ∀ σ : ℝ, ∀ p ∈ A σ, (∃ ε > 0, ∀ z ∈ ball p.1 ε, ∀ w ∈ ball p.2 ε,
      u z = shiftA σ u w → z = p.1 ∧ w = p.2) → ∀ c : ℕ → ℝ, Tendsto c atTop (𝓝 σ) →
      ∀ᶠ k in atTop, (A (c k)).Nonempty := by
    intro σ p hp hisoσ c hc
    have hcu : JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => shiftA 0 u) (shiftA 0 u) Set.univ :=
      tendstoCInftyLocOn_shiftA u hsm (fun _ => 0) 0 tendsto_const_nhds Set.univ
    rw [pe_shiftA_zero] at hcu
    have hcv := tendstoCInftyLocOn_shiftA u hsm c σ hc Set.univ
    obtain ⟨z, w, -, -, hev⟩ := exists_intersection_of_tendstoCInftyLocOn H hH J hJ Set.univ
      Set.univ isOpen_univ isOpen_univ u (shiftA σ u) (fun _ => u) (fun k => shiftA (c k) u)
      hfc (hsh σ) (fun z _ => hui z) (fun w _ => hshi σ w) (fun _ => hfc) (fun k => hsh (c k))
      hcu hcv p.1 p.2 trivial trivial hp hisoσ
    exact hev.mono fun k hk => ⟨(z k, w k), hk⟩
  -- no intersections with positive translations
  have hpos : ∀ τ > (0 : ℝ), A τ = ∅ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨τ₀, hτ₀, hne⟩ := hcon
    set S : Set ℝ := {τ : ℝ | 0 < τ ∧ (A τ).Nonempty} with hS
    have hτ₀S : τ₀ ∈ S := ⟨hτ₀, hne⟩
    obtain ⟨Mx, hMx⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      (f := u) hcont.continuousOn
    obtain ⟨Mi, hMi⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      (f := fun z => ‖u z‖⁻¹)
      ((hcont.norm.inv₀ (fun z => norm_ne_zero_iff.2 (hu0 z))).continuousOn)
    have hbdd : BddAbove S := by
      refine ⟨Mx * Mi, fun τ hτ => ?_⟩
      obtain ⟨hτ0', q, hq⟩ := hτ
      have hqK := hAsub τ hτ0'.ne' q hq
      have hq' : u q.1 = Real.exp (2 * τ) • u q.2 := hq
      have n1 : ‖u q.1‖ = Real.exp (2 * τ) * ‖u q.2‖ := by
        rw [hq', norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      have b1 := hMx q.1 hqK.1
      have b2 := hMi q.2 hqK.2
      rw [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))] at b2
      have hpos2 : 0 < ‖u q.2‖ := norm_pos_iff.2 (hu0 _)
      have e3 : Real.exp (2 * τ) = ‖u q.1‖ * ‖u q.2‖⁻¹ := by
        rw [n1]; field_simp
      have h4 : Real.exp (2 * τ) ≤ Mx * Mi := by
        rw [e3]
        exact mul_le_mul b1 b2 (inv_nonneg.2 (norm_nonneg _)) ((norm_nonneg _).trans b1)
      have := Real.add_one_le_exp (2 * τ)
      linarith
    obtain ⟨t, -, ht, htS⟩ := exists_seq_tendsto_sSup ⟨τ₀, hτ₀S⟩ hbdd
    set σ := sSup S with hσ
    have hσpos : 0 < σ := lt_of_lt_of_le hτ₀ (le_csSup hbdd hτ₀S)
    choose q hq using fun n => (htS n).2
    have hqK : ∀ n, q n ∈ KK := fun n => hAsub (t n) (htS n).1.ne' (q n) (hq n)
    obtain ⟨p, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq hqK
    have hpA : p ∈ A σ := by
      have h1 : Tendsto (fun n => u (q (φ n)).1) atTop (𝓝 (u p.1)) :=
        (hcont.tendsto _).comp ((continuous_fst.tendsto _).comp hlim)
      have h2 : Tendsto (fun n => Real.exp (2 * t (φ n)) • u (q (φ n)).2) atTop
          (𝓝 (Real.exp (2 * σ) • u p.2)) :=
        ((Real.continuous_exp.tendsto _).comp
          (tendsto_const_nhds.mul (ht.comp hφ.tendsto_atTop))).smul
          ((hcont.tendsto _).comp ((continuous_snd.tendsto _).comp hlim))
      exact tendsto_nhds_unique h1 (Tendsto.congr (fun n => (hq (φ n)).symm) h2)
    have hev := hpers σ p hpA (hiso σ hσpos.ne' p hpA) (fun k : ℕ => σ + 1 / ((k : ℝ) + 1)) (by
      have := (tendsto_const_nhds (x := σ)).add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at this; exact this)
    obtain ⟨k, hk⟩ := hev.exists
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hkS : σ + 1 / ((k : ℝ) + 1) ∈ S := ⟨by linarith, hk⟩
    have := le_csSup hbdd hkS
    linarith
  have hnz : ∀ τ ≠ (0 : ℝ), A τ = ∅ := by
    intro τ hτ
    rcases lt_or_gt_of_ne hτ with h | h
    · ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hp
      have hp' : u p.1 = Real.exp (2 * τ) • u p.2 := hp
      have hsw : (p.2, p.1) ∈ A (-τ) := by
        show u p.2 = Real.exp (2 * -τ) • u p.1
        rw [hp', smul_smul, ← Real.exp_add, show 2 * -τ + 2 * τ = 0 by ring, Real.exp_zero,
          one_smul]
      rw [hpos (-τ) (by linarith)] at hsw
      exact hsw
    · exact hpos τ h
  -- no self-intersections
  have hself : ∀ z w, u z = u w → z = w := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₀, w₀, he, hne⟩ := hcon
    set O : Set (ℂ × ℂ) := {p | p.1 ≠ p.2} with hO
    have hOo : IsOpen O := isOpen_ne_fun continuous_fst continuous_snd
    have hBK : {p : ℂ × ℂ | p ∈ O ∧ u p.1 = u p.2} ⊆ KK := fun p hp => by
      have := hB p.1 p.2 hp.1 (by rw [hp.2])
      exact ⟨mem_closedBall_zero_iff.2 this.1.le, mem_closedBall_zero_iff.2 this.2.le⟩
    have hBcl : IsClosed {p : ℂ × ℂ | p ∈ O ∧ u p.1 = u p.2} := by
      rw [← closure_subset_iff_isClosed]
      intro p hp
      obtain ⟨s, hsB, hs⟩ := mem_closure_iff_seq_limit.1 hp
      have h1 := (continuous_fst.tendsto p).comp hs
      have h2 := (continuous_snd.tendsto p).comp hs
      have heq : u p.1 = u p.2 := tendsto_nhds_unique ((hcont.tendsto _).comp h1)
        (Tendsto.congr (fun k => ((hsB k).2).symm) ((hcont.tendsto _).comp h2))
      refine ⟨?_, heq⟩
      intro hpp
      obtain ⟨δ, hδ, hinj⟩ :=
        injOn_ball_of_hasStrictFDerivAt_aux (hsm.contDiffAt.hasStrictFDerivAt (by simp)) (hui p.1)
      have e1 : ∀ᶠ k in atTop, (s k).1 ∈ ball p.1 δ := h1 (ball_mem_nhds _ hδ)
      have e2 : ∀ᶠ k in atTop, (s k).2 ∈ ball p.1 δ :=
        h2 (by rw [← hpp]; exact ball_mem_nhds _ hδ)
      obtain ⟨k, hk1, hk2⟩ := (e1.and e2).exists
      exact (hsB k).1 (hinj hk1 hk2 (hsB k).2)
    obtain ⟨ε, hε, hisoε⟩ := pe_isolated H hH J hJ u u hfc hfc hui hui O hOo hBcl
      (hKc.isBounded.subset hBK) (z₀, w₀) hne he
    have hp' : (z₀, w₀) ∈ A 0 := by
      show u z₀ = shiftA 0 u w₀
      rw [pe_shiftA_zero]; exact he
    have hiso0 : ∃ ε > 0, ∀ z ∈ ball (z₀, w₀).1 ε, ∀ w ∈ ball (z₀, w₀).2 ε,
        u z = shiftA 0 u w → z = (z₀, w₀).1 ∧ w = (z₀, w₀).2 :=
      ⟨ε, hε, by rw [pe_shiftA_zero]; exact hisoε⟩
    have hev := hpers 0 (z₀, w₀) hp' hiso0 (fun k : ℕ => 1 / ((k : ℝ) + 1))
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨k, hk⟩ := hev.exists
    have := hnz (1 / ((k : ℝ) + 1)) (by positivity)
    rw [this] at hk
    exact Set.not_nonempty_empty hk
  have hinj : Function.Injective (proj H ∘ u) := by
    intro z w h
    have h' : proj H (u z) = proj H (u w) := h
    have hr := hray z w h'
    by_cases hτ : aCoord H (u z) - aCoord H (u w) = 0
    · rw [hτ, pe_shiftA_zero] at hr
      exact hself z w hr
    · have hmem : (z, w) ∈ A (aCoord H (u z) - aCoord H (u w)) := hr
      rw [hnz _ hτ] at hmem
      exact hmem.elim
  exact ⟨hinj, himm, fun K hK hKP =>
    isBounded_preimage_proj_of_isNondegenerateEnd H hH P u huP K hK hKP⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hmiss : ∀ z, proj H (u z) ∉ Set.range P.x) :
    Function.Injective (proj H ∘ u) ∧
      (∀ z, Function.Injective (fderiv ℝ (proj H ∘ u) z)) ∧
      ∀ K : Set (V 1), IsCompact K → Disjoint K (Set.range P.x) →
        Bornology.IsBounded ((proj H ∘ u) ⁻¹' K) :=
  pe_main H hH J hJ P u hu huP hmiss
