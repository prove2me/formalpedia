-- Prove2me | solution 1 for FiniteEnergyPlane.range_eq_or_disjoint_of_isFastPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T23:17:51.240317+00:00
-- url     : https://prove2.me/submissions/734db38f-1f7f-4571-84aa-d24c3e290f9c

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_holomorphic_eqOn_of_accPt_intersection
import Theorems.Thm_FiniteEnergyPlane_exists_intersection_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
import Theorems.Thm_FiniteEnergyPlane_isBounded_preimage_proj_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_shiftA
import Theorems.Thm_FiniteEnergyPlane_forall_ne_shiftA_of_forall_norm_lt
import Theorems.Thm_FiniteEnergyPlane_exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane

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

/-!
# Hryniewicz Lemma 6.23 (`range_eq_or_disjoint_of_isFastPlane`): glue

HWZ95 Theorem 4.11 route with the translations `τ · v = shiftA τ v`:
* far bound (child): intersections `u z = (τ · v) w` with `|τ - τ₀| ≥ ε` stay in a ball;
* hence (child) `u` meets no `τ · v` with `τ > τ₀`, and, swapping `u, v`, none with `τ < τ₀`;
* if `u` meets `τ₀ · v`, every intersection is non-isolated (an isolated one persists to nearby
  translations), so by McDuff Lemma 2.7 the sets `{z | ∃ w, u z = (τ₀ · v) w}` and
  `{w | ∃ z, …}` are open; they are closed by properness of `proj ∘ u`, `proj ∘ v` off `x(ℝ)`,
  hence all of `ℂ`, and the images agree;
* otherwise `u` meets no translate of `v`, i.e. the images are disjoint.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem rd_shiftA_zero {n : ℕ} (u : ℂ → V n) : shiftA 0 u = u := by
  funext z; simp [shiftA]

theorem rd_fderiv_shiftA_inj {n : ℕ} (u : ℂ → V n) (hu : ContDiff ℝ ∞ u) (c : ℝ) (z : ℂ)
    (h : Function.Injective (fderiv ℝ u z)) : Function.Injective (fderiv ℝ (shiftA c u) z) := by
  have e : shiftA c u = Real.exp (2 * c) • u := rfl
  rw [e, fderiv_const_smul (hu.differentiable (by simp) z)]
  intro a b hab
  simp only [ContinuousLinearMap.smul_apply] at hab
  exact h ((smul_right_injective _ (Real.exp_pos _).ne') hab)

theorem rd_swap {n : ℕ} {f g : ℂ → V n} {τ : ℝ} {z w : ℂ} (h : f z = shiftA τ g w) :
    g w = shiftA (-τ) f z := by
  show g w = Real.exp (2 * -τ) • f z
  rw [h]
  simp only [shiftA]
  rw [smul_smul, ← Real.exp_add, show 2 * -τ + 2 * τ = 0 by ring, Real.exp_zero, one_smul]

/-- Clopen argument: if every intersection of `f, g` is non-isolated and `g`-preimages of
bounded sets of intersections are bounded, one intersection forces `f(ℂ) ⊆ g(ℂ)`. -/
theorem rd_clopen (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (f g : ℂ → V 1)
    (hf : IsFiniteEnergyCurve H J Set.univ f) (hg : IsFiniteEnergyCurve H J Set.univ g)
    (hfi : ∀ z, Function.Injective (fderiv ℝ f z)) (hgi : ∀ w, Function.Injective (fderiv ℝ g w))
    (hnon : ∀ z w, f z = g w → ∀ ε > 0, ∃ z' ∈ ball z ε, ∃ w' ∈ ball w ε,
      f z' = g w' ∧ (z', w') ≠ (z, w))
    (hbd : ∀ R : ℝ, ∃ R' : ℝ, ∀ z w, ‖z‖ ≤ R → f z = g w → ‖w‖ ≤ R')
    (h0 : ∃ z w, f z = g w) : ∀ z, ∃ w, f z = g w := by
  set D : Set ℂ := {z | ∃ w, f z = g w} with hDdef
  have hfc : Continuous f := (contDiffOn_univ.1 hf.1).continuous
  have hgc : Continuous g := (contDiffOn_univ.1 hg.1).continuous
  have hopen : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨w, hzw⟩
    choose z' hz' w' hw' heq hne using fun k : ℕ =>
      hnon z w hzw (1 / ((k : ℝ) + 1)) (by positivity)
    have hlim : ∀ (a : ℂ) (b : ℕ → ℂ), (∀ k : ℕ, b k ∈ ball a (1 / ((k : ℝ) + 1))) →
        Tendsto b atTop (𝓝 a) := by
      intro a b hb
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
      refine ⟨N, fun k hk => lt_of_lt_of_le (mem_ball.1 (hb k)) ?_⟩
      have : ((N : ℝ) + 1) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk
      exact le_trans (one_div_le_one_div_of_le (by positivity) this) hN.le
    obtain ⟨ε, hε, φ, -, -, -, -, hEq⟩ :=
      exists_holomorphic_eqOn_of_accPt_intersection H hH J hJ Set.univ Set.univ isOpen_univ
        isOpen_univ f g hf hg (fun z _ => hfi z) (fun w _ => hgi w) z w trivial trivial z' w'
        (hlim z z' hz') (hlim w w' hw') hne heq
    exact Filter.mem_of_superset (ball_mem_nhds z hε) fun y hy => ⟨φ y, hEq hy⟩
  have hclosed : IsClosed D := by
    refine isClosed_of_closure_subset fun z hz => ?_
    obtain ⟨zs, hzsD, hzs⟩ := mem_closure_iff_seq_limit.1 hz
    choose ws hws using hzsD
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto zs hzs)
    obtain ⟨R', hR'⟩ := hbd R
    have hwsb : ∀ k, ws k ∈ closedBall (0 : ℂ) R' := fun k =>
      mem_closedBall_zero_iff.2 (hR' _ _ (hR _ ⟨k, rfl⟩) (hws k))
    obtain ⟨w, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) R').tendsto_subseq hwsb
    refine ⟨w, tendsto_nhds_unique ((hfc.tendsto z).comp (hzs.comp hφ.tendsto_atTop)) ?_⟩
    exact Tendsto.congr (fun k => (hws (φ k)).symm) ((hgc.tendsto w).comp hlim)
  obtain ⟨z₀, w₀, h₀⟩ := h0
  have hD : D = Set.univ :=
    (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨z₀, w₀, h₀⟩)
  intro z
  have : z ∈ D := hD ▸ Set.mem_univ z
  exact this

/-- Properness off the orbit: intersections `f z = e^{2c} g w` with `z` bounded have `w`
bounded. -/
theorem rd_bound (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (f g : ℂ → V 1) (hf0 : ∀ z, f z ≠ 0) (hg0 : ∀ w, g w ≠ 0) (hfc : Continuous f)
    (hgP : IsNondegenerateEnd H g cylInf P 1) (hfmiss : ∀ z, proj H (f z) ∉ Set.range P.x)
    (c : ℝ) (R : ℝ) : ∃ R' : ℝ, ∀ z w, ‖z‖ ≤ R → f z = shiftA c g w → ‖w‖ ≤ R' := by
  set K : Set (V 1) := (proj H ∘ f) '' closedBall (0 : ℂ) R with hK
  have hpc : Continuous (proj H ∘ f) := (continuous_aCoord_proj_comp_aux H hH f hf0 hfc).2
  have hKc : IsCompact K := (isCompact_closedBall _ _).image hpc
  have hKP : Disjoint K (Set.range P.x) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, -, rfl⟩
    exact hfmiss z
  obtain ⟨R', hR'⟩ := isBounded_iff_forall_norm_le.1
    (isBounded_preimage_proj_of_isNondegenerateEnd H hH P g hgP K hKc hKP)
  refine ⟨R', fun z w hz h => hR' w ?_⟩
  show proj H (g w) ∈ K
  refine ⟨z, mem_closedBall_zero_iff.2 hz, ?_⟩
  show proj H (f z) = proj H (g w)
  rw [h]
  exact (proj_aCoord_exp_smul_aux H hH c (g w) (hg0 w)).1

theorem rd_main (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1) (hve : IsEmbeddedPlane v)
    (humiss : ∀ z, proj H (u z) ∉ Set.range P.x) (hvmiss : ∀ z, proj H (v z) ∉ Set.range P.x) :
    Set.range (proj H ∘ u) = Set.range (proj H ∘ v) ∨
      Disjoint (Set.range (proj H ∘ u)) (Set.range (proj H ∘ v)) := by
  have hfu := hu.1
  have hfv := hv.1
  have hsu : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfu.1
  have hsv : ContDiff ℝ ∞ v := contDiffOn_univ.1 hfv.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfu.2.1 z trivial
  have hv0 : ∀ z, v z ≠ 0 := fun z => hfv.2.1 z trivial
  have hcu : Continuous u := hsu.continuous
  have hcv : Continuous v := hsv.continuous
  have hui := hue.2
  have hvi := hve.2
  obtain ⟨τ₀, hF⟩ :=
    exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane H hH J hJ P u v hu huP hv hvP humiss hvmiss
  have hpos := forall_ne_shiftA_of_forall_norm_lt H hH J hJ u v hu hv hui hvi τ₀ hF
  have hF' : ∀ ε > 0, ∃ R : ℝ, ∀ (τ : ℝ) (w z : ℂ), v w = shiftA τ u z → ε ≤ |τ - -τ₀| →
      ‖w‖ < R ∧ ‖z‖ < R := by
    intro ε hε
    obtain ⟨R, hR⟩ := hF ε hε
    refine ⟨R, fun τ w z h hτ => ?_⟩
    have h' : u z = shiftA (-τ) v w := rd_swap h
    have := hR (-τ) z w h' (by rwa [show -τ - τ₀ = -(τ - -τ₀) by ring, abs_neg])
    exact ⟨this.2, this.1⟩
  have hneg := forall_ne_shiftA_of_forall_norm_lt H hH J hJ v u hv hu hvi hui (-τ₀) hF'
  have hne : ∀ τ ≠ τ₀, ∀ z w, u z ≠ shiftA τ v w := by
    intro τ hτ z w h
    rcases lt_or_gt_of_ne hτ with hl | hl
    · exact hneg (-τ) (by linarith) w z (rd_swap h)
    · exact hpos τ hl z w h
  have hray : ∀ z w, proj H (u z) = proj H (v w) →
      u z = shiftA (aCoord H (u z) - aCoord H (v w)) v w := by
    intro z w h
    have e1 := emb_exp_aCoord_smul_proj H hH (u z) (hu0 z)
    have e2 := emb_exp_aCoord_smul_proj H hH (v w) (hv0 w)
    have : Real.exp (2 * (aCoord H (u z) - aCoord H (v w))) • v w =
        Real.exp (2 * (aCoord H (u z) - aCoord H (v w))) •
          (Real.exp (2 * aCoord H (v w)) • proj H (v w)) := by rw [e2]
    rw [smul_smul, ← Real.exp_add, ← h,
      show 2 * (aCoord H (u z) - aCoord H (v w)) + 2 * aCoord H (v w) = 2 * aCoord H (u z) by ring,
      e1] at this
    exact this.symm
  by_cases hA : ∃ z w, u z = shiftA τ₀ v w
  · left
    set V' : ℂ → V 1 := shiftA τ₀ v with hV'
    have hfV : IsFiniteEnergyCurve H J Set.univ V' := (isFastPlane_shiftA H hH J hJ v hv τ₀).1
    have hVi : ∀ w, Function.Injective (fderiv ℝ V' w) := fun w =>
      rd_fderiv_shiftA_inj v hsv τ₀ w (hvi w)
    have hV0 : ∀ w, V' w ≠ 0 := fun w => hfV.2.1 w trivial
    have hcV : Continuous V' := (contDiffOn_univ.1 hfV.1).continuous
    have hnon : ∀ z w, u z = V' w → ∀ ε > 0, ∃ z' ∈ ball z ε, ∃ w' ∈ ball w ε,
        u z' = V' w' ∧ (z', w') ≠ (z, w) := by
      intro z w hzw ε hε
      by_contra hcon
      push_neg at hcon
      have hiso : ∃ ε > 0, ∀ z' ∈ ball z ε, ∀ w' ∈ ball w ε, u z' = V' w' → z' = z ∧ w' = w :=
        ⟨ε, hε, fun z' hz' w' hw' h => Prod.ext_iff.1 (hcon z' hz' w' hw' h)⟩
      have hcu' : JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => shiftA 0 u) (shiftA 0 u)
          Set.univ :=
        tendstoCInftyLocOn_shiftA u hsu (fun _ => 0) 0 tendsto_const_nhds Set.univ
      rw [rd_shiftA_zero] at hcu'
      have hc : Tendsto (fun k : ℕ => τ₀ + 1 / ((k : ℝ) + 1)) atTop (𝓝 τ₀) := by
        have := (tendsto_const_nhds (x := τ₀)).add tendsto_one_div_add_atTop_nhds_zero_nat
        rwa [add_zero] at this
      have hcv' := tendstoCInftyLocOn_shiftA v hsv (fun k : ℕ => τ₀ + 1 / ((k : ℝ) + 1)) τ₀ hc
        Set.univ
      obtain ⟨zs, ws, -, -, hev⟩ := exists_intersection_of_tendstoCInftyLocOn H hH J hJ Set.univ
        Set.univ isOpen_univ isOpen_univ u V' (fun _ => u)
        (fun k => shiftA (τ₀ + 1 / ((k : ℝ) + 1)) v) hfu hfV (fun z _ => hui z)
        (fun w _ => hVi w) (fun _ => hfu) (fun k => (isFastPlane_shiftA H hH J hJ v hv _).1)
        hcu' hcv' z w trivial trivial hzw hiso
      obtain ⟨k, hk⟩ := hev.exists
      have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      exact hne _ (by linarith : τ₀ < τ₀ + 1 / ((k : ℝ) + 1)).ne' _ _ hk
    have hnon' : ∀ w z, V' w = u z → ∀ ε > 0, ∃ w' ∈ ball w ε, ∃ z' ∈ ball z ε,
        V' w' = u z' ∧ (w', z') ≠ (w, z) := by
      intro w z h ε hε
      obtain ⟨z', hz', w', hw', heq, hne'⟩ := hnon z w h.symm ε hε
      refine ⟨w', hw', z', hz', heq.symm, fun hh => hne' ?_⟩
      rw [Prod.mk.injEq] at hh ⊢
      exact ⟨hh.2, hh.1⟩
    have hbd1 : ∀ R : ℝ, ∃ R' : ℝ, ∀ z w, ‖z‖ ≤ R → u z = V' w → ‖w‖ ≤ R' := fun R =>
      rd_bound H hH P u v hu0 hv0 hcu hvP humiss τ₀ R
    have hbd2 : ∀ R : ℝ, ∃ R' : ℝ, ∀ w z, ‖w‖ ≤ R → V' w = u z → ‖z‖ ≤ R' := by
      intro R
      obtain ⟨R', hR'⟩ := rd_bound H hH P V' u hV0 hu0 hcV huP
        (fun w => by
          rw [hV', show shiftA τ₀ v w = Real.exp (2 * τ₀) • v w from rfl,
            (proj_aCoord_exp_smul_aux H hH τ₀ (v w) (hv0 w)).1]
          exact hvmiss w) 0 R
      exact ⟨R', fun w z hw h => hR' w z hw (by rw [rd_shiftA_zero]; exact h)⟩
    obtain ⟨z₀, w₀, h₀⟩ := hA
    have D1 := rd_clopen H hH J hJ u V' hfu hfV hui hVi hnon hbd1 ⟨z₀, w₀, h₀⟩
    have D2 := rd_clopen H hH J hJ V' u hfV hfu hVi hui hnon' hbd2 ⟨w₀, z₀, h₀.symm⟩
    have hpv : ∀ w, proj H (V' w) = proj H (v w) := fun w =>
      (proj_aCoord_exp_smul_aux H hH τ₀ (v w) (hv0 w)).1
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := D1 z
      exact ⟨w, by simp only [Function.comp]; rw [hw, hpv]⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := D2 w
      exact ⟨z, by simp only [Function.comp]; rw [← hz, hpv]⟩
  · right
    rw [Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨w, hw⟩
    have h := hray z w hw.symm
    by_cases hτ : aCoord H (u z) - aCoord H (v w) = τ₀
    · exact hA ⟨z, w, hτ ▸ h⟩
    · exact hne _ hτ z w h

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1) (hve : IsEmbeddedPlane v)
    (humiss : ∀ z, proj H (u z) ∉ Set.range P.x) (hvmiss : ∀ z, proj H (v z) ∉ Set.range P.x) :
    Set.range (proj H ∘ u) = Set.range (proj H ∘ v) ∨
      Disjoint (Set.range (proj H ∘ u)) (Set.range (proj H ∘ v)) :=
  FiniteEnergyPlane.rd_main H hH J hJ P u v hu huP hue hv hvP hve humiss hvmiss
