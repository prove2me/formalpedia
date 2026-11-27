-- Prove2me | solution 1 for FiniteEnergyPlane.proj_notMem_range_or_forall_mem_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T22:26:50.2638+00:00
-- url     : https://prove2.me/submissions/33d6084e-47f0-4053-9be6-6de8622aa60a

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_intersection_of_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_exists_holomorphic_eqOn_of_accPt_intersection
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_orbitCylinder
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

/-! Child I of `proj_notMem_range_of_tendsto_disk`: limits of curves missing `ℝ × x(ℝ)` either miss it or
lie in it. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff ENNReal

section
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H)

/-- The cylinder map. -/
noncomputable def pnriCyl (P : ReebOrbit H) (ζ : ℂ) : V 1 := Real.exp (2 * ζ.re) • P.x ζ.im

lemma pnri_range_eq (P : ReebOrbit H) : P.x '' Icc 0 P.T = range P.x := by
  have hp : Function.Periodic P.x P.T := P.periodic
  simpa using hp.image_Icc P.T_pos 0

include hH in
lemma pnri_contDiff (P : ReebOrbit H) : ContDiff ℝ ∞ (pnriCyl P) := by
  unfold pnriCyl
  exact (Real.contDiff_exp.comp (contDiff_const.mul Complex.reCLM.contDiff)).smul
    ((ReebOrbit.contDiff_x H hH P).comp Complex.imCLM.contDiff)

include hH in
lemma pnri_mem_of_eq (P : ReebOrbit H) {y : V 1} {ζ : ℂ} (h : y = pnriCyl P ζ) :
    proj H y ∈ range P.x := by
  rw [h, pnriCyl, (isFiniteEnergyCurve_orbitCylinder H hH 0 P 0 1).2.2 ζ]
  exact mem_range_self _

include hH in
lemma pnri_exists_eq (P : ReebOrbit H) {y : V 1} (hy : y ≠ 0) (h : proj H y ∈ range P.x) :
    ∃ τ ∈ Icc 0 P.T, y = pnriCyl P ⟨aCoord H y, τ⟩ := by
  rw [← pnri_range_eq] at h
  obtain ⟨τ, hτ, hxτ⟩ := h
  refine ⟨τ, hτ, ?_⟩
  have hr := (ka_scale_spec H hH y hy).1
  unfold pnriCyl aCoord
  simp only
  rw [hxτ, show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring,
    Real.exp_neg, Real.exp_log hr, proj, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

include hH in
lemma pnri_scale_continuousAt {y : V 1} (hy : y ≠ 0) : ContinuousAt (scaleToS H) y :=
  (ka_scale_contDiffAt H hH y hy).continuousAt

include hH in
lemma pnri_proj_continuousAt {y : V 1} (hy : y ≠ 0) : ContinuousAt (proj H) y := by
  have : proj H = fun y => scaleToS H y • y := rfl
  rw [this]
  exact (pnri_scale_continuousAt hH hy).smul continuousAt_id

include hH in
lemma pnri_aCoord_continuousAt {y : V 1} (hy : y ≠ 0) : ContinuousAt (aCoord H) y := by
  have : aCoord H = fun y => -Real.log (scaleToS H y) / 2 := rfl
  rw [this]
  have hr := (ka_scale_spec H hH y hy).1
  exact (((pnri_scale_continuousAt hH hy).log hr.ne').neg).div_const 2

lemma pnri_locInj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : ℂ → E) (a : ℂ) (hf : ContDiffAt ℝ 1 f a) (hinj : Function.Injective (fderiv ℝ f a)) :
    ∃ ε > 0, Set.InjOn f (ball a ε) := by
  set D := fderiv ℝ f a with hD
  have hker : LinearMap.ker (D : ℂ →ₗ[ℝ] E) = ⊥ := LinearMap.ker_eq_bot.2 hinj
  obtain ⟨Lₗ, hL⟩ := LinearMap.exists_leftInverse_of_injective (D : ℂ →ₗ[ℝ] E) hker
  set L : E →L[ℝ] ℂ := LinearMap.toContinuousLinearMap Lₗ with hLdef
  have hLD : L.comp D = ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) := by
    ext1 v
    have := congrArg (fun g : ℂ →ₗ[ℝ] ℂ => g v) hL
    simpa [hLdef] using this
  have hs : HasStrictFDerivAt f D a := hf.hasStrictFDerivAt (by norm_num)
  have hg : HasStrictFDerivAt (fun z => L (f z))
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) a := by
    rw [← hLD]; exact L.hasStrictFDerivAt.comp a hs
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_left_inverse
  refine ⟨ε, hε, fun x hx y hy hxy => ?_⟩
  have h1 := hball x hx
  have h2 := hball y hy
  rw [← h1, ← h2, hxy]

end

theorem proj_notMem_range_or_forall_mem_of_tendsto_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U) (u : ℂ → V 1) (un : ℕ → ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J U u) (hui : ∀ z ∈ U, Function.Injective (fderiv ℝ u z))
    (hun : ∀ n, IsFiniteEnergyCurve H J U (un n))
    (hconv : JHolomorphic.TendstoCInftyLocOn un u U)
    (hdis : ∀ n, ∀ z ∈ U, proj H (un n z) ∉ Set.range P.x) :
    (∀ z ∈ U, proj H (u z) ∉ Set.range P.x) ∨ ∀ z ∈ U, proj H (u z) ∈ Set.range P.x := by
  set v := pnriCyl P with hvdef
  have hG := fun (w₀ : ℂ) => isFiniteEnergyCurve_orbitCylinder H hH J P w₀ 1
  have hvc : Continuous v := (pnri_contDiff hH P).continuous
  have hu0 : ∀ z ∈ U, u z ≠ 0 := hu.2.1
  have hucont : ContinuousOn u U := hu.1.continuousOn
  -- constant sequence convergence
  have hcv : ∀ W : Set ℂ, JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => v) v W := by
    intro W K _ _ m
    exact fun s hs => Eventually.of_forall fun _ x _ => refl_mem_uniformity hs
  -- the local statement
  have hloc : ∀ z₀ ∈ U, proj H (u z₀) ∈ range P.x →
      ∃ ε > 0, ∀ z ∈ ball z₀ ε, z ∈ U ∧ proj H (u z) ∈ range P.x := by
    intro z₀ hz₀ hm
    obtain ⟨δU, hδU, hδUs⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
    by_cases hfreq : ∃ᶠ z in 𝓝[≠] z₀, z ∈ U ∧ proj H (u z) ∈ range P.x
    · -- accumulation: holomorphic reparametrization of the cylinder
      have hfreq' : ∃ᶠ z in 𝓝[≠] z₀, (z ∈ U ∧ proj H (u z) ∈ range P.x) ∧ z ≠ z₀ :=
        hfreq.and_eventually self_mem_nhdsWithin
      obtain ⟨zs, hzs, hzp⟩ := Filter.exists_seq_forall_of_frequently hfreq'
      have hzs' : Tendsto zs atTop (𝓝 z₀) := tendsto_nhds_of_tendsto_nhdsWithin hzs
      have hex : ∀ k, ∃ τ ∈ Icc 0 P.T, u (zs k) = v ⟨aCoord H (u (zs k)), τ⟩ := fun k =>
        pnri_exists_eq hH P (hu0 _ (hzp k).1.1) (hzp k).1.2
      choose τ hτ hτeq using hex
      obtain ⟨τs, -, φ, hφ, hτφ⟩ := (isCompact_Icc).tendsto_subseq hτ
      set ζs : ℕ → ℂ := fun k => ⟨aCoord H (u (zs (φ k))), τ (φ k)⟩
      set ζs₀ : ℂ := ⟨aCoord H (u z₀), τs⟩
      have hzφ : Tendsto (zs ∘ φ) atTop (𝓝 z₀) := hzs'.comp hφ.tendsto_atTop
      have huφ : Tendsto (fun k => u (zs (φ k))) atTop (𝓝 (u z₀)) :=
        ((hucont z₀ hz₀).continuousAt (hU.mem_nhds hz₀)).tendsto.comp hzφ
      have haφ : Tendsto (fun k => aCoord H (u (zs (φ k)))) atTop (𝓝 (aCoord H (u z₀))) :=
        (pnri_aCoord_continuousAt hH (hu0 _ hz₀)).tendsto.comp huφ
      have hζ : Tendsto ζs atTop (𝓝 ζs₀) := by
        have := (haφ.prodMk_nhds hτφ)
        have hce : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
          Complex.equivRealProdCLM.symm.continuous
        exact (hce.tendsto _).comp this
      have heq : ∀ k, u (zs (φ k)) = v (ζs k) := fun k => hτeq (φ k)
      have hu₀ : u z₀ = v ζs₀ := by
        have h1 : Tendsto (fun k => v (ζs k)) atTop (𝓝 (v ζs₀)) := (hvc.tendsto _).comp hζ
        have h2 : Tendsto (fun k => v (ζs k)) atTop (𝓝 (u z₀)) := by
          simpa only [← heq] using huφ
        exact tendsto_nhds_unique h2 h1
      have hne : ∀ k, ((zs ∘ φ) k, ζs k) ≠ (z₀, ζs₀) := fun k h =>
        (hzp (φ k)).2 (congrArg Prod.fst h)
      obtain ⟨ε, hε, ψ, -, -, -, -, hEq⟩ := exists_holomorphic_eqOn_of_accPt_intersection H hH J hJ
        U (ball ζs₀ 1) hU isOpen_ball u v hu (hG ζs₀).1 hui (fun w _ => (hG ζs₀).2.1 w) z₀ ζs₀ hz₀
        (mem_ball_self one_pos) (zs ∘ φ) ζs hzφ hζ hne heq
      refine ⟨min ε δU, lt_min hε hδU, fun z hz => ?_⟩
      have hz1 : z ∈ ball z₀ ε := ball_subset_ball (min_le_left _ _) hz
      have hz2 : z ∈ ball z₀ δU := ball_subset_ball (min_le_right _ _) hz
      exact ⟨hδUs hz2, pnri_mem_of_eq hH P (hEq hz1)⟩
    · -- isolated: persistence gives an intersection of some `u_n` with the cylinder
      exfalso
      rw [not_frequently] at hfreq
      obtain ⟨ε₁, hε₁, hiso₁⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_nhdsWithin_iff.1 hfreq)
      obtain ⟨τ₀, -, hτ₀⟩ := pnri_exists_eq hH P (hu0 _ hz₀) hm
      set ζ₀ : ℂ := ⟨aCoord H (u z₀), τ₀⟩
      obtain ⟨δ, hδ, hinj⟩ := pnri_locInj v ζ₀ ((pnri_contDiff hH P).contDiffAt.of_le (by simp))
        ((hG ζ₀).2.1 ζ₀)
      set ε := min (min ε₁ δU) δ
      have hε : 0 < ε := lt_min (lt_min hε₁ hδU) hδ
      have hiso : ∃ ε > 0, ∀ z ∈ ball z₀ ε, ∀ w ∈ ball ζ₀ ε, u z = v w → z = z₀ ∧ w = ζ₀ := by
        refine ⟨ε, hε, fun z hz w hw hzw => ?_⟩
        have hz1 : z ∈ ball z₀ ε₁ := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hz
        have hz2 : z ∈ ball z₀ δU := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hz
        have hzU := hδUs hz2
        have hzz : z = z₀ := by
          by_contra hne
          exact hiso₁ z hz1 hne ⟨hzU, pnri_mem_of_eq hH P hzw⟩
        refine ⟨hzz, hinj (ball_subset_ball (min_le_right _ _) hw) (mem_ball_self hδ) ?_⟩
        rw [← hzw, hzz, hτ₀]
      obtain ⟨zs, ws, hzs, -, hev⟩ := exists_intersection_of_tendstoCInftyLocOn H hH J hJ U
        (ball ζ₀ 1) hU isOpen_ball u v un (fun _ => v) hu (hG ζ₀).1 hui (fun w _ => (hG ζ₀).2.1 w)
        hun (fun _ => (hG ζ₀).1) hconv (hcv _) z₀ ζ₀ hz₀ (mem_ball_self one_pos) hτ₀ hiso
      have hevU : ∀ᶠ k in atTop, zs k ∈ U := hzs (hU.mem_nhds hz₀)
      obtain ⟨k, hk1, hk2⟩ := (hev.and hevU).exists
      exact hdis k (zs k) hk2 (pnri_mem_of_eq hH P hk1)
  -- clopen argument
  set Z := {z | z ∈ U ∧ proj H (u z) ∈ range P.x}
  set Y := U ∩ (fun z => proj H (u z)) ⁻¹' (range P.x)ᶜ
  have hZo : IsOpen Z := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨ε, hε, h⟩ := hloc z hz.1 hz.2
    exact ⟨ε, hε, fun w hw => h w hw⟩
  have hpc : ContinuousOn (fun z => proj H (u z)) U := fun z hz =>
    ((pnri_proj_continuousAt hH (hu0 z hz)).comp_continuousWithinAt (hucont z hz))
  have hcl : IsClosed (range P.x) := by
    rw [← pnri_range_eq]
    exact (isCompact_Icc.image (ReebOrbit.contDiff_x H hH P).continuous).isClosed
  have hYo : IsOpen Y := hpc.isOpen_inter_preimage hU hcl.isOpen_compl
  have hdisj : Disjoint Z Y := by
    rw [Set.disjoint_left]
    intro z hz hy
    exact hy.2 hz.2
  have hcov : U ⊆ Z ∪ Y := by
    intro z hz
    by_cases h : proj H (u z) ∈ range P.x
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  rcases hUc.subset_or_subset hZo hYo hdisj hcov with h | h
  · exact Or.inr fun z hz => (h hz).2
  · exact Or.inl fun z hz => (h hz).2

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U) (u : ℂ → V 1) (un : ℕ → ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J U u) (hui : ∀ z ∈ U, Function.Injective (fderiv ℝ u z))
    (hun : ∀ n, IsFiniteEnergyCurve H J U (un n))
    (hconv : JHolomorphic.TendstoCInftyLocOn un u U)
    (hdis : ∀ n, ∀ z ∈ U, proj H (un n z) ∉ Set.range P.x) :
    (∀ z ∈ U, proj H (u z) ∉ Set.range P.x) ∨ ∀ z ∈ U, proj H (u z) ∈ Set.range P.x :=
  proj_notMem_range_or_forall_mem_of_tendsto_aux H hH J hJ P U hU hUc u un hu hui hun hconv hdis
