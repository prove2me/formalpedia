-- Prove2me | solution 1 for FiniteEnergyPlane.exists_normalFrame_of_isFastPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T20:41:31.493723+00:00
-- url     : https://prove2.me/submissions/2568ee15-fdee-4888-9713-8e29a0e540e3

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_triangular_iff
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_isInXi_linearizedReeb_deriv
import Theorems.Thm_FiniteEnergyPlane_asympOp_frame_bridge
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_comp_periodic
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_mul_norm_of_periodic
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_of_tendstoZeroCInfty
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_fderiv
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_prodMk
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_conj
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd

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

/-! Linear algebra of Hryniewicz's global frame `Z₁, Z₂` of `ξ` (copied from the
`exists_prime_periodicOrbit_cover` solution, renamed `r26_*`). -/

namespace HryniewiczCriterion

open scoped ContDiff

lemma r26_clm_apply_eq_sum (L : R4 →L[ℝ] ℝ) (v : R4) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) +
      v 2 * L (Pi.single 2 1) + v 3 * L (Pi.single 3 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, Fin.sum_univ_four, smul_eq_mul]

lemma r26_omega0_X_right (H : R4 → ℝ) (y p : R4) :
    omega0 p (hamiltonianVectorField H y) = fderiv ℝ H y p := by
  rw [r26_clm_apply_eq_sum (fderiv ℝ H y) p]
  simp [omega0, hamiltonianVectorField, partialDeriv]

lemma r26_omega0_antisymm (u v : R4) : omega0 u v = -omega0 v u := by
  simp [omega0]; ring

lemma r26_omega0_self (u : R4) : omega0 u u = 0 := by
  simp [omega0]; ring

lemma r26_omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma r26_omega0_lin_left (u a b : R4) (p q : ℝ) :
    omega0 (p • a + q • b) u = p * omega0 a u + q * omega0 b u := by
  simp [omega0]; ring

lemma r26_omega0_lin_right2 (u a b : R4) (p q : ℝ) :
    omega0 u (p • a + q • b) = p * omega0 u a + q * omega0 u b := by
  simp [omega0]; ring

lemma r26_omega0_smul_left (u v : R4) (p : ℝ) : omega0 (p • u) v = p * omega0 u v := by
  simp [omega0]; ring

lemma r26_omega0_smul_right (u v : R4) (p : ℝ) : omega0 u (p • v) = p * omega0 u v := by
  simp [omega0]; ring

lemma r26_eq_frame_of_omega0 (Z₁ Z₂ a b v : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0) :
    v = omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set w : Fin 4 → R4 := ![Z₁, Z₂, a, b] with hw
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    replace hg : g 0 • Z₁ + g 1 • Z₂ + g 2 • a + g 3 • b = 0 := by
      simpa [Fin.sum_univ_four, hw] using hg
    have e1 := congrArg (omega0 Z₁) hg
    have e2 := congrArg (omega0 Z₂) hg
    have e3 := congrArg (omega0 a) hg
    have e4 := congrArg (omega0 b) hg
    rw [r26_omega0_lin_right] at e1 e2 e3 e4
    have z : ∀ u : R4, omega0 u 0 = 0 := fun u => by simp [omega0]
    rw [z] at e1 e2 e3 e4
    rw [r26_omega0_self, h12, h1a, h1b] at e1
    rw [r26_omega0_antisymm Z₂ Z₁, h12, r26_omega0_self, h2a, h2b] at e2
    rw [r26_omega0_antisymm a Z₁, r26_omega0_antisymm a Z₂, h1a, h2a, r26_omega0_self] at e3
    rw [r26_omega0_antisymm b Z₁, r26_omega0_antisymm b Z₂, r26_omega0_antisymm b a, h1b, h2b,
      r26_omega0_self] at e4
    have g1 : g 1 = 0 := by linarith
    have g0 : g 0 = 0 := by linarith
    have g3 : g 3 = 0 := by
      have : g 3 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    have g2 : g 2 = 0 := by
      have : g 2 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    intro i; fin_cases i <;> assumption
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℝ (Set.range w) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  replace hc : c 0 • Z₁ + c 1 • Z₂ + c 2 • a + c 3 • b = v := by
    simpa [Fin.sum_univ_four, hw] using hc
  have ea : omega0 v a = c 0 * omega0 Z₁ a + c 1 * omega0 Z₂ a + c 2 * omega0 a a +
      c 3 * omega0 b a := by
    rw [← hc, r26_omega0_antisymm, r26_omega0_lin_right]
    rw [r26_omega0_antisymm a Z₁, r26_omega0_antisymm a Z₂, r26_omega0_antisymm a b,
      r26_omega0_self]; ring
  have eb : omega0 v b = c 0 * omega0 Z₁ b + c 1 * omega0 Z₂ b + c 2 * omega0 a b +
      c 3 * omega0 b b := by
    rw [← hc, r26_omega0_antisymm, r26_omega0_lin_right]
    rw [r26_omega0_antisymm b Z₁, r26_omega0_antisymm b Z₂, r26_omega0_antisymm b a,
      r26_omega0_self]; ring
  rw [h1a, h2a, r26_omega0_self, r26_omega0_antisymm b a, hva] at ea
  rw [h1b, h2b, r26_omega0_self, hvb] at eb
  have c3 : c 3 = 0 := by
    have : c 3 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have c2 : c 2 = 0 := by
    have : c 2 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have hv2 : v = c 0 • Z₁ + c 1 • Z₂ := by rw [← hc, c2, c3]; simp
  have k0 : omega0 v Z₂ = c 0 := by
    rw [hv2, r26_omega0_lin_left, r26_omega0_self, h12]; ring
  have k1 : omega0 Z₁ v = c 1 := by
    rw [hv2, r26_omega0_antisymm, r26_omega0_lin_left, r26_omega0_self,
      r26_omega0_antisymm Z₂ Z₁, h12]; ring
  rw [k0, k1]; exact hv2

variable {H : R4 → ℝ}

lemma r26_ne_zero_of_dH_pos {y : R4} (hy : 0 < fderiv ℝ H y y) : y ≠ 0 := by
  rintro rfl; simp at hy

lemma r26_dot4_pos {y : R4} (hy : y ≠ 0) : 0 < dot4 y y := by
  by_contra h
  push_neg at h
  apply hy
  have hs : ∀ i, y i * y i = 0 := by
    intro i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ y j * y j := fun j _ => mul_self_nonneg _
    have hsum : ∑ j, y j * y j = 0 := le_antisymm h (Finset.sum_nonneg hnn)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  ext i; simpa using hs i

lemma r26_euclidNorm_sq (y : R4) : euclidNorm y * euclidNorm y = dot4 y y := by
  have : 0 ≤ dot4 y y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
  exact Real.mul_self_sqrt this

lemma r26_dH_xiFrameRaw {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    fderiv ℝ H y (xiFrameRaw H Q y) = 0 := by
  simp only [xiFrameRaw, map_sub, map_smul, smul_eq_mul]
  field_simp; ring

lemma r26_omega0_xiFrameRaw_self (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) (y : R4) :
    omega0 y (xiFrameRaw H Q y) = 0 := by
  have := hQ y
  simp only [xiFrameRaw, omega0] at this ⊢
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination this

lemma r26_omega0_quatQ1 (y : R4) : omega0 y (quatQ1 y) = 0 := by
  simp [omega0, quatQ1]; ring

lemma r26_omega0_quatQ2 (y : R4) : omega0 y (quatQ2 y) = 0 := by
  simp [omega0, quatQ2]; ring

lemma r26_omega0_raw21 (y : R4) :
    omega0 (xiFrameRaw H quatQ2 y) (xiFrameRaw H quatQ1 y) = dot4 y y := by
  simp [xiFrameRaw, omega0, quatQ1, quatQ2, dot4, Fin.sum_univ_four]; ring

lemma r26_omega0_xiFrame12 {y : R4} (hy : 0 < fderiv ℝ H y y) :
    omega0 (xiFrame1 H y) (xiFrame2 H y) = 1 := by
  have hpos := r26_dot4_pos (r26_ne_zero_of_dH_pos hy)
  have hn := r26_euclidNorm_sq y
  have hne : euclidNorm y ≠ 0 := by
    intro h; rw [h] at hn; linarith
  rw [xiFrame1, xiFrame2, r26_omega0_smul_left, r26_omega0_smul_right, r26_omega0_raw21, ← hn]
  field_simp

/-- `ω₀(y, Zᵢ) = 0`. -/
lemma r26_omega0_y_xiFrame (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) (y : R4) :
    omega0 y ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) = 0 := by
  rw [r26_omega0_smul_right, r26_omega0_xiFrameRaw_self Q hQ y, mul_zero]

/-- `dH(Zᵢ) = 0`. -/
lemma r26_dH_xiFrame {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    fderiv ℝ H y ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) = 0 := by
  rw [map_smul, r26_dH_xiFrameRaw hy, smul_zero]

lemma r26_cd_omega0 {p q : ℝ → R4} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun τ => omega0 (p τ) (q τ)) := by
  have h := fun i => contDiff_pi.1 hp i
  have k := fun i => contDiff_pi.1 hq i
  simp only [omega0]
  exact ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
    ((h 3).mul (k 2))

lemma r26_cd_dH (hH : ContDiff ℝ ∞ H) {c v : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (fun τ => fderiv ℝ H (c τ) (v τ)) :=
  ((hH.fderiv_right le_rfl).comp hc).clm_apply hv

lemma r26_cd_quatQ1 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ1 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ1] <;> first | exact h _ | exact (h _).neg

lemma r26_cd_quatQ2 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ2 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ2] <;> first | exact h _ | exact (h _).neg

lemma r26_cd_xiFrame (hH : ContDiff ℝ ∞ H) {c : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ τ, 0 < fderiv ℝ H (c τ) (c τ)) (Q : R4 → R4)
    (hQ : ContDiff ℝ ∞ (fun τ => Q (c τ))) :
    ContDiff ℝ ∞ (fun τ => (euclidNorm (c τ))⁻¹ • xiFrameRaw H Q (c τ)) := by
  have hraw : ContDiff ℝ ∞ (fun τ => xiFrameRaw H Q (c τ)) :=
    hQ.sub (((r26_cd_dH hH hc hQ).div (r26_cd_dH hH hc hc) fun τ => (hpos τ).ne').smul hc)
  have hdot : ContDiff ℝ ∞ (fun τ => dot4 (c τ) (c τ)) := by
    have h := fun i => contDiff_pi.1 hc i
    simp only [dot4, Fin.sum_univ_four]
    exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add
      ((h 3).mul (h 3))
  have hdne : ∀ τ, dot4 (c τ) (c τ) ≠ 0 := fun τ =>
    (r26_dot4_pos (r26_ne_zero_of_dH_pos (hpos τ))).ne'
  have hnorm : ContDiff ℝ ∞ (fun τ => euclidNorm (c τ)) := hdot.sqrt hdne
  have hnne : ∀ τ, euclidNorm (c τ) ≠ 0 := fun τ h => by
    have := r26_euclidNorm_sq (c τ); rw [h] at this; exact hdne τ (by linarith)
  exact (hnorm.inv hnne).smul hraw

end HryniewiczCriterion

namespace FiniteEnergyPlane

open scoped ContDiff

lemma r26_omega0_eq (u v : V 1) : omega0 u v = HryniewiczCriterion.omega0 u v := by
  simp [omega0, HryniewiczCriterion.omega0, dot, j0, Fin.sum_univ_four]; ring

lemma r26_omega0_bilin (a b c d : HryniewiczCriterion.R4) (p q r s : ℝ) :
    HryniewiczCriterion.omega0 (p • a + q • b) (r • c + s • d) =
      p * r * HryniewiczCriterion.omega0 a c + p * s * HryniewiczCriterion.omega0 a d +
      q * r * HryniewiczCriterion.omega0 b c + q * s * HryniewiczCriterion.omega0 b d := by
  simp [HryniewiczCriterion.omega0]; ring

lemma r26_J0_inl (a : CauchyRiemannIndex.Vec 1) :
    Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a (Sum.inl 0) = -a (Sum.inr 0) := by
  simp [Matrix.J, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Matrix.fromBlocks]

lemma r26_J0_inr (a : CauchyRiemannIndex.Vec 1) :
    Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a (Sum.inr 0) = a (Sum.inl 0) := by
  simp [Matrix.J, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Matrix.fromBlocks]

lemma r26_isInXi_comb {H : V 1 → ℝ} {x u v : V 1} (hu : IsInXi H x u) (hv : IsInXi H x v)
    (p q : ℝ) : IsInXi H x (p • u + q • v) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [liouville, r26_omega0_eq] at hu1 hv1 ⊢
    have e : HryniewiczCriterion.omega0 x (p • u + q • v) =
        p * HryniewiczCriterion.omega0 x u + q * HryniewiczCriterion.omega0 x v := by
      simp [HryniewiczCriterion.omega0]; ring
    rw [e]
    have h1 : HryniewiczCriterion.omega0 x u = 0 := by linarith
    have h2 : HryniewiczCriterion.omega0 x v = 0 := by linarith
    rw [h1, h2]; simp
  · rw [map_add, map_smul, map_smul, hu2, hv2]; simp

/-! ### The frame at a point of `S` -/

/-- `Z₁(x)`, the first vector of the global frame. -/
noncomputable def r26e (H : V 1 → ℝ) (x : V 1) : V 1 := HryniewiczCriterion.xiFrame1 H x

/-- `β(x) = ω₀(Z₁, J Z₁)`. -/
noncomputable def r26β (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) : ℝ :=
  HryniewiczCriterion.omega0 (r26e H x) (J x (r26e H x))

/-- `W = β^{-1/2} Z₁`. -/
noncomputable def r26W (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) : V 1 :=
  (Real.sqrt (r26β H J x))⁻¹ • r26e H x

/-- `Z(x) a = a₁ W + a₂ J W`. -/
noncomputable def r26ZAt (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) :
    CauchyRiemannIndex.Vec 1 →L[ℝ] V 1 :=
  (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).smulRight (r26W H J x) +
    (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).smulRight (J x (r26W H J x))

lemma r26ZAt_apply (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1)
    (a : CauchyRiemannIndex.Vec 1) :
    r26ZAt H J x a = a (Sum.inl 0) • r26W H J x + a (Sum.inr 0) • J x (r26W H J x) := by
  simp [r26ZAt]

section point

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J) {x : V 1} (hx : H x = 1)

include hH hx in
lemma r26_pos : 0 < fderiv ℝ H x x := hH.2.2 x hx

include hH hx in
lemma r26_e12 : HryniewiczCriterion.omega0 (r26e H x) (HryniewiczCriterion.xiFrame2 H x) = 1 :=
  HryniewiczCriterion.r26_omega0_xiFrame12 (r26_pos hH hx)

include hH hx in
lemma r26_e_xi : IsInXi H x (r26e H x) := by
  refine ⟨?_, ?_⟩
  · rw [liouville, r26_omega0_eq, r26e, HryniewiczCriterion.xiFrame1,
      HryniewiczCriterion.r26_omega0_y_xiFrame _ HryniewiczCriterion.r26_omega0_quatQ2]
    simp
  · exact HryniewiczCriterion.r26_dH_xiFrame (r26_pos hH hx) _

include hH hx in
lemma r26_e2_xi : IsInXi H x (HryniewiczCriterion.xiFrame2 H x) := by
  refine ⟨?_, ?_⟩
  · rw [liouville, r26_omega0_eq, HryniewiczCriterion.xiFrame2,
      HryniewiczCriterion.r26_omega0_y_xiFrame _ HryniewiczCriterion.r26_omega0_quatQ1]
    simp
  · exact HryniewiczCriterion.r26_dH_xiFrame (r26_pos hH hx) _

include hH hx in
/-- Every `w ∈ ξ_x` is `ω₀(w, Z₂) Z₁ + ω₀(Z₁, w) Z₂`. -/
lemma r26_decomp {w : V 1} (hw : IsInXi H x w) :
    w = HryniewiczCriterion.omega0 w (HryniewiczCriterion.xiFrame2 H x) • r26e H x +
      HryniewiczCriterion.omega0 (r26e H x) w • HryniewiczCriterion.xiFrame2 H x := by
  have hpos := r26_pos hH hx
  have xi_a : ∀ v, IsInXi H x v → HryniewiczCriterion.omega0 v x = 0 := by
    intro v hv
    have := hv.1
    rw [liouville, r26_omega0_eq] at this
    rw [HryniewiczCriterion.r26_omega0_antisymm]; linarith
  have xi_b : ∀ v, IsInXi H x v →
      HryniewiczCriterion.omega0 v (HryniewiczCriterion.hamiltonianVectorField H x) = 0 := by
    intro v hv
    rw [HryniewiczCriterion.r26_omega0_X_right]; exact hv.2
  have := HryniewiczCriterion.r26_eq_frame_of_omega0 (r26e H x) (HryniewiczCriterion.xiFrame2 H x)
    x (HryniewiczCriterion.hamiltonianVectorField H x) w (r26_e12 hH hx)
    (xi_a _ (r26_e_xi hH hx)) (xi_b _ (r26_e_xi hH hx)) (xi_a _ (r26_e2_xi hH hx))
    (xi_b _ (r26_e2_xi hH hx))
    (by rw [HryniewiczCriterion.r26_omega0_X_right]; exact hpos.ne') (xi_a _ hw) (xi_b _ hw)
  exact this

include hH hJ hx in
lemma r26_β_pos : 0 < r26β H J x := by
  have h := (hJ.2 x hx _ _ (r26_e_xi hH hx) (r26_e_xi hH hx)).2.2.1
  have hne : r26e H x ≠ 0 := by
    intro h0
    have := r26_e12 hH hx
    rw [h0] at this; simp [HryniewiczCriterion.omega0] at this
  have := h hne
  rw [r26_omega0_eq] at this
  exact this

include hH hJ hx in
lemma r26_W_xi : IsInXi H x (r26W H J x) := by
  have := r26_isInXi_comb (r26_e_xi hH hx) (r26_e_xi hH hx) (Real.sqrt (r26β H J x))⁻¹ 0
  simpa [r26W] using this

include hH hJ hx in
lemma r26_JW_xi : IsInXi H x (J x (r26W H J x)) :=
  (hJ.2 x hx _ _ (r26_W_xi hH hJ hx) (r26_W_xi hH hJ hx)).1

include hH hJ hx in
lemma r26_JJW : J x (J x (r26W H J x)) = -r26W H J x :=
  (hJ.2 x hx _ _ (r26_W_xi hH hJ hx) (r26_W_xi hH hJ hx)).2.1

include hH hJ hx in
lemma r26_sqrt_pos : 0 < Real.sqrt (r26β H J x) := Real.sqrt_pos.2 (r26_β_pos hH hJ hx)

include hH hJ hx in
lemma r26_W_JW : HryniewiczCriterion.omega0 (r26W H J x) (J x (r26W H J x)) = 1 := by
  have hs := r26_sqrt_pos hH hJ hx
  have hss : Real.sqrt (r26β H J x) * Real.sqrt (r26β H J x) = r26β H J x :=
    Real.mul_self_sqrt (r26_β_pos hH hJ hx).le
  rw [r26W, map_smul, HryniewiczCriterion.r26_omega0_smul_left,
    HryniewiczCriterion.r26_omega0_smul_right]
  change _ * (_ * r26β H J x) = 1
  rw [inv_mul_eq_div (Real.sqrt _) (r26β H J x), Real.div_sqrt]
  exact inv_mul_cancel₀ hs.ne'

include hH hJ hx in
lemma r26_unitary_xi (a : CauchyRiemannIndex.Vec 1) : IsInXi H x (r26ZAt H J x a) := by
  rw [r26ZAt_apply]; exact r26_isInXi_comb (r26_W_xi hH hJ hx) (r26_JW_xi hH hJ hx) _ _

include hH hJ hx in
lemma r26_unitary_surj (w : V 1) (hw : IsInXi H x w) :
    ∃ a, r26ZAt H J x a = w := by
  set e := r26e H x
  set e2 := HryniewiczCriterion.xiFrame2 H x
  set s := Real.sqrt (r26β H J x)
  set β := r26β H J x
  have hs := r26_sqrt_pos hH hJ hx
  have hβ := r26_β_pos hH hJ hx
  have hJe := r26_decomp hH hx ((hJ.2 x hx _ _ (r26_e_xi hH hx) (r26_e_xi hH hx)).1)
  have hβdef : HryniewiczCriterion.omega0 e (J x e) = β := rfl
  rw [hβdef] at hJe
  set α := HryniewiczCriterion.omega0 (J x e) e2
  set p := HryniewiczCriterion.omega0 w e2
  set q := HryniewiczCriterion.omega0 e w
  have hw' := r26_decomp hH hx hw
  have hβ0 : β ≠ 0 := hβ.ne'
  have hs0 : s ≠ 0 := hs.ne'
  refine ⟨(WithLp.equiv 2 (Fin 1 ⊕ Fin 1 → ℝ)).symm
    (Sum.elim (fun _ => s * (p - q * α / β)) (fun _ => s * q / β)), ?_⟩
  rw [r26ZAt_apply]
  simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, Sum.elim_inl, Sum.elim_inr]
  rw [r26W, map_smul, hJe]
  conv_rhs => rw [hw']
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

include hH hJ hx in
lemma r26_unitary_J (a : CauchyRiemannIndex.Vec 1) :
    J x (r26ZAt H J x a) =
      r26ZAt H J x (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) := by
  rw [r26ZAt_apply, r26ZAt_apply, r26_J0_inl, r26_J0_inr, map_add, map_smul, map_smul,
    r26_JJW hH hJ hx]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

include hH hJ hx in
lemma r26_unitary_omega (a b : CauchyRiemannIndex.Vec 1) :
    omega0 (r26ZAt H J x a) (r26ZAt H J x b) =
      inner ℝ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) b := by
  rw [r26_omega0_eq, r26ZAt_apply, r26ZAt_apply, r26_omega0_bilin,
    HryniewiczCriterion.r26_omega0_self, HryniewiczCriterion.r26_omega0_self,
    HryniewiczCriterion.r26_omega0_antisymm (J x _) (r26W H J x), r26_W_JW hH hJ hx]
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_one, r26_J0_inl, r26_J0_inr,
    RCLike.inner_apply, conj_trivial]
  ring

include hH hJ hx in
lemma r26_coord (a : CauchyRiemannIndex.Vec 1) :
    xiCoordC H x (r26ZAt H J x a) =
      ((((Real.sqrt (r26β H J x))⁻¹ * a (Sum.inl 0) +
        (Real.sqrt (r26β H J x))⁻¹ *
          HryniewiczCriterion.omega0 (J x (r26e H x)) (HryniewiczCriterion.xiFrame2 H x) *
            a (Sum.inr 0) : ℝ)) : ℂ) +
        ((Real.sqrt (r26β H J x) * a (Sum.inr 0) : ℝ) : ℂ) * Complex.I := by
  have hs := r26_sqrt_pos hH hJ hx
  have hss : Real.sqrt (r26β H J x) * Real.sqrt (r26β H J x) = r26β H J x :=
    Real.mul_self_sqrt (r26_β_pos hH hJ hx).le
  have h12 := r26_e12 hH hx
  have hc : xiCoordC H x (r26ZAt H J x a) =
      ⟨HryniewiczCriterion.omega0 (r26ZAt H J x a) (HryniewiczCriterion.xiFrame2 H x),
        HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H x) (r26ZAt H J x a)⟩ := rfl
  rw [hc]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    rw [r26ZAt_apply, HryniewiczCriterion.r26_omega0_lin_left, r26W, map_smul,
      HryniewiczCriterion.r26_omega0_smul_left, HryniewiczCriterion.r26_omega0_smul_left,
      h12]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    change HryniewiczCriterion.omega0 (r26e H x) _ = _
    rw [r26ZAt_apply, HryniewiczCriterion.r26_omega0_lin_right2, r26W, map_smul,
      HryniewiczCriterion.r26_omega0_smul_right, HryniewiczCriterion.r26_omega0_smul_right,
      HryniewiczCriterion.r26_omega0_self]
    change _ * (_ * 0) + _ * (_ * r26β H J x) = _
    rw [inv_mul_eq_div (Real.sqrt _) (r26β H J x), Real.div_sqrt]
    ring

end point

theorem exists_unitaryXiFrame_hasXiLoopWind_iff_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J P Z ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k) := by
  set c : ℝ → V 1 := fun t => P.x (P.T * t) with hcdef
  have hc : ContDiff ℝ ∞ c := (ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_id)
  have hcper : ∀ t, c (t + 1) = c t := fun t => by
    simp only [hcdef, mul_add, mul_one, P.periodic]
  have hcS : ∀ t, H (c t) = 1 := fun t => P.mem _
  have hpos : ∀ t, 0 < fderiv ℝ H (c t) (c t) := fun t => r26_pos hH (hcS t)
  have he : ContDiff ℝ ∞ (fun t => r26e H (c t)) :=
    HryniewiczCriterion.r26_cd_xiFrame hH.1 hc hpos HryniewiczCriterion.quatQ2
      (HryniewiczCriterion.r26_cd_quatQ2 hc)
  have he2 : ContDiff ℝ ∞ (fun t => HryniewiczCriterion.xiFrame2 H (c t)) :=
    HryniewiczCriterion.r26_cd_xiFrame hH.1 hc hpos HryniewiczCriterion.quatQ1
      (HryniewiczCriterion.r26_cd_quatQ1 hc)
  have hJc : ContDiff ℝ ∞ (fun t => J (c t)) := hJ.1.comp hc
  have hβ : ContDiff ℝ ∞ (fun t => r26β H J (c t)) :=
    HryniewiczCriterion.r26_cd_omega0 he (hJc.clm_apply he)
  have hs : ContDiff ℝ ∞ (fun t => Real.sqrt (r26β H J (c t))) :=
    hβ.sqrt (fun t => (r26_β_pos hH hJ (hcS t)).ne')
  have hsinv : ContDiff ℝ ∞ (fun t => (Real.sqrt (r26β H J (c t)))⁻¹) :=
    hs.inv (fun t => (r26_sqrt_pos hH hJ (hcS t)).ne')
  have hW : ContDiff ℝ ∞ (fun t => r26W H J (c t)) := hsinv.smul he
  have hJW : ContDiff ℝ ∞ (fun t => J (c t) (r26W H J (c t))) := hJc.clm_apply hW
  have hb : ContDiff ℝ ∞ (fun t => (Real.sqrt (r26β H J (c t)))⁻¹ *
      HryniewiczCriterion.omega0 (J (c t) (r26e H (c t))) (HryniewiczCriterion.xiFrame2 H (c t))) :=
    hsinv.mul (HryniewiczCriterion.r26_cd_omega0 (hJc.clm_apply he) he2)
  refine ⟨fun t => r26ZAt H J (c t), ⟨?_, ?_, fun t => ⟨r26_unitary_xi hH hJ (hcS t),
    r26_unitary_surj hH hJ (hcS t), r26_unitary_J hH hJ (hcS t),
    r26_unitary_omega hH hJ (hcS t)⟩⟩, ?_⟩
  · exact (contDiff_const.smulRight hW).add (contDiff_const.smulRight hJW)
  · intro t; simp only [hcper]
  · intro ζ hζ hζp hζ0 k
    have h1 : Continuous fun t => ζ t (Sum.inl 0) :=
      (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).continuous.comp hζ
    have h2 : Continuous fun t => ζ t (Sum.inr 0) :=
      (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).continuous.comp hζ
    have hzeq : (fun t => vecToC (ζ t)) = fun t => ((ζ t (Sum.inl 0) : ℝ) : ℂ) +
        ((ζ t (Sum.inr 0) : ℝ) : ℂ) * Complex.I :=
      funext fun t => Complex.ext (by simp [vecToC]) (by simp [vecToC])
    have hz : Continuous (fun t => vecToC (ζ t)) := by rw [hzeq]; fun_prop
    have hzp : Function.Periodic (fun t => vecToC (ζ t)) 1 := fun t => by
      simp only [hζp t]
    have hz0 : ∀ t, vecToC (ζ t) ≠ 0 := by
      intro t h
      apply hζ0 t
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [vecToC, Complex.zero_re, Complex.zero_im] at hre him
      ext i
      rcases i with i | i <;> fin_cases i
      · simpa using hre
      · simpa using him
    have hA := hasLoopWind_triangular_iff hsinv.continuous hb.continuous hs.continuous
      (fun t => by simp only [hcper]) (fun t => by simp only [hcper])
      (fun t => by simp only [hcper])
      (fun t => inv_pos.2 (r26_sqrt_pos hH hJ (hcS t))) (fun t => r26_sqrt_pos hH hJ (hcS t))
      hz hzp hz0 k
    have hfun : (fun t => xiCoordC H (P.x (P.T * t)) (r26ZAt H J (c t) (ζ t))) =
        fun t => (((Real.sqrt (r26β H J (c t)))⁻¹ * (vecToC (ζ t)).re +
          (Real.sqrt (r26β H J (c t)))⁻¹ *
            HryniewiczCriterion.omega0 (J (c t) (r26e H (c t)))
              (HryniewiczCriterion.xiFrame2 H (c t)) * (vecToC (ζ t)).im : ℝ) : ℂ) +
          ((Real.sqrt (r26β H J (c t)) * (vecToC (ζ t)).im : ℝ) : ℂ) * Complex.I := by
      funext t
      exact r26_coord hH hJ (hcS t) (ζ t)
    unfold HasXiLoopWind
    rw [hfun]
    exact hA

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

section
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- The linearized Cauchy–Riemann operator along `y` in the directions `e₁, e₂`:
`∂₁W + Jt(y) ∂₂W + (DJt(y) W) ∂₂y`. -/
noncomputable def linDbar (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (y W : D → E) (z : D) : E :=
  fderiv ℝ W z e₁ + Jt (y z) (fderiv ℝ W z e₂) + fderiv ℝ Jt (y z) (W z) (fderiv ℝ y z e₂)

lemma linDbar_add (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (y W₁ W₂ : D → E) (z : D)
    (h₁ : DifferentiableAt ℝ W₁ z) (h₂ : DifferentiableAt ℝ W₂ z) :
    linDbar Jt e₁ e₂ y (fun q => W₁ q + W₂ q) z =
      linDbar Jt e₁ e₂ y W₁ z + linDbar Jt e₁ e₂ y W₂ z := by
  unfold linDbar
  rw [fderiv_fun_add h₁ h₂]
  simp only [ContinuousLinearMap.add_apply, map_add]
  abel

lemma linDbar_smul (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (y W : D → E) (f : D → ℝ) (z : D)
    (hf : DifferentiableAt ℝ f z) (hW : DifferentiableAt ℝ W z) :
    linDbar Jt e₁ e₂ y (fun q => f q • W q) z =
      f z • linDbar Jt e₁ e₂ y W z + fderiv ℝ f z e₁ • W z +
        fderiv ℝ f z e₂ • Jt (y z) (W z) := by
  unfold linDbar
  rw [fderiv_fun_smul hf hW]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_add]
  abel

/-- Linearization of the Cauchy–Riemann equation along a `C²` family. -/
theorem linDbar_eq_zero_of_family (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (G : D × ℝ → E) (z₀ : D) (τ₀ : ℝ)
    (hG : ContDiffAt ℝ 2 G (z₀, τ₀)) (hJt : DifferentiableAt ℝ Jt (G (z₀, τ₀)))
    (hhol : ∀ᶠ q in 𝓝 (z₀, τ₀),
      fderiv ℝ G q (e₁, 0) + Jt (G q) (fderiv ℝ G q (e₂, 0)) = 0) :
    linDbar Jt e₁ e₂ (fun z => G (z, τ₀)) (fun z => fderiv ℝ G (z, τ₀) (0, 1)) z₀ = 0 := by
  set q₀ : D × ℝ := (z₀, τ₀) with hq₀
  have hGd : DifferentiableAt ℝ G q₀ := hG.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ G) q₀ :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : ∀ a b, fderiv ℝ (fderiv ℝ G) q₀ a b = fderiv ℝ (fderiv ℝ G) q₀ b a := by
    have := hG.isSymmSndFDerivAt (by simp)
    exact fun a b => this a b
  have hinc : ∀ z : D, HasFDerivAt (fun z => (z, τ₀)) (ContinuousLinearMap.inl ℝ D ℝ) z :=
    fun z => (hasFDerivAt_id z).prodMk (hasFDerivAt_const τ₀ z)
  -- the slice derivative of `G`
  have hy : fderiv ℝ (fun z => G (z, τ₀)) z₀ = (fderiv ℝ G q₀).comp (ContinuousLinearMap.inl ℝ D ℝ) :=
    (hGd.hasFDerivAt.comp z₀ (hinc z₀)).fderiv
  -- the slice derivative of `∂_τ G`
  have hW : HasFDerivAt (fun z => fderiv ℝ G (z, τ₀) ((0 : D), (1 : ℝ)))
      (((fderiv ℝ (fderiv ℝ G) q₀).comp (ContinuousLinearMap.inl ℝ D ℝ)).flip ((0 : D), (1 : ℝ))) z₀ := by
    have h1 : HasFDerivAt (fun z => fderiv ℝ G (z, τ₀))
        ((fderiv ℝ (fderiv ℝ G) q₀).comp (ContinuousLinearMap.inl ℝ D ℝ)) z₀ :=
      hD.hasFDerivAt.comp z₀ (hinc z₀)
    have := h1.clm_apply (hasFDerivAt_const (((0 : D), (1 : ℝ))) z₀)
    convert this using 1
    ext1 v
    simp
  -- differentiate the equation along `∂_τ`
  set A : D × ℝ → E := fun q => fderiv ℝ G q (e₁, 0) + Jt (G q) (fderiv ℝ G q (e₂, 0)) with hA
  have hA0 : A =ᶠ[𝓝 q₀] fun _ => 0 := hhol
  have hAd : HasFDerivAt A
      (((fderiv ℝ (fderiv ℝ G) q₀).flip (e₁, 0)) +
        ((fderiv ℝ Jt (G q₀)).comp (fderiv ℝ G q₀)).flip (fderiv ℝ G q₀ (e₂, 0)) +
          (Jt (G q₀)).comp ((fderiv ℝ (fderiv ℝ G) q₀).flip (e₂, 0))) q₀ := by
    have h1 := hD.hasFDerivAt.clm_apply (hasFDerivAt_const ((e₁, (0 : ℝ))) q₀)
    have h2 := hD.hasFDerivAt.clm_apply (hasFDerivAt_const ((e₂, (0 : ℝ))) q₀)
    have h3 : HasFDerivAt (fun q => Jt (G q)) ((fderiv ℝ Jt (G q₀)).comp (fderiv ℝ G q₀)) q₀ :=
      hJt.hasFDerivAt.comp q₀ hGd.hasFDerivAt
    have h4 := h3.clm_apply h2
    refine (h1.add h4).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [add_assoc, add_comm, add_left_comm]
  have h00 : (((fderiv ℝ (fderiv ℝ G) q₀).flip (e₁, 0)) +
        ((fderiv ℝ Jt (G q₀)).comp (fderiv ℝ G q₀)).flip (fderiv ℝ G q₀ (e₂, 0)) +
          (Jt (G q₀)).comp ((fderiv ℝ (fderiv ℝ G) q₀).flip (e₂, 0))) = 0 := by
    have h' : HasFDerivAt A (0 : D × ℝ →L[ℝ] E) q₀ :=
      (hasFDerivAt_const (0 : E) q₀).congr_of_eventuallyEq hA0
    exact hAd.unique h'
  have hval := DFunLike.congr_fun h00 ((0 : D), (1 : ℝ))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hval
  unfold linDbar
  rw [hW.fderiv, hy]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]
  rw [hsym (e₁, 0) (0, 1), hsym (e₂, 0) (0, 1)]
  rw [← hval]
  abel

/-- The coefficient identity of a solution of the linearized equation in a frame
`τ₁, τ₂ = J τ₁, F₁, F₂ = J F₁`. -/
theorem linDbar_frame_identity (Jt : E → E →L[ℝ] E) (e₁ e₂ : D) (y W τ₁ τ₂ F₁ F₂ : D → E)
    (f₁ f₂ n₁ n₂ : D → ℝ) (z : D)
    (hf₁ : DifferentiableAt ℝ f₁ z) (hf₂ : DifferentiableAt ℝ f₂ z)
    (hn₁ : DifferentiableAt ℝ n₁ z) (hn₂ : DifferentiableAt ℝ n₂ z)
    (hτ₁ : DifferentiableAt ℝ τ₁ z) (hτ₂ : DifferentiableAt ℝ τ₂ z)
    (hF₁ : DifferentiableAt ℝ F₁ z) (hF₂ : DifferentiableAt ℝ F₂ z)
    (hW : W =ᶠ[𝓝 z] fun q => f₁ q • τ₁ q + f₂ q • τ₂ q + n₁ q • F₁ q + n₂ q • F₂ q)
    (hL : linDbar Jt e₁ e₂ y W z = 0)
    (hLτ₁ : linDbar Jt e₁ e₂ y τ₁ z = 0) (hLτ₂ : linDbar Jt e₁ e₂ y τ₂ z = 0)
    (hJτ₁ : Jt (y z) (τ₁ z) = τ₂ z) (hJτ₂ : Jt (y z) (τ₂ z) = -τ₁ z)
    (hJF₁ : Jt (y z) (F₁ z) = F₂ z) (hJF₂ : Jt (y z) (F₂ z) = -F₁ z) :
    (fderiv ℝ f₁ z e₁ - fderiv ℝ f₂ z e₂) • τ₁ z + (fderiv ℝ f₁ z e₂ + fderiv ℝ f₂ z e₁) • τ₂ z +
      (fderiv ℝ n₁ z e₁ - fderiv ℝ n₂ z e₂) • F₁ z + (fderiv ℝ n₁ z e₂ + fderiv ℝ n₂ z e₁) • F₂ z +
      n₁ z • linDbar Jt e₁ e₂ y F₁ z + n₂ z • linDbar Jt e₁ e₂ y F₂ z = 0 := by
  have hcongr : linDbar Jt e₁ e₂ y W z = linDbar Jt e₁ e₂ y
      (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q + n₁ q • F₁ q + n₂ q • F₂ q) z := by
    unfold linDbar
    rw [hW.fderiv_eq, hW.self_of_nhds]
  rw [hcongr] at hL
  have d1 : DifferentiableAt ℝ (fun q => f₁ q • τ₁ q) z := hf₁.smul hτ₁
  have d2 : DifferentiableAt ℝ (fun q => f₂ q • τ₂ q) z := hf₂.smul hτ₂
  have d3 : DifferentiableAt ℝ (fun q => n₁ q • F₁ q) z := hn₁.smul hF₁
  have d4 : DifferentiableAt ℝ (fun q => n₂ q • F₂ q) z := hn₂.smul hF₂
  have d12 : DifferentiableAt ℝ (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q) z := d1.add d2
  have d123 : DifferentiableAt ℝ (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q + n₁ q • F₁ q) z := d12.add d3
  rw [linDbar_add Jt e₁ e₂ y (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q + n₁ q • F₁ q)
      (fun q => n₂ q • F₂ q) z d123 d4,
    linDbar_add Jt e₁ e₂ y (fun q => f₁ q • τ₁ q + f₂ q • τ₂ q) (fun q => n₁ q • F₁ q) z d12 d3,
    linDbar_add Jt e₁ e₂ y (fun q => f₁ q • τ₁ q) (fun q => f₂ q • τ₂ q) z d1 d2,
    linDbar_smul Jt e₁ e₂ y _ _ z hf₁ hτ₁, linDbar_smul Jt e₁ e₂ y _ _ z hf₂ hτ₂,
    linDbar_smul Jt e₁ e₂ y _ _ z hn₁ hF₁, linDbar_smul Jt e₁ e₂ y _ _ z hn₂ hF₂,
    hLτ₁, hLτ₂, hJτ₁, hJτ₂, hJF₁, hJF₂] at hL
  refine Eq.trans ?_ hL
  simp only [smul_zero]
  module

end

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff

/-! ### A frame map on `V 1` and its inverse -/

/-- The four coordinate indices of `V 1`. -/
abbrev fi0 : Fin (2 * (1 + 1)) := ⟨0, by norm_num⟩
abbrev fi1 : Fin (2 * (1 + 1)) := ⟨1, by norm_num⟩
abbrev fi2 : Fin (2 * (1 + 1)) := ⟨2, by norm_num⟩
abbrev fi3 : Fin (2 * (1 + 1)) := ⟨3, by norm_num⟩

lemma fas_sum (f : Fin (2 * (1 + 1)) → ℝ) : ∑ k, f k = f fi0 + f fi1 + f fi2 + f fi3 :=
  Fin.sum_univ_four f

/-- `v ↦ v₀ a + v₁ b + v₂ c + v₃ d`. -/
noncomputable def fasB (a b c d : V 1) : V 1 →L[ℝ] V 1 :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ) fi0).smulRight a +
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ) fi1).smulRight b +
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ) fi2).smulRight c +
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ) fi3).smulRight d

lemma fasB_apply (a b c d v : V 1) :
    fasB a b c d v = v fi0 • a + v fi1 • b + v fi2 • c + v fi3 • d := by
  simp [fasB]

lemma fasB_contDiffAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {a b c d : X → V 1}
    {x : X} (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x)
    (hd : ContDiffAt ℝ ∞ d x) : ContDiffAt ℝ ∞ (fun y => fasB (a y) (b y) (c y) (d y)) x := by
  unfold fasB
  exact ((((contDiffAt_const.smulRight ha).add (contDiffAt_const.smulRight hb)).add
    (contDiffAt_const.smulRight hc)).add (contDiffAt_const.smulRight hd))

lemma fas_isUnit_of_injective (B : V 1 →L[ℝ] V 1) (h : Function.Injective B) : IsUnit B := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨h, (LinearMap.injective_iff_surjective (f := (B : V 1 →ₗ[ℝ] V 1))).1 h⟩

/-- The coordinates in an invertible frame. -/
noncomputable def fasC (a b c d : V 1) : V 1 →L[ℝ] V 1 := Ring.inverse (fasB a b c d)

section coords
variable {a b c d : V 1} (hB : IsUnit (fasB a b c d))
include hB

lemma fasC_expand (w : V 1) :
    (fasC a b c d w) fi0 • a + (fasC a b c d w) fi1 • b + (fasC a b c d w) fi2 • c +
      (fasC a b c d w) fi3 • d = w := by
  rw [← fasB_apply]
  have h : fasB a b c d * fasC a b c d = 1 := Ring.mul_inverse_cancel _ hB
  exact DFunLike.congr_fun h w

lemma fasC_comb (p q r s : ℝ) (i : Fin (2 * (1 + 1))) :
    fasC a b c d (p • a + q • b + r • c + s • d) i =
      (![p, q, r, s] : Fin 4 → ℝ) (Fin.cast (by norm_num) i) := by
  have hv : p • a + q • b + r • c + s • d =
      fasB a b c d (fun k => (![p, q, r, s] : Fin 4 → ℝ) (Fin.cast (by norm_num) k)) := by
    rw [fasB_apply]; simp [fi0, fi1, fi2, fi3]
  have h : fasC a b c d * fasB a b c d = 1 := Ring.inverse_mul_cancel _ hB
  rw [hv]
  exact congrFun (DFunLike.congr_fun h _) i

lemma fasC_comb2 (p q r s : ℝ) :
    fasC a b c d (p • a + q • b + r • c + s • d) fi2 = r := by
  rw [fasC_comb hB]; rfl

lemma fasC_comb3 (p q r s : ℝ) :
    fasC a b c d (p • a + q • b + r • c + s • d) fi3 = s := by
  rw [fasC_comb hB]; rfl

lemma fasC_comb0 (p q r s : ℝ) :
    fasC a b c d (p • a + q • b + r • c + s • d) fi0 = p := by
  rw [fasC_comb hB]; rfl

lemma fasC_comb1 (p q r s : ℝ) :
    fasC a b c d (p • a + q • b + r • c + s • d) fi1 = q := by
  rw [fasC_comb hB]; rfl

/-- Coordinates of `L w` for a map rotating the frame. -/
lemma fasC_rot (L : V 1 →L[ℝ] V 1) (hab : L a = b) (hba : L b = -a) (hcd : L c = d)
    (hdc : L d = -c) (w : V 1) :
    fasC a b c d (L w) fi2 = -(fasC a b c d w fi3) ∧
      fasC a b c d (L w) fi3 = fasC a b c d w fi2 := by
  have hexp := fasC_expand hB w
  set C := fasC a b c d with hC
  have hL : L w = (-(C w fi1)) • a + (C w fi0) • b + (-(C w fi3)) • c + (C w fi2) • d := by
    conv_lhs => rw [← hexp]
    simp only [map_add, map_smul, hab, hba, hcd, hdc]
    module
  rw [hL]
  exact ⟨fasC_comb2 hB _ _ _ _, fasC_comb3 hB _ _ _ _⟩

/-- A combination of the frame with coefficients `A, B, C', D'` and vectors `G₁, G₂` vanishing:
the two normal components. -/
lemma fasC_identity {A B' C' D' n₁ n₂ : ℝ} {G₁ G₂ : V 1}
    (h : A • a + B' • b + C' • c + D' • d + n₁ • G₁ + n₂ • G₂ = 0) :
    C' + n₁ * fasC a b c d G₁ fi2 + n₂ * fasC a b c d G₂ fi2 = 0 ∧
      D' + n₁ * fasC a b c d G₁ fi3 + n₂ * fasC a b c d G₂ fi3 = 0 := by
  have h0 := congrArg (fasC a b c d) h
  simp only [map_add, map_smul, map_zero] at h0
  have h1 : fasC a b c d (A • a + B' • b + C' • c + D' • d) =
      A • fasC a b c d a + B' • fasC a b c d b + C' • fasC a b c d c + D' • fasC a b c d d := by
    simp only [map_add, map_smul]
  rw [← h1] at h0
  have e2 := congrFun h0 fi2
  have e3 := congrFun h0 fi3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2 e3
  rw [fasC_comb2 hB] at e2
  rw [fasC_comb3 hB] at e3
  exact ⟨e2, e3⟩

end coords

/-! ### Point identities for `J̃` -/

section points
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

omit hH in
lemma fas_Jt_apply (y v : V 1) :
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
lemma fas_y_eq {y : V 1} (hy : y ≠ 0) : y = (scaleToS H y)⁻¹ • proj H y := by
  have hr := (ka_scale_spec H hH y hy).1
  rw [proj, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

include hH in
/-- `J̃` sends the lifted Reeb field to `-∂ₐ`. -/
lemma fas_Jt_lift {y : V 1} (hy : y ≠ 0) :
    Jtilde H J y ((scaleToS H y)⁻¹ • reeb H (proj H y)) = -((2 : ℝ) • y) := by
  have hr := (ka_scale_spec H hH y hy).1
  have hx : proj H y ∈ energySurface H := (ka_scale_spec H hH y hy).2
  obtain ⟨-, h1, h2, -⟩ := ka_reeb_spec H hH _ hx
  have hl : liouville (proj H y) ((scaleToS H y)⁻¹ • reeb H (proj H y)) = (scaleToS H y)⁻¹ := by
    rw [← ka_liouvilleCLM_apply, map_smul, ka_liouvilleCLM_apply, h1, smul_eq_mul, mul_one]
  have hd : fderiv ℝ H (proj H y) ((scaleToS H y)⁻¹ • reeb H (proj H y)) = 0 := by
    rw [map_smul, h2, smul_zero]
  rw [fas_Jt_apply, hl, hd, mul_inv_cancel₀ hr.ne']
  simp

include hH in
/-- `J̃` sends `∂ₐ = 2y` to the lifted Reeb field. -/
lemma fas_Jt_two {y : V 1} (hy : y ≠ 0) :
    Jtilde H J y ((2 : ℝ) • y) = (scaleToS H y)⁻¹ • reeb H (proj H y) := by
  have hr := (ka_scale_spec H hH y hy).1
  have hx : proj H y ∈ energySurface H := (ka_scale_spec H hH y hy).2
  have hD : 0 < fderiv ℝ H (proj H y) (proj H y) := hH.2.2 _ hx
  have hye := fas_y_eq hH hy
  have hy2 : (2 : ℝ) • y = (2 * (scaleToS H y)⁻¹) • proj H y := by
    conv_lhs => rw [hye]
    rw [smul_smul]
  have hl : liouville (proj H y) ((2 : ℝ) • y) = 0 := by
    rw [hy2, ← ka_liouvilleCLM_apply, map_smul, ka_liouvilleCLM_apply]
    unfold liouville
    rw [ka_om_self]; simp
  have hd : scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y)) *
      fderiv ℝ H (proj H y) ((2 : ℝ) • y) = 1 := by
    rw [hy2, map_smul, smul_eq_mul]
    field_simp
  rw [fas_Jt_apply, hl, hd]
  simp

include hH in
/-- On `ξ`, `J̃` is `J`. -/
lemma fas_Jt_xi {y p : V 1} (hp : IsInXi H (proj H y) p) :
    Jtilde H J y p = J (proj H y) p := by
  rw [fas_Jt_apply, hp.1, hp.2]
  simp

include hH in
lemma fas_ne_zero_of_mem {x : V 1} (hx : x ∈ energySurface H) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

include hH in
lemma fas_scale_mem {x : V 1} (hx : x ∈ energySurface H) : scaleToS H x = 1 :=
  ka_scale_unique H hH x (fas_ne_zero_of_mem hH hx) 1 one_pos (by rw [one_smul]; exact hx)

include hH in
lemma fas_Jt_two_mem {x : V 1} (hx : x ∈ energySurface H) :
    Jtilde H J x ((2 : ℝ) • x) = reeb H x := by
  have h := fas_Jt_two (J := J) hH (fas_ne_zero_of_mem hH hx)
  rwa [fas_scale_mem hH hx, N1.proj_of_mem H hH hx, inv_one, one_smul] at h

include hH in
lemma fas_Jt_reeb_mem {x : V 1} (hx : x ∈ energySurface H) :
    Jtilde H J x (reeb H x) = -((2 : ℝ) • x) := by
  have h := fas_Jt_lift (J := J) hH (fas_ne_zero_of_mem hH hx)
  rwa [fas_scale_mem hH hx, N1.proj_of_mem H hH hx, inv_one, one_smul] at h

include hH in
lemma fas_Jt_xi_mem {x p : V 1} (hx : x ∈ energySurface H) (hp : IsInXi H x p) :
    Jtilde H J x p = J x p := by
  have h := fas_Jt_xi (J := J) hH (y := x) (p := p) (by rwa [N1.proj_of_mem H hH hx])
  rwa [N1.proj_of_mem H hH hx] at h

include hH hJ in
lemma fas_Jt_differentiableAt {y : V 1} (hy : y ≠ 0) : DifferentiableAt ℝ (Jtilde H J) y := by
  obtain ⟨hO, hC, -⟩ := (jtilde_isAlmostComplexOn H hH J hJ).1
  exact (hC.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)

include hH hJ in
lemma fas_Jt_contDiffAt {y : V 1} (hy : y ≠ 0) : ContDiffAt ℝ ∞ (Jtilde H J) y := by
  obtain ⟨hO, hC, -⟩ := (jtilde_isAlmostComplexOn H hH J hJ).1
  exact hC.contDiffAt (hO.mem_nhds hy)

include hH hJ in
lemma fas_Jt_sq {y : V 1} (hy : y ≠ 0) (v : V 1) :
    Jtilde H J y (Jtilde H J y v) = -v := by
  have h := (jtilde_isAlmostComplexOn H hH J hJ).1.2.2 y hy
  simpa using DFunLike.congr_fun h v

include hH hJ in
lemma fas_Jt_scale {y : V 1} (hy : y ≠ 0) {c : ℝ} (hc : 0 < c) :
    Jtilde H J (c • y) = Jtilde H J y :=
  (jtilde_isAlmostComplexOn H hH J hJ).2.2.2.2 y hy c hc

include hH hJ in
/-- `DJ̃(c y) = c⁻¹ DJ̃(y)`. -/
lemma fas_dJt_scale {y : V 1} (hy : y ≠ 0) {c : ℝ} (hc : 0 < c) (v : V 1) :
    fderiv ℝ (Jtilde H J) (c • y) v = c⁻¹ • fderiv ℝ (Jtilde H J) y v := by
  have hcy : c • y ≠ 0 := smul_ne_zero hc.ne' hy
  have hd := (fas_Jt_differentiableAt hH hJ hcy).hasFDerivAt
  have hl : HasFDerivAt (fun w : V 1 => c • w) (c • ContinuousLinearMap.id ℝ (V 1)) y :=
    (hasFDerivAt_id y).const_smul c
  have h1 := hd.comp y hl
  have hev : (Jtilde H J ∘ fun w : V 1 => c • w) =ᶠ[𝓝 y] Jtilde H J := by
    filter_upwards [isOpen_ne.mem_nhds hy] with w hw
    exact fas_Jt_scale hH hJ hw hc
  have h2 := (h1.congr_of_eventuallyEq hev.symm).fderiv
  have h3 := (fas_Jt_differentiableAt hH hJ hy).hasFDerivAt
  have h4 : fderiv ℝ (Jtilde H J) y = (fderiv ℝ (Jtilde H J) (c • y)).comp
      (c • ContinuousLinearMap.id ℝ (V 1)) := by
    have := (h1.congr_of_eventuallyEq hev.symm)
    exact h3.unique this
  rw [h4]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

include hH hJ in
/-- `DJ̃(x)[v] R(x) = -2v - J̃(x) DR(x)[v]` for `v ∈ ξ_x`. -/
lemma fas_dJt_reeb {x v : V 1} (hx : x ∈ energySurface H) (hv : IsInXi H x v) :
    fderiv ℝ (Jtilde H J) x v (reeb H x) =
      -((2 : ℝ) • v) - Jtilde H J x (fderiv ℝ (reeb H) x v) := by
  have hx0 := fas_ne_zero_of_mem hH hx
  have hr1 := fas_scale_mem hH hx
  have hpx := N1.proj_of_mem H hH hx
  have hs := ka_scale_hasFDerivAt H hH x hx0
  have hsi : HasFDerivAt (fun y => (scaleToS H y)⁻¹)
      (-(((scaleToS H x) ^ 2)⁻¹) • ((-(scaleToS H x ^ 2 / fderiv ℝ H (proj H x) (proj H x))) •
        fderiv ℝ H (proj H x))) x := by
    have := (hasDerivAt_inv (x := scaleToS H x) (by rw [hr1]; exact one_ne_zero)).comp_hasFDerivAt
      x hs
    exact this
  have hp := N1.proj_hasFDerivAt_mem H hH hx
  have hR : HasFDerivAt (reeb H) (fderiv ℝ (reeb H) x) (proj H x) := by
    rw [hpx]
    exact ((ka_reeb_contDiffAt H hH x hx).differentiableAt (by simp)).hasFDerivAt
  have hRp := hR.comp x hp
  have hL := hsi.smul hRp
  have hJd := (fas_Jt_differentiableAt hH hJ hx0).hasFDerivAt
  have hA := hJd.clm_apply hL
  have hev : (fun y => Jtilde H J y ((scaleToS H y)⁻¹ • (reeb H ∘ proj H) y)) =ᶠ[𝓝 x]
      fun y => -((2 : ℝ) • y) := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
    exact fas_Jt_lift hH hy
  have hB : HasFDerivAt (fun y : V 1 => -((2 : ℝ) • y)) (-((2 : ℝ) • ContinuousLinearMap.id ℝ (V 1))) x :=
    ((hasFDerivAt_id x).const_smul (2 : ℝ)).neg
  have hu := (hA.congr_of_eventuallyEq hev.symm).unique hB
  have hval := DFunLike.congr_fun hu v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply,
    Function.comp_apply, hpx, hr1, hv.2] at hval
  simp only [inv_one, one_smul, smul_eq_mul, mul_zero, zero_div, zero_smul, sub_zero, add_zero,
    zero_add, map_zero, smul_zero] at hval
  simp only [Pi.smul_apply', Function.comp_apply, hr1, hpx, inv_one, one_smul] at hval
  rw [eq_sub_iff_add_eq, add_comm]
  exact hval

end points

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff

section frame
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

/-- Where the frame `W, J W` is smooth. -/
def fasO (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) : Set (V 1) :=
  {x | 0 < fderiv ℝ H x x ∧ 0 < r26β H J x}

lemma fas_quat2_contDiff : ContDiff ℝ ∞ HryniewiczCriterion.quatQ2 := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [HryniewiczCriterion.quatQ2] <;> fun_prop

include hH in
lemma fas_e_contDiffAt {x : V 1} (hx : 0 < fderiv ℝ H x x) : ContDiffAt ℝ ∞ (r26e H) x := by
  have hdH := ka_dH_contDiff H hH.1
  have hQ := fas_quat2_contDiff
  have hne := hx.ne'
  have hraw : ContDiffAt ℝ ∞ (fun y : V 1 => HryniewiczCriterion.xiFrameRaw H HryniewiczCriterion.quatQ2 y) x := by
    unfold HryniewiczCriterion.xiFrameRaw
    exact hQ.contDiffAt.sub ((((hdH.clm_apply hQ).contDiffAt).div
      ((hdH.clm_apply contDiff_id).contDiffAt) hne).smul contDiffAt_id)
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hdot : ContDiff ℝ ∞ (fun y : V 1 => HryniewiczCriterion.dot4 y y) := by
    have h := fun i : Fin 4 => (contDiff_apply ℝ ℝ (i : Fin 4) : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y i))
    simp only [HryniewiczCriterion.dot4, Fin.sum_univ_four]
    exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add ((h 3).mul (h 3))
  have hdne : HryniewiczCriterion.dot4 x x ≠ 0 := (HryniewiczCriterion.r26_dot4_pos hx0).ne'
  have hnorm : ContDiffAt ℝ ∞ (fun y : V 1 => HryniewiczCriterion.euclidNorm y) x :=
    hdot.contDiffAt.sqrt hdne
  have hnne : HryniewiczCriterion.euclidNorm x ≠ 0 := fun h => by
    have := HryniewiczCriterion.r26_euclidNorm_sq x
    rw [h] at this
    exact hdne (by linarith)
  exact (hnorm.inv hnne).smul hraw

include hH hJ in
lemma fas_β_contDiffAt {x : V 1} (hx : 0 < fderiv ℝ H x x) : ContDiffAt ℝ ∞ (r26β H J) x := by
  have he := fas_e_contDiffAt hH hx
  have hJe : ContDiffAt ℝ ∞ (fun y => J y (r26e H y)) x := hJ.1.contDiffAt.clm_apply he
  have hc : ∀ (p q : V 1 → V 1) (i j : Fin 4), ContDiffAt ℝ ∞ p x → ContDiffAt ℝ ∞ q x →
      ContDiffAt ℝ ∞ (fun y => p y i * q y j) x := fun p q i j hp hq =>
    (contDiffAt_pi.1 hp i).mul (contDiffAt_pi.1 hq j)
  unfold r26β HryniewiczCriterion.omega0
  exact (((hc _ _ _ _ he hJe).sub (hc _ _ _ _ he hJe)).add (hc _ _ _ _ he hJe)).sub
    (hc _ _ _ _ he hJe)

include hH hJ in
lemma fas_isOpen_O : IsOpen (fasO H J) := by
  have h1 : IsOpen {x : V 1 | 0 < fderiv ℝ H x x} :=
    isOpen_lt continuous_const ((ka_dH_contDiff H hH.1).clm_apply contDiff_id).continuous
  have hc : ContinuousOn (r26β H J) {x : V 1 | 0 < fderiv ℝ H x x} :=
    fun x hx => (fas_β_contDiffAt hH hJ hx).continuousAt.continuousWithinAt
  exact hc.isOpen_inter_preimage h1 isOpen_Ioi

include hH hJ in
lemma fas_mem_O {x : V 1} (hx : x ∈ energySurface H) : x ∈ fasO H J :=
  ⟨hH.2.2 x hx, r26_β_pos hH hJ hx⟩

include hH hJ in
lemma fas_W_contDiffAt {x : V 1} (hx : x ∈ fasO H J) : ContDiffAt ℝ ∞ (r26W H J) x := by
  have hβ := fas_β_contDiffAt hH hJ hx.1
  have hs : ContDiffAt ℝ ∞ (fun y => Real.sqrt (r26β H J y)) x := hβ.sqrt hx.2.ne'
  have hsi : ContDiffAt ℝ ∞ (fun y => (Real.sqrt (r26β H J y))⁻¹) x :=
    hs.inv (Real.sqrt_pos.2 hx.2).ne'
  exact hsi.smul (fas_e_contDiffAt hH hx.1)

/-- The two frame vectors. -/
noncomputable def fasE (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (j : Fin 1 ⊕ Fin 1) (x : V 1) : V 1 :=
  Sum.elim (fun _ => r26W H J x) (fun _ => J x (r26W H J x)) j

include hH hJ in
lemma fasE_contDiffAt (j : Fin 1 ⊕ Fin 1) {x : V 1} (hx : x ∈ fasO H J) :
    ContDiffAt ℝ ∞ (fasE H J j) x := by
  rcases j with j | j
  · exact fas_W_contDiffAt hH hJ hx
  · exact hJ.1.contDiffAt.clm_apply (fas_W_contDiffAt hH hJ hx)

/-- The index in the frame coordinates. -/
def fasI : Fin 1 ⊕ Fin 1 → Fin (2 * (1 + 1)) := Sum.elim (fun _ => fi2) (fun _ => fi3)

include hH hJ in
/-- Hryniewicz, Remark 2.6 in the frame `W, J W`. -/
lemma fas_frame (P : ReebOrbit H) :
    IsUnitaryXiFrame J P (fun t => r26ZAt H J (P.x (P.T * t))) ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => r26ZAt H J (P.x (P.T * t)) (ζ t)) k ↔
            HasLoopWind (fun t => vecToC (ζ t)) k) := by
  set c : ℝ → V 1 := fun t => P.x (P.T * t) with hcdef
  have hc : ContDiff ℝ ∞ c := (ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_id)
  have hcper : ∀ t, c (t + 1) = c t := fun t => by
    simp only [hcdef, mul_add, mul_one, P.periodic]
  have hcS : ∀ t, H (c t) = 1 := fun t => P.mem _
  have hpos : ∀ t, 0 < fderiv ℝ H (c t) (c t) := fun t => r26_pos hH (hcS t)
  have he : ContDiff ℝ ∞ (fun t => r26e H (c t)) :=
    HryniewiczCriterion.r26_cd_xiFrame hH.1 hc hpos HryniewiczCriterion.quatQ2
      (HryniewiczCriterion.r26_cd_quatQ2 hc)
  have he2 : ContDiff ℝ ∞ (fun t => HryniewiczCriterion.xiFrame2 H (c t)) :=
    HryniewiczCriterion.r26_cd_xiFrame hH.1 hc hpos HryniewiczCriterion.quatQ1
      (HryniewiczCriterion.r26_cd_quatQ1 hc)
  have hJc : ContDiff ℝ ∞ (fun t => J (c t)) := hJ.1.comp hc
  have hβ : ContDiff ℝ ∞ (fun t => r26β H J (c t)) :=
    HryniewiczCriterion.r26_cd_omega0 he (hJc.clm_apply he)
  have hs : ContDiff ℝ ∞ (fun t => Real.sqrt (r26β H J (c t))) :=
    hβ.sqrt (fun t => (r26_β_pos hH hJ (hcS t)).ne')
  have hsinv : ContDiff ℝ ∞ (fun t => (Real.sqrt (r26β H J (c t)))⁻¹) :=
    hs.inv (fun t => (r26_sqrt_pos hH hJ (hcS t)).ne')
  have hW : ContDiff ℝ ∞ (fun t => r26W H J (c t)) := hsinv.smul he
  have hJW : ContDiff ℝ ∞ (fun t => J (c t) (r26W H J (c t))) := hJc.clm_apply hW
  have hb : ContDiff ℝ ∞ (fun t => (Real.sqrt (r26β H J (c t)))⁻¹ *
      HryniewiczCriterion.omega0 (J (c t) (r26e H (c t))) (HryniewiczCriterion.xiFrame2 H (c t))) :=
    hsinv.mul (HryniewiczCriterion.r26_cd_omega0 (hJc.clm_apply he) he2)
  refine ⟨⟨?_, ?_, fun t => ⟨r26_unitary_xi hH hJ (hcS t),
    r26_unitary_surj hH hJ (hcS t), r26_unitary_J hH hJ (hcS t),
    r26_unitary_omega hH hJ (hcS t)⟩⟩, ?_⟩
  · exact (contDiff_const.smulRight hW).add (contDiff_const.smulRight hJW)
  · intro t; simp only [hcdef, mul_add, mul_one, P.periodic]
  · intro ζ hζ hζp hζ0 k
    have h1 : Continuous fun t => ζ t (Sum.inl 0) :=
      (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).continuous.comp hζ
    have h2 : Continuous fun t => ζ t (Sum.inr 0) :=
      (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).continuous.comp hζ
    have hzeq : (fun t => vecToC (ζ t)) = fun t => ((ζ t (Sum.inl 0) : ℝ) : ℂ) +
        ((ζ t (Sum.inr 0) : ℝ) : ℂ) * Complex.I :=
      funext fun t => Complex.ext (by simp [vecToC]) (by simp [vecToC])
    have hz : Continuous (fun t => vecToC (ζ t)) := by rw [hzeq]; fun_prop
    have hzp : Function.Periodic (fun t => vecToC (ζ t)) 1 := fun t => by
      simp only [hζp t]
    have hz0 : ∀ t, vecToC (ζ t) ≠ 0 := by
      intro t h
      apply hζ0 t
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [vecToC, Complex.zero_re, Complex.zero_im] at hre him
      ext i
      rcases i with i | i <;> fin_cases i
      · simpa using hre
      · simpa using him
    have hA := hasLoopWind_triangular_iff hsinv.continuous hb.continuous hs.continuous
      (fun t => by simp only [hcper]) (fun t => by simp only [hcper])
      (fun t => by simp only [hcper])
      (fun t => inv_pos.2 (r26_sqrt_pos hH hJ (hcS t))) (fun t => r26_sqrt_pos hH hJ (hcS t))
      hz hzp hz0 k
    have hfun : (fun t => xiCoordC H (P.x (P.T * t)) (r26ZAt H J (c t) (ζ t))) =
        fun t => (((Real.sqrt (r26β H J (c t)))⁻¹ * (vecToC (ζ t)).re +
          (Real.sqrt (r26β H J (c t)))⁻¹ *
            HryniewiczCriterion.omega0 (J (c t) (r26e H (c t)))
              (HryniewiczCriterion.xiFrame2 H (c t)) * (vecToC (ζ t)).im : ℝ) : ℂ) +
          ((Real.sqrt (r26β H J (c t)) * (vecToC (ζ t)).im : ℝ) : ℂ) * Complex.I := by
      funext t
      exact r26_coord hH hJ (hcS t) (ζ t)
    unfold HasXiLoopWind
    rw [hfun]
    exact hA

end frame

/-! ### The coefficient function on the end -/

/-- Data: the orbit defect, its derivative, the derivative of the `a`-defect. -/
abbrev FasE := V 1 × (ℝ × ℝ →L[ℝ] V 1) × (ℝ × ℝ →L[ℝ] ℝ)

section coeff
variable {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H)

/-- The point `x(φ) + δ`. -/
noncomputable def fX (q : ℝ × FasE) : V 1 := P.x q.1 + q.2.1
/-- `∂ₛw` from the data. -/
noncomputable def fDs (q : ℝ × FasE) : V 1 := q.2.2.1 (1, 0)
/-- `∂ₜw` from the data. -/
noncomputable def fDt (q : ℝ × FasE) : V 1 := P.T • reeb H (P.x q.1) + q.2.2.1 (0, 1)
/-- `∂ₛa` from the data. -/
noncomputable def fAs (q : ℝ × FasE) : ℝ := P.T + q.2.2.2 (1, 0)
/-- `∂ₜa` from the data. -/
noncomputable def fAt (q : ℝ × FasE) : ℝ := q.2.2.2 (0, 1)
/-- The rescaled tangent `r ∂ₛy`. -/
noncomputable def fC1 (q : ℝ × FasE) : V 1 := (2 * fAs P q) • fX P q + fDs q
/-- The rescaled tangent `r ∂ₜy`. -/
noncomputable def fC2 (q : ℝ × FasE) : V 1 := (2 * fAt q) • fX P q + fDt P q
/-- The frame map. -/
noncomputable def fBB (q : ℝ × FasE) : V 1 →L[ℝ] V 1 :=
  fasB (fC1 P q) (fC2 P q) (fasE H J (Sum.inl 0) (fX P q)) (fasE H J (Sum.inr 0) (fX P q))
/-- The frame coordinates. -/
noncomputable def fCC (q : ℝ × FasE) : V 1 →L[ℝ] V 1 :=
  fasC (fC1 P q) (fC2 P q) (fasE H J (Sum.inl 0) (fX P q)) (fasE H J (Sum.inr 0) (fX P q))
/-- `r D(ρ E_j)` in the data. -/
noncomputable def fG (j : Fin 1 ⊕ Fin 1) (q : ℝ × FasE) : V 1 :=
  fderiv ℝ (fasE H J j) (fX P q) (fDs q) +
    Jtilde H J (fX P q) (fderiv ℝ (fasE H J j) (fX P q) (fDt P q)) +
    fderiv ℝ (Jtilde H J) (fX P q) (fasE H J j (fX P q)) (fC2 P q) +
    (2 * fAs P q) • fasE H J j (fX P q) +
    (2 * fAt q) • Jtilde H J (fX P q) (fasE H J j (fX P q))
/-- The coefficient. -/
noncomputable def fPhi (i j : Fin 1 ⊕ Fin 1) (q : ℝ × FasE) : ℝ :=
  fCC J P q (fG J P j q) (fasI i)

/-- The good set. -/
def fU : Set (ℝ × FasE) := {q | fX P q ∈ fasO H J ∧ IsUnit (fBB J P q)}

lemma fX_per (φ : ℝ) (v : FasE) : fX P (φ + P.T, v) = fX P (φ, v) := by
  simp only [fX, P.periodic]
lemma fC1_per (φ : ℝ) (v : FasE) : fC1 P (φ + P.T, v) = fC1 P (φ, v) := by
  simp only [fC1, fAs, fDs, fX_per]
lemma fC2_per (φ : ℝ) (v : FasE) : fC2 P (φ + P.T, v) = fC2 P (φ, v) := by
  simp only [fC2, fAt, fDt, fX_per, P.periodic]
lemma fBB_per (φ : ℝ) (v : FasE) : fBB J P (φ + P.T, v) = fBB J P (φ, v) := by
  simp only [fBB, fX_per, fC1_per, fC2_per]
lemma fCC_per (φ : ℝ) (v : FasE) : fCC J P (φ + P.T, v) = fCC J P (φ, v) := by
  simp only [fCC, fX_per, fC1_per, fC2_per]
lemma fG_per (j : Fin 1 ⊕ Fin 1) (φ : ℝ) (v : FasE) : fG J P j (φ + P.T, v) = fG J P j (φ, v) := by
  simp only [fG, fX_per, fC2_per, fDs, fDt, fAs, fAt, P.periodic]
lemma fPhi_per (i j : Fin 1 ⊕ Fin 1) (φ : ℝ) (v : FasE) :
    fPhi J P i j (φ + P.T, v) = fPhi J P i j (φ, v) := by
  simp only [fPhi, fCC_per, fG_per]
lemma fU_per (φ : ℝ) (v : FasE) : (φ + P.T, v) ∈ fU J P ↔ (φ, v) ∈ fU J P := by
  simp only [fU, Set.mem_setOf_eq, fX_per, fBB_per]

end coeff

section smooth
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)

include hH in
lemma fX_contDiff : ContDiff ℝ ∞ (fX P) :=
  ((ReebOrbit.contDiff_x H hH P).comp contDiff_fst).add contDiff_snd.fst

lemma fDs_contDiff : ContDiff ℝ ∞ (fDs : ℝ × FasE → V 1) :=
  contDiff_snd.snd.fst.clm_apply contDiff_const

lemma fAs_contDiff : ContDiff ℝ ∞ (fAs P) :=
  contDiff_const.add (contDiff_snd.snd.snd.clm_apply contDiff_const)

lemma fAt_contDiff : ContDiff ℝ ∞ (fAt : ℝ × FasE → ℝ) :=
  contDiff_snd.snd.snd.clm_apply contDiff_const

include hH in
lemma fReeb_contDiff : ContDiff ℝ ∞ (fun φ : ℝ => reeb H (P.x φ)) := by
  refine contDiff_iff_contDiffAt.2 fun φ => ?_
  exact (ka_reeb_contDiffAt H hH _ (P.mem φ)).comp φ (ReebOrbit.contDiff_x H hH P).contDiffAt

include hH in
lemma fDt_contDiff : ContDiff ℝ ∞ (fDt P) := by
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × FasE => reeb H (P.x q.1)) :=
    (fReeb_contDiff hH P).comp contDiff_fst
  exact (h1.const_smul P.T).add (contDiff_snd.snd.fst.clm_apply contDiff_const)

include hH in
lemma fC1_contDiff : ContDiff ℝ ∞ (fC1 P) :=
  (contDiff_const.mul (fAs_contDiff P)).smul (fX_contDiff hH P) |>.add fDs_contDiff

include hH in
lemma fC2_contDiff : ContDiff ℝ ∞ (fC2 P) :=
  (contDiff_const.mul fAt_contDiff).smul (fX_contDiff hH P) |>.add (fDt_contDiff hH P)

include hH hJ in
lemma fE_contDiffAt (j : Fin 1 ⊕ Fin 1) {q : ℝ × FasE} (hq : fX P q ∈ fasO H J) :
    ContDiffAt ℝ ∞ (fun q => fasE H J j (fX P q)) q :=
  (fasE_contDiffAt hH hJ j hq).comp q (fX_contDiff hH P).contDiffAt

include hH hJ in
lemma fBB_contDiffAt {q : ℝ × FasE} (hq : fX P q ∈ fasO H J) :
    ContDiffAt ℝ ∞ (fBB J P) q :=
  fasB_contDiffAt (fC1_contDiff hH P).contDiffAt (fC2_contDiff hH P).contDiffAt
    (fE_contDiffAt hH hJ P _ hq) (fE_contDiffAt hH hJ P _ hq)

include hH hJ in
lemma fCC_contDiffAt {q : ℝ × FasE} (hq : q ∈ fU J P) : ContDiffAt ℝ ∞ (fCC J P) q := by
  obtain ⟨u, hu⟩ := hq.2
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (fBB J P q) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact h1.comp q (fBB_contDiffAt hH hJ P hq.1)

include hH hJ in
lemma fG_contDiffAt (j : Fin 1 ⊕ Fin 1) {q : ℝ × FasE} (hq : fX P q ∈ fasO H J) :
    ContDiffAt ℝ ∞ (fG J P j) q := by
  have hx : ContDiffAt ℝ ∞ (fX P) q := (fX_contDiff hH P).contDiffAt
  have hq0 : fX P q ≠ 0 := by
    intro h
    have := hq.1
    rw [h] at this
    simp at this
  have hE := fE_contDiffAt hH hJ P j hq
  have hDE : ContDiffAt ℝ ∞ (fun q => fderiv ℝ (fasE H J j) (fX P q)) q :=
    ((fasE_contDiffAt hH hJ j hq).fderiv_right (m := ∞) (by simp)).comp q hx
  have hJt : ContDiffAt ℝ ∞ (fun q => Jtilde H J (fX P q)) q :=
    (fas_Jt_contDiffAt hH hJ hq0).comp q hx
  have hDJ : ContDiffAt ℝ ∞ (fun q => fderiv ℝ (Jtilde H J) (fX P q)) q :=
    ((fas_Jt_contDiffAt hH hJ hq0).fderiv_right (m := ∞) (by simp)).comp q hx
  unfold fG
  exact (((((hDE.clm_apply fDs_contDiff.contDiffAt).add
    (hJt.clm_apply (hDE.clm_apply (fDt_contDiff hH P).contDiffAt))).add
    ((hDJ.clm_apply hE).clm_apply (fC2_contDiff hH P).contDiffAt)).add
    ((contDiffAt_const.mul (fAs_contDiff P).contDiffAt).smul hE)).add
    ((contDiffAt_const.mul fAt_contDiff.contDiffAt).smul (hJt.clm_apply hE)))

include hH hJ in
lemma fPhi_contDiffAt (i j : Fin 1 ⊕ Fin 1) {q : ℝ × FasE} (hq : q ∈ fU J P) :
    ContDiffAt ℝ ∞ (fPhi J P i j) q := by
  have h := (fCC_contDiffAt hH hJ P hq).clm_apply (fG_contDiffAt hH hJ P j hq.1)
  exact contDiffAt_pi.1 h (fasI i)

include hH hJ in
lemma fU_isOpen : IsOpen (fU J P) := by
  have hO := fas_isOpen_O hH hJ
  have h1 : IsOpen {q : ℝ × FasE | fX P q ∈ fasO H J} := hO.preimage (fX_contDiff hH P).continuous
  have hc : ContinuousOn (fBB J P) {q : ℝ × FasE | fX P q ∈ fasO H J} :=
    fun q hq => (fBB_contDiffAt hH hJ P hq).continuousAt.continuousWithinAt
  have hu : IsOpen {B : V 1 →L[ℝ] V 1 | IsUnit B} := Units.isOpen
  have := hc.isOpen_inter_preimage h1 hu
  exact this

/-! The base point `v = 0`. -/

omit hH hJ in
lemma fX_zero (φ : ℝ) : fX P (φ, 0) = P.x φ := by simp [fX]
omit hH hJ in
lemma fC1_zero (φ : ℝ) : fC1 P (φ, 0) = (2 * P.T) • P.x φ := by
  simp [fC1, fAs, fDs, fX]
omit hH hJ in
lemma fC2_zero (φ : ℝ) : fC2 P (φ, 0) = P.T • reeb H (P.x φ) := by
  simp [fC2, fAt, fDt]

include hH hJ in
lemma fBB_zero_isUnit (φ : ℝ) : IsUnit (fBB J P (φ, 0)) := by
  apply fas_isUnit_of_injective
  have hx : P.x φ ∈ energySurface H := P.mem φ
  have hT := P.T_pos
  have hD : 0 < fderiv ℝ H (P.x φ) (P.x φ) := hH.2.2 _ hx
  obtain ⟨-, hR1, hRH, -⟩ := ka_reeb_spec H hH _ hx
  have hW := r26_W_xi hH hJ hx
  have hJW := r26_JW_xi hH hJ hx
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [fBB, fC1_zero, fC2_zero, fX_zero, fasB_apply] at hv
  simp only [fasE, Sum.elim_inl, Sum.elim_inr] at hv
  have h1 := congrArg (fderiv ℝ H (P.x φ)) hv
  simp only [map_add, map_smul, hRH, hW.2, hJW.2, map_zero, smul_zero, add_zero, smul_eq_mul] at h1
  have hv0 : v fi0 = 0 := by
    have : v fi0 * (2 * P.T * fderiv ℝ H (P.x φ) (P.x φ)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (by positivity)
  have h2 := congrArg (liouvilleCLM (P.x φ)) hv
  simp only [map_add, map_smul, ka_liouvilleCLM_apply, hR1, hW.1, hJW.1, map_zero, smul_zero,
    add_zero, smul_eq_mul, mul_one] at h2
  have hll : liouville (P.x φ) (P.x φ) = 0 := by
    unfold liouville; rw [ka_om_self]; simp
  rw [hll] at h2
  simp only [mul_zero, zero_add] at h2
  have hv1 : v fi1 = 0 := by
    have h2' : v fi1 * P.T = 0 := by linarith
    rcases mul_eq_zero.1 h2' with h | h
    · exact h
    · exact absurd h hT.ne'
  rw [hv0, hv1, zero_smul, zero_smul, zero_add, zero_add] at hv
  have hWJW := r26_W_JW hH hJ hx
  have h3' : v fi3 = 0 := by
    have h3 : HryniewiczCriterion.omega0 (r26W H J (P.x φ))
        (v fi2 • r26W H J (P.x φ) + v fi3 • J (P.x φ) (r26W H J (P.x φ))) = 0 := by
      rw [hv]; simp [HryniewiczCriterion.omega0]
    rw [HryniewiczCriterion.r26_omega0_lin_right2, HryniewiczCriterion.r26_omega0_self, hWJW] at h3
    linarith
  rw [h3', zero_smul, add_zero] at hv
  have hWne : r26W H J (P.x φ) ≠ 0 := by
    intro h
    rw [h] at hWJW
    simp [HryniewiczCriterion.omega0] at hWJW
  have h2' : v fi2 = 0 := (smul_eq_zero.1 hv).resolve_right hWne
  funext k
  obtain ⟨k, hk⟩ := k
  have hk4 : k < 4 := hk
  interval_cases k
  · exact hv0
  · exact hv1
  · exact h2'
  · exact h3'

include hH hJ in
lemma fU_zero (φ : ℝ) : (φ, (0 : FasE)) ∈ fU J P :=
  ⟨by rw [fX_zero]; exact fas_mem_O hH hJ (P.mem φ), fBB_zero_isUnit hH hJ P φ⟩

include hH hJ in
/-- The uniform tube. -/
lemma fU_tube : ∃ ρ > 0, ∀ (φ : ℝ) (v : FasE), ‖v‖ < ρ → (φ, v) ∈ fU J P := by
  have hT := P.T_pos
  have hsub : Set.Icc (0 : ℝ) P.T ×ˢ ({0} : Set FasE) ⊆ fU J P := by
    rintro ⟨φ, v⟩ ⟨-, hv⟩
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact fU_zero hH hJ P φ
  obtain ⟨U₁, U₂, -, hU₂, hs, ht, hprod⟩ := generalized_tube_lemma isCompact_Icc
    isCompact_singleton (fU_isOpen hH hJ P) hsub
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU₂ 0 (ht rfl)
  refine ⟨ρ, hρ, fun φ v hv => ?_⟩
  have hper : Function.Periodic (fun φ : ℝ => (φ, v) ∈ fU J P) P.T := fun φ => by
    simp only [fU_per]
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ hT φ
  have : (y, v) ∈ fU J P := hprod ⟨hs ⟨hy.1, hy.2.le⟩, hball (by simpa using hv)⟩
  have e : (φ, v) ∈ fU J P ↔ (y, v) ∈ fU J P := by
    have := hty
    simpa using this
  exact e.2 this

include hH hJ in
/-- The limit coefficient is the loop of the asymptotic operator. -/
lemma fPhi_zero (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hZS : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => r26ZAt H J (P.x (P.T * t)) (η t)) t =
        r26ZAt H J (P.x (P.T * t))
          (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (i j : Fin 1 ⊕ Fin 1) (t : ℝ) :
    fPhi J P i j (P.T * t, 0) = Sinf t i j := by
  have hT := P.T_pos
  set x := P.x (P.T * t) with hxdef
  have hx : x ∈ energySurface H := P.mem _
  set b : CauchyRiemannIndex.Vec 1 := EuclideanSpace.single j 1 with hb
  -- the frame vector as a loop
  have hZb : ∀ s, r26ZAt H J (P.x (P.T * s)) b = fasE H J j (P.x (P.T * s)) := by
    intro s
    rw [r26ZAt_apply]
    rcases j with j | j <;> fin_cases j <;> simp [hb, fasE]
  have hxE := fasE_contDiffAt hH hJ j (fas_mem_O hH hJ hx)
  have hxc : HasDerivAt (fun s => P.x (P.T * s)) (P.T • reeb H x) t := by
    have h0 : HasDerivAt (fun s => P.T * s) P.T t := by
      simpa using (hasDerivAt_id t).const_mul P.T
    exact (P.hasDerivAt (P.T * t)).scomp t h0
  have hEd : HasDerivAt (fun s => fasE H J j (P.x (P.T * s)))
      (fderiv ℝ (fasE H J j) x (P.T • reeb H x)) t := by
    have h := (hxE.differentiableAt (by simp)).hasFDerivAt
    exact h.comp_hasDerivAt t hxc
  have hcurve : ∀ s, DifferentiableAt ℝ (fun s => fasE H J j (P.x (P.T * s))) s := by
    intro s
    have hxs : P.x (P.T * s) ∈ energySurface H := P.mem _
    have hc : DifferentiableAt ℝ (fun s => P.x (P.T * s)) s :=
      ((ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_id)).differentiable
        (by simp) s
    exact ((fasE_contDiffAt hH hJ j (fas_mem_O hH hJ hxs)).differentiableAt (by simp)).comp s hc
  have hxiE : ∀ s, IsInXi H (P.x (P.T * s)) (fasE H J j (P.x (P.T * s))) := by
    intro s
    rw [← hZb]
    exact r26_unitary_xi hH hJ (P.mem _) b
  have hEx := hxiE t
  rw [← hxdef] at hEx
  have hxi := isInXi_linearizedReeb_deriv H hH P _ hcurve hxiE t
  rw [hEd.deriv, ← hxdef] at hxi
  have hA := hZS (fun _ => b) contDiff_const (fun _ => rfl) t
  simp only [asympOp, deriv_const, map_zero, neg_zero, zero_sub, hZb] at hA
  rw [show (fun s => fasE H J j (P.x (P.T * s))) = fun s => fasE H J j (P.x (P.T * s)) from rfl,
    hEd.deriv, ← hxdef] at hA
  -- evaluate the coefficient vector
  have hG : fG J P j (P.T * t, 0) = r26ZAt H J x (Matrix.toEuclideanLin (Sinf t) b) := by
    have hdJ := fas_dJt_reeb hH hJ hx hEx
    simp only [fG, fX_zero, fC2_zero, fDs, fDt, fAs, fAt, ContinuousLinearMap.zero_apply,
      Prod.snd_zero, Prod.fst_zero, map_zero, add_zero, zero_add, ← hxdef]
    have hJv := fas_Jt_xi_mem (J := J) hH hx hxi
    rw [map_smul, map_smul, map_smul, hdJ]
    have e1 : Jtilde H J x (-fderiv ℝ (fasE H J j) x (P.T • reeb H x) +
        P.T • fderiv ℝ (reeb H) x (fasE H J j x)) =
        -(P.T • Jtilde H J x (fderiv ℝ (fasE H J j) x (reeb H x))) +
          P.T • Jtilde H J x (fderiv ℝ (reeb H) x (fasE H J j x)) := by
      simp only [map_add, map_neg, map_smul]
    rw [hJv] at e1
    have e2 : J x (-fderiv ℝ (fasE H J j) x (P.T • reeb H x) +
        P.T • fderiv ℝ (reeb H) x (fasE H J j x)) =
        -(r26ZAt H J x (Matrix.toEuclideanLin (Sinf t) b)) := by
      rw [hA, map_neg]
    rw [e2] at e1
    have e3 := congrArg Neg.neg e1
    rw [neg_neg] at e3
    rw [e3]
    module
  -- coordinates
  have hunit := fBB_zero_isUnit hH hJ P (P.T * t)
  unfold fBB at hunit
  have hZexp : r26ZAt H J x (Matrix.toEuclideanLin (Sinf t) b) =
      (0 : ℝ) • fC1 P (P.T * t, 0) + (0 : ℝ) • fC2 P (P.T * t, 0) +
        (Matrix.toEuclideanLin (Sinf t) b (Sum.inl 0)) • fasE H J (Sum.inl 0) (fX P (P.T * t, 0)) +
        (Matrix.toEuclideanLin (Sinf t) b (Sum.inr 0)) • fasE H J (Sum.inr 0) (fX P (P.T * t, 0)) := by
    rw [r26ZAt_apply, fX_zero]
    simp [fasE, hxdef]
  have hentry : ∀ i', Matrix.toEuclideanLin (Sinf t) b i' = Sinf t i' j := by
    intro i'
    simp [Matrix.toEuclideanLin_apply, hb, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  unfold fPhi fCC
  rw [hG, hZexp]
  rcases i with i | i <;> obtain rfl : i = 0 := Subsingleton.elim _ _
  · exact (fasC_comb2 hunit _ _ _ _).trans (hentry _)
  · exact (fasC_comb3 hunit _ _ _ _).trans (hentry _)

end smooth

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff Real

lemma fas_two_le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

section gen
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

include hH hJ in
/-- Derivatives of a `J̃`-holomorphic map solve the linearized equation. -/
lemma fas_linDbar_fderiv (e₁ e₂ : D) (y : D → V 1) (hy : ContDiff ℝ ∞ y) (hy0 : ∀ q, y q ≠ 0)
    (hhol : ∀ q, fderiv ℝ y q e₁ + Jtilde H J (y q) (fderiv ℝ y q e₂) = 0) (e p : D) :
    linDbar (Jtilde H J) e₁ e₂ y (fun q => fderiv ℝ y q e) p = 0 := by
  set G : D × ℝ → V 1 := fun q => y (q.1 + q.2 • e) with hGdef
  have hG : ContDiff ℝ ∞ G := hy.comp (contDiff_fst.add (contDiff_snd.smul contDiff_const))
  have hd : ∀ (q : D × ℝ) (w : D × ℝ), fderiv ℝ G q w = fderiv ℝ y (q.1 + q.2 • e) (w.1 + w.2 • e) := by
    intro q w
    have h1 : HasFDerivAt (fun q : D × ℝ => q.1 + q.2 • e)
        (ContinuousLinearMap.fst ℝ D ℝ + (ContinuousLinearMap.snd ℝ D ℝ).smulRight e) q :=
      hasFDerivAt_fst.add (hasFDerivAt_snd.smul_const e)
    have h2 := ((hy.differentiable (by simp) (q.1 + q.2 • e)).hasFDerivAt.comp q h1).fderiv
    have h3 : fderiv ℝ G q = _ := h2
    rw [h3]
    simp
  have := linDbar_eq_zero_of_family (Jtilde H J) e₁ e₂ G p 0 ((hG.of_le fas_two_le).contDiffAt)
    (fas_Jt_differentiableAt hH hJ (hy0 _)) (Eventually.of_forall fun q => ?_)
  · have e1 : (fun z => G (z, (0 : ℝ))) = y := by
      funext z; simp [hGdef]
    have e2 : (fun z => fderiv ℝ G (z, (0 : ℝ)) ((0 : D), (1 : ℝ))) = fun q => fderiv ℝ y q e := by
      funext z; rw [hd]; simp
    rwa [e1, e2] at this
  · rw [hd, hd]
    simpa [hGdef] using hhol (q.1 + q.2 • e)

include hH hJ in
/-- The map itself solves the linearized equation (scale invariance of `J̃`). -/
lemma fas_linDbar_self (e₁ e₂ : D) (y : D → V 1) (hy : ContDiff ℝ ∞ y) (hy0 : ∀ q, y q ≠ 0)
    (hhol : ∀ q, fderiv ℝ y q e₁ + Jtilde H J (y q) (fderiv ℝ y q e₂) = 0) (p : D) :
    linDbar (Jtilde H J) e₁ e₂ y y p = 0 := by
  set G : D × ℝ → V 1 := fun q => Real.exp q.2 • y q.1 with hGdef
  have hG : ContDiff ℝ ∞ G :=
    (Real.contDiff_exp.comp contDiff_snd).smul (hy.comp contDiff_fst)
  have hd : ∀ (q : D × ℝ) (w : D × ℝ), fderiv ℝ G q w =
      Real.exp q.2 • fderiv ℝ y q.1 w.1 + w.2 • (Real.exp q.2 • y q.1) := by
    intro q w
    have h0 : HasFDerivAt y (fderiv ℝ y q.1) q.1 := (hy.differentiable (by simp) q.1).hasFDerivAt
    have h1 : HasFDerivAt (fun q : D × ℝ => y q.1)
        ((fderiv ℝ y q.1).comp (ContinuousLinearMap.fst ℝ D ℝ)) q := h0.comp q hasFDerivAt_fst
    have h2 : HasFDerivAt (fun q : D × ℝ => Real.exp q.2)
        (Real.exp q.2 • ContinuousLinearMap.snd ℝ D ℝ) q := hasFDerivAt_snd.exp
    have h3 := (h2.smul h1).fderiv
    have h4 : fderiv ℝ G q = _ := h3
    rw [h4]
    simp [smul_smul, mul_comm]
  have := linDbar_eq_zero_of_family (Jtilde H J) e₁ e₂ G p 0 ((hG.of_le fas_two_le).contDiffAt)
    (fas_Jt_differentiableAt hH hJ (by simpa [hGdef] using hy0 p)) (Eventually.of_forall fun q => ?_)
  · have e1 : (fun z => G (z, (0 : ℝ))) = y := by
      funext z; simp [hGdef]
    have e2 : (fun z => fderiv ℝ G (z, (0 : ℝ)) ((0 : D), (1 : ℝ))) = y := by
      funext z; rw [hd]; simp
    rwa [e1, e2] at this
  · rw [hd, hd]
    have hs : G q = Real.exp q.2 • y q.1 := rfl
    rw [hs, fas_Jt_scale hH hJ (hy0 _) (Real.exp_pos _)]
    simp only [zero_smul, add_zero, map_smul, ← smul_add, hhol, smul_zero]

end gen

/-! ### Cylindrical coordinates -/

lemma fas_cyl_eq (s t : ℝ) :
    cylInf s t = Complex.exp ((2 * π : ℝ) • ((s : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold cylInf ccwLoop
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The derivative of the cylindrical coordinates. -/
lemma fas_cyl_hasFDerivAt (q : ℝ × ℝ) :
    ∃ L : ℝ × ℝ →L[ℝ] ℂ, HasFDerivAt (fun q : ℝ × ℝ => cylInf q.1 q.2) L q ∧
      L (1, 0) = (2 * π : ℝ) • cylInf q.1 q.2 ∧
      L (0, 1) = (2 * π : ℝ) • (cylInf q.1 q.2 * Complex.I) := by
  set Λ : ℝ × ℝ →L[ℝ] ℂ := (2 * π : ℝ) • ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I) with hΛ
  have hval : ∀ q : ℝ × ℝ, Λ q = (2 * π : ℝ) • ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by
    intro q
    simp [hΛ]
  have hfun : (fun q : ℝ × ℝ => cylInf q.1 q.2) = fun q => Complex.exp (Λ q) := by
    funext q
    rw [hval, fas_cyl_eq]
  have h := Λ.hasFDerivAt (x := q)
  refine ⟨Complex.exp (Λ q) • Λ, ?_, ?_, ?_⟩
  · rw [hfun]; exact h.cexp
  · rw [ContinuousLinearMap.smul_apply, hval, fas_cyl_eq, hval]
    simp [mul_comm]
  · rw [ContinuousLinearMap.smul_apply, hval, fas_cyl_eq, hval]
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_add, one_mul, Complex.real_smul,
      smul_eq_mul]
    ring

section cyl
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

include hH hJ in
/-- `v ∘ cylInf` solves the Cauchy–Riemann equation in `(s, t)`. -/
lemma fas_cyl_dbar (v : ℂ → V 1) (q : ℝ × ℝ) (hv : DifferentiableAt ℝ v (cylInf q.1 q.2))
    (hv0 : v (cylInf q.1 q.2) ≠ 0)
    (hdb : fderiv ℝ v (cylInf q.1 q.2) 1 +
      Jtilde H J (v (cylInf q.1 q.2)) (fderiv ℝ v (cylInf q.1 q.2) Complex.I) = 0) :
    fderiv ℝ (fun q : ℝ × ℝ => v (cylInf q.1 q.2)) q (1, 0) +
      Jtilde H J (v (cylInf q.1 q.2)) (fderiv ℝ (fun q : ℝ × ℝ => v (cylInf q.1 q.2)) q (0, 1)) = 0 := by
  obtain ⟨L, hL, hL1, hL2⟩ := fas_cyl_hasFDerivAt q
  have hc : fderiv ℝ (fun q : ℝ × ℝ => v (cylInf q.1 q.2)) q =
      (fderiv ℝ v (cylInf q.1 q.2)).comp L := (hv.hasFDerivAt.comp q hL).fderiv
  rw [hc]
  simp only [ContinuousLinearMap.comp_apply, hL1, hL2, map_smul]
  set z := cylInf q.1 q.2
  set A := fderiv ℝ v z
  set Jt := Jtilde H J (v z)
  have hsq : ∀ w, Jt (Jt w) = -w := fas_Jt_sq hH hJ hv0
  have hAI : A Complex.I = Jt (A 1) := by
    have := congrArg Jt hdb
    rw [map_add, map_zero, hsq] at this
    exact (sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact this)).symm
  have hz : ∀ w : ℂ, A w = w.re • A 1 + w.im • A Complex.I := by
    intro w
    conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
      apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul]
  have h1 := hz z
  have h2 := hz (z * Complex.I)
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_eq_add_neg, zero_add, add_zero] at h2
  rw [h1, h2, hAI]
  simp only [map_add, map_smul, hsq, map_neg]
  module

end cyl

/-! ### The frame equation on a domain in `ℝ × ℝ` -/

section local_eq
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

/-- `(2 Da e) x + Dx e`, for `a = aCoord ∘ y` and `x = proj ∘ y`. -/
noncomputable def gCol (H : V 1 → ℝ) (y : ℝ × ℝ → V 1) (e q : ℝ × ℝ) : V 1 :=
  (2 * fderiv ℝ (fun q => aCoord H (y q)) q e) • proj H (y q) +
    fderiv ℝ (fun q => proj H (y q)) q e

/-- The local form of the coefficient vector. -/
noncomputable def gG (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (y : ℝ × ℝ → V 1)
    (j : Fin 1 ⊕ Fin 1) (q : ℝ × ℝ) : V 1 :=
  fderiv ℝ (fasE H J j) (proj H (y q)) (fderiv ℝ (fun q => proj H (y q)) q (1, 0)) +
    Jtilde H J (proj H (y q))
      (fderiv ℝ (fasE H J j) (proj H (y q)) (fderiv ℝ (fun q => proj H (y q)) q (0, 1))) +
    fderiv ℝ (Jtilde H J) (proj H (y q)) (fasE H J j (proj H (y q))) (gCol H y (0, 1) q) +
    (2 * fderiv ℝ (fun q => aCoord H (y q)) q (1, 0)) • fasE H J j (proj H (y q)) +
    (2 * fderiv ℝ (fun q => aCoord H (y q)) q (0, 1)) •
      Jtilde H J (proj H (y q)) (fasE H J j (proj H (y q)))

/-- The frame map on the domain. -/
noncomputable def gB (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (y : ℝ × ℝ → V 1) (q : ℝ × ℝ) :
    V 1 →L[ℝ] V 1 :=
  fasB (gCol H y (1, 0) q) (gCol H y (0, 1) q) (fasE H J (Sum.inl 0) (proj H (y q)))
    (fasE H J (Sum.inr 0) (proj H (y q)))

/-- The frame coordinates on the domain. -/
noncomputable def gC (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (y : ℝ × ℝ → V 1) (q : ℝ × ℝ) :
    V 1 →L[ℝ] V 1 :=
  fasC (gCol H y (1, 0) q) (gCol H y (0, 1) q) (fasE H J (Sum.inl 0) (proj H (y q)))
    (fasE H J (Sum.inr 0) (proj H (y q)))

include hH hJ in
lemma fas_exp_two_a {y : V 1} (hy : y ≠ 0) :
    Real.exp (2 * aCoord H y) = (scaleToS H y)⁻¹ := by
  have hr := (ka_scale_spec H hH y hy).1
  unfold aCoord
  rw [show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring, Real.exp_neg,
    Real.exp_log hr]

variable (y : ℝ × ℝ → V 1) (hy : ContDiff ℝ ∞ y) (hy0 : ∀ q, y q ≠ 0)

include hH hJ hy hy0 in
lemma fas_a_contDiff : ContDiff ℝ ∞ (fun q => aCoord H (y q)) := by
  obtain ⟨-, -, ha, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  refine contDiff_iff_contDiffAt.2 fun q => ?_
  have hO : IsOpen {y : V 1 | y ≠ 0} := isOpen_ne
  exact (ha.contDiffAt (hO.mem_nhds (hy0 q))).comp q hy.contDiffAt

include hH hJ hy hy0 in
lemma fas_x_contDiff : ContDiff ℝ ∞ (fun q => proj H (y q)) := by
  obtain ⟨-, hp, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  refine contDiff_iff_contDiffAt.2 fun q => ?_
  have hO : IsOpen {y : V 1 | y ≠ 0} := isOpen_ne
  exact (hp.contDiffAt (hO.mem_nhds (hy0 q))).comp q hy.contDiffAt

include hH hJ hy hy0 in
/-- The columns are the rescaled tangent vectors. -/
lemma gCol_eq (e q : ℝ × ℝ) : gCol H y e q = scaleToS H (y q) • fderiv ℝ y q e := by
  have ha := fas_a_contDiff hH hJ y hy hy0
  have hx := fas_x_contDiff hH hJ y hy hy0
  have hr := (ka_scale_spec H hH (y q) (hy0 q)).1
  have hfun : ∀ q, y q = Real.exp (2 * aCoord H (y q)) • proj H (y q) := fun q =>
    (jtilde_isAlmostComplexOn H hH J hJ).2.2.2.1 (y q) (hy0 q) |>.2
  have h1 : HasFDerivAt (fun q => aCoord H (y q)) (fderiv ℝ (fun q => aCoord H (y q)) q) q :=
    (ha.differentiable (by simp) q).hasFDerivAt
  have h2 : HasFDerivAt (fun q => proj H (y q)) (fderiv ℝ (fun q => proj H (y q)) q) q :=
    (hx.differentiable (by simp) q).hasFDerivAt
  have h3 := ((h1.const_mul 2).exp).smul h2
  have h4 := (h3.congr_of_eventuallyEq (f₁ := y) (Eventually.of_forall hfun)).fderiv
  rw [h4, fas_exp_two_a hH hJ (hy0 q)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_add, smul_smul, smul_eq_mul, gCol]
  rw [mul_inv_cancel₀ hr.ne', one_smul, add_comm]
  congr 2
  field_simp

include hH hJ hy hy0 in
lemma gCol_contDiff (e : ℝ × ℝ) : ContDiff ℝ ∞ (gCol H y e) := by
  have ha := fas_a_contDiff hH hJ y hy hy0
  have hx := fas_x_contDiff hH hJ y hy hy0
  have h1 : ContDiff ℝ ∞ (fun q => fderiv ℝ (fun q => aCoord H (y q)) q e) :=
    (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun q => fderiv ℝ (fun q => proj H (y q)) q e) :=
    (hx.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact ((contDiff_const.mul h1).smul hx).add h2

include hH hJ hy hy0 in
lemma gB_contDiffAt (q : ℝ × ℝ) : ContDiffAt ℝ ∞ (gB H J y) q := by
  have hx := fas_x_contDiff hH hJ y hy hy0
  have hm : proj H (y q) ∈ fasO H J :=
    fas_mem_O hH hJ (ka_scale_spec H hH (y q) (hy0 q)).2
  exact fasB_contDiffAt (gCol_contDiff hH hJ y hy hy0 _).contDiffAt
    (gCol_contDiff hH hJ y hy hy0 _).contDiffAt
    (ContDiffAt.comp (g := fasE H J _) q (fasE_contDiffAt hH hJ _ hm) hx.contDiffAt)
    (ContDiffAt.comp (g := fasE H J _) q (fasE_contDiffAt hH hJ _ hm) hx.contDiffAt)

include hH hJ hy hy0 in
lemma gC_contDiffAt {q : ℝ × ℝ} (hu : IsUnit (gB H J y q)) : ContDiffAt ℝ ∞ (gC H J y) q := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (gB H J y q) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact h1.comp q (gB_contDiffAt hH hJ y hy hy0 q)

/-- The frame vector on the domain, of the scale of `y`. -/
noncomputable def gF (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (y : ℝ × ℝ → V 1)
    (j : Fin 1 ⊕ Fin 1) (q : ℝ × ℝ) : V 1 :=
  Real.exp (2 * aCoord H (y q)) • fasE H J j (proj H (y q))

include hH hJ hy hy0 in
/-- The rescaled image of the frame vector under the linearized operator. -/
lemma gF_linDbar (j : Fin 1 ⊕ Fin 1) (p : ℝ × ℝ) :
    scaleToS H (y p) • linDbar (Jtilde H J) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) y (gF H J y j) p =
      gG H J y j p := by
  have ha := fas_a_contDiff hH hJ y hy hy0
  have hx := fas_x_contDiff hH hJ y hy hy0
  have hS : proj H (y p) ∈ energySurface H := (ka_scale_spec H hH (y p) (hy0 p)).2
  have hx0 := fas_ne_zero_of_mem hH hS
  have hr := (ka_scale_spec H hH (y p) (hy0 p)).1
  have hE : DifferentiableAt ℝ (fasE H J j) (proj H (y p)) :=
    (fasE_contDiffAt hH hJ j (fas_mem_O hH hJ hS)).differentiableAt (by simp)
  have hEc : HasFDerivAt (fun q => fasE H J j (proj H (y q)))
      ((fderiv ℝ (fasE H J j) (proj H (y p))).comp (fderiv ℝ (fun q => proj H (y q)) p)) p :=
    HasFDerivAt.comp (g := fasE H J j) p hE.hasFDerivAt (hx.differentiable (by simp) p).hasFDerivAt
  have hexp : HasFDerivAt (fun q => Real.exp (2 * aCoord H (y q)))
      (Real.exp (2 * aCoord H (y p)) • ((2 : ℝ) • fderiv ℝ (fun q => aCoord H (y q)) p)) p :=
    (((ha.differentiable (by simp) p).hasFDerivAt.const_smul (2 : ℝ))).exp
  have hyp : y p = Real.exp (2 * aCoord H (y p)) • proj H (y p) :=
    (jtilde_isAlmostComplexOn H hH J hJ).2.2.2.1 (y p) (hy0 p) |>.2
  have hρ : Real.exp (2 * aCoord H (y p)) = (scaleToS H (y p))⁻¹ := fas_exp_two_a hH hJ (hy0 p)
  have hJy : Jtilde H J (y p) = Jtilde H J (proj H (y p)) := by
    conv_lhs => rw [hyp]
    exact fas_Jt_scale hH hJ hx0 (Real.exp_pos _)
  have hDJ : ∀ v, fderiv ℝ (Jtilde H J) (y p) v =
      (scaleToS H (y p)) • fderiv ℝ (Jtilde H J) (proj H (y p)) v := by
    intro v
    conv_lhs => rw [hyp]
    rw [fas_dJt_scale hH hJ hx0 (Real.exp_pos _), hρ, inv_inv]
  have hτ : fderiv ℝ y p ((0 : ℝ), (1 : ℝ)) = (scaleToS H (y p))⁻¹ • gCol H y (0, 1) p := by
    rw [gCol_eq hH hJ y hy hy0, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hF : gF H J y j = fun q => Real.exp (2 * aCoord H (y q)) • fasE H J j (proj H (y q)) := rfl
  rw [hF, linDbar_smul (Jtilde H J) _ _ y _ _ p hexp.differentiableAt hEc.differentiableAt]
  unfold linDbar
  rw [hEc.fderiv, hexp.fderiv, hJy, hDJ, hτ, hρ]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul,
    smul_add, smul_smul, inv_mul_cancel₀ hr.ne', mul_inv_cancel₀ hr.ne', one_smul, one_mul, gG]
  simp only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, inv_mul_cancel₀ hr.ne', add_assoc]

include hH hJ hy hy0 in
/-- The two normal components of a solution of the linearized equation in the frame. -/
theorem fas_local (hhol : ∀ q, fderiv ℝ y q ((1 : ℝ), (0 : ℝ)) +
      Jtilde H J (y q) (fderiv ℝ y q ((0 : ℝ), (1 : ℝ))) = 0)
    (O : Set (ℝ × ℝ)) (hO : IsOpen O) (hU : ∀ q ∈ O, IsUnit (gB H J y q))
    (W : ℝ × ℝ → V 1) (p : ℝ × ℝ) (hp : p ∈ O) (hW : DifferentiableAt ℝ W p)
    (hL : linDbar (Jtilde H J) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) y W p = 0) :
    fderiv ℝ (fun q => gC H J y q (scaleToS H (y q) • W q) fi2) p (1, 0) -
        fderiv ℝ (fun q => gC H J y q (scaleToS H (y q) • W q) fi3) p (0, 1) +
        gC H J y p (scaleToS H (y p) • W p) fi2 * gC H J y p (gG H J y (Sum.inl 0) p) fi2 +
        gC H J y p (scaleToS H (y p) • W p) fi3 * gC H J y p (gG H J y (Sum.inr 0) p) fi2 = 0 ∧
    fderiv ℝ (fun q => gC H J y q (scaleToS H (y q) • W q) fi2) p (0, 1) +
        fderiv ℝ (fun q => gC H J y q (scaleToS H (y q) • W q) fi3) p (1, 0) +
        gC H J y p (scaleToS H (y p) • W p) fi2 * gC H J y p (gG H J y (Sum.inl 0) p) fi3 +
        gC H J y p (scaleToS H (y p) • W p) fi3 * gC H J y p (gG H J y (Sum.inr 0) p) fi3 = 0 := by
  have hr := (ka_scale_spec H hH (y p) (hy0 p)).1
  have hS : proj H (y p) ∈ energySurface H := (ka_scale_spec H hH (y p) (hy0 p)).2
  have hx0 := fas_ne_zero_of_mem hH hS
  have hx := fas_x_contDiff hH hJ y hy hy0
  have ha := fas_a_contDiff hH hJ y hy hy0
  have hyp : y p = Real.exp (2 * aCoord H (y p)) • proj H (y p) :=
    (jtilde_isAlmostComplexOn H hH J hJ).2.2.2.1 (y p) (hy0 p) |>.2
  have hρ := fas_exp_two_a hH hJ (hy0 p)
  have hJy : Jtilde H J (y p) = Jtilde H J (proj H (y p)) := by
    conv_lhs => rw [hyp]
    exact fas_Jt_scale hH hJ hx0 (Real.exp_pos _)
  -- the coefficient functions
  set c : ℝ × ℝ → V 1 := fun q => gC H J y q (scaleToS H (y q) • W q) with hc
  have hrd : DifferentiableAt ℝ (fun q => scaleToS H (y q)) p :=
    ((ka_scale_contDiffAt H hH (y p) (hy0 p)).differentiableAt (by simp)).comp p
      (hy.differentiable (by simp) p)
  have hCd : DifferentiableAt ℝ (gC H J y) p :=
    (gC_contDiffAt hH hJ y hy hy0 (hU p hp)).differentiableAt (by simp)
  have hcd : DifferentiableAt ℝ c p := hCd.clm_apply (hrd.smul hW)
  have hck : ∀ k, DifferentiableAt ℝ (fun q => c q k) p := fun k => differentiableAt_pi.1 hcd k
  -- the frame fields
  set τ₁ : ℝ × ℝ → V 1 := fun q => fderiv ℝ y q ((1 : ℝ), (0 : ℝ)) with hτ₁
  set τ₂ : ℝ × ℝ → V 1 := fun q => fderiv ℝ y q ((0 : ℝ), (1 : ℝ)) with hτ₂
  have hdτ : ∀ e : ℝ × ℝ, DifferentiableAt ℝ (fun q => fderiv ℝ y q e) p := fun e =>
    ((hy.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) p
  have hdF : ∀ j, DifferentiableAt ℝ (gF H J y j) p := by
    intro j
    have hm : proj H (y p) ∈ fasO H J := fas_mem_O hH hJ hS
    have h1 : DifferentiableAt ℝ (fun q => fasE H J j (proj H (y q))) p :=
      DifferentiableAt.comp (g := fasE H J j) p ((fasE_contDiffAt hH hJ j hm).differentiableAt (by simp))
        (hx.differentiable (by simp) p)
    have h2 : DifferentiableAt ℝ (fun q => Real.exp (2 * aCoord H (y q))) p :=
      ((ha.differentiable (by simp) p).const_mul 2).exp
    exact h2.smul h1
  have hexpand : W =ᶠ[𝓝 p] fun q => c q fi0 • τ₁ q + c q fi1 • τ₂ q +
      c q fi2 • gF H J y (Sum.inl 0) q + c q fi3 • gF H J y (Sum.inr 0) q := by
    filter_upwards [hO.mem_nhds hp] with q hq
    have hr' := (ka_scale_spec H hH (y q) (hy0 q)).1
    have h : c q fi0 • gCol H y (1, 0) q + c q fi1 • gCol H y (0, 1) q +
        c q fi2 • fasE H J (Sum.inl 0) (proj H (y q)) +
        c q fi3 • fasE H J (Sum.inr 0) (proj H (y q)) = scaleToS H (y q) • W q :=
      fasC_expand (hU q hq) (scaleToS H (y q) • W q)
    have e1 : ∀ (a : ℝ) (v : V 1), (scaleToS H (y q))⁻¹ • a • scaleToS H (y q) • v = a • v := by
      intro a v
      rw [smul_comm a, inv_smul_smul₀ hr'.ne']
    have hWq : W q = (scaleToS H (y q))⁻¹ • (scaleToS H (y q) • W q) :=
      (inv_smul_smul₀ hr'.ne' _).symm
    refine hWq.trans ?_
    rw [← h, gCol_eq hH hJ y hy hy0, gCol_eq hH hJ y hy hy0, smul_add, smul_add, smul_add, e1, e1]
    simp only [gF, fas_exp_two_a hH hJ (hy0 q), hτ₁, hτ₂]
    rw [smul_comm (c q fi2), smul_comm (c q fi3)]
  -- complex structure
  have hsq : ∀ w, Jtilde H J (y p) (Jtilde H J (y p) w) = -w := fas_Jt_sq hH hJ (hy0 p)
  have hτ2J : Jtilde H J (y p) (τ₂ p) = -τ₁ p := eq_neg_of_add_eq_zero_right (hhol p)
  have hτ1J : Jtilde H J (y p) (τ₁ p) = τ₂ p := by
    have := congrArg (Jtilde H J (y p)) hτ2J
    rw [hsq, map_neg] at this
    exact (neg_inj.1 this).symm
  have hWxi := r26_W_xi hH hJ hS
  have hJWxi := r26_JW_xi hH hJ hS
  have hF1 : Jtilde H J (y p) (gF H J y (Sum.inl 0) p) = gF H J y (Sum.inr 0) p := by
    simp only [gF, fasE, Sum.elim_inl, Sum.elim_inr, map_smul, hJy]
    rw [fas_Jt_xi_mem hH hS hWxi]
  have hF2 : Jtilde H J (y p) (gF H J y (Sum.inr 0) p) = -gF H J y (Sum.inl 0) p := by
    simp only [gF, fasE, Sum.elim_inl, Sum.elim_inr, map_smul, hJy]
    rw [fas_Jt_xi_mem hH hS hJWxi, r26_JJW hH hJ hS, smul_neg]
  have hid := linDbar_frame_identity (Jtilde H J) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) y W τ₁ τ₂
    (gF H J y (Sum.inl 0)) (gF H J y (Sum.inr 0)) (fun q => c q fi0) (fun q => c q fi1)
    (fun q => c q fi2) (fun q => c q fi3) p (hck _) (hck _) (hck _) (hck _) (hdτ _) (hdτ _)
    (hdF _) (hdF _) hexpand hL (fas_linDbar_fderiv hH hJ _ _ y hy hy0 hhol _ p)
    (fas_linDbar_fderiv hH hJ _ _ y hy hy0 hhol _ p) hτ1J hτ2J hF1 hF2
  -- rescale
  have hid2 := congrArg (fun v => scaleToS H (y p) • v) hid
  simp only [smul_add, smul_zero] at hid2
  have e1 : ∀ a : ℝ, scaleToS H (y p) • a • τ₁ p = a • gCol H y (1, 0) p := by
    intro a; rw [gCol_eq hH hJ y hy hy0, smul_comm]
  have e2 : ∀ a : ℝ, scaleToS H (y p) • a • τ₂ p = a • gCol H y (0, 1) p := by
    intro a; rw [gCol_eq hH hJ y hy hy0, smul_comm]
  have e3 : ∀ (a : ℝ) j, scaleToS H (y p) • a • gF H J y j p = a • fasE H J j (proj H (y p)) := by
    intro a j
    simp only [gF, hρ, smul_smul]
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  have e4 : ∀ (a : ℝ) j, scaleToS H (y p) •
      a • linDbar (Jtilde H J) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) y (gF H J y j) p =
      a • gG H J y j p := by
    intro a j
    rw [smul_comm, gF_linDbar hH hJ y hy hy0]
  rw [e1, e2, e3, e3, e4, e4] at hid2
  exact fasC_identity (hU p hp) hid2

end local_eq

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff

lemma fas_tendsto_of_exp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × ℝ → F} {b : ℝ}
    (hb : 0 < b) (h : ExpDecayCInfty f b) : TendstoZeroCInfty f := by
  refine ⟨h.1, fun m ε hε => ?_⟩
  obtain ⟨C, s₁, hC⟩ := h.2 m
  have ht : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 (C * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)).const_mul C
  rw [mul_zero] at ht
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hε))
  refine ⟨max s₁ s₂, fun s hs t => ?_⟩
  exact (hC s (le_trans (le_max_left _ _) hs) t).trans
    (hs₂ s (le_trans (le_max_right _ _) hs)).le

lemma fas_fderiv_per {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    (hf : ∀ s t, f (s, t + 1) = f (s, t)) (s t : ℝ) :
    fderiv ℝ f (s, t + 1) = fderiv ℝ f (s, t) := by
  have h : (fun q : ℝ × ℝ => f (q + ((0 : ℝ), (1 : ℝ)))) = f := by
    funext q
    obtain ⟨a, b⟩ := q
    simpa using hf a b
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := f) ((0 : ℝ), (1 : ℝ)) (x := (s, t))
  rw [h] at h2
  rw [h2]
  simp

section
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

lemma gCol_per {y : ℝ × ℝ → V 1} (hyp : ∀ s t, y (s, t + 1) = y (s, t)) (e : ℝ × ℝ) (s t : ℝ) :
    gCol H y e (s, t + 1) = gCol H y e (s, t) := by
  have h1 := fas_fderiv_per (f := fun q => aCoord H (y q)) (fun a b => by simp only [hyp]) s t
  have h2 := fas_fderiv_per (f := fun q => proj H (y q)) (fun a b => by simp only [hyp]) s t
  simp only [gCol, h1, h2, hyp]

lemma gC_per {y : ℝ × ℝ → V 1} (hyp : ∀ s t, y (s, t + 1) = y (s, t)) (s t : ℝ) :
    gC H J y (s, t + 1) = gC H J y (s, t) := by
  simp only [gC, gCol_per hyp, hyp]

/-- The rate data: the difference from the trivial cylinder and its first derivatives. -/
noncomputable def fasV (H : V 1 → ℝ) (P : ReebOrbit H) (d₀ : ℝ) (y : ℝ × ℝ → V 1) (p : ℝ × ℝ) :
    FasE :=
  (proj H (y p) - P.x (P.T * p.2),
    fderiv ℝ (fun p : ℝ × ℝ => proj H (y p) - P.x (P.T * p.2)) p,
    fderiv ℝ (fun p : ℝ × ℝ => aCoord H (y p) - P.T * p.1 - d₀) p)

variable (y : ℝ × ℝ → V 1) (hy : ContDiff ℝ ∞ y) (hy0 : ∀ q, y q ≠ 0) (P : ReebOrbit H) (d₀ : ℝ)

include hH hJ hy hy0 in
/-- The data at `(T t, v)` are those of `y`. -/
lemma fasV_ident (q : ℝ × ℝ) :
    fX P (P.T * q.2, fasV H P d₀ y q) = proj H (y q) ∧
    fDs (P.T * q.2, fasV H P d₀ y q) = fderiv ℝ (fun q => proj H (y q)) q (1, 0) ∧
    fDt P (P.T * q.2, fasV H P d₀ y q) = fderiv ℝ (fun q => proj H (y q)) q (0, 1) ∧
    fAs P (P.T * q.2, fasV H P d₀ y q) = fderiv ℝ (fun q => aCoord H (y q)) q (1, 0) ∧
    fAt (P.T * q.2, fasV H P d₀ y q) = fderiv ℝ (fun q => aCoord H (y q)) q (0, 1) := by
  have hx := fas_x_contDiff hH hJ y hy hy0
  have ha := fas_a_contDiff hH hJ y hy hy0
  have hT : HasFDerivAt (fun p : ℝ × ℝ => P.x (P.T * p.2))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (P.T • reeb H (P.x (P.T * q.2)))) q := by
    have h1 : HasFDerivAt (fun p : ℝ × ℝ => P.T * p.2) (P.T • ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
      hasFDerivAt_snd.const_mul P.T
    have h2 := HasFDerivAt.comp (g := P.x) (f := fun p : ℝ × ℝ => P.T * p.2) q
      (P.hasDerivAt (P.T * q.2)).hasFDerivAt h1
    refine HasFDerivAt.congr_fderiv h2 (ContinuousLinearMap.ext fun v => ?_)
    simp [smul_smul, mul_comm]
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => proj H (y p) - P.x (P.T * p.2))
      (fderiv ℝ (fun q => proj H (y q)) q -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (P.T • reeb H (P.x (P.T * q.2)))) q :=
    (hx.differentiable (by simp) q).hasFDerivAt.sub hT
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => aCoord H (y p) - P.T * p.1 - d₀)
      (fderiv ℝ (fun q => aCoord H (y q)) q - P.T • ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    ((ha.differentiable (by simp) q).hasFDerivAt.sub (hasFDerivAt_fst.const_mul P.T)).sub_const d₀
  simp only [fX, fDs, fDt, fAs, fAt, fasV, h1.fderiv, h2.fderiv]
  simp

include hH hJ hy hy0 in
lemma fasV_contDiff : ContDiff ℝ ∞ (fasV H P d₀ y) := by
  have hx := fas_x_contDiff hH hJ y hy hy0
  have ha := fas_a_contDiff hH hJ y hy hy0
  have hP : ContDiff ℝ ∞ (fun p : ℝ × ℝ => P.x (P.T * p.2)) :=
    (ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_snd)
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => proj H (y p) - P.x (P.T * p.2)) := hx.sub hP
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => aCoord H (y p) - P.T * p.1 - d₀) :=
    (ha.sub (contDiff_const.mul contDiff_fst)).sub contDiff_const
  exact h1.prodMk ((h1.fderiv_right (m := ∞) (by simp)).prodMk (h2.fderiv_right (m := ∞) (by simp)))

include hH hJ hy hy0 in
lemma fasC_ident (q : ℝ × ℝ) :
    fCC J P (P.T * q.2, fasV H P d₀ y q) = gC H J y q ∧
    fBB J P (P.T * q.2, fasV H P d₀ y q) = gB H J y q ∧
    ∀ j, fG J P j (P.T * q.2, fasV H P d₀ y q) = gG H J y j q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := fasV_ident hH hJ y hy hy0 P d₀ q
  refine ⟨?_, ?_, fun j => ?_⟩
  · simp only [fCC, fC1, fC2, h1, h2, h3, h4, h5, gC, gCol]
  · simp only [fBB, fC1, fC2, h1, h2, h3, h4, h5, gB, gCol]
  · simp only [fG, fC2, h1, h2, h3, h4, h5, gG, gCol]

lemma fasV_per (hyp : ∀ s t, y (s, t + 1) = y (s, t)) (s t : ℝ) :
    fasV H P d₀ y (s, t + 1) = fasV H P d₀ y (s, t) := by
  have e0 : ∀ a b : ℝ, P.x (P.T * (b + 1)) = P.x (P.T * b) := by
    intro a b
    rw [mul_add, mul_one, P.periodic]
  have h1 := fas_fderiv_per (f := fun p : ℝ × ℝ => proj H (y p) - P.x (P.T * p.2))
    (fun a b => by simp only [hyp, e0 a b]) s t
  have h2 := fas_fderiv_per (f := fun p : ℝ × ℝ => aCoord H (y p) - P.T * p.1 - d₀)
    (fun a b => by simp only [hyp]) s t
  simp only [fasV, h1, h2, hyp, e0 s t]

include hH hJ hy hy0 in
/-- The linear equation of the end of a curve, in the frame adapted to the end. -/
theorem fas_asymp (hyp : ∀ s t, y (s, t + 1) = y (s, t)) (b : ℝ) (hb : 0 < b)
    (h1 : ExpDecayCInfty (fun p : ℝ × ℝ => aCoord H (y p) - P.T * p.1 - d₀) b)
    (h2 : ExpDecayCInfty (fun p : ℝ × ℝ => proj H (y p) - P.x (P.T * p.2)) b)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hZS : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => r26ZAt H J (P.x (P.T * t)) (η t)) t =
        r26ZAt H J (P.x (P.T * t))
          (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t))) :
    ∃ (s₁ C₁ d : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1), 0 < d ∧ 0 ≤ C₁ ∧
      IsExpAsymptoticTo S Sinf d ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ)) ∧
      (∀ s t, S (s, t + 1) = S (s, t)) ∧
      ∀ q : ℝ × ℝ, s₁ < q.1 → IsUnit (gB H J y q) ∧ ‖gC H J y q‖ ≤ C₁ ∧
        0 < fderiv ℝ (fun q => aCoord H (y q)) q (1, 0) ∧
        ∀ i j, S q i j = gC H J y q (gG H J y j q) (fasI i) := by
  have hT := P.T_pos
  obtain ⟨ρ, hρ, htube⟩ := fU_tube hH hJ P
  set v := fasV H P d₀ y with hv
  have hvc : ContDiff ℝ ∞ v := fasV_contDiff hH hJ y hy hy0 P d₀
  have hδ1 := fas_tendsto_of_exp hb h1
  have hδ2 := fas_tendsto_of_exp hb h2
  have hvt : TendstoZeroCInfty v :=
    tendstoZeroCInfty_prodMk hδ2
      (tendstoZeroCInfty_prodMk (tendstoZeroCInfty_fderiv hδ2) (tendstoZeroCInfty_fderiv hδ1))
  -- the size of the data
  set ρ' := min ρ P.T / 2 with hρ'
  have hρ'0 : 0 < ρ' := by have := lt_min hρ hT; positivity
  have hρ'1 : ρ' ≤ ρ / 2 := by
    have := min_le_left ρ P.T
    rw [hρ']; linarith
  have hρ'2 : ρ' ≤ P.T / 2 := by
    have := min_le_right ρ P.T
    rw [hρ']; linarith
  obtain ⟨s₂, hs₂⟩ := hvt.2 0 ρ' hρ'0
  have hvsmall : ∀ q : ℝ × ℝ, s₂ ≤ q.1 → ‖v q‖ ≤ ρ' := by
    rintro ⟨s, t⟩ hq
    simpa [norm_iteratedFDeriv_zero] using hs₂ s hq t
  have hvdec : ∃ (Cv sv : ℝ), ∀ s ≥ sv, ∀ t : ℝ, ‖v (s, t)‖ ≤ Cv * Real.exp (-(b * s)) := by
    obtain ⟨C0, s0, hC0⟩ := h2.2 0
    obtain ⟨C1, s1, hC1⟩ := h2.2 1
    obtain ⟨C2, s3, hC2⟩ := h1.2 1
    refine ⟨|C0| + |C1| + |C2|, max s0 (max s1 s3), fun s hs t => ?_⟩
    have a0 := hC0 s (le_trans (le_max_left _ _) hs) t
    have a1 := hC1 s (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs) t
    have a2 := hC2 s (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs) t
    rw [norm_iteratedFDeriv_zero] at a0
    rw [norm_iteratedFDeriv_one] at a1 a2
    have hE := Real.exp_pos (-(b * s))
    have b0 := mul_le_mul_of_nonneg_right (le_abs_self C0) hE.le
    have b1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hE.le
    have b2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hE.le
    have p0 := mul_nonneg (abs_nonneg C0) hE.le
    have p1 := mul_nonneg (abs_nonneg C1) hE.le
    have p2 := mul_nonneg (abs_nonneg C2) hE.le
    have hexp : (|C0| + |C1| + |C2|) * Real.exp (-(b * s)) =
        |C0| * Real.exp (-(b * s)) + |C1| * Real.exp (-(b * s)) + |C2| * Real.exp (-(b * s)) := by
      ring
    rw [hexp]
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
    · exact a0.trans (by linarith)
    · exact a1.trans (by linarith)
    · exact a2.trans (by linarith)
  obtain ⟨Cv, sv, hCv⟩ := hvdec
  have hin : ∀ (φ : ℝ) (w : FasE), ‖w‖ < ρ → (φ, w) ∈ fU J P := htube
  have hin0 : ∀ φ : ℝ, (φ, (0 : FasE)) ∈ fU J P := fun φ => htube φ 0 (by simpa using hρ)
  set S : ℝ × ℝ → CauchyRiemannIndex.Mat 1 :=
    fun p => Matrix.of fun i j => fPhi J P i j (P.T * p.2, v p) with hS
  -- the entries
  have hasy : ∀ i j, ExpDecayCInfty (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j) (b / 2) := by
    intro i j
    set Φ : ℝ × FasE → ℝ := fun z => fPhi J P i j z - fPhi J P i j (z.1, 0) with hΦ
    have hΦc : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : FasE) ρ) := by
      intro z hz
      have hz2 : ‖z.2‖ < ρ := by simpa using hz.2
      refine ContDiffAt.contDiffWithinAt (ContDiffAt.sub ?_ ?_)
      · exact fPhi_contDiffAt hH hJ P i j (hin z.1 z.2 hz2)
      · exact ContDiffAt.comp (g := fPhi J P i j) z
          (fPhi_contDiffAt hH hJ P i j (hin0 z.1)) (contDiff_fst.prodMk contDiff_const).contDiffAt
    have hΦp : ∀ (φ : ℝ) (w : FasE), ‖w‖ < ρ → Φ (φ + P.T, w) = Φ (φ, w) := by
      intro φ w _
      simp only [hΦ, fPhi_per]
    have hΦ0 : ∀ φ : ℝ, Φ (φ, 0) = 0 := by intro φ; simp [hΦ]
    have heq : (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j) =
        fun p : ℝ × ℝ => Φ (P.T * p.2 + 0, v p) := by
      funext p
      simp only [hΦ, hS, Matrix.of_apply, add_zero]
      rw [fPhi_zero hH hJ P Sinf hZS i j p.2]
    have hC := tendstoZeroCInfty_comp_periodic Φ P.T ρ P.T 0 hT hρ hΦc hΦp hΦ0 v hvt
    rw [← heq] at hC
    obtain ⟨L, hL0, hL⟩ := exists_norm_le_mul_norm_of_periodic Φ P.T ρ hT hρ
      (hΦc.of_le (by simp)) hΦp hΦ0
    refine expDecayCInfty_of_tendstoZeroCInfty _ hC b (L * Cv) (max s₂ sv) ?_ (b / 2) (by linarith)
    intro s hs t
    have hval : S (s, t) i j - Sinf t i j = Φ (P.T * t + 0, v (s, t)) := congrFun heq (s, t)
    simp only
    rw [hval]
    have h3 := hL (P.T * t + 0) (v (s, t))
      ((hvsmall (s, t) (le_trans (le_max_left _ _) hs)).trans hρ'1)
    have h4 := hCv s (le_trans (le_max_right _ _) hs) t
    calc _ ≤ L * ‖v (s, t)‖ := h3
      _ ≤ L * (Cv * Real.exp (-(b * s))) := mul_le_mul_of_nonneg_left h4 hL0
      _ = _ := by ring
  -- the bound on the frame coordinates
  obtain ⟨C₁, hC₁0, hC₁⟩ : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (φ : ℝ) (w : FasE), ‖w‖ ≤ ρ / 2 →
      ‖fCC J P (φ, w)‖ ≤ C₁ := by
    set Ψ : ℝ × FasE → (V 1 →L[ℝ] V 1) := fun z => fCC J P z - fCC J P (z.1, 0) with hΨ
    have hΨc : ContDiffOn ℝ ∞ Ψ (Set.univ ×ˢ ball (0 : FasE) ρ) := by
      intro z hz
      have hz2 : ‖z.2‖ < ρ := by simpa using hz.2
      refine ContDiffAt.contDiffWithinAt (ContDiffAt.sub ?_ ?_)
      · exact fCC_contDiffAt hH hJ P (hin z.1 z.2 hz2)
      · exact ContDiffAt.comp (g := fCC J P) z
          (fCC_contDiffAt hH hJ P (hin0 z.1)) (contDiff_fst.prodMk contDiff_const).contDiffAt
    have hΨp : ∀ (φ : ℝ) (w : FasE), ‖w‖ < ρ → Ψ (φ + P.T, w) = Ψ (φ, w) := by
      intro φ w _
      simp only [hΨ, fCC_per]
    have hΨ0 : ∀ φ : ℝ, Ψ (φ, 0) = 0 := by intro φ; simp [hΨ]
    obtain ⟨L, hL0, hL⟩ := exists_norm_le_mul_norm_of_periodic Ψ P.T ρ hT hρ
      (hΨc.of_le (by simp)) hΨp hΨ0
    have hcont : Continuous fun φ : ℝ => ‖fCC J P (φ, (0 : FasE))‖ := by
      refine (continuous_iff_continuousAt.2 fun φ => ?_).norm
      exact ContinuousAt.comp (g := fCC J P)
        (fCC_contDiffAt hH hJ P (hin0 φ)).continuousAt (by fun_prop)
    obtain ⟨φ₀, -, hφ₀⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) P.T)
      ⟨0, by simp [hT.le]⟩ hcont.continuousOn
    have hper : Function.Periodic (fun φ : ℝ => ‖fCC J P (φ, (0 : FasE))‖) P.T := fun φ => by
      simp only [fCC_per]
    refine ⟨L * (ρ / 2) + ‖fCC J P (φ₀, (0 : FasE))‖, by positivity, fun φ w hw => ?_⟩
    have h3 : ‖Ψ (φ, w)‖ ≤ L * (ρ / 2) := (hL φ w hw).trans (mul_le_mul_of_nonneg_left hw hL0)
    have h4 : ‖fCC J P (φ, (0 : FasE))‖ ≤ ‖fCC J P (φ₀, (0 : FasE))‖ := by
      obtain ⟨y', hy', hty⟩ := hper.exists_mem_Ico₀ hT φ
      have hy'' : y' ∈ Set.Icc (0 : ℝ) P.T := ⟨hy'.1, by simpa using hy'.2.le⟩
      have := hφ₀ hy''
      simp only [Set.mem_setOf_eq] at this
      rw [hty]
      exact this
    have h5 : fCC J P (φ, w) = Ψ (φ, w) + fCC J P (φ, 0) := by simp [hΨ]
    rw [h5]
    exact (norm_add_le _ _).trans (add_le_add h3 h4)
  refine ⟨s₂, C₁, b / 2, S, by positivity, hC₁0, hasy, ?_, ?_, ?_⟩
  · intro i j q hq
    have hq2 : ‖v q‖ < ρ := by
      have := hvsmall q (le_of_lt hq.1); linarith
    have hm := hin (P.T * q.2) (v q) hq2
    have h3 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (P.T * p.2, v p)) q :=
      ((contDiff_const.mul contDiff_snd).prodMk hvc).contDiffAt
    exact (ContDiffAt.comp (g := fPhi J P i j) q (fPhi_contDiffAt hH hJ P i j hm) h3).contDiffWithinAt
  · intro s t
    ext i j
    simp only [hS, Matrix.of_apply, mul_add, mul_one, hv, fasV_per y P d₀ hyp, fPhi_per]
  · intro q hq
    have hq1 := hvsmall q (le_of_lt hq)
    have hq2 : ‖v q‖ < ρ := by linarith
    have hm := hin (P.T * q.2) (v q) hq2
    obtain ⟨c1, c2, c3⟩ := fasC_ident hH hJ y hy hy0 P d₀ q
    refine ⟨c2 ▸ hm.2, c1 ▸ hC₁ _ _ (hq1.trans hρ'1), ?_, fun i j => ?_⟩
    · have h5 := (fasV_ident hH hJ y hy hy0 P d₀ q).2.2.2.1
      rw [← h5]
      have h6 : ‖(v q).2.2 ((1 : ℝ), (0 : ℝ))‖ ≤ ‖v q‖ := by
        have h7 := (v q).2.2.le_opNorm ((1 : ℝ), (0 : ℝ))
        have h8 : ‖(((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)‖ = 1 := by simp
        rw [h8, mul_one] at h7
        exact h7.trans ((norm_snd_le (v q).2).trans (norm_snd_le (v q)))
      have h9 := abs_le.1 (Real.norm_eq_abs _ ▸ h6.trans (hq1.trans hρ'2))
      show 0 < P.T + (v q).2.2 (1, 0)
      linarith [h9.1]
    · show fCC J P (P.T * q.2, fasV H P d₀ y q) (fG J P j (P.T * q.2, fasV H P d₀ y q)) (fasI i) = _
      rw [c1, c3]

end

end FiniteEnergyPlane

/-!
# N (normal frame), layer A: the complex frame `(2x, R, W, J W)` at a point of `S`

`nfF x (c₁, c₂) = c₁.re • 2x + c₁.im • R(x) + Z(x)(c₂)` and its inverse `nfC x`, for `x ∈ S`;
`J̃(x)` acts as multiplication by `i` in this frame.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff

/-! ### `ℂ ↔ ℝ²` -/

lemma nf_vecToC_J₀ (a : CauchyRiemannIndex.Vec 1) :
    vecToC (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) = Complex.I * vecToC a := by
  apply Complex.ext <;>
    simp [vecToC, CauchyRiemannIndex.J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec,
      dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]

lemma nf_cToVec_vecToC (a : CauchyRiemannIndex.Vec 1) : cToVec (vecToC a) = a := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [cToVec, vecToC]

lemma nf_vecToC_cToVec (z : ℂ) : vecToC (cToVec z) = z := by
  apply Complex.ext <;> simp [cToVec, vecToC]

lemma nf_vecToC_injective : Function.Injective vecToC := fun a b h => by
  rw [← nf_cToVec_vecToC a, h, nf_cToVec_vecToC]

lemma nf_vecToC_add (a b : CauchyRiemannIndex.Vec 1) : vecToC (a + b) = vecToC a + vecToC b := by
  apply Complex.ext <;> simp [vecToC]

lemma nf_vecToC_smul (r : ℝ) (a : CauchyRiemannIndex.Vec 1) :
    vecToC (r • a) = (r : ℂ) * vecToC a := by
  apply Complex.ext <;> simp [vecToC]

lemma nf_cToVec_add (a b : ℂ) : cToVec (a + b) = cToVec a + cToVec b :=
  nf_vecToC_injective (by rw [nf_vecToC_add, nf_vecToC_cToVec, nf_vecToC_cToVec, nf_vecToC_cToVec])

lemma nf_cToVec_smul (r : ℝ) (a : ℂ) : cToVec (r • a) = r • cToVec a :=
  nf_vecToC_injective (by
    rw [nf_vecToC_smul, nf_vecToC_cToVec, nf_vecToC_cToVec, Complex.real_smul])

lemma nf_cToVec_zero : cToVec 0 = 0 :=
  nf_vecToC_injective (by rw [nf_vecToC_cToVec]; apply Complex.ext <;> simp [vecToC])

lemma nf_cToVec_I (a : ℂ) :
    cToVec (Complex.I * a) = Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (cToVec a) :=
  nf_vecToC_injective (by rw [nf_vecToC_cToVec, nf_vecToC_J₀, nf_vecToC_cToVec])

/-- `cToVec` as a continuous linear map. -/
noncomputable def nfCV : ℂ →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  (LinearMap.mk ⟨cToVec, nf_cToVec_add⟩ nf_cToVec_smul).toContinuousLinearMap

lemma nfCV_apply (a : ℂ) : nfCV a = cToVec a := rfl

/-! ### `ω₀` bilinearity -/

lemma nf_omega_add_left (u v w : V 1) : omega0 (u + v) w = omega0 u w + omega0 v w := by
  simp [omega0, dot, j0, Fin.sum_univ_four]; ring

lemma nf_omega_add_right (u v w : V 1) : omega0 u (v + w) = omega0 u v + omega0 u w := by
  simp [omega0, dot, j0, Fin.sum_univ_four]; ring

lemma nf_omega_smul_left (c : ℝ) (v w : V 1) : omega0 (c • v) w = c * omega0 v w := by
  simp [omega0, dot, j0, Fin.sum_univ_four]; ring

lemma nf_omega_smul_right (c : ℝ) (v w : V 1) : omega0 v (c • w) = c * omega0 v w := by
  simp [omega0, dot, j0, Fin.sum_univ_four]; ring

lemma nf_omega_self (v : V 1) : omega0 v v = 0 := by
  simp [omega0, dot, j0, Fin.sum_univ_four]; ring

/-! ### The frame -/

/-- The complex coordinate of `p ∈ ξ_x` in the frame `W, J W`. -/
noncomputable def nfXi (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x p : V 1) : ℂ :=
  ⟨omega0 p (J x (r26W H J x)), omega0 (r26W H J x) p⟩

/-- The `∂ₐ`-coefficient `dH(x) X / (2 dH(x) x)`. -/
noncomputable def nfα (H : V 1 → ℝ) (x X : V 1) : ℝ := fderiv ℝ H x X / (2 * fderiv ℝ H x x)

/-- The `ξ`-part `X - α 2x - λ₀(X) R`. -/
noncomputable def nfP (H : V 1 → ℝ) (x X : V 1) : V 1 :=
  X - nfα H x X • ((2 : ℝ) • x) - liouville x X • reeb H x

/-- The complex coordinates of `X` in the frame `(2x, R, W, J W)`. -/
noncomputable def nfC (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x X : V 1) : ℂ × ℂ :=
  (⟨nfα H x X, liouville x X⟩, nfXi H J x (nfP H x X))

/-- The frame map `(c₁, c₂) ↦ c₁.re 2x + c₁.im R + Z(c₂)`. -/
noncomputable def nfF (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) (c : ℂ × ℂ) : V 1 :=
  c.1.re • ((2 : ℝ) • x) + c.1.im • reeb H x + r26ZAt H J x (cToVec c.2)

lemma nfF_add (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) (c d : ℂ × ℂ) :
    nfF H J x (c + d) = nfF H J x c + nfF H J x d := by
  simp only [nfF, Prod.fst_add, Prod.snd_add, Complex.add_re, Complex.add_im, nf_cToVec_add,
    map_add, add_smul]
  abel

lemma nfF_smul (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) (r : ℝ) (c : ℂ × ℂ) :
    nfF H J x (r • c) = r • nfF H J x c := by
  simp only [nfF, Prod.smul_fst, Prod.smul_snd, Complex.smul_re, Complex.smul_im, nf_cToVec_smul,
    map_smul, smul_eq_mul]
  module

lemma nfF_zero (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) : nfF H J x 0 = 0 := by
  simp [nfF, nf_cToVec_zero]

section point
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J) {x : V 1} (hx : x ∈ energySurface H)

include hH hJ hx in
lemma nfXi_r26 (a : CauchyRiemannIndex.Vec 1) : nfXi H J x (r26ZAt H J x a) = vecToC a := by
  have h1 : omega0 (r26W H J x) (J x (r26W H J x)) = 1 := by
    rw [r26_omega0_eq]; exact r26_W_JW hH hJ hx
  have h2 : omega0 (J x (r26W H J x)) (r26W H J x) = -1 := by
    rw [r26_omega0_eq, HryniewiczCriterion.r26_omega0_antisymm, ← r26_omega0_eq, h1]
  rw [r26ZAt_apply]
  apply Complex.ext
  · simp only [nfXi, vecToC]
    rw [nf_omega_add_left, nf_omega_smul_left, nf_omega_smul_left, h1, nf_omega_self]
    ring
  · simp only [nfXi, vecToC]
    rw [nf_omega_add_right, nf_omega_smul_right, nf_omega_smul_right, h1, nf_omega_self]
    ring

include hH hJ hx in
lemma nf_r26_nfXi {p : V 1} (hp : IsInXi H x p) : r26ZAt H J x (cToVec (nfXi H J x p)) = p := by
  obtain ⟨a, rfl⟩ := r26_unitary_surj hH hJ hx p hp
  rw [nfXi_r26 hH hJ hx, nf_cToVec_vecToC]

include hH hx in
lemma nf_liouville_self : liouville x x = 0 := by
  have := ka_liouvilleCLM_apply x x
  simp only [liouville]
  rw [ka_om_self]; simp

include hH hx in
lemma nfP_xi (X : V 1) : IsInXi H x (nfP H x X) := by
  obtain ⟨-, hR1, hR2, -⟩ := reeb_spec H hH x hx
  have hD : 0 < fderiv ℝ H x x := hH.2.2 x hx
  constructor
  · rw [nfP, ← ka_liouvilleCLM_apply, map_sub, map_sub, map_smul, map_smul, map_smul,
      ka_liouvilleCLM_apply, ka_liouvilleCLM_apply, ka_liouvilleCLM_apply, nf_liouville_self hH hx,
      hR1]
    simp
  · rw [nfP, map_sub, map_sub, map_smul, map_smul, map_smul, hR2, nfα]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    field_simp
    ring

include hH hJ hx in
/-- `nfF ∘ nfC = id` at `x ∈ S`. -/
lemma nfF_nfC (X : V 1) : nfF H J x (nfC H J x X) = X := by
  simp only [nfF, nfC]
  rw [nf_r26_nfXi hH hJ hx (nfP_xi hH hx X), nfP]
  abel

include hH hJ hx in
/-- `nfC ∘ nfF = id` at `x ∈ S`. -/
lemma nfC_nfF (c : ℂ × ℂ) : nfC H J x (nfF H J x c) = c := by
  obtain ⟨-, hR1, hR2, -⟩ := reeb_spec H hH x hx
  have hD : 0 < fderiv ℝ H x x := hH.2.2 x hx
  have hZ := r26_unitary_xi hH hJ hx (cToVec c.2)
  have hα : nfα H x (nfF H J x c) = c.1.re := by
    rw [nfα, nfF, map_add, map_add, map_smul, map_smul, map_smul, hR2, hZ.2]
    simp only [smul_eq_mul, mul_zero, add_zero]
    field_simp
  have hβ : liouville x (nfF H J x c) = c.1.im := by
    rw [nfF, ← ka_liouvilleCLM_apply, map_add, map_add, map_smul, map_smul, map_smul,
      ka_liouvilleCLM_apply, ka_liouvilleCLM_apply, ka_liouvilleCLM_apply, nf_liouville_self hH hx,
      hR1, hZ.1]
    simp
  have hp : nfP H x (nfF H J x c) = r26ZAt H J x (cToVec c.2) := by
    rw [nfP, hα, hβ, nfF]; abel
  simp only [nfC]
  rw [hα, hβ, hp, nfXi_r26 hH hJ hx, nf_vecToC_cToVec]

include hH hJ hx in
lemma nfF_injective {c d : ℂ × ℂ} (h : nfF H J x c = nfF H J x d) : c = d := by
  rw [← nfC_nfF hH hJ hx c, h, nfC_nfF hH hJ hx d]

include hH hJ hx in
/-- `J̃(x)` is multiplication by `i` in the frame. -/
lemma nf_Jt_nfF (c : ℂ × ℂ) :
    Jtilde H J x (nfF H J x c) = nfF H J x (Complex.I • c) := by
  have hZ := r26_unitary_xi hH hJ hx (cToVec c.2)
  rw [nfF, map_add, map_add, (Jtilde H J x).map_smul c.1.re, (Jtilde H J x).map_smul c.1.im,
    fas_Jt_two_mem hH hx, fas_Jt_reeb_mem hH hx,
    fas_Jt_xi_mem hH hx hZ, r26_unitary_J hH hJ hx, nfF]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.mul_im, zero_mul, one_mul, zero_sub, zero_add, nf_cToVec_I]
  rw [neg_smul, smul_neg]
  abel

include hH hJ hx in
/-- Complex scalars: `w.re • nfF c + w.im • J̃ (nfF c) = nfF (w • c)`. -/
lemma nf_cmul_nfF (w : ℂ) (c : ℂ × ℂ) :
    w.re • nfF H J x c + w.im • Jtilde H J x (nfF H J x c) = nfF H J x (w • c) := by
  rw [nf_Jt_nfF hH hJ hx, ← nfF_smul, ← nfF_smul, ← nfF_add]
  congr 1
  refine Prod.ext ?_ ?_ <;> apply Complex.ext <;> simp <;> ring

end point

end FiniteEnergyPlane

/-!
# N (normal frame), layer M: the rotated unitary frame along an orbit

`M t = Z(t) ∘ (rotation by θ e^{2πit})` with `|θ| = 1`: a unitary frame of `ξ` along `P` whose
winding is one more than that of the frame `Z` of `fas_frame` (which has winding `0`).
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff Real

/-- `θ e^{2πit}`. -/
noncomputable def nfE (θ : ℂ) (t : ℝ) : ℂ := θ * Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I)

lemma nfE_contDiff (θ : ℂ) : ContDiff ℝ ∞ (nfE θ) := by
  unfold nfE
  refine contDiff_const.mul (Complex.contDiff_exp.comp ?_)
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const

lemma nfE_per (θ : ℂ) (t : ℝ) : nfE θ (t + 1) = nfE θ t := by
  unfold nfE
  congr 1
  rw [show (((2 * π * (t + 1) : ℝ)) : ℂ) * Complex.I =
    (((2 * π * t : ℝ)) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

lemma nfE_norm (θ : ℂ) (t : ℝ) : ‖nfE θ t‖ = ‖θ‖ := by
  unfold nfE
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma nfE_conj_mul (θ : ℂ) (hθ : ‖θ‖ = 1) (t : ℝ) : starRingEnd ℂ (nfE θ t) * nfE θ t = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, nfE_norm, hθ]; simp

lemma nfE_hasLoopWind (θ : ℂ) (hθ : θ ≠ 0) : HasLoopWind (nfE θ) 1 := by
  refine ⟨(nfE_contDiff θ).continuous, nfE_per θ, fun t => ?_, ?_⟩
  · unfold nfE; exact mul_ne_zero hθ (Complex.exp_ne_zero _)
  refine ⟨fun t => Complex.arg θ + 2 * π * t, by fun_prop, fun t => ?_, by ring⟩
  rw [nfE_norm]
  unfold nfE
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I θ]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- Multiplication by `w` on `ℝ² ≅ ℂ`. -/
noncomputable def nfRot (w : ℂ) : CauchyRiemannIndex.Vec 1 →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  w.re • ContinuousLinearMap.id ℝ _ +
    w.im • (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1)).toContinuousLinearMap

lemma vecToC_nfRot (w : ℂ) (a : CauchyRiemannIndex.Vec 1) :
    vecToC (nfRot w a) = w * vecToC a := by
  simp only [nfRot, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, LinearMap.coe_toContinuousLinearMap']
  rw [nf_vecToC_add, nf_vecToC_smul, nf_vecToC_smul, nf_vecToC_J₀]
  conv_rhs => rw [← Complex.re_add_im w]
  ring

lemma nfRot_contDiff {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ fun t => nfRot (w t) := by
  unfold nfRot
  exact ((Complex.reCLM.contDiff.comp hw).smul contDiff_const).add
    ((Complex.imCLM.contDiff.comp hw).smul contDiff_const)

lemma nf_inner_eq (a b : CauchyRiemannIndex.Vec 1) :
    inner ℝ a b = (starRingEnd ℂ (vecToC a) * vecToC b).re := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_one, RCLike.inner_apply,
    conj_trivial, vecToC, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

section frame
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

/-- The rotated frame. -/
noncomputable def nfM (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (θ : ℂ) (t : ℝ) :
    CauchyRiemannIndex.Vec 1 →L[ℝ] V 1 :=
  (r26ZAt H J (P.x (P.T * t))).comp (nfRot (nfE θ t))

lemma nfM_apply (P : ReebOrbit H) (θ : ℂ) (t : ℝ) (a : CauchyRiemannIndex.Vec 1) :
    nfM H J P θ t a = r26ZAt H J (P.x (P.T * t)) (cToVec (nfE θ t * vecToC a)) := by
  simp only [nfM, ContinuousLinearMap.comp_apply]
  rw [← vecToC_nfRot, nf_cToVec_vecToC]

include hH hJ in
/-- The rotated frame is unitary, and its winding is shifted by one. -/
theorem nf_frame_rot (P : ReebOrbit H) (θ : ℂ) (hθ : ‖θ‖ = 1) :
    IsUnitaryXiFrame J P (nfM H J P θ) ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => nfM H J P θ t (ζ t)) (k + 1) ↔
            HasLoopWind (fun t => vecToC (ζ t)) k) := by
  obtain ⟨⟨hZc, hZp, hZt⟩, hwind⟩ := fas_frame hH hJ P
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  have hR := nfRot_contDiff (nfE_contDiff θ)
  have hvinj := nf_vecToC_injective
  refine ⟨⟨hZc.clm_comp hR, fun t => ?_, fun t => ⟨fun a => (hZt t).1 _, fun w hw => ?_,
    fun a => ?_, fun a b => ?_⟩⟩, ?_⟩
  · simp only [nfM, nfE_per]
    have := hZp t
    simp only at this
    rw [this]
  · obtain ⟨a, ha⟩ := (hZt t).2.1 w hw
    refine ⟨cToVec (starRingEnd ℂ (nfE θ t) * vecToC a), ?_⟩
    simp only [nfM, ContinuousLinearMap.comp_apply]
    rw [← ha]
    congr 1
    apply hvinj
    rw [vecToC_nfRot, nf_vecToC_cToVec, ← mul_assoc, mul_comm (nfE θ t), nfE_conj_mul θ hθ,
      one_mul]
  · simp only [nfM, ContinuousLinearMap.comp_apply]
    rw [(hZt t).2.2.1]
    congr 1
    apply hvinj
    rw [nf_vecToC_J₀, vecToC_nfRot, vecToC_nfRot, nf_vecToC_J₀]
    ring
  · simp only [nfM, ContinuousLinearMap.comp_apply]
    rw [(hZt t).2.2.2, nf_inner_eq, nf_inner_eq, nf_vecToC_J₀, nf_vecToC_J₀, vecToC_nfRot,
      vecToC_nfRot]
    have := nfE_conj_mul θ hθ t
    congr 1
    simp only [map_mul]
    linear_combination (starRingEnd ℂ Complex.I * starRingEnd ℂ (vecToC a) * vecToC b) * this
  · intro ζ hζ hζp hζ0 k
    set ζ' : ℝ → CauchyRiemannIndex.Vec 1 := fun t => nfRot (nfE θ t) (ζ t) with hζ'
    have hc : Continuous ζ' := hR.continuous.clm_apply hζ
    have hp : Function.Periodic ζ' 1 := fun t => by simp only [hζ', nfE_per, hζp t]
    have h0 : ∀ t, ζ' t ≠ 0 := by
      intro t h
      have := congrArg vecToC h
      rw [vecToC_nfRot] at this
      have hz : vecToC (0 : CauchyRiemannIndex.Vec 1) = 0 := by
        apply Complex.ext <;> simp [vecToC]
      rw [hz] at this
      rcases mul_eq_zero.1 this with h1 | h1
      · have := nfE_norm θ t; rw [h1, hθ] at this; simp at this
      · exact hζ0 t (hvinj (h1.trans hz.symm))
    have e1 := hwind ζ' hc hp h0 (k + 1)
    have e2 : (fun t => nfM H J P θ t (ζ t)) = fun t => r26ZAt H J (P.x (P.T * t)) (ζ' t) := rfl
    have e3 : (fun t => vecToC (ζ' t)) = fun t => nfE θ t * vecToC (ζ t) :=
      funext fun t => vecToC_nfRot _ _
    rw [e2, e1, e3]
    have hE := nfE_hasLoopWind θ hθ0
    constructor
    · intro h
      have := hasLoopWind_mul (hasLoopWind_conj hE) h
      have e4 : (fun t => starRingEnd ℂ (nfE θ t) * (nfE θ t * vecToC (ζ t))) =
          fun t => vecToC (ζ t) := funext fun t => by
        rw [← mul_assoc, nfE_conj_mul θ hθ, one_mul]
      rw [e4, show -(1 : ℤ) + (k + 1) = k by ring] at this
      exact this
    · intro h
      have := hasLoopWind_mul hE h
      rwa [add_comm] at this

end frame

end FiniteEnergyPlane

/-!
# N (normal frame), layer P: the normal field on the plane

With `(A, B) = nfC(x)(r ∂ₛu)` (`x = proj u`, `r = scaleToS u`), the Hermitian complement
`σ = (-B̄, Ā)` gives `N z ν = e^{2a(u z)} nfF x (ν c₀ ρ(z) σ(z))`, where `ρ > 0` is smooth,
`ρ(0) = ρ₀` and `ρ(z) = |z|` for `|z| ≥ 1`.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff Real

lemma nf_mk_eq (a b : ℝ) : (⟨a, b⟩ : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

lemma nf_omega_eq (a b : V 1) : omega0 a b = 2 * liouvilleCLM a b := by
  rw [ka_liouvilleCLM_apply, liouville]; ring

section smooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {q : X}

lemma nf_ofReal_contDiffAt {a : X → ℝ} (ha : ContDiffAt ℝ ∞ a q) :
    ContDiffAt ℝ ∞ (fun q => (a q : ℂ)) q :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp q ha

lemma nf_mk_contDiffAt {a b : X → ℝ} (ha : ContDiffAt ℝ ∞ a q) (hb : ContDiffAt ℝ ∞ b q) :
    ContDiffAt ℝ ∞ (fun q => (⟨a q, b q⟩ : ℂ)) q := by
  have e : (fun q => (⟨a q, b q⟩ : ℂ)) = fun q => (a q : ℂ) + (b q : ℂ) * Complex.I :=
    funext fun q => nf_mk_eq _ _
  rw [e]
  exact (nf_ofReal_contDiffAt ha).add ((nf_ofReal_contDiffAt hb).mul contDiffAt_const)

lemma nf_re_contDiffAt {a : X → ℂ} (ha : ContDiffAt ℝ ∞ a q) :
    ContDiffAt ℝ ∞ (fun q => (a q).re) q :=
  Complex.reCLM.contDiff.contDiffAt.comp q ha

lemma nf_im_contDiffAt {a : X → ℂ} (ha : ContDiffAt ℝ ∞ a q) :
    ContDiffAt ℝ ∞ (fun q => (a q).im) q :=
  Complex.imCLM.contDiff.contDiffAt.comp q ha

lemma nf_conj_contDiffAt {a : X → ℂ} (ha : ContDiffAt ℝ ∞ a q) :
    ContDiffAt ℝ ∞ (fun q => starRingEnd ℂ (a q)) q :=
  Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp q ha

lemma nf_omega_contDiffAt {a b : X → V 1} (ha : ContDiffAt ℝ ∞ a q) (hb : ContDiffAt ℝ ∞ b q) :
    ContDiffAt ℝ ∞ (fun q => omega0 (a q) (b q)) q := by
  have e : (fun q => omega0 (a q) (b q)) = fun q => 2 * liouvilleCLM (a q) (b q) :=
    funext fun q => nf_omega_eq _ _
  rw [e]
  exact ((ka_liouvilleCLM_contDiff.contDiffAt.comp q ha).clm_apply hb).const_smul (2 : ℝ)

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

include hH hJ in
lemma nf_W_contDiffAt {f : X → V 1} (hf : ContDiffAt ℝ ∞ f q) (hfS : f q ∈ energySurface H) :
    ContDiffAt ℝ ∞ (fun q => r26W H J (f q)) q :=
  (fas_W_contDiffAt hH hJ (fas_mem_O hH hJ hfS)).comp q hf

include hJ in
lemma nf_Japp_contDiffAt {f g : X → V 1} (hf : ContDiffAt ℝ ∞ f q) (hg : ContDiffAt ℝ ∞ g q) :
    ContDiffAt ℝ ∞ (fun q => J (f q) (g q)) q :=
  (hJ.1.contDiffAt.comp q hf).clm_apply hg

include hH hJ in
lemma nfF_contDiffAt {f : X → V 1} {c : X → ℂ × ℂ} (hf : ContDiffAt ℝ ∞ f q)
    (hfS : f q ∈ energySurface H) (hc : ContDiffAt ℝ ∞ c q) :
    ContDiffAt ℝ ∞ (fun q => nfF H J (f q) (c q)) q := by
  have e : (fun q => nfF H J (f q) (c q)) = fun q =>
      (c q).1.re • ((2 : ℝ) • f q) + (c q).1.im • reeb H (f q) +
        ((c q).2.re • r26W H J (f q) + (c q).2.im • J (f q) (r26W H J (f q))) := by
    funext q; simp only [nfF, r26ZAt_apply]; simp [cToVec]
  rw [e]
  have hW := nf_W_contDiffAt hH hJ hf hfS
  have hR : ContDiffAt ℝ ∞ (fun q => reeb H (f q)) q :=
    (ka_reeb_contDiffAt H hH (f q) hfS).comp q hf
  exact (((nf_re_contDiffAt hc.fst).smul (hf.const_smul (2 : ℝ))).add
    ((nf_im_contDiffAt hc.fst).smul hR)).add (((nf_re_contDiffAt hc.snd).smul hW).add
    ((nf_im_contDiffAt hc.snd).smul (nf_Japp_contDiffAt hJ hf hW)))

include hH hJ in
lemma nfC_contDiffAt {f g : X → V 1} (hf : ContDiffAt ℝ ∞ f q) (hfS : f q ∈ energySurface H)
    (hg : ContDiffAt ℝ ∞ g q) : ContDiffAt ℝ ∞ (fun q => nfC H J (f q) (g q)) q := by
  have hdH : ContDiffAt ℝ ∞ (fun q => fderiv ℝ H (f q)) q :=
    (hH.1.fderiv_right (m := ∞) (by simp)).contDiffAt.comp q hf
  have hD : 2 * fderiv ℝ H (f q) (f q) ≠ 0 := by
    have := hH.2.2 _ hfS; positivity
  have hα : ContDiffAt ℝ ∞ (fun q => nfα H (f q) (g q)) q :=
    (hdH.clm_apply hg).div ((hdH.clm_apply hf).const_smul (2 : ℝ)) hD
  have hlv : ∀ {b : X → V 1}, ContDiffAt ℝ ∞ b q →
      ContDiffAt ℝ ∞ (fun q => liouville (f q) (b q)) q := fun hb =>
    (nf_omega_contDiffAt hf hb).div_const 2
  have hR : ContDiffAt ℝ ∞ (fun q => reeb H (f q)) q :=
    (ka_reeb_contDiffAt H hH (f q) hfS).comp q hf
  have hP : ContDiffAt ℝ ∞ (fun q => nfP H (f q) (g q)) q :=
    (hg.sub (hα.smul (hf.const_smul (2 : ℝ)))).sub ((hlv hg).smul hR)
  have hW := nf_W_contDiffAt hH hJ hf hfS
  have hJW := nf_Japp_contDiffAt hJ hf hW
  exact (nf_mk_contDiffAt hα (hlv hg)).prodMk
    (nf_mk_contDiffAt (nf_omega_contDiffAt hP hJW) (nf_omega_contDiffAt hW hP))

end smooth

/-! ### The normalisation `ρ` -/

/-- `χ(z) = smoothTransition(2|z|² - 1)`: `0` for `|z|² ≤ 1/2`, `1` for `|z| ≥ 1`. -/
noncomputable def nfChi (z : ℂ) : ℝ := Real.smoothTransition (2 * ‖z‖ ^ 2 - 1)

/-- `ρ(z) = √(|z|² + (1 - χ(z)) ρ₀²)`. -/
noncomputable def nfRho (ρ₀ : ℝ) (z : ℂ) : ℝ := Real.sqrt (‖z‖ ^ 2 + (1 - nfChi z) * ρ₀ ^ 2)

lemma nfChi_contDiff : ContDiff ℝ ∞ nfChi :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_norm_sq ℝ)).sub contDiff_const)

lemma nfRho_arg_pos {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (z : ℂ) : 0 < ‖z‖ ^ 2 + (1 - nfChi z) * ρ₀ ^ 2 := by
  have h1 : nfChi z ≤ 1 := Real.smoothTransition.le_one _
  by_cases hz : z = 0
  · subst hz
    have : nfChi 0 = 0 := Real.smoothTransition.zero_of_nonpos (by simp)
    rw [this]; simp; positivity
  · have : 0 < ‖z‖ ^ 2 := by positivity
    have : 0 ≤ (1 - nfChi z) * ρ₀ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith

lemma nfRho_pos {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (z : ℂ) : 0 < nfRho ρ₀ z :=
  Real.sqrt_pos.2 (nfRho_arg_pos hρ₀ z)

lemma nfRho_contDiff {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) : ContDiff ℝ ∞ (nfRho ρ₀) :=
  ((contDiff_norm_sq ℝ).add ((contDiff_const.sub nfChi_contDiff).mul contDiff_const)).sqrt
    fun z => (nfRho_arg_pos hρ₀ z).ne'

lemma nfRho_zero {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) : nfRho ρ₀ 0 = ρ₀ := by
  have : nfChi 0 = 0 := Real.smoothTransition.zero_of_nonpos (by simp)
  rw [nfRho, this]; simp [Real.sqrt_sq hρ₀.le]

lemma nfRho_of_one_le (ρ₀ : ℝ) {z : ℂ} (hz : 1 ≤ ‖z‖) : nfRho ρ₀ z = ‖z‖ := by
  have : nfChi z = 1 := Real.smoothTransition.one_of_one_le (by nlinarith)
  rw [nfRho, this]; simp

/-! ### The normal field -/

/-- `(A, B) = nfC(x)(r ∂ₛu)`. -/
noncomputable def nfAB (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (u : ℂ → V 1) (z : ℂ) : ℂ × ℂ :=
  nfC H J (proj H (u z)) (scaleToS H (u z) • fderiv ℝ u z 1)

/-- `σ = (-B̄, Ā)`. -/
noncomputable def nfSig (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (u : ℂ → V 1) (z : ℂ) : ℂ × ℂ :=
  (-(starRingEnd ℂ (nfAB H J u z).2), starRingEnd ℂ (nfAB H J u z).1)

/-- The normal vector `n(z) = e^{2a} nfF x (c₀ ρ σ)`. -/
noncomputable def nfVec (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (u : ℂ → V 1) (c₀ : ℂ) (ρ₀ : ℝ)
    (z : ℂ) : V 1 :=
  Real.exp (2 * aCoord H (u z)) • nfF H J (proj H (u z)) ((c₀ * (nfRho ρ₀ z : ℂ)) • nfSig H J u z)

/-- `N z ν = ν.re n + ν.im J̃ n`. -/
noncomputable def nfN (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (u : ℂ → V 1) (c₀ : ℂ) (ρ₀ : ℝ)
    (z : ℂ) : ℂ →L[ℝ] V 1 :=
  Complex.reCLM.smulRight (nfVec H J u c₀ ρ₀ z) +
    Complex.imCLM.smulRight (Jtilde H J (u z) (nfVec H J u c₀ ρ₀ z))

section plane
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
  (hhol : ∀ z, fderiv ℝ u z 1 + Jtilde H J (u z) (fderiv ℝ u z Complex.I) = 0)
  (hp : ∀ z, piXi H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z 1) ≠ 0)

include hH hJ hu hu0 in
lemma nf_ua_contDiff : ContDiff ℝ ∞ (fun z => aCoord H (u z)) := by
  obtain ⟨-, -, ha, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  refine contDiff_iff_contDiffAt.2 fun q => ?_
  have hO : IsOpen {y : V 1 | y ≠ 0} := isOpen_ne
  exact (ha.contDiffAt (hO.mem_nhds (hu0 q))).comp q hu.contDiffAt

include hH hJ hu hu0 in
lemma nf_ux_contDiff : ContDiff ℝ ∞ (fun z => proj H (u z)) := by
  obtain ⟨-, hp, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  refine contDiff_iff_contDiffAt.2 fun q => ?_
  have hO : IsOpen {y : V 1 | y ≠ 0} := isOpen_ne
  exact (hp.contDiffAt (hO.mem_nhds (hu0 q))).comp q hu.contDiffAt

include hH hu0 in
lemma nf_mem (z : ℂ) : proj H (u z) ∈ energySurface H := (ka_scale_spec H hH (u z) (hu0 z)).2

include hH hu0 in
lemma nf_r_pos (z : ℂ) : 0 < scaleToS H (u z) := (ka_scale_spec H hH (u z) (hu0 z)).1

include hH hJ hu0 in
lemma nf_Jt_eq (z : ℂ) : Jtilde H J (u z) = Jtilde H J (proj H (u z)) := by
  have hS := nf_mem hH u hu0 z
  conv_lhs => rw [fas_y_eq hH (hu0 z)]
  exact fas_Jt_scale hH hJ (fas_ne_zero_of_mem hH hS) (inv_pos.2 (nf_r_pos hH u hu0 z))

include hH hJ hu0 in
lemma nf_r_exp (z : ℂ) : scaleToS H (u z) * Real.exp (2 * aCoord H (u z)) = 1 := by
  rw [fas_exp_two_a hH hJ (hu0 z), mul_inv_cancel₀ (nf_r_pos hH u hu0 z).ne']

include hH hJ hu0 in
lemma nfN_apply (c₀ : ℂ) (ρ₀ : ℝ) (z ν : ℂ) :
    nfN H J u c₀ ρ₀ z ν = Real.exp (2 * aCoord H (u z)) •
      nfF H J (proj H (u z)) ((ν * (c₀ * (nfRho ρ₀ z : ℂ))) • nfSig H J u z) := by
  have hS := nf_mem hH u hu0 z
  simp only [nfN, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, nfVec]
  rw [nf_Jt_eq hH hJ u hu0, map_smul, smul_comm ν.re, smul_comm ν.im, ← smul_add,
    nf_cmul_nfF hH hJ hS, smul_smul]

include hH hJ hu0 in
lemma nfN_I (c₀ : ℂ) (ρ₀ : ℝ) (z ν : ℂ) :
    nfN H J u c₀ ρ₀ z (Complex.I * ν) = Jtilde H J (u z) (nfN H J u c₀ ρ₀ z ν) := by
  simp only [nfN, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, map_add, map_smul, fas_Jt_sq hH hJ (hu0 z),
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp only [zero_mul, one_mul, zero_sub, zero_add, neg_smul, smul_neg]
  abel

include hH hJ hu hu0 in
lemma nfN_contDiff (c₀ : ℂ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) : ContDiff ℝ ∞ (nfN H J u c₀ ρ₀) := by
  have hx := nf_ux_contDiff hH hJ u hu hu0
  have ha := nf_ua_contDiff hH hJ u hu hu0
  have hr : (fun z => scaleToS H (u z)) = fun z => (Real.exp (2 * aCoord H (u z)))⁻¹ := by
    funext z; rw [fas_exp_two_a hH hJ (hu0 z), inv_inv]
  have hrc : ContDiff ℝ ∞ (fun z => scaleToS H (u z)) := by
    rw [hr]; exact (Real.contDiff_exp.comp (contDiff_const.mul ha)).inv fun z => (Real.exp_pos _).ne'
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ u z 1) :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hAB : ContDiff ℝ ∞ (nfAB H J u) := contDiff_iff_contDiffAt.2 fun z =>
    nfC_contDiffAt hH hJ hx.contDiffAt (nf_mem hH u hu0 z) (hrc.smul hd).contDiffAt
  have hσ : ContDiff ℝ ∞ (nfSig H J u) := contDiff_iff_contDiffAt.2 fun z =>
    (nf_conj_contDiffAt hAB.contDiffAt.snd).neg.prodMk (nf_conj_contDiffAt hAB.contDiffAt.fst)
  have hk : ContDiff ℝ ∞ (fun z => c₀ * (nfRho ρ₀ z : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (nfRho_contDiff hρ₀))
  have hn : ContDiff ℝ ∞ (nfVec H J u c₀ ρ₀) := contDiff_iff_contDiffAt.2 fun z =>
    (Real.contDiff_exp.comp (contDiff_const.mul ha)).contDiffAt.smul
      (nfF_contDiffAt hH hJ hx.contDiffAt (nf_mem hH u hu0 z) (hk.smul hσ).contDiffAt)
  have hJn : ContDiff ℝ ∞ (fun z => Jtilde H J (u z) (nfVec H J u c₀ ρ₀ z)) :=
    contDiff_iff_contDiffAt.2 fun z =>
      ((fas_Jt_contDiffAt hH hJ (hu0 z)).comp z hu.contDiffAt).clm_apply hn.contDiffAt
  exact (contDiff_const.smulRight hn).add (contDiff_const.smulRight hJn)

include hH hJ hu hu0 in
lemma nf_Du_C (z : ℂ) : scaleToS H (u z) • fderiv ℝ u z 1 =
    (2 * fderiv ℝ (fun z => aCoord H (u z)) z 1) • proj H (u z) +
      fderiv ℝ (fun z => proj H (u z)) z 1 := by
  have ha := nf_ua_contDiff hH hJ u hu hu0
  have hx := nf_ux_contDiff hH hJ u hu hu0
  have hr := nf_r_pos hH u hu0 z
  have hfun : ∀ q, u q = Real.exp (2 * aCoord H (u q)) • proj H (u q) := fun q =>
    (jtilde_isAlmostComplexOn H hH J hJ).2.2.2.1 (u q) (hu0 q) |>.2
  have h1 : HasFDerivAt (fun q => aCoord H (u q)) (fderiv ℝ (fun q => aCoord H (u q)) z) z :=
    (ha.differentiable (by simp) z).hasFDerivAt
  have h2 : HasFDerivAt (fun q => proj H (u q)) (fderiv ℝ (fun q => proj H (u q)) z) z :=
    (hx.differentiable (by simp) z).hasFDerivAt
  have h3 := ((h1.const_mul 2).exp).smul h2
  have h4 := (h3.congr_of_eventuallyEq (f₁ := u) (Eventually.of_forall hfun)).fderiv
  rw [h4, fas_exp_two_a hH hJ (hu0 z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_add, smul_smul, smul_eq_mul]
  rw [mul_inv_cancel₀ hr.ne', one_smul, add_comm]
  congr 2
  field_simp

include hH hJ hu hu0 hhol in
/-- `r Du(z) w = nfF x (w • (A, B))`. -/
lemma nf_Du (z w : ℂ) :
    scaleToS H (u z) • fderiv ℝ u z w = nfF H J (proj H (u z)) (w • nfAB H J u z) := by
  have hS := nf_mem hH u hu0 z
  have hsq := fas_Jt_sq hH hJ (hu0 z)
  have h2 : Jtilde H J (u z) (fderiv ℝ u z Complex.I) = -fderiv ℝ u z 1 :=
    eq_neg_of_add_eq_zero_right (hhol z)
  have h3 : fderiv ℝ u z Complex.I = Jtilde H J (u z) (fderiv ℝ u z 1) := by
    have := congrArg (Jtilde H J (u z)) h2
    rw [hsq, map_neg] at this
    exact (neg_inj.1 this)
  have hw : fderiv ℝ u z w = w.re • fderiv ℝ u z 1 + w.im • fderiv ℝ u z Complex.I := by
    conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
      apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul]
  have h1 : scaleToS H (u z) • fderiv ℝ u z 1 = nfF H J (proj H (u z)) (nfAB H J u z) :=
    (nfF_nfC hH hJ hS _).symm
  rw [hw, h3, nf_Jt_eq hH hJ u hu0, ← nf_cmul_nfF hH hJ hS, ← h1, map_smul]
  module

include hH hJ hu hu0 hp in
lemma nfAB_snd_ne (z : ℂ) : (nfAB H J u z).2 ≠ 0 := by
  have hS := nf_mem hH u hu0 z
  have hx := nf_ux_contDiff hH hJ u hu hu0
  obtain ⟨-, hR1, hR2, -⟩ := reeb_spec H hH _ hS
  have hD : 0 < fderiv ℝ H (proj H (u z)) (proj H (u z)) := hH.2.2 _ hS
  have hcol := nf_Du_C hH hJ u hu hu0 z
  set x := proj H (u z) with hxdef
  set v := fderiv ℝ (fun z => proj H (u z)) z 1 with hv
  set a := fderiv ℝ (fun z => aCoord H (u z)) z 1 with ha
  have hdH : fderiv ℝ H x v = 0 := by
    have h1 : HasFDerivAt (H ∘ fun q => proj H (u q))
        ((fderiv ℝ H x).comp (fderiv ℝ (fun q => proj H (u q)) z)) z :=
      HasFDerivAt.comp (g := H) z ((hH.1.differentiable (by simp)) x).hasFDerivAt
        (hx.differentiable (by simp) z).hasFDerivAt
    have hc : (H ∘ fun q => proj H (u q)) = fun _ => (1 : ℝ) :=
      funext fun q => nf_mem hH u hu0 q
    rw [hc] at h1
    have := congrArg (fun L => L 1) (h1.unique (hasFDerivAt_const (1 : ℝ) z))
    simpa using this
  have hα : nfα H x (scaleToS H (u z) • fderiv ℝ u z 1) = a := by
    rw [hcol, nfα, map_add, map_smul, hdH, smul_eq_mul, add_zero]
    field_simp
  have hβ : liouville x (scaleToS H (u z) • fderiv ℝ u z 1) = liouville x v := by
    rw [hcol, ← ka_liouvilleCLM_apply, map_add, map_smul, ka_liouvilleCLM_apply,
      ka_liouvilleCLM_apply, nf_liouville_self hH hS]
    simp
  have hP : nfP H x (scaleToS H (u z) • fderiv ℝ u z 1) = piXi H x v := by
    rw [nfP, hα, hβ, hcol, piXi]
    module
  intro h0
  apply hp z
  have hxi := nfP_xi hH hS (scaleToS H (u z) • fderiv ℝ u z 1)
  have := nf_r26_nfXi hH hJ hS hxi
  have h0' : nfXi H J x (nfP H x (scaleToS H (u z) • fderiv ℝ u z 1)) = 0 := h0
  rw [h0', nf_cToVec_zero, map_zero, hP] at this
  exact this.symm

lemma nf_D_ne (A B : ℂ) (hB : B ≠ 0) : A * starRingEnd ℂ A + B * starRingEnd ℂ B ≠ 0 := by
  rw [Complex.mul_conj, Complex.mul_conj]
  have := Complex.normSq_pos.2 hB
  have h2 := Complex.normSq_nonneg A
  exact_mod_cast (by linarith : (0 : ℝ) < Complex.normSq A + Complex.normSq B).ne'

include hH hJ hu hu0 hhol hp in
/-- `Du(z) ℂ ⊕ N(z) ℂ = V`. -/
lemma nfN_compl {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (z Δ ν : ℂ)
    (h : fderiv ℝ u z Δ + nfN H J u c₀ ρ₀ z ν = 0) : Δ = 0 ∧ ν = 0 := by
  have hS := nf_mem hH u hu0 z
  have hr := nf_r_pos hH u hu0 z
  have hB := nfAB_snd_ne hH hJ u hu hu0 hp z
  set k : ℂ := ν * (c₀ * (nfRho ρ₀ z : ℂ)) with hk
  have h1 := congrArg (fun v => scaleToS H (u z) • v) h
  simp only [smul_add, smul_zero] at h1
  rw [nf_Du hH hJ u hu hu0 hhol, nfN_apply hH hJ u hu0, smul_smul, nf_r_exp hH hJ u hu0, one_smul,
    ← nfF_add, ← nfF_zero H J (proj H (u z))] at h1
  have h2 := nfF_injective hH hJ hS h1
  set A := (nfAB H J u z).1
  set B := (nfAB H J u z).2
  have e1 : Δ * A + k * -(starRingEnd ℂ B) = 0 := by
    have := congrArg Prod.fst h2; simpa [nfSig] using this
  have e2 : Δ * B + k * starRingEnd ℂ A = 0 := by
    have := congrArg Prod.snd h2; simpa [nfSig] using this
  have hΔ : Δ = 0 := by
    have hD := nf_D_ne A B hB
    have : Δ * (A * starRingEnd ℂ A + B * starRingEnd ℂ B) = 0 := by
      linear_combination (starRingEnd ℂ A) * e1 + (starRingEnd ℂ B) * e2
    exact (mul_eq_zero.1 this).resolve_right hD
  refine ⟨hΔ, ?_⟩
  rw [hΔ, zero_mul, zero_add, mul_neg, neg_eq_zero] at e1
  have hBc : starRingEnd ℂ B ≠ 0 := (map_ne_zero _).2 hB
  have hk0 : k = 0 := (mul_eq_zero.1 e1).resolve_right hBc
  have hρ := nfRho_pos hρ₀ z
  have hρc : (nfRho ρ₀ z : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  rcases mul_eq_zero.1 hk0 with h3 | h3
  · exact h3
  · exact absurd h3 (mul_ne_zero hc₀ hρc)

include hH hJ hu hu0 hhol hp in
/-- The point `u 0` lies in `N 0 1 + Du(0) ℂ` for the right `c₀ ρ₀`. -/
lemma nfN_tau {c₀ : ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hk : c₀ * (ρ₀ : ℂ) = -(nfAB H J u 0).2 /
      (2 * ((nfAB H J u 0).1 * starRingEnd ℂ (nfAB H J u 0).1 +
        (nfAB H J u 0).2 * starRingEnd ℂ (nfAB H J u 0).2))) :
    ∃ τ : ℂ, fderiv ℝ u 0 τ + nfN H J u c₀ ρ₀ 0 1 = u 0 := by
  have hS := nf_mem hH u hu0 0
  have hr := nf_r_pos hH u hu0 0
  have hB := nfAB_snd_ne hH hJ u hu hu0 hp 0
  set A := (nfAB H J u 0).1 with hA
  set B := (nfAB H J u 0).2 with hBdef
  set D := A * starRingEnd ℂ A + B * starRingEnd ℂ B with hD
  have hD0 : D ≠ 0 := nf_D_ne A B hB
  refine ⟨starRingEnd ℂ A / (2 * D), ?_⟩
  apply smul_right_injective (V 1) hr.ne'
  simp only
  rw [smul_add, nf_Du hH hJ u hu hu0 hhol, nfN_apply hH hJ u hu0, smul_smul, nf_r_exp hH hJ u hu0,
    one_smul, nfRho_zero hρ₀, ← nfF_add]
  have hux : scaleToS H (u 0) • u 0 = nfF H J (proj H (u 0)) ((1 / 2 : ℂ), 0) := by
    nth_rewrite 2 [fas_y_eq hH (hu0 0)]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, nfF]
    simp [nf_cToVec_zero]
  rw [hux]
  congr 1
  rw [one_mul, hk]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, nfSig]
    rw [← hA, ← hBdef]
    field_simp
    linear_combination (-2 : ℂ) * hD
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, nfSig]
    rw [← hA, ← hBdef]
    field_simp
    ring

end plane

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem fas_norm_vecToC (a : CauchyRiemannIndex.Vec 1) : ‖vecToC a‖ = ‖a‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
  simp [vecToC, Fintype.sum_sum_type, sq]

theorem fas_norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem fas_exists_cylInf (z : ℂ) (hz : z ≠ 0) : ∃ s t : ℝ, cylInf s t = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  refine ⟨Real.log ‖z‖ / (2 * π), Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [mul_div_cancel₀ _ hpi, Real.exp_log hn, mul_div_cancel₀ _ hpi]
  exact Complex.norm_mul_exp_arg_mul_I z

theorem fas_re_conj_mul_pos (a b : ℂ) (hlt : ‖b - a‖ < ‖a‖) :
    0 < (starRingEnd ℂ a * b).re := by
  have hapos : 0 < ‖a‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have h1 : starRingEnd ℂ a * b = (‖a‖ ^ 2 : ℝ) + starRingEnd ℂ a * (b - a) := by
    rw [mul_sub, Complex.conj_mul']
    push_cast
    ring
  rw [h1, Complex.add_re, Complex.ofReal_re]
  have h2 : -(‖a‖ * ‖b - a‖) ≤ (starRingEnd ℂ a * (b - a)).re := by
    have := Complex.abs_re_le_norm (starRingEnd ℂ a * (b - a))
    rw [norm_mul, Complex.norm_conj] at this
    exact (abs_le.1 this).1
  nlinarith

lemma fas_vecToC_cont : Continuous vecToC := by
  have e : vecToC = fun a : CauchyRiemannIndex.Vec 1 =>
      ((a (Sum.inl 0) : ℝ) : ℂ) + ((a (Sum.inr 0) : ℝ) : ℂ) * Complex.I :=
    funext fun a => Complex.ext (by simp [vecToC]) (by simp [vecToC])
  rw [e]
  have h1 : Continuous fun a : CauchyRiemannIndex.Vec 1 => a (Sum.inl 0) :=
    (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).continuous
  have h2 : Continuous fun a : CauchyRiemannIndex.Vec 1 => a (Sum.inr 0) :=
    (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).continuous
  exact (Complex.continuous_ofReal.comp h1).add
    ((Complex.continuous_ofReal.comp h2).mul continuous_const)

end FiniteEnergyPlane

/-!
# N (normal frame), layer D: the exponential decay of `e^{-2(Ts+d)} N(cyl) ν - M(t) ν`

For `s ≥ 0` the difference is `Φ(t, v(s, t))` with `Φ` smooth, `1`-periodic, `Φ(φ, 0) = 0`, and
`v` the decaying data of the end (`fasV`), so it decays in `C^∞` at half the rate.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff Real

/-! ### Two facts on `ExpDecayCInfty` -/

lemma nf_expDecay_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : ℝ × ℝ → F}
    {b s₀ : ℝ} (hf : ExpDecayCInfty f b) (h : ∀ s > s₀, ∀ t, g (s, t) = f (s, t)) :
    ExpDecayCInfty g b := by
  have hO : IsOpen (Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hev : ∀ p ∈ Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ), g =ᶠ[𝓝 p] f := by
    intro p hp
    filter_upwards [hO.mem_nhds hp] with q hq
    obtain ⟨s, t⟩ := q
    exact h s hq.1 t
  obtain ⟨⟨s₁, hs₁⟩, hb⟩ := hf
  refine ⟨⟨max s₀ s₁, ?_⟩, fun m => ?_⟩
  · refine (hs₁.mono ?_).congr fun p hp => ?_
    · exact Set.prod_mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
    · obtain ⟨s, t⟩ := p
      exact h s (lt_of_le_of_lt (le_max_left _ _) hp.1) t
  · obtain ⟨C, s₂, hC⟩ := hb m
    refine ⟨C, max s₂ (s₀ + 1), fun s hs t => ?_⟩
    have hs0 : s₀ < s := by linarith [le_max_right s₂ (s₀ + 1)]
    rw [((hev (s, t) ⟨hs0, Set.mem_univ _⟩).iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
    exact hC s (le_trans (le_max_left _ _) hs) t

lemma nf_expDecay_mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    {b b' : ℝ} (hf : ExpDecayCInfty f b) (hbb : b' ≤ b) : ExpDecayCInfty f b' := by
  refine ⟨hf.1, fun m => ?_⟩
  obtain ⟨C, s₁, hC⟩ := hf.2 m
  refine ⟨|C|, max s₁ 0, fun s hs t => ?_⟩
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
  calc _ ≤ C * Real.exp (-(b * s)) := hC s (le_trans (le_max_left _ _) hs) t
    _ ≤ |C| * Real.exp (-(b * s)) := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (-(b' * s)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
      exact Real.exp_le_exp.2 (by nlinarith)

/-! ### The cylinder -/

lemma nf_cyl_contDiff : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  have hfun : (fun q : ℝ × ℝ => cylInf q.1 q.2) =
      fun q : ℝ × ℝ => Complex.exp ((2 * π : ℝ) • ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) := by
    funext q
    exact fas_cyl_eq q.1 q.2
  rw [hfun]
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (q.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (q.2 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_snd
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp ((h1.add (h2.mul contDiff_const)).const_smul _)

/-- `σ` as a function of `(A, B)`. -/
def nfSigOf (c : ℂ × ℂ) : ℂ × ℂ := (-(starRingEnd ℂ c.2), starRingEnd ℂ c.1)

lemma nfSigOf_smul (w : ℂ) (c : ℂ × ℂ) : nfSigOf (w • c) = starRingEnd ℂ w • nfSigOf c := by
  simp [nfSigOf, Prod.smul_fst, Prod.smul_snd, map_mul]

section decay
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

/-- The limit map: `Φ(φ, (α, w))`. -/
noncomputable def nfPhi (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (c₀ θ ν : ℂ)
    (q : ℝ × (ℝ × FasE)) : V 1 :=
  Real.exp (2 * q.2.1) • nfF H J (proj H (fX P (P.T * q.1, q.2.2)))
      ((ν * (c₀ / (2 * π) * nfE 1 q.1)) •
        nfSigOf (nfC H J (proj H (fX P (P.T * q.1, q.2.2))) (fC1 P (P.T * q.1, q.2.2)))) -
    nfM H J P θ q.1 (cToVec ν)

include hH hJ in
lemma nfPhi_zero (P : ReebOrbit H) (c₀ θ ν : ℂ) (hθ : θ = c₀ / (2 * π) * P.T) (φ : ℝ) :
    nfPhi H J P c₀ θ ν (φ, 0) = 0 := by
  have hS := P.mem (P.T * φ)
  have hp : proj H (P.x (P.T * φ)) = P.x (P.T * φ) := N1.proj_of_mem H hH hS
  have hcol : fC1 P (P.T * φ, 0) = nfF H J (P.x (P.T * φ)) ((P.T : ℂ), 0) := by
    rw [fC1_zero, nfF]
    simp [nf_cToVec_zero, smul_smul, mul_comm]
  simp only [nfPhi, Prod.snd_zero, Prod.fst_zero, mul_zero, Real.exp_zero, one_smul]
  rw [fX_zero, hp, hcol, nfC_nfF hH hJ hS, nfM_apply, nf_vecToC_cToVec, sub_eq_zero]
  have hk : (ν * (c₀ / (2 * π) * nfE 1 φ)) • nfSigOf ((P.T : ℂ), (0 : ℂ)) = (0, nfE θ φ * ν) := by
    simp only [nfSigOf, map_zero, neg_zero, Complex.conj_ofReal]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.smul_snd, smul_eq_mul]; rw [hθ, nfE, nfE]; ring
  rw [hk, nfF]
  simp

include hH hJ in
lemma nfPhi_per (P : ReebOrbit H) (c₀ θ ν : ℂ) (hθ : ‖θ‖ = 1) (φ : ℝ) (w : ℝ × FasE) :
    nfPhi H J P c₀ θ ν (φ + 1, w) = nfPhi H J P c₀ θ ν (φ, w) := by
  have hM := (nf_frame_rot hH hJ P θ hθ).1.2.1 φ
  simp only [nfPhi, mul_add, mul_one, fX_per, fC1_per, nfE_per, hM]

include hH hJ in
lemma nfPhi_contDiffOn (P : ReebOrbit H) (c₀ θ ν : ℂ) (hθ : ‖θ‖ = 1) {ρ : ℝ}
    (htube : ∀ (φ : ℝ) (v : FasE), ‖v‖ < ρ → (φ, v) ∈ fU J P) :
    ContDiffOn ℝ ∞ (nfPhi H J P c₀ θ ν) (Set.univ ×ˢ ball (0 : ℝ × FasE) ρ) := by
  intro q hq
  have hq2 : ‖q.2‖ < ρ := by simpa using hq.2
  have hw : ‖q.2.2‖ < ρ := lt_of_le_of_lt (norm_snd_le q.2) hq2
  have hO := (htube (P.T * q.1) q.2.2 hw).1
  have hne : fX P (P.T * q.1, q.2.2) ≠ 0 := by
    intro h; have := hO.1; rw [h] at this; simp at this
  have hm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × FasE) => ((P.T * q.1, q.2.2) : ℝ × FasE)) :=
    (contDiff_const.mul contDiff_fst).prodMk contDiff_snd.snd
  have hfX : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × FasE) => fX P (P.T * q.1, q.2.2)) q :=
    ((fX_contDiff hH P).comp hm).contDiffAt
  obtain ⟨-, hpr, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hX : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × FasE) => proj H (fX P (P.T * q.1, q.2.2))) q :=
    ContDiffAt.comp (g := proj H) q
      (hpr.contDiffAt ((isOpen_ne : IsOpen {y : V 1 | y ≠ 0}).mem_nhds hne)) hfX
  have hXS : proj H (fX P (P.T * q.1, q.2.2)) ∈ energySurface H := (ka_scale_spec H hH _ hne).2
  have hcol : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × FasE) => fC1 P (P.T * q.1, q.2.2)) q :=
    ((fC1_contDiff hH P).comp hm).contDiffAt
  have hAB := nfC_contDiffAt hH hJ hX hXS hcol
  have hσ : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × FasE) => nfSigOf (nfC H J
      (proj H (fX P (P.T * q.1, q.2.2))) (fC1 P (P.T * q.1, q.2.2)))) q :=
    (nf_conj_contDiffAt hAB.snd).neg.prodMk (nf_conj_contDiffAt hAB.fst)
  have hk : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × FasE) => ν * (c₀ / (2 * π) * nfE 1 q.1)) q :=
    (contDiff_const.mul (contDiff_const.mul ((nfE_contDiff 1).comp contDiff_fst))).contDiffAt
  have hF := nfF_contDiffAt hH hJ hX hXS (hk.smul hσ)
  have he : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × FasE) => Real.exp (2 * q.2.1)) q :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd.fst)).contDiffAt
  have hM : ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × FasE) => nfM H J P θ q.1 (cToVec ν)) q :=
    ((((nf_frame_rot hH hJ P θ hθ).1.1).clm_apply contDiff_const).comp contDiff_fst).contDiffAt
  exact ((he.smul hF).sub hM).contDiffWithinAt

variable (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
  (hhol : ∀ z, fderiv ℝ u z 1 + Jtilde H J (u z) (fderiv ℝ u z Complex.I) = 0)

include hH hJ hu hu0 hhol in
/-- On `s ≥ 0` the decaying quantity is `Φ` of the data. -/
lemma nf_ident (P : ReebOrbit H) (c₀ θ ν : ℂ) (ρ₀ d : ℝ) (s t : ℝ) (hs : 0 ≤ s) :
    Real.exp (-(2 * (P.T * s + d))) • nfN H J u c₀ ρ₀ (cylInf s t) ν - nfM H J P θ t (cToVec ν) =
      nfPhi H J P c₀ θ ν (1 * t + 0, (aCoord H (u (cylInf s t)) - P.T * s - d,
        fasV H P d (fun p : ℝ × ℝ => u (cylInf p.1 p.2)) (s, t))) := by
  set y : ℝ × ℝ → V 1 := fun p => u (cylInf p.1 p.2) with hydef
  have hy : ContDiff ℝ ∞ y := hu.comp nf_cyl_contDiff
  have hy0 : ∀ q, y q ≠ 0 := fun q => hu0 _
  obtain ⟨hX, -, -, -, -⟩ := fasV_ident hH hJ y hy hy0 P d (s, t)
  have hcol : fC1 P (P.T * t, fasV H P d y (s, t)) = gCol H y (1, 0) (s, t) := by
    obtain ⟨h1, h2, -, h4, -⟩ := fasV_ident hH hJ y hy hy0 P d (s, t)
    simp only [fC1, gCol]
    rw [h1, h2, h4]
  rw [gCol_eq hH hJ y hy hy0] at hcol
  obtain ⟨L, hL, hL1, -⟩ := fas_cyl_hasFDerivAt (s, t)
  have hdy : fderiv ℝ y (s, t) (1, 0) = fderiv ℝ u (cylInf s t) ((2 * π : ℝ) • cylInf s t) := by
    have h := (HasFDerivAt.comp (s, t) ((hu.differentiable (by simp)) _).hasFDerivAt hL).fderiv
    have h2 : fderiv ℝ y (s, t) = _ := h
    rw [h2, ContinuousLinearMap.comp_apply, hL1]
  rw [hdy] at hcol
  set z := cylInf s t with hz
  have hS := nf_mem hH u hu0 z
  have hyz : y (s, t) = u z := rfl
  rw [hyz, nf_Du hH hJ u hu hu0 hhol] at hcol
  have hXz : proj H (fX P (P.T * t, fasV H P d y (s, t))) = proj H (u z) := by
    rw [hX, hyz, N1.proj_of_mem H hH hS]
  have hρ : nfRho ρ₀ z = ‖z‖ := by
    apply nfRho_of_one_le
    rw [hz, fas_norm_cylInf]
    exact Real.one_le_exp (by positivity)
  set E : ℂ := Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) with hE
  have hEE : E * starRingEnd ℂ E = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hE, Complex.norm_exp_ofReal_mul_I]; simp
  have hc : cylInf s t = (Real.exp (2 * π * s) : ℂ) * E := rfl
  have hpi : (2 * (π : ℂ)) ≠ 0 := by
    have : (2 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have key : c₀ / (2 * (π : ℂ)) * (2 * (π : ℂ)) = c₀ := div_mul_cancel₀ _ hpi
  have hscal : ν * (c₀ / (2 * π) * nfE 1 t) * starRingEnd ℂ ((2 * π : ℝ) • z) =
      ν * (c₀ * (nfRho ρ₀ z : ℂ)) := by
    rw [hρ, hz, fas_norm_cylInf, hc, nfE, ← hE]
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, one_mul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, map_ofNat]
    linear_combination (ν * (Real.exp (2 * π * s) : ℂ) * E * starRingEnd ℂ E) * key +
      (ν * c₀ * (Real.exp (2 * π * s) : ℂ)) * hEE
  have hσ : nfSig H J u z = nfSigOf (nfAB H J u z) := rfl
  have hA : nfF H J (proj H (u z)) ((ν * (c₀ / (2 * π) * nfE 1 t)) •
      (starRingEnd ℂ ((2 * π : ℝ) • z) • nfSigOf (nfAB H J u z))) =
      nfF H J (proj H (u z)) ((ν * (c₀ * (nfRho ρ₀ z : ℂ))) • nfSig H J u z) := by
    rw [smul_smul, hscal, hσ]
  simp only [nfPhi, one_mul, add_zero]
  rw [hXz, hcol, nfC_nfF hH hJ hS, nfSigOf_smul, hA, nfN_apply hH hJ u hu0, smul_smul,
    ← Real.exp_add]
  congr 2
  ring

end decay

end FiniteEnergyPlane

/-!
# N `exists_normalFrame_of_isFastPlane` (80d14cc7): the glue

`N = nfN` (layer P), `M = nfM` (layer M) along the shifted orbit `P'`, decay from layer D.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff Real

section
variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J)

include hH hJ in
/-- The decay of `e^{-2(Ts+d)} N(cyl) ν - M(t) ν`. -/
theorem nf_decay (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : ∀ z, fderiv ℝ u z 1 + Jtilde H J (u z) (fderiv ℝ u z Complex.I) = 0)
    (P : ReebOrbit H) (d b : ℝ) (hb : 0 < b)
    (h1 : ExpDecayCInfty (fun p : ℝ × ℝ => aCoord H (u (cylInf p.1 p.2)) - P.T * p.1 - d) b)
    (h2 : ExpDecayCInfty (fun p : ℝ × ℝ => proj H (u (cylInf p.1 p.2)) - P.x (P.T * p.2)) b)
    (c₀ θ : ℂ) (hθ : θ = c₀ / (2 * π) * P.T) (hθ1 : ‖θ‖ = 1) (ρ₀ : ℝ) (ν : ℂ) :
    ExpDecayCInfty (fun p : ℝ × ℝ => Real.exp (-(2 * (P.T * p.1 + d))) •
      nfN H J u c₀ ρ₀ (cylInf p.1 p.2) ν - nfM H J P θ p.2 (cToVec ν)) (b / 2) := by
  set y : ℝ × ℝ → V 1 := fun p => u (cylInf p.1 p.2) with hydef
  obtain ⟨ρ, hρ, htube⟩ := fU_tube hH hJ P
  set v : ℝ × ℝ → ℝ × FasE := fun p => (aCoord H (y p) - P.T * p.1 - d, fasV H P d y p) with hv
  have hδ1 := fas_tendsto_of_exp hb h1
  have hδ2 := fas_tendsto_of_exp hb h2
  have hvt : TendstoZeroCInfty v :=
    tendstoZeroCInfty_prodMk hδ1 (tendstoZeroCInfty_prodMk hδ2
      (tendstoZeroCInfty_prodMk (tendstoZeroCInfty_fderiv hδ2) (tendstoZeroCInfty_fderiv hδ1)))
  obtain ⟨s₂, hs₂⟩ := hvt.2 0 (ρ / 2) (half_pos hρ)
  have hvsmall : ∀ q : ℝ × ℝ, s₂ ≤ q.1 → ‖v q‖ ≤ ρ / 2 := by
    rintro ⟨s, t⟩ hq
    simpa [norm_iteratedFDeriv_zero] using hs₂ s hq t
  have hvdec : ∃ (Cv sv : ℝ), ∀ s ≥ sv, ∀ t : ℝ, ‖v (s, t)‖ ≤ Cv * Real.exp (-(b * s)) := by
    obtain ⟨C0, s0, hC0⟩ := h2.2 0
    obtain ⟨C1, s1, hC1⟩ := h2.2 1
    obtain ⟨C2, s3, hC2⟩ := h1.2 1
    obtain ⟨C3, s4, hC3⟩ := h1.2 0
    refine ⟨|C0| + |C1| + |C2| + |C3|, max (max s0 s1) (max s3 s4), fun s hs t => ?_⟩
    have a0 := hC0 s (by linarith [le_max_left s0 s1, le_max_left (max s0 s1) (max s3 s4)]) t
    have a1 := hC1 s (by linarith [le_max_right s0 s1, le_max_left (max s0 s1) (max s3 s4)]) t
    have a2 := hC2 s (by linarith [le_max_left s3 s4, le_max_right (max s0 s1) (max s3 s4)]) t
    have a3 := hC3 s (by linarith [le_max_right s3 s4, le_max_right (max s0 s1) (max s3 s4)]) t
    rw [norm_iteratedFDeriv_zero] at a0 a3
    rw [norm_iteratedFDeriv_one] at a1 a2
    have hE := Real.exp_pos (-(b * s))
    have b0 := mul_le_mul_of_nonneg_right (le_abs_self C0) hE.le
    have b1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hE.le
    have b2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hE.le
    have b3 := mul_le_mul_of_nonneg_right (le_abs_self C3) hE.le
    have p0 := mul_nonneg (abs_nonneg C0) hE.le
    have p1 := mul_nonneg (abs_nonneg C1) hE.le
    have p2 := mul_nonneg (abs_nonneg C2) hE.le
    have p3 := mul_nonneg (abs_nonneg C3) hE.le
    have hexp : (|C0| + |C1| + |C2| + |C3|) * Real.exp (-(b * s)) =
        |C0| * Real.exp (-(b * s)) + |C1| * Real.exp (-(b * s)) + |C2| * Real.exp (-(b * s)) +
          |C3| * Real.exp (-(b * s)) := by ring
    rw [hexp]
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩⟩
    · exact a3.trans (by linarith)
    · exact a0.trans (by linarith)
    · exact a1.trans (by linarith)
    · exact a2.trans (by linarith)
  obtain ⟨Cv, sv, hCv⟩ := hvdec
  set Φ := nfPhi H J P c₀ θ ν with hΦ
  have hΦc := nfPhi_contDiffOn hH hJ P c₀ θ ν hθ1 htube
  have hΦp : ∀ (φ : ℝ) (w : ℝ × FasE), ‖w‖ < ρ → Φ (φ + 1, w) = Φ (φ, w) :=
    fun φ w _ => nfPhi_per hH hJ P c₀ θ ν hθ1 φ w
  have hΦ0 : ∀ φ : ℝ, Φ (φ, 0) = 0 := nfPhi_zero hH hJ P c₀ θ ν hθ
  have hC := tendstoZeroCInfty_comp_periodic Φ 1 ρ 1 0 one_pos hρ hΦc hΦp hΦ0 v hvt
  obtain ⟨L, hL0, hL⟩ := exists_norm_le_mul_norm_of_periodic Φ 1 ρ one_pos hρ
    (hΦc.of_le (by simp)) hΦp hΦ0
  have hE := expDecayCInfty_of_tendstoZeroCInfty _ hC b (L * Cv) (max s₂ sv) (by
    intro s hs t
    show ‖Φ (1 * t + 0, v (s, t))‖ ≤ _
    have h3 := hL (1 * t + 0) (v (s, t)) (hvsmall (s, t) (le_trans (le_max_left _ _) hs))
    have h4 := hCv s (le_trans (le_max_right _ _) hs) t
    calc _ ≤ L * ‖v (s, t)‖ := h3
      _ ≤ L * (Cv * Real.exp (-(b * s))) := mul_le_mul_of_nonneg_left h4 hL0
      _ = _ := by ring) (b / 2) (by linarith)
  refine nf_expDecay_congr hE (s₀ := 0) fun s hs t => ?_
  exact nf_ident hH hJ u hu hu0 hhol P c₀ θ ν ρ₀ d s t hs.le

include hH hJ in
lemma nf_xi_zero {x : V 1} (hx : x ∈ energySurface H) : xiCoordC H x 0 = 0 := by
  have := r26_coord hH hJ hx (0 : CauchyRiemannIndex.Vec 1)
  rw [map_zero] at this
  rw [this]
  simp

include hH hJ in
/-- The basic data of a fast plane. -/
lemma nf_prelim (u : ℂ → V 1) (hfast : IsFastPlane H J u) :
    ContDiff ℝ ∞ u ∧ (∀ z, u z ≠ 0) ∧
      (∀ z, fderiv ℝ u z 1 + Jtilde H J (u z) (fderiv ℝ u z Complex.I) = 0) ∧
      ∀ z, piXi H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z 1) ≠ 0 := by
  have hfe := hfast.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfe.2.1 z (Set.mem_univ z)
  refine ⟨contDiffOn_univ.1 hfe.1, hu0, fun z => (hfe.2.2.1 z (Set.mem_univ z)).2, fun z h0 => ?_⟩
  apply piDs_ne_zero_of_isFastPlane H hH J hJ u hfast z
  show xiCoordC H (proj H (u z)) (piXi H (proj H (u z)) (fderiv ℝ (fun z => proj H (u z)) z 1)) = 0
  rw [h0]
  exact nf_xi_zero hH hJ (ka_scale_spec H hH (u z) (hu0 z)).2

end

/-- A unitary normal frame along a fast plane (statement of `exists_normalFrame_of_isFastPlane`). -/
theorem exists_normalFrame_of_isFastPlane_glue (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ (d c b : ℝ) (P' : ReebOrbit H) (N : ℂ → ℂ →L[ℝ] V 1)
      (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1),
      0 < b ∧ P'.T = P.T ∧ (∀ τ : ℝ, P'.x τ = P.x (τ + c)) ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P'.x (P.T * p.2)) b ∧
      ContDiff ℝ ∞ N ∧
      (∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν)) ∧
      (∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0) ∧
      (∃ τ : ℂ, fderiv ℝ u 0 τ + N 0 1 = u 0) ∧
      IsUnitaryXiFrame J P' M ∧
      (∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P' (fun t => M t (ζ t)) (k + 1) ↔
            HasLoopWind (fun t => vecToC (ζ t)) k)) ∧
      ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
        Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b := by
  obtain ⟨hsm, hu0, hhol, hp⟩ := nf_prelim hH hJ u hu
  obtain ⟨b, hb, d, c, he1, he2⟩ :=
    exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd H hH J hJ u hu.1 P huP
  set P' : ReebOrbit H :=
    { x := fun τ => P.x (τ + c)
      T := P.T
      T_pos := P.T_pos
      mem := fun τ => P.mem (τ + c)
      hasDerivAt := fun τ => HasDerivAt.comp_add_const τ c (P.hasDerivAt (τ + c))
      periodic := fun τ => by
        show P.x (τ + P.T + c) = P.x (τ + c)
        rw [add_right_comm]; exact P.periodic (τ + c) } with hP'
  have h1 : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b := by
    have e : (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) =
        fun p : ℝ × ℝ => endA H u cylInf p - 1 * P.T * p.1 - d := by
      funext p; simp only [one_mul]
    rw [e]; exact he1
  have h2 : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P'.x (P.T * p.2)) b := by
    have e : (fun p : ℝ × ℝ => endW H u cylInf p - P'.x (P.T * p.2)) =
        fun p : ℝ × ℝ => endW H u cylInf p - P.x (1 * P.T * p.2 + c) := by
      funext p; simp only [one_mul]; rfl
    rw [e]; exact he2
  have hT := P.T_pos
  -- the constants
  have hB := nfAB_snd_ne hH hJ u hsm hu0 hp 0
  set A₀ := (nfAB H J u 0).1 with hA₀
  set B₀ := (nfAB H J u 0).2 with hB₀
  set D₀ := A₀ * starRingEnd ℂ A₀ + B₀ * starRingEnd ℂ B₀ with hD₀
  have hD0 : D₀ ≠ 0 := nf_D_ne A₀ B₀ hB
  set κ₀ : ℂ := -B₀ / (2 * D₀) with hκ₀
  have hκ0 : κ₀ ≠ 0 := div_ne_zero (neg_ne_zero.2 hB) (mul_ne_zero two_ne_zero hD0)
  have hκn : 0 < ‖κ₀‖ := norm_pos_iff.2 hκ0
  set ρ₀ : ℝ := ‖κ₀‖ * P.T / (2 * π) with hρ₀def
  have hρ₀ : 0 < ρ₀ := by positivity
  set c₀ : ℂ := κ₀ / (ρ₀ : ℂ) with hc₀def
  have hρc : (ρ₀ : ℂ) ≠ 0 := by exact_mod_cast hρ₀.ne'
  have hc₀ : c₀ ≠ 0 := div_ne_zero hκ0 hρc
  have hk : c₀ * (ρ₀ : ℂ) = κ₀ := div_mul_cancel₀ _ hρc
  set θ : ℂ := c₀ / (2 * π) * P.T with hθdef
  have hθ1 : ‖θ‖ = 1 := by
    rw [hθdef, hc₀def, norm_mul, norm_div, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hρ₀, abs_of_pos hT, hρ₀def]
    have h2 : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2]
    field_simp
  obtain ⟨hMU, hMW⟩ := nf_frame_rot hH hJ P' θ hθ1
  refine ⟨d, c, b / 2, P', nfN H J u c₀ ρ₀, nfM H J P' θ, by linarith, rfl, fun τ => rfl,
    nf_expDecay_mono h1 (by linarith), nf_expDecay_mono h2 (by linarith),
    nfN_contDiff hH hJ u hsm hu0 c₀ hρ₀, nfN_I hH hJ u hu0 c₀ ρ₀,
    nfN_compl hH hJ u hsm hu0 hhol hp hc₀ hρ₀, nfN_tau hH hJ u hsm hu0 hhol hp hρ₀ hk,
    hMU, hMW, fun ν => ?_⟩
  have h1' : ExpDecayCInfty (fun p : ℝ × ℝ => aCoord H (u (cylInf p.1 p.2)) - P'.T * p.1 - d) b :=
    h1
  have h2' : ExpDecayCInfty (fun p : ℝ × ℝ => proj H (u (cylInf p.1 p.2)) - P'.x (P'.T * p.2)) b :=
    h2
  exact nf_decay hH hJ u hsm hu0 hhol P' d b hb h1' h2' c₀ θ rfl hθ1 ρ₀ ν

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ (d c b : ℝ) (P' : ReebOrbit H) (N : ℂ → ℂ →L[ℝ] V 1)
      (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1),
      0 < b ∧ P'.T = P.T ∧ (∀ τ : ℝ, P'.x τ = P.x (τ + c)) ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P'.x (P.T * p.2)) b ∧
      ContDiff ℝ ∞ N ∧
      (∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν)) ∧
      (∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0) ∧
      (∃ τ : ℂ, fderiv ℝ u 0 τ + N 0 1 = u 0) ∧
      IsUnitaryXiFrame J P' M ∧
      (∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P' (fun t => M t (ζ t)) (k + 1) ↔
            HasLoopWind (fun t => vecToC (ζ t)) k)) ∧
      ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
        Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b :=
  exists_normalFrame_of_isFastPlane_glue H hH J hJ P u hu huP
