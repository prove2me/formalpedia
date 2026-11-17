-- Prove2me | solution 1 for FiniteEnergyPlane.exists_mul_le_tubeMap_of_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T23:48:49.341479+00:00
-- url     : https://prove2.me/submissions/50d8095d-2ccd-4d70-9f82-2359464af07e

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_triangular_iff
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_isInXi_linearizedReeb_deriv
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_sub_model
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_fderiv_sub_model
import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_comp_sub
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_aCoord_proj_comp_iff
import Theorems.Thm_FiniteEnergyPlane_exists_ball_tubeMap_ne_zero_injective
import Theorems.Thm_FiniteEnergyPlane_exists_mul_le_norm_sub_of_cylBounds
import Theorems.Thm_FiniteEnergyPlane_exists_cylindrical_bounds_of_expDecayCInftyTube

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

/-!
# S model, layer A (local): the model map `Y(ζ, w) = e^{2T Re ζ} (x(T Im ζ) + M(Im ζ)(cToVec w))`
and its derivative.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace SM

/-- `cToVec` as a continuous real-linear map. -/
def cToVecL : ℂ →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := cToVec
      map_add' := fun a b => by ext i; rcases i with i | i <;> simp [cToVec]
      map_smul' := fun c a => by ext i; rcases i with i | i <;> simp [cToVec] }

@[simp] lemma cToVecL_apply (z : ℂ) : cToVecL z = cToVec z := rfl

lemma cToVec_vecToC (a : CauchyRiemannIndex.Vec 1) : cToVec (vecToC a) = a := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [cToVec, vecToC]

lemma vecToC_cToVec (z : ℂ) : vecToC (cToVec z) = z := by
  apply Complex.ext <;> simp [cToVec, vecToC]

lemma cToVec_I_mul (z : ℂ) :
    cToVec (Complex.I * z) = Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (cToVec z) := by
  have h : vecToC (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (cToVec z)) =
      Complex.I * vecToC (cToVec z) := by
    apply Complex.ext <;>
      simp [vecToC, CauchyRiemannIndex.J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec,
        dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]
  rw [vecToC_cToVec] at h
  rw [← h, cToVec_vecToC]

variable {H : V 1 → ℝ} (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)

/-- The model `m(t, w) = x(T t) + M(t)(cToVec w)`. -/
def mm (t : ℝ) (w : ℂ) : V 1 := P.x (P.T * t) + M t (cToVecL w)

/-- The model map `Y(ζ, w) = e^{2T Re ζ} m(Im ζ, w)`. -/
def Y (q : ℂ × ℂ) : V 1 := Real.exp (2 * P.T * q.1.re) • mm P M q.1.im q.2

/-- The explicit derivative of `Y` at `(it, w)`. -/
def Lx (H : V 1 → ℝ) (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (t : ℝ) (w : ℂ) : ℂ × ℂ →L[ℝ] V 1 :=
  ((2 * P.T) • (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ))).smulRight (mm P M t w) +
    (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).smulRight
      (P.T • reeb H (P.x (P.T * t)) + deriv M t (cToVecL w)) +
    (M t).comp (cToVecL.comp (ContinuousLinearMap.snd ℝ ℂ ℂ))

lemma Lx_apply (t : ℝ) (w : ℂ) (h : ℂ × ℂ) :
    Lx H P M t w h = (2 * P.T * h.1.re) • mm P M t w +
      h.1.im • (P.T • reeb H (P.x (P.T * t)) + deriv M t (cToVecL w)) + M t (cToVec h.2) := by
  simp [Lx, smul_eq_mul, mul_assoc]

variable (hH : IsStrictlyStarShapedLevel H)

include hH in
lemma contDiff_x : ContDiff ℝ ∞ (fun t : ℝ => P.x (P.T * t)) :=
  (ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_id)

include hH in
lemma hasDerivAt_x (t : ℝ) :
    HasDerivAt (fun s : ℝ => P.x (P.T * s)) (P.T • reeb H (P.x (P.T * t))) t := by
  have h0 : HasDerivAt (fun s => P.T * s) P.T t := by
    simpa using (hasDerivAt_id t).const_mul P.T
  exact (P.hasDerivAt (P.T * t)).scomp t h0

variable (hMc : ContDiff ℝ ∞ M)

include hMc in
lemma hasDerivAt_M (t : ℝ) : HasDerivAt M (deriv M t) t :=
  ((hMc.differentiable (by simp)) t).hasDerivAt

include hH hMc in
lemma contDiff_Y : ContDiff ℝ ∞ (Y P M) := by
  unfold Y mm
  have hx := contDiff_x P hH
  have him : ContDiff ℝ ∞ (fun q : ℂ × ℂ => q.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have hre : ContDiff ℝ ∞ (fun q : ℂ × ℂ => q.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst
  refine (Real.contDiff_exp.comp (contDiff_const.mul hre)).smul ((hx.comp him).add ?_)
  exact (hMc.comp him).clm_apply (cToVecL.contDiff.comp contDiff_snd)

include hH hMc in
/-- The derivative of `Y` at a general point. -/
lemma hasFDerivAt_Y_gen (q : ℂ × ℂ) :
    HasFDerivAt (Y P M) (Real.exp (2 * P.T * q.1.re) • Lx H P M q.1.im q.2) q := by
  have him : HasFDerivAt (fun q : ℂ × ℂ => q.1.im)
      (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) q :=
    (Complex.imCLM.hasFDerivAt).comp q (hasFDerivAt_fst)
  have hre : HasFDerivAt (fun q : ℂ × ℂ => q.1.re)
      (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) q :=
    (Complex.reCLM.hasFDerivAt).comp q (hasFDerivAt_fst)
  have hx : HasFDerivAt (fun q : ℂ × ℂ => P.x (P.T * q.1.im))
      ((Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).smulRight
        (P.T • reeb H (P.x (P.T * q.1.im)))) q := by
    have h0 := (hasDerivAt_x P hH q.1.im).hasFDerivAt
    have h1 := h0.comp q him
    exact h1.congr_fderiv (ContinuousLinearMap.ext fun h => by simp)
  have hM : HasFDerivAt (fun q : ℂ × ℂ => M q.1.im)
      ((Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).smulRight (deriv M q.1.im)) q :=
    (((hasDerivAt_M M hMc q.1.im).hasFDerivAt).comp q him).congr_fderiv
      (ContinuousLinearMap.ext fun h => by simp)
  have hc : HasFDerivAt (fun q : ℂ × ℂ => cToVecL q.2)
      (cToVecL.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)) q :=
    cToVecL.hasFDerivAt.comp q hasFDerivAt_snd
  have hm := hx.add (hM.clm_apply hc)
  have he : HasFDerivAt (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re))
      (Real.exp (2 * P.T * q.1.re) • ((2 * P.T) • (Complex.reCLM.comp
        (ContinuousLinearMap.fst ℝ ℂ ℂ)))) q :=
    (hre.const_mul (2 * P.T)).exp
  have hY := he.smul hm
  refine hY.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  rw [ContinuousLinearMap.smul_apply, Lx_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Complex.reCLM_apply,
    Complex.imCLM_apply, ContinuousLinearMap.flip_apply, mm, smul_eq_mul, Pi.add_apply,
    cToVecL_apply]
  module

include hH hMc in
lemma hasFDerivAt_Y (t : ℝ) (w : ℂ) :
    HasFDerivAt (Y P M) (Lx H P M t w) ((t : ℂ) * Complex.I, w) := by
  have h := hasFDerivAt_Y_gen P M hH hMc ((t : ℂ) * Complex.I, w)
  simpa using h

end SM

end

end FiniteEnergyPlane

/-!
# S model, layer B (local): invertibility of the model derivative near `w = 0`, a uniform
width, and the limit structure `Jinf = L⁻¹ ∘ J̃(m) ∘ L`.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace SM

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
  {M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hM : IsUnitaryXiFrame J P M)

lemma vecToC_J₀ (a : CauchyRiemannIndex.Vec 1) :
    vecToC (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) = Complex.I * vecToC a := by
  apply Complex.ext <;>
    simp [vecToC, CauchyRiemannIndex.J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec,
      dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]

lemma finrank_CC : Module.finrank ℝ (ℂ × ℂ) = 4 := by
  rw [Module.finrank_prod, Complex.finrank_real_complex]

lemma finrank_V1 : Module.finrank ℝ (V 1) = 4 := by
  simp [V]

/-- An injective map `ℂ × ℂ → V 1` is an isomorphism. -/
lemma exists_equiv_of_injective (L : ℂ × ℂ →L[ℝ] V 1) (hL : Function.Injective L) :
    ∃ e : (ℂ × ℂ) ≃L[ℝ] V 1, (e : ℂ × ℂ →L[ℝ] V 1) = L := by
  let e₀ := LinearMap.linearEquivOfInjective L.toLinearMap hL (by rw [finrank_CC, finrank_V1])
  refine ⟨e₀.toContinuousLinearEquiv, ?_⟩
  ext h <;> rfl

include hM in
lemma M_injective (t : ℝ) : Function.Injective (M t) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := (hM.2.2 t).2.2.2 a (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a)
  rw [ha] at h
  have h0 : omega0 (0 : V 1) (M t (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a)) = 0 := by
    simp [omega0, dot, j0]
  rw [h0, eq_comm, real_inner_self_eq_norm_sq] at h
  have hJa : Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    exact norm_eq_zero.1 this
  have hc := congrArg vecToC hJa
  rw [vecToC_J₀] at hc
  have : vecToC a = 0 := by
    have h0' : vecToC (0 : CauchyRiemannIndex.Vec 1) = 0 := by
      apply Complex.ext <;> simp [vecToC]
    rw [h0'] at hc
    simpa using hc
  rw [← cToVec_vecToC a, this]
  ext i; rcases i with i | i <;> simp [cToVec]


include hH hM in
/-- The model derivative along `w = 0` is injective. -/
lemma Lx_zero_injective (t : ℝ) : Function.Injective (Lx H P M t 0) := by
  have hT := P.T_pos
  set x := P.x (P.T * t) with hxdef
  have hx : x ∈ energySurface H := P.mem _
  have hD : 0 < fderiv ℝ H x x := hH.2.2 _ hx
  obtain ⟨-, hR1, hRH, -⟩ := ka_reeb_spec H hH _ hx
  rw [injective_iff_map_eq_zero]
  rintro ⟨ζ, μ⟩ hv
  rw [Lx_apply] at hv
  simp only [mm, map_zero, add_zero, ← hxdef, cToVecL_apply] at hv
  have hMξ := (hM.2.2 t).1 (cToVec μ)
  rw [← hxdef] at hMξ
  have h1 := congrArg (fderiv ℝ H x) hv
  simp only [map_add, map_smul, hRH, hMξ.2, map_zero, smul_zero, add_zero, smul_eq_mul] at h1
  have hre : ζ.re = 0 := by
    have : ζ.re * (2 * P.T * fderiv ℝ H x x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (by positivity)
  have h2 := congrArg (liouvilleCLM x) hv
  simp only [map_add, map_smul, ka_liouvilleCLM_apply, hR1, hMξ.1, map_zero, smul_zero,
    add_zero, smul_eq_mul, mul_one] at h2
  have hll : liouville x x = 0 := by
    unfold liouville; rw [ka_om_self]; simp
  rw [hll] at h2
  have him : ζ.im = 0 := by
    have h2' : ζ.im * P.T = 0 := by linarith
    rcases mul_eq_zero.1 h2' with h | h
    · exact h
    · exact absurd h hT.ne'
  rw [hre, him, mul_zero, zero_smul, zero_smul, zero_add, zero_add] at hv
  have hμ : cToVec μ = 0 := (injective_iff_map_eq_zero _).1 (M_injective P hM t) _ hv
  have hμ' : μ = 0 := by
    rw [← vecToC_cToVec μ, hμ]
    apply Complex.ext <;> simp [vecToC]
  simp [Prod.ext_iff, Complex.ext_iff, hre, him, hμ']


section tube
variable (M) (hMc : ContDiff ℝ ∞ M)

include hH hMc in
lemma Lx_eq_fderiv (t : ℝ) (w : ℂ) :
    fderiv ℝ (Y P M) ((t : ℂ) * Complex.I, w) = Lx H P M t w :=
  (hasFDerivAt_Y P M hH hMc t w).fderiv

lemma contDiff_embed : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ((p.1 : ℂ) * Complex.I, p.2)) :=
  ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const).prodMk contDiff_snd

include hH hMc in
lemma contDiff_Lx : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Lx H P M p.1 p.2) := by
  have h : (fun p : ℝ × ℂ => Lx H P M p.1 p.2) =
      fun p => fderiv ℝ (Y P M) ((p.1 : ℂ) * Complex.I, p.2) := by
    funext p; rw [Lx_eq_fderiv hH P M hMc]
  rw [h]
  exact ((contDiff_Y P M hH hMc).fderiv_right (m := ∞) (by simp)).comp contDiff_embed

include hH hMc in
lemma contDiff_mm : ContDiff ℝ ∞ (fun p : ℝ × ℂ => mm P M p.1 p.2) := by
  unfold mm
  exact ((contDiff_x P hH).comp contDiff_fst).add
    ((hMc.comp contDiff_fst).clm_apply (cToVecL.contDiff.comp contDiff_snd))

include hM in
lemma mm_periodic (t : ℝ) (w : ℂ) : mm P M (t + 1) w = mm P M t w := by
  simp only [mm, mul_add, mul_one, P.periodic, hM.2.1 t]

include hM in
lemma deriv_M_periodic (t : ℝ) : deriv M (t + 1) = deriv M t := by
  rw [← deriv_comp_add_const]
  congr 1
  funext s
  exact hM.2.1 s

include hM in
lemma Lx_periodic (t : ℝ) (w : ℂ) : Lx H P M (t + 1) w = Lx H P M t w := by
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [Lx_apply, mm_periodic P M hM, deriv_M_periodic P M hM, hM.2.1 t, mul_add, mul_one,
    P.periodic]

/-- Where the model derivative is an isomorphism and the model is nonzero. -/
def goodSet (H : V 1 → ℝ) (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) :
    Set (ℝ × ℂ) :=
  {p | mm P M p.1 p.2 ≠ 0 ∧
    Lx H P M p.1 p.2 ∈ Set.range ((↑) : ((ℂ × ℂ) ≃L[ℝ] V 1) → ℂ × ℂ →L[ℝ] V 1)}

include hH hMc in
lemma goodSet_isOpen : IsOpen (goodSet H P M) :=
  (isOpen_ne_fun (contDiff_mm hH P M hMc).continuous continuous_const).inter
    (ContinuousLinearEquiv.isOpen.preimage (contDiff_Lx hH P M hMc).continuous)

include hH hM in
lemma mem_goodSet_zero (t : ℝ) : (t, (0 : ℂ)) ∈ goodSet H P M := by
  refine ⟨?_, ?_⟩
  · simp only [mm, map_zero, add_zero]
    exact fas_ne_zero_of_mem hH (P.mem _)
  · obtain ⟨e, he⟩ := exists_equiv_of_injective _ (Lx_zero_injective hH P hM t)
    exact ⟨e, he⟩

include hH hM hMc in
lemma goodSet_tube : ∃ ρ > 0, ∀ (t : ℝ) (w : ℂ), ‖w‖ < ρ → (t, w) ∈ goodSet H P M := by
  have hsub : Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℂ) ⊆ goodSet H P M := by
    rintro ⟨t, w⟩ ⟨-, hw⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact mem_goodSet_zero hH P M hM t
  obtain ⟨U₁, U₂, -, hU₂, hs, ht, hprod⟩ := generalized_tube_lemma isCompact_Icc
    isCompact_singleton (goodSet_isOpen hH P M hMc) hsub
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU₂ 0 (ht rfl)
  refine ⟨ρ, hρ, fun t w hw => ?_⟩
  have hper : Function.Periodic (fun t : ℝ => (t, w) ∈ goodSet H P M) 1 := fun t => by
    simp only [goodSet, Set.mem_setOf_eq, mm_periodic P M hM, Lx_periodic P M hM]
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
  have : (y, w) ∈ goodSet H P M := hprod ⟨hs ⟨hy.1, hy.2.le⟩, hball (by simpa using hw)⟩
  have e : (t, w) ∈ goodSet H P M ↔ (y, w) ∈ goodSet H P M := by
    have := hty
    simpa using this
  exact e.2 this

end tube

end SM

end

end FiniteEnergyPlane

/-!
# S, child C5 (local proof), layer A: the tube map is nondegenerate far out.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SME

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  simp only [cylInf, ccwLoop]
  exact mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') (Complex.exp_ne_zero _)

lemma cylScale_cylScaleInv (s t : ℝ) (v : ℂ × ℂ) : cylScale s t (cylScaleInv s t v) = v := by
  have hc : (((2 * Real.pi : ℝ) : ℂ) * cylInf s t) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)) (cylInf_ne_zero s t)
  rcases v with ⟨a, b⟩
  have hz := cylInf_ne_zero s t
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [cylScale, cylScaleInv]
  field_simp

/-- If `c • (D ∘ cylScale)` is injective, so is `D`. -/
lemma injective_of_comp_cylScale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : ℂ × ℂ →L[ℝ] F) (s t c : ℝ) (h : Function.Injective (c • D.comp (cylScale s t))) :
    Function.Injective D := by
  rw [injective_iff_map_eq_zero] at h ⊢
  intro v hv
  have h1 : (c • D.comp (cylScale s t)) (cylScaleInv s t v) = 0 := by
    simp [cylScale_cylScaleInv, hv]
  have h2 := h _ h1
  rw [← cylScale_cylScaleInv s t v, h2, map_zero]

lemma eventually_const_mul_exp_lt (C b δ : ℝ) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ S : ℝ, ∀ s ≥ S, C * Real.exp (-(b * s)) < δ := by
  have h : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 (C * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)).const_mul C
  rw [mul_zero] at h
  exact eventually_atTop.1 (h.eventually_lt_const hδ)

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (P : ReebOrbit H) {M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hM : IsUnitaryXiFrame J P M)

/-- The model pair `(m, L)`. -/
def gm (H : V 1 → ℝ) (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (p : ℝ × ℂ) : V 1 × (ℂ × ℂ →L[ℝ] V 1) :=
  (SM.mm P M p.1 p.2, SM.Lx H P M p.1 p.2)

/-- The good set of pairs. -/
def Og : Set (V 1 × (ℂ × ℂ →L[ℝ] V 1)) :=
  {y : V 1 × (ℂ × ℂ →L[ℝ] V 1) | y.1 ≠ 0 ∧
    y.2 ∈ Set.range ((↑) : ((ℂ × ℂ) ≃L[ℝ] V 1) → ℂ × ℂ →L[ℝ] V 1)}

lemma Og_isOpen : IsOpen Og :=
  (isOpen_ne_fun continuous_fst continuous_const).inter
    (ContinuousLinearEquiv.isOpen.preimage continuous_snd)

include hH hM in
/-- A uniform neighbourhood of the model values inside the good set. -/
lemma exists_uniform_margin :
    ∃ ρ > 0, ∃ δ > 0, ∀ (t : ℝ) (w : ℂ), w ∈ ball (0 : ℂ) ρ →
      ∀ y, dist y (gm H P M (t, w)) < δ → y ∈ Og := by
  have hMc : ContDiff ℝ ∞ M := hM.1
  obtain ⟨ρ₁, hρ₁, hg⟩ := SM.goodSet_tube hH P M hM hMc
  set K0 := gm H P M '' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) (ρ₁ / 2)) with hK0
  have hcont : Continuous (gm H P M) :=
    (SM.contDiff_mm hH P M hMc).continuous.prodMk (SM.contDiff_Lx hH P M hMc).continuous
  have hK : IsCompact K0 :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image hcont
  have hsub : K0 ⊆ Og := by
    rintro _ ⟨⟨t, w⟩, ⟨-, hw⟩, rfl⟩
    have hw' : ‖w‖ < ρ₁ := by
      have := mem_closedBall_zero_iff.1 hw
      linarith
    obtain ⟨hm, e, he⟩ := hg t w hw'
    exact ⟨hm, e, he⟩
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open Og_isOpen hsub
  refine ⟨ρ₁ / 2, by positivity, δ, hδ, fun t w hw y hy => hth ?_⟩
  have hper : Function.Periodic (fun t : ℝ => gm H P M (t, w)) 1 := fun t => by
    simp only [gm, SM.mm_periodic P M hM, SM.Lx_periodic P M hM]
  obtain ⟨t', ht', hty⟩ := hper.exists_mem_Ico₀ one_pos t
  refine Metric.mem_thickening_iff.2 ⟨gm H P M (t, w), ?_, hy⟩
  have : gm H P M (t, w) = gm H P M (t', w) := hty
  rw [this]
  exact ⟨(t', w), ⟨⟨ht'.1, ht'.2.le⟩, ball_subset_closedBall hw⟩, rfl⟩

variable (u : ℂ → V 1) (N : ℂ → ℂ →L[ℝ] V 1)

include hH hM in
/-- Far part: nondegeneracy of `Φ` at `(e^{2π(s+it)}, w)` for large `s`. -/
lemma far_part (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (hN : ContDiff ℝ ∞ N)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∃ S : ℝ, ∀ s ≥ S, ∀ (t : ℝ) (w : ℂ), w ∈ ball (0 : ℂ) ρ →
      u (cylInf s t) + N (cylInf s t) w ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (cylInf s t, w)) := by
  have hMc : ContDiff ℝ ∞ M := hM.1
  obtain ⟨ρ, hρ, δ, hδ, hmargin⟩ := exists_uniform_margin hH P hM
  obtain ⟨-, h3⟩ := expDecayCInftyTube_rescaled_sub_model H hH P u hu0 d b hb ha hw N M hNM ρ hρ
  obtain ⟨-, h4⟩ := expDecayCInftyTube_rescaled_fderiv_sub_model H hH P u hu hu0 d b hb ha hw
    N hN M hMc hNM ρ hρ
  obtain ⟨C₁, s₁, hC₁⟩ := h3 0
  obtain ⟨C₂, s₂, hC₂⟩ := h4 0
  obtain ⟨S₁, hS₁⟩ := eventually_const_mul_exp_lt C₁ b δ hb hδ
  obtain ⟨S₂, hS₂⟩ := eventually_const_mul_exp_lt C₂ b δ hb hδ
  refine ⟨ρ, hρ, max (max s₁ s₂) (max S₁ S₂), fun s hs t w hw => ?_⟩
  have hs₁ : s ≥ s₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs₂ : s ≥ s₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hS₁' : s ≥ S₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hS₂' : s ≥ S₂ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have e1 := hC₁ s hs₁ t w hw
  have e2 := hC₂ s hs₂ t w hw
  rw [norm_iteratedFDeriv_zero] at e1 e2
  set c : ℝ := Real.exp (-(2 * (P.T * s + d)))
  set y : V 1 × (ℂ × ℂ →L[ℝ] V 1) :=
    (c • (u (cylInf s t) + N (cylInf s t) w),
      c • (fderiv ℝ (fun p : ℂ × ℂ => u p.1 + N p.1 p.2) (cylInf s t, w)).comp (cylScale s t))
  have hY : fderiv ℝ (fun p : ℂ × ℂ => Real.exp (2 * P.T * p.1.re) •
      (P.x (P.T * p.1.im) + M p.1.im (cToVec p.2))) ((t : ℂ) * Complex.I, w) =
      SM.Lx H P M t w := SM.Lx_eq_fderiv hH P M hMc t w
  rw [hY] at e2
  have hdist : dist y (gm H P M (t, w)) < δ := by
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
    exact ⟨lt_of_le_of_lt e1 (hS₁ s hS₁'), lt_of_le_of_lt e2 (hS₂ s hS₂')⟩
  obtain ⟨hy1, e, he⟩ := hmargin t w hw y hdist
  refine ⟨fun h0 => hy1 ?_, ?_⟩
  · show c • (u (cylInf s t) + N (cylInf s t) w) = 0
    rw [h0, smul_zero]
  · refine injective_of_comp_cylScale _ s t c ?_
    have : (c • (fderiv ℝ (fun p : ℂ × ℂ => u p.1 + N p.1 p.2) (cylInf s t, w)).comp
        (cylScale s t)) = (e : ℂ × ℂ →L[ℝ] V 1) := he.symm
    rw [this]
    exact e.injective

end SME

end

end FiniteEnergyPlane

/-!
# S, child C5 (local proof), layer B: compact part and assembly.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SME

/-- The derivative of `(z, w) ↦ u z + N z w` along `w = 0`. -/
lemma fderiv_tubeMap_zero (u : ℂ → V 1) (N : ℂ → ℂ →L[ℝ] V 1) (hu : Differentiable ℝ u)
    (hN : Differentiable ℝ N) (z Δ ν : ℂ) :
    fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (z, 0) (Δ, ν) = fderiv ℝ u z Δ + N z ν := by
  have h1 : HasFDerivAt (fun q : ℂ × ℂ => u q.1)
      ((fderiv ℝ u z).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) (z, 0) :=
    (hu z).hasFDerivAt.comp (z, (0 : ℂ)) hasFDerivAt_fst
  have hc : HasFDerivAt (fun q : ℂ × ℂ => N q.1)
      ((fderiv ℝ N z).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) (z, 0) :=
    (hN z).hasFDerivAt.comp (z, (0 : ℂ)) hasFDerivAt_fst
  have h2 := hc.clm_apply (hasFDerivAt_snd (p := ((z, 0) : ℂ × ℂ)))
  have h3 : HasFDerivAt (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) _ (z, 0) := h1.add h2
  rw [h3.fderiv]
  simp

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (P : ReebOrbit H) {M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hM : IsUnitaryXiFrame J P M)

/-- Polar form in cylindrical coordinates. -/
lemma exists_cylInf_of_lt (S : ℝ) (z : ℂ) (hz : Real.exp (2 * Real.pi * S) < ‖z‖) :
    ∃ s ≥ S, ∃ t : ℝ, cylInf s t = z := by
  have hpos : 0 < ‖z‖ := lt_trans (Real.exp_pos _) hz
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨Real.log ‖z‖ / (2 * Real.pi), ?_, Complex.arg z / (2 * Real.pi), ?_⟩
  · rw [ge_iff_le, le_div_iff₀ hpi, mul_comm S, Real.le_log_iff_exp_le hpos]
    exact hz.le
  · simp only [cylInf, ccwLoop]
    have e1 : 2 * Real.pi * (Real.log ‖z‖ / (2 * Real.pi)) = Real.log ‖z‖ := by
      field_simp
    have e2 : 2 * Real.pi * (Complex.arg z / (2 * Real.pi)) = Complex.arg z := by
      field_simp
    rw [e1, e2, Real.exp_log hpos]
    exact Complex.norm_mul_exp_arg_mul_I z

variable (u : ℂ → V 1) (N : ℂ → ℂ →L[ℝ] V 1)

include hH hM in
theorem main (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) := by
  obtain ⟨ρ₂, hρ₂, S, hfar⟩ := far_part hH P hM u N hu hu0 d b hb ha hw hN hNM
  set Φ : ℂ × ℂ → V 1 := fun q => u q.1 + N q.1 q.2 with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ :=
    (hu.comp contDiff_fst).add ((hN.comp contDiff_fst).clm_apply contDiff_snd)
  set G : Set (ℂ × ℂ) := {p | Φ p ≠ 0 ∧
    fderiv ℝ Φ p ∈ Set.range ((↑) : ((ℂ × ℂ) ≃L[ℝ] V 1) → ℂ × ℂ →L[ℝ] V 1)} with hG
  have hGo : IsOpen G :=
    (isOpen_ne_fun hΦ.continuous continuous_const).inter
      (ContinuousLinearEquiv.isOpen.preimage (hΦ.continuous_fderiv (by simp)))
  set R := Real.exp (2 * Real.pi * S)
  have hsub : closedBall (0 : ℂ) R ×ˢ ({0} : Set ℂ) ⊆ G := by
    rintro ⟨z, w⟩ ⟨-, hw0⟩
    rw [Set.mem_singleton_iff] at hw0
    subst hw0
    refine ⟨?_, ?_⟩
    · simpa [hΦdef] using hu0 z
    · have hinj : Function.Injective (fderiv ℝ Φ (z, 0)) := by
        rw [injective_iff_map_eq_zero]
        rintro ⟨Δ, ν⟩ h0
        rw [hΦdef, fderiv_tubeMap_zero u N (hu.differentiable (by simp))
          (hN.differentiable (by simp))] at h0
        obtain ⟨h1, h2⟩ := hNinj z Δ ν h0
        simp [h1, h2]
      obtain ⟨e, he⟩ := SM.exists_equiv_of_injective _ hinj
      exact ⟨e, he⟩
  obtain ⟨U₁, U₂, -, hU₂, hs, ht, hprod⟩ := generalized_tube_lemma (isCompact_closedBall _ _)
    isCompact_singleton hGo hsub
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU₂ 0 (ht rfl)
  refine ⟨min ρ₂ ε, lt_min hρ₂ hε, ?_⟩
  rintro ⟨z, w⟩ ⟨-, hw⟩
  have hw₂ : w ∈ ball (0 : ℂ) ρ₂ := ball_subset_ball (min_le_left _ _) hw
  have hwε : w ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_right _ _) hw
  by_cases hz : ‖z‖ ≤ R
  · have hmem : (z, w) ∈ G := hprod ⟨hs (mem_closedBall_zero_iff.2 hz), hball hwε⟩
    obtain ⟨h1, e, he⟩ := hmem
    refine ⟨h1, ?_⟩
    show Function.Injective (fderiv ℝ Φ (z, w))
    rw [← he]
    exact e.injective
  · obtain ⟨s, hs', t, rfl⟩ := exists_cylInf_of_lt S z (lt_of_not_ge hz)
    exact hfar s hs' t w hw₂

end SME

end

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
# X transfer, child A, part 1: from bounds in the cylinder chart to plane bounds

`Pc (s, t, w) = (cylInf s t, w)`. If `F ∘ Pc` has bounded first and second derivatives on
`s ≥ s₁`, `w ∈ closedBall 0 ρ'`, then `F` has cylindrical bounds on `‖ζ‖ ≥ e^{2π s₁}`.
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real
open ContinuousLinearMap (fst snd)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linear form `(s, t, w) ↦ 2π (s + i t)`. -/
noncomputable def lc : ℝ × ℝ × ℂ →L[ℝ] ℂ :=
  ((2 * π : ℝ) : ℂ) • (Complex.ofRealCLM.comp (fst ℝ ℝ (ℝ × ℂ)) +
    Complex.I • Complex.ofRealCLM.comp ((fst ℝ ℝ ℂ).comp (snd ℝ ℝ (ℝ × ℂ))))

lemma lc_apply (h : ℝ × ℝ × ℂ) :
    lc h = ((2 * π : ℝ) : ℂ) * ((h.1 : ℂ) + Complex.I * (h.2.1 : ℂ)) := by
  simp [lc]
  ring

lemma cylInf_eq (q : ℝ × ℝ × ℂ) : cylInf q.1 q.2.1 = Complex.exp (lc q) := by
  rw [lc_apply]
  unfold cylInf ccwLoop
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The cylinder chart. -/
noncomputable def Pc (q : ℝ × ℝ × ℂ) : ℂ × ℂ := (cylInf q.1 q.2.1, q.2.2)

/-- The derivative of the cylinder chart. -/
noncomputable def Lc (q : ℝ × ℝ × ℂ) : ℝ × ℝ × ℂ →L[ℝ] ℂ × ℂ :=
  ((cylInf q.1 q.2.1) • lc).prod ((snd ℝ ℝ ℂ).comp (snd ℝ ℝ (ℝ × ℂ)))

lemma Lc_apply (q h : ℝ × ℝ × ℂ) : Lc q h = (cylInf q.1 q.2.1 * lc h, h.2.2) := by
  simp [Lc]

lemma hasFDerivAt_cyl (q : ℝ × ℝ × ℂ) :
    HasFDerivAt (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) ((cylInf q.1 q.2.1) • lc) q := by
  have h := (lc.hasFDerivAt (x := q)).cexp
  have e : (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) = fun q => Complex.exp (lc q) :=
    funext cylInf_eq
  rw [e, cylInf_eq]
  exact h

lemma hasFDerivAt_Pc (q : ℝ × ℝ × ℂ) : HasFDerivAt Pc (Lc q) q :=
  (hasFDerivAt_cyl q).prodMk ((snd ℝ ℝ ℂ).comp (snd ℝ ℝ (ℝ × ℂ))).hasFDerivAt

lemma contDiff_Pc : ContDiff ℝ ∞ Pc := by
  have e : (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) = fun q => Complex.exp (lc q) :=
    funext cylInf_eq
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) := by
    rw [e]; exact Complex.contDiff_exp.comp lc.contDiff
  exact h1.prodMk ((snd ℝ ℝ ℂ).comp (snd ℝ ℝ (ℝ × ℂ))).contDiff

lemma isOpen_tube (ρ : ℝ) : IsOpen {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} :=
  isOpen_ball.preimage (continuous_snd.comp continuous_snd)

lemma isOpen_plane (ρ : ℝ) : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) :=
  isOpen_univ.prod isOpen_ball

section chart

variable {F : ℂ × ℂ → E} {ρ : ℝ}

lemma contDiffAt_plane (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) {p : ℂ × ℂ}
    (hp : p.2 ∈ ball (0 : ℂ) ρ) : ContDiffAt ℝ ∞ F p :=
  hF.contDiffAt ((isOpen_plane ρ).mem_nhds ⟨Set.mem_univ _, hp⟩)

lemma hasFDerivAt_comp_Pc (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ))
    {q : ℝ × ℝ × ℂ} (hq : q.2.2 ∈ ball (0 : ℂ) ρ) :
    HasFDerivAt (fun q => F (Pc q)) ((fderiv ℝ F (Pc q)).comp (Lc q)) q :=
  ((contDiffAt_plane hF (p := Pc q) hq).differentiableAt (by simp)).hasFDerivAt.comp q
    (hasFDerivAt_Pc q)

lemma contDiffOn_comp_Pc (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiffOn ℝ ∞ (fun q => F (Pc q)) {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} :=
  hF.comp contDiff_Pc.contDiffOn (fun q hq => ⟨Set.mem_univ _, hq⟩)

lemma fderiv2_comp_Pc (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ))
    {q : ℝ × ℝ × ℂ} (hq : q.2.2 ∈ ball (0 : ℂ) ρ) (h k : ℝ × ℝ × ℂ) :
    fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q h k =
      fderiv ℝ (fderiv ℝ F) (Pc q) (Lc q h) (Lc q k) +
        fderiv ℝ F (Pc q) (lc k * (cylInf q.1 q.2.1 * lc h), 0) := by
  have hnh : {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} ∈ 𝓝 q := (isOpen_tube ρ).mem_nhds hq
  have hdd : DifferentiableAt ℝ (fderiv ℝ (fun q => F (Pc q))) q :=
    (((contDiffOn_comp_Pc hF).contDiffAt hnh).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)
  have e1 : fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q h k =
      fderiv ℝ (fun q' => fderiv ℝ (fun q => F (Pc q)) q' k) q h := by
    rw [fderiv_clm_apply hdd (differentiableAt_const k)]
    simp
  have hev : (fun q' => fderiv ℝ (fun q => F (Pc q)) q' k) =ᶠ[𝓝 q]
      fun q' => fderiv ℝ F (Pc q') (Lc q' k) := by
    filter_upwards [hnh] with q' hq'
    rw [(hasFDerivAt_comp_Pc hF hq').fderiv]
    rfl
  have hFd : DifferentiableAt ℝ (fderiv ℝ F) (Pc q) :=
    ((contDiffAt_plane hF (p := Pc q) hq).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)
  have hc : HasFDerivAt (fun q' => fderiv ℝ F (Pc q'))
      ((fderiv ℝ (fderiv ℝ F) (Pc q)).comp (Lc q)) q :=
    hFd.hasFDerivAt.comp q (hasFDerivAt_Pc q)
  have hu : HasFDerivAt (fun q' => Lc q' k)
      (((lc k) • ((cylInf q.1 q.2.1) • lc)).prod (0 : ℝ × ℝ × ℂ →L[ℝ] ℂ)) q := by
    have : (fun q' => Lc q' k) = fun q' : ℝ × ℝ × ℂ => (cylInf q'.1 q'.2.1 * lc k, k.2.2) :=
      funext fun q' => Lc_apply q' k
    rw [this]
    exact ((hasFDerivAt_cyl q).mul_const (lc k)).prodMk (hasFDerivAt_const _ _)
  have key := (hc.clm_apply hu).congr_of_eventuallyEq hev
  rw [e1, key.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_eq_mul]
  rw [add_comm]

end chart

lemma exists_cylInf_eq (z : ℂ) (hz : z ≠ 0) :
    ∃ t : ℝ, cylInf (Real.log ‖z‖ / (2 * π)) t = z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hexp : Real.exp (2 * π * (Real.log ‖z‖ / (2 * π))) = ‖z‖ := by
    rw [mul_div_cancel₀ _ h2pi.ne', Real.exp_log hzpos]
  refine ⟨Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [hexp]
  have e : ((2 * π * (Complex.arg z / (2 * π)) : ℝ) : ℂ) = (Complex.arg z : ℂ) := by
    congr 1
    field_simp
  rw [e]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- A preimage of `(Δ, o)` under the chart derivative at a point over `ζ`. -/
noncomputable def hsol (ζ Δ o : ℂ) : ℝ × ℝ × ℂ :=
  ((Δ / (((2 * π : ℝ) : ℂ) * ζ)).re, (Δ / (((2 * π : ℝ) : ℂ) * ζ)).im, o)

lemma two_pi_ne : (((2 * π : ℝ) : ℂ)) ≠ 0 := by
  have : (0 : ℝ) < 2 * π := by positivity
  exact_mod_cast this.ne'

lemma lc_hsol {ζ : ℂ} (hζ : ζ ≠ 0) (Δ o : ℂ) : lc (hsol ζ Δ o) = Δ / ζ := by
  rw [lc_apply]
  simp only [hsol]
  rw [mul_comm Complex.I, Complex.re_add_im]
  have := two_pi_ne
  field_simp

lemma norm_hsol_le {ζ : ℂ} (hζ : ζ ≠ 0) (Δ o : ℂ) : ‖hsol ζ Δ o‖ ≤ ‖Δ‖ / ‖ζ‖ + ‖o‖ := by
  have hζn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  have h2 : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have hx : ‖Δ / (((2 * π : ℝ) : ℂ) * ζ)‖ ≤ ‖Δ‖ / ‖ζ‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply div_le_div_of_nonneg_left (norm_nonneg _) hζn
    nlinarith
  have hre := Complex.abs_re_le_norm (Δ / (((2 * π : ℝ) : ℂ) * ζ))
  have him := Complex.abs_im_le_norm (Δ / (((2 * π : ℝ) : ℂ) * ζ))
  have hd : 0 ≤ ‖Δ‖ / ‖ζ‖ := by positivity
  simp only [hsol, Prod.norm_def, Real.norm_eq_abs]
  refine max_le (by linarith [norm_nonneg o]) (max_le (by linarith [norm_nonneg o]) (by linarith))

/-- From the cylinder chart to the plane. -/
theorem chart_bound {F : ℂ × ℂ → E} {ρ ρ' : ℝ} (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) {s₁ C₁ C₂ : ℝ}
    (h1 : ∀ q : ℝ × ℝ × ℂ, s₁ ≤ q.1 → q.2.2 ∈ closedBall (0 : ℂ) ρ' →
      ‖fderiv ℝ (fun q => F (Pc q)) q‖ ≤ C₁)
    (h2 : ∀ q : ℝ × ℝ × ℂ, s₁ ≤ q.1 → q.2.2 ∈ closedBall (0 : ℂ) ρ' →
      ‖fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q‖ ≤ C₂) :
    ∀ ζ w : ℂ, Real.exp (2 * π * s₁) ≤ ‖ζ‖ → w ∈ closedBall (0 : ℂ) ρ' →
      (∀ h : ℂ × ℂ, ‖fderiv ℝ F (ζ, w) h‖ ≤ C₁ * (‖h.1‖ / ‖ζ‖ + ‖h.2‖)) ∧
      ∀ h k : ℂ × ℂ, ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        (C₁ + C₂) * (‖h.1‖ / ‖ζ‖ + ‖h.2‖) * (‖k.1‖ / ‖ζ‖ + ‖k.2‖) := by
  intro ζ w hζR hw
  have hζn : 0 < ‖ζ‖ := lt_of_lt_of_le (Real.exp_pos _) hζR
  have hζ0 : ζ ≠ 0 := norm_pos_iff.1 hζn
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨t, ht⟩ := exists_cylInf_eq ζ hζ0
  set q : ℝ × ℝ × ℂ := (Real.log ‖ζ‖ / (2 * π), t, w) with hq
  have hs : s₁ ≤ q.1 := by
    show s₁ ≤ Real.log ‖ζ‖ / (2 * π)
    rw [le_div_iff₀ h2pi, mul_comm]
    exact (Real.le_log_iff_exp_le hζn).2 hζR
  have hcyl : cylInf q.1 q.2.1 = ζ := ht
  have hPq : Pc q = (ζ, w) := by
    show (cylInf (Real.log ‖ζ‖ / (2 * π)) t, w) = (ζ, w)
    rw [ht]
  have hqb : q.2.2 ∈ ball (0 : ℂ) ρ :=
    mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ)
  have hC1 : 0 ≤ C₁ := (norm_nonneg _).trans (h1 q hs hw)
  have hC2 : 0 ≤ C₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q)) (h2 q hs hw)
  have L1 : ∀ Δ o : ℂ, Lc q (hsol ζ Δ o) = (Δ, o) := by
    intro Δ o
    rw [Lc_apply, lc_hsol hζ0, hcyl]
    simp only [hsol]
    rw [mul_div_cancel₀ _ hζ0]
  have D1 : ∀ Δ o : ℂ, ‖fderiv ℝ F (ζ, w) (Δ, o)‖ ≤ C₁ * (‖Δ‖ / ‖ζ‖ + ‖o‖) := by
    intro Δ o
    have e : fderiv ℝ F (ζ, w) (Δ, o) = fderiv ℝ (fun q => F (Pc q)) q (hsol ζ Δ o) := by
      rw [(hasFDerivAt_comp_Pc hF hqb).fderiv, ContinuousLinearMap.comp_apply, L1, hPq]
    rw [e]
    exact ((fderiv ℝ (fun q => F (Pc q)) q).le_opNorm _).trans
      (mul_le_mul (h1 q hs hw) (norm_hsol_le hζ0 Δ o) (norm_nonneg _) hC1)
  refine ⟨fun h => D1 h.1 h.2, ?_⟩
  rintro ⟨Δ₁, o₁⟩ ⟨Δ₂, o₂⟩
  have I2 := fderiv2_comp_Pc hF hqb (hsol ζ Δ₁ o₁) (hsol ζ Δ₂ o₂)
  rw [L1, L1, hPq, lc_hsol hζ0, lc_hsol hζ0, hcyl] at I2
  have e : fderiv ℝ (fderiv ℝ F) (ζ, w) (Δ₁, o₁) (Δ₂, o₂) =
      fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q (hsol ζ Δ₁ o₁) (hsol ζ Δ₂ o₂) -
        fderiv ℝ F (ζ, w) (Δ₂ / ζ * (ζ * (Δ₁ / ζ)), 0) := eq_sub_of_add_eq I2.symm
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have n1 := norm_hsol_le hζ0 Δ₁ o₁
  have n2 := norm_hsol_le hζ0 Δ₂ o₂
  have a1 : 0 ≤ ‖Δ₁‖ / ‖ζ‖ := by positivity
  have a2 : 0 ≤ ‖Δ₂‖ / ‖ζ‖ := by positivity
  have b1 : ‖fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q (hsol ζ Δ₁ o₁) (hsol ζ Δ₂ o₂)‖ ≤
      C₂ * (‖Δ₁‖ / ‖ζ‖ + ‖o₁‖) * (‖Δ₂‖ / ‖ζ‖ + ‖o₂‖) := by
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    exact mul_le_mul (mul_le_mul (h2 q hs hw) n1 (norm_nonneg _) hC2) n2 (norm_nonneg _)
      (by positivity)
  have b2 : ‖fderiv ℝ F (ζ, w) (Δ₂ / ζ * (ζ * (Δ₁ / ζ)), 0)‖ ≤
      C₁ * ((‖Δ₁‖ / ‖ζ‖) * (‖Δ₂‖ / ‖ζ‖)) := by
    refine (D1 _ 0).trans (le_of_eq ?_)
    rw [norm_zero, add_zero, norm_mul, norm_mul, norm_div, norm_div]
    field_simp
  have b3 : (‖Δ₁‖ / ‖ζ‖) * (‖Δ₂‖ / ‖ζ‖) ≤ (‖Δ₁‖ / ‖ζ‖ + ‖o₁‖) * (‖Δ₂‖ / ‖ζ‖ + ‖o₂‖) :=
    mul_le_mul (by linarith [norm_nonneg o₁]) (by linarith [norm_nonneg o₂]) a2 (by positivity)
  calc _ ≤ C₂ * (‖Δ₁‖ / ‖ζ‖ + ‖o₁‖) * (‖Δ₂‖ / ‖ζ‖ + ‖o₂‖) +
        C₁ * ((‖Δ₁‖ / ‖ζ‖ + ‖o₁‖) * (‖Δ₂‖ / ‖ζ‖ + ‖o₂‖)) :=
        add_le_add b1 (b2.trans (mul_le_mul_of_nonneg_left b3 hC1))
    _ = _ := by ring

end XT

end FiniteEnergyPlane

/-!
# X transfer, child A, part 2: bounds in the cylinder chart from a periodic model with
exponentially decaying remainder.
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real
open ContinuousLinearMap (fst snd)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv2_apply {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y} {x : X} (hf : ContDiffAt ℝ ∞ f x)
    (h k : X) : fderiv ℝ (fderiv ℝ f) x h k = fderiv ℝ (fun y => fderiv ℝ f y k) x h := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hdd (differentiableAt_const k)]
  simp

lemma periodic_fract {Y : Type*} {g : ℝ × ℂ → Y}
    (hg : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w)) (t : ℝ) (w : ℂ) :
    g (t, w) = g (Int.fract t, w) := by
  have hp : Function.Periodic (fun t => g (t, w)) 1 := fun t => hg t w
  have := hp.sub_int_mul_eq (x := t) ⌊t⌋
  simp only [mul_one] at this
  rw [Int.self_sub_floor] at this
  exact this.symm

lemma fderiv_periodic {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {g : ℝ × ℂ → Y}
    (hg : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w)) (t : ℝ) (w : ℂ) :
    fderiv ℝ g (t + 1, w) = fderiv ℝ g (t, w) := by
  have e : (fun x : ℝ × ℂ => g (x + ((1 : ℝ), (0 : ℂ)))) = g := by
    funext x
    rcases x with ⟨t, w⟩
    simp [hg]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := (t, w)) ((1 : ℝ), (0 : ℂ))
  rw [e] at this
  simpa using this.symm

lemma isOpen_model (ρ : ℝ) : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℂ)) :=
  isOpen_univ.prod isOpen_ball

lemma model_bounds {M : ℝ × ℂ → E} {ρ ρ' : ℝ} (hρ : ρ' < ρ)
    (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w)) :
    ∃ N₁ N₂ : ℝ, ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ' →
      ‖fderiv ℝ M (t, w)‖ ≤ N₁ ∧ ‖fderiv ℝ (fderiv ℝ M) (t, w)‖ ≤ N₂ := by
  have hd1 : ContDiffOn ℝ ∞ (fderiv ℝ M) (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    hM.fderiv_of_isOpen (isOpen_model ρ) (by simp)
  have hd2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ M)) (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    hd1.fderiv_of_isOpen (isOpen_model ρ) (by simp)
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) ρ') :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hsub : Set.Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) ρ' ⊆ Set.univ ×ˢ ball (0 : ℂ) ρ :=
    fun x hx => ⟨Set.mem_univ _,
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hx.2) hρ)⟩
  obtain ⟨N₁, hN₁⟩ := hK.exists_bound_of_continuousOn (hd1.continuousOn.mono hsub)
  have hc2 : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ M) x‖)
      (Set.Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) ρ') :=
    ContinuousOn.norm (E := ℝ × ℂ →L[ℝ] ℝ × ℂ →L[ℝ] E) (hd2.continuousOn.mono hsub)
  obtain ⟨N₂, hN₂⟩ := hK.exists_bound_of_continuousOn hc2
  refine ⟨N₁, N₂, fun t w hw => ?_⟩
  have p1 := periodic_fract (g := fderiv ℝ M) (fderiv_periodic hper) t w
  have p2 := periodic_fract (g := fderiv ℝ (fderiv ℝ M))
    (fderiv_periodic (fderiv_periodic hper)) t w
  have hmem : (Int.fract t, w) ∈ Set.Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) ρ' :=
    ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, hw⟩
  rw [p1, p2]
  have h2 := hN₂ _ hmem
  rw [Real.norm_eq_abs] at h2
  exact ⟨hN₁ _ hmem, (le_abs_self _).trans h2⟩

/-- The cylinder model `(s, t, w) ↦ s • ℓ + M (t, w)`. -/
def Mdl (ℓ : E) (M : ℝ × ℂ → E) (q : ℝ × ℝ × ℂ) : E := q.1 • ℓ + M q.2

section model

variable {ℓ : E} {M : ℝ × ℂ → E} {ρ : ℝ}

lemma contDiffAt_M (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ)) {x : ℝ × ℂ}
    (hx : x.2 ∈ ball (0 : ℂ) ρ) : ContDiffAt ℝ ∞ M x :=
  hM.contDiffAt ((isOpen_model ρ).mem_nhds ⟨Set.mem_univ _, hx⟩)

lemma hasFDerivAt_Mdl (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    {q : ℝ × ℝ × ℂ} (hq : q.2.2 ∈ ball (0 : ℂ) ρ) :
    HasFDerivAt (Mdl ℓ M) ((fst ℝ ℝ (ℝ × ℂ)).smulRight ℓ +
      (fderiv ℝ M q.2).comp (snd ℝ ℝ (ℝ × ℂ))) q := by
  have hMd : DifferentiableAt ℝ M q.2 := (contDiffAt_M hM hq).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun q : ℝ × ℝ × ℂ => q.1 • ℓ) ((fst ℝ ℝ (ℝ × ℂ)).smulRight ℓ) q :=
    hasFDerivAt_fst.smul_const ℓ
  have h2 : HasFDerivAt (fun q : ℝ × ℝ × ℂ => M q.2)
      ((fderiv ℝ M q.2).comp (snd ℝ ℝ (ℝ × ℂ))) q :=
    hMd.hasFDerivAt.comp q hasFDerivAt_snd
  exact h1.add h2

lemma contDiffOn_Mdl (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiffOn ℝ ∞ (Mdl ℓ M) {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} := by
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => q.1 • ℓ) := contDiff_fst.smul contDiff_const
  have h2 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ => M q.2)
      {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} :=
    hM.comp contDiff_snd.contDiffOn (fun q hq => ⟨Set.mem_univ _, hq⟩)
  exact h1.contDiffOn.add h2

lemma Mdl_bounds (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    {q : ℝ × ℝ × ℂ} (hq : q.2.2 ∈ ball (0 : ℂ) ρ) :
    ‖fderiv ℝ (Mdl ℓ M) q‖ ≤ ‖ℓ‖ + ‖fderiv ℝ M q.2‖ ∧
      ‖fderiv ℝ (fderiv ℝ (Mdl ℓ M)) q‖ ≤ ‖fderiv ℝ (fderiv ℝ M) q.2‖ := by
  have hnh : {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} ∈ 𝓝 q := (isOpen_tube ρ).mem_nhds hq
  constructor
  · rw [(hasFDerivAt_Mdl hM hq).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun k => ?_)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, add_mul]
    have a1 : ‖k.1‖ ≤ ‖k‖ := norm_fst_le k
    have a2 : ‖k.2‖ ≤ ‖k‖ := norm_snd_le k
    have a3 := (fderiv ℝ M q.2).le_opNorm k.2
    have a4 : ‖fderiv ℝ M q.2‖ * ‖k.2‖ ≤ ‖fderiv ℝ M q.2‖ * ‖k‖ :=
      mul_le_mul_of_nonneg_left a2 (norm_nonneg _)
    have a5 : ‖k.1‖ * ‖ℓ‖ ≤ ‖ℓ‖ * ‖k‖ := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left a1 (norm_nonneg _)
    linarith
  · have hMc := contDiffAt_M hM (x := q.2) hq
    have hMdlc : ContDiffAt ℝ ∞ (Mdl ℓ M) q := (contDiffOn_Mdl hM).contDiffAt hnh
    refine ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (fderiv ℝ (fderiv ℝ M) q.2)) (fun h => ?_)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun k => ?_)
    rw [fderiv2_apply hMdlc h k]
    have hev : (fun q' => fderiv ℝ (Mdl ℓ M) q' k) =ᶠ[𝓝 q]
        fun q' : ℝ × ℝ × ℂ => k.1 • ℓ + fderiv ℝ M q'.2 k.2 := by
      filter_upwards [hnh] with q' hq'
      rw [(hasFDerivAt_Mdl hM hq').fderiv]
      rfl
    have hdd : DifferentiableAt ℝ (fderiv ℝ M) q.2 :=
      (hMc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hk : HasFDerivAt (fun x : ℝ × ℂ => fderiv ℝ M x k.2)
        (fderiv ℝ (fun x : ℝ × ℂ => fderiv ℝ M x k.2) q.2) q.2 :=
      (hdd.clm_apply (differentiableAt_const k.2)).hasFDerivAt
    have key := ((hk.comp q hasFDerivAt_snd).const_add (k.1 • ℓ)).congr_of_eventuallyEq hev
    rw [key.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ← fderiv2_apply hMc h.2 k.2]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    have n0 : 0 ≤ ‖fderiv ℝ (fderiv ℝ M) q.2‖ := norm_nonneg (fderiv ℝ (fderiv ℝ M) q.2)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_snd_le h) n0)
      (norm_snd_le k) (norm_nonneg k.2) (mul_nonneg n0 (norm_nonneg h))

end model

/-- Bounds in the cylinder chart. -/
theorem cyl_bounds {F : ℂ × ℂ → E} {ρ ρ' b : ℝ} (hb : 0 < b) (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (ℓ : E)
    (M : ℝ × ℂ → E) (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w))
    (hdec : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) ρ b) :
    ∃ s₁ C₁ C₂ : ℝ,
      (∀ q : ℝ × ℝ × ℂ, s₁ ≤ q.1 → q.2.2 ∈ closedBall (0 : ℂ) ρ' →
        ‖fderiv ℝ (fun q => F (Pc q)) q‖ ≤ C₁) ∧
      (∀ q : ℝ × ℝ × ℂ, s₁ ≤ q.1 → q.2.2 ∈ closedBall (0 : ℂ) ρ' →
        ‖fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q‖ ≤ C₂) := by
  obtain ⟨N₁, N₂, hN⟩ := model_bounds hρ hM hper
  obtain ⟨Ca, sa, ha⟩ := hdec.2 1
  obtain ⟨Cb, sb, hbb⟩ := hdec.2 2
  have hDe : (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) =
      fun q => F (Pc q) - Mdl ℓ M q := by
    funext q
    simp only [Pc, Mdl, Prod.mk.eta]
    abel
  rw [hDe] at ha hbb
  have hexp : ∀ (C s : ℝ), 0 ≤ s → C * Real.exp (-(b * s)) ≤ |C| := by
    intro C s hs
    have h1 : Real.exp (-(b * s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hb.le hs))
    calc C * Real.exp (-(b * s)) ≤ |C| * Real.exp (-(b * s)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ = |C| := mul_one _
  -- pointwise facts at a point of the tube
  have hpt : ∀ q : ℝ × ℝ × ℂ, q.2.2 ∈ ball (0 : ℂ) ρ →
      fderiv ℝ (fun q => F (Pc q)) q =
        fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q) q + fderiv ℝ (Mdl ℓ M) q := by
    intro q hq
    have hA := hasFDerivAt_comp_Pc hF hq
    have hB := hasFDerivAt_Mdl (ℓ := ℓ) hM hq
    have hD : HasFDerivAt (fun q => F (Pc q) - Mdl ℓ M q) _ q := hA.sub hB
    rw [hD.fderiv, hA.fderiv, hB.fderiv]
    abel
  refine ⟨max (max sa sb) 0, |Ca| + (‖ℓ‖ + N₁), |Cb| + N₂, ?_, ?_⟩
  · rintro ⟨s, t, w⟩ hs hw
    have hs0 : (0 : ℝ) ≤ s := (le_max_right _ _).trans hs
    have hsa : sa ≤ s := ((le_max_left _ _).trans (le_max_left _ _)).trans hs
    have hwb : w ∈ ball (0 : ℂ) ρ :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ)
    rw [hpt (s, t, w) hwb]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [← norm_iteratedFDeriv_one]
      exact (ha s hsa t w hwb).trans (hexp Ca s hs0)
    · exact ((Mdl_bounds hM (q := (s, t, w)) hwb).1).trans
        (add_le_add le_rfl (hN t w hw).1)
  · rintro ⟨s, t, w⟩ hs hw
    have hs0 : (0 : ℝ) ≤ s := (le_max_right _ _).trans hs
    have hsb : sb ≤ s := ((le_max_right _ _).trans (le_max_left _ _)).trans hs
    have hwb : w ∈ ball (0 : ℂ) ρ :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ)
    have hnh : {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} ∈ 𝓝 ((s, t, w) : ℝ × ℝ × ℂ) :=
      (isOpen_tube ρ).mem_nhds hwb
    have hev : fderiv ℝ (fun q => F (Pc q)) =ᶠ[𝓝 ((s, t, w) : ℝ × ℝ × ℂ)]
        fun q => fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q) q + fderiv ℝ (Mdl ℓ M) q := by
      filter_upwards [hnh] with q hq using hpt q hq
    have hFc : ContDiffAt ℝ ∞ (fun q => F (Pc q)) ((s, t, w) : ℝ × ℝ × ℂ) :=
      (contDiffOn_comp_Pc hF).contDiffAt hnh
    have hMc : ContDiffAt ℝ ∞ (Mdl ℓ M) ((s, t, w) : ℝ × ℝ × ℂ) :=
      (contDiffOn_Mdl hM).contDiffAt hnh
    have hDc : ContDiffAt ℝ ∞ (fun q => F (Pc q) - Mdl ℓ M q) ((s, t, w) : ℝ × ℝ × ℂ) :=
      hFc.sub hMc
    have d1 : DifferentiableAt ℝ (fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q))
        ((s, t, w) : ℝ × ℝ × ℂ) :=
      (hDc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have d2 : DifferentiableAt ℝ (fderiv ℝ (Mdl ℓ M)) ((s, t, w) : ℝ × ℝ × ℂ) :=
      (hMc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hsum : HasFDerivAt (fun q => fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q) q +
        fderiv ℝ (Mdl ℓ M) q) _ ((s, t, w) : ℝ × ℝ × ℂ) := d1.hasFDerivAt.add d2.hasFDerivAt
    rw [hev.fderiv_eq, hsum.fderiv]
    refine le_trans (norm_add_le
      (fderiv ℝ (fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q)) ((s, t, w) : ℝ × ℝ × ℂ))
      (fderiv ℝ (fderiv ℝ (Mdl ℓ M)) ((s, t, w) : ℝ × ℝ × ℂ))) (add_le_add ?_ ?_)
    · rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact (hbb s hsb t w hwb).trans (hexp Cb s hs0)
    · exact ((Mdl_bounds hM (q := (s, t, w)) hwb).2).trans (hN t w hw).2

end XT

end FiniteEnergyPlane

/-!
# X transfer, child A: cylindrical `C²` bounds from an exponentially attained periodic model
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma wt_far {R : ℝ} (hR : 0 < R) {ζ : ℂ} (hζ : R ≤ ‖ζ‖) (h : ℂ × ℂ) :
    ‖h.1‖ / ‖ζ‖ + ‖h.2‖ ≤ (1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := by
  have hn : 0 < ‖ζ‖ := lt_of_lt_of_le hR hζ
  have hR1 : 0 ≤ 1 / R := by positivity
  have k1 : ‖h.1‖ / ‖ζ‖ ≤ (1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖)) := by
    rw [div_le_iff₀ hn]
    have hX : 1 ≤ (1 + 1 / R) * ‖ζ‖ / (1 + ‖ζ‖) := by
      rw [le_div_iff₀ (by linarith)]
      have h1 : 1 ≤ ‖ζ‖ / R := (one_le_div hR).2 hζ
      have e : (1 + 1 / R) * ‖ζ‖ = ‖ζ‖ + ‖ζ‖ / R := by ring
      linarith
    calc ‖h.1‖ ≤ ‖h.1‖ * ((1 + 1 / R) * ‖ζ‖ / (1 + ‖ζ‖)) :=
          le_mul_of_one_le_right (norm_nonneg _) hX
      _ = _ := by ring
  have k2 : ‖h.2‖ ≤ (1 + 1 / R) * ‖h.2‖ := le_mul_of_one_le_left (norm_nonneg _) (by linarith)
  rw [mul_add]
  linarith

lemma wt_near {R : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ ≤ R) (h : ℂ × ℂ) :
    ‖h‖ ≤ (1 + R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := by
  have hp : 0 < 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  have hR : 0 ≤ R := (norm_nonneg ζ).trans hζ
  have k1 : ‖h.1‖ ≤ (1 + R) * (‖h.1‖ / (1 + ‖ζ‖)) := by
    rw [← mul_div_assoc, le_div_iff₀ hp]
    nlinarith [mul_nonneg (norm_nonneg h.1) (sub_nonneg.2 hζ)]
  have k2 : ‖h.2‖ ≤ (1 + R) * ‖h.2‖ := le_mul_of_one_le_left (norm_nonneg _) (by linarith)
  have k3 : ‖h‖ ≤ ‖h.1‖ + ‖h.2‖ := by
    rw [Prod.norm_def]
    exact max_le (by linarith [norm_nonneg h.2]) (by linarith [norm_nonneg h.1])
  rw [mul_add]
  linarith

theorem exists_cylBound (ρ b ρ' : ℝ) (hb : 0 < b) (hρ' : 0 < ρ') (hρ : ρ' < ρ)
    (F : ℂ × ℂ → E) (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (ℓ : E)
    (M : ℝ × ℂ → E) (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hMper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w))
    (hdec : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) ρ b) :
    ∃ C : ℝ, CylBound F ρ' C := by
  obtain ⟨s₁, C₁, C₂, h1, h2⟩ := cyl_bounds (ρ' := ρ') hb hρ hF ℓ M hM hMper hdec
  have far := chart_bound hρ hF h1 h2
  have hR : 0 < Real.exp (2 * π * s₁) := Real.exp_pos _
  generalize Real.exp (2 * π * s₁) = R at far hR
  have hw0 : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ' := by simpa using hρ'.le
  have hC1 : 0 ≤ C₁ := (norm_nonneg _).trans (h1 (s₁, 0, 0) le_rfl hw0)
  have hC2 : 0 ≤ C₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) (s₁, 0, 0)))
      (h2 (s₁, 0, 0) le_rfl hw0)
  have hd1 : ContDiffOn ℝ ∞ (fderiv ℝ F) (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    hF.fderiv_of_isOpen (isOpen_plane ρ) (by simp)
  have hd2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ F)) (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    hd1.fderiv_of_isOpen (isOpen_plane ρ) (by simp)
  have hK : IsCompact (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) ρ') :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hsub : closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) ρ' ⊆ Set.univ ×ˢ ball (0 : ℂ) ρ :=
    fun x hx => ⟨Set.mem_univ _,
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hx.2) hρ)⟩
  obtain ⟨N₁, hN₁⟩ := hK.exists_bound_of_continuousOn (hd1.continuousOn.mono hsub)
  have hc2 : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ F) x‖)
      (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) ρ') :=
    ContinuousOn.norm (E := ℂ × ℂ →L[ℝ] ℂ × ℂ →L[ℝ] E) (hd2.continuousOn.mono hsub)
  obtain ⟨N₂, hN₂⟩ := hK.exists_bound_of_continuousOn hc2
  have hc1 : (1 : ℝ) ≤ 1 + 1 / R := by
    have : 0 ≤ 1 / R := by positivity
    linarith
  have hc0 : (0 : ℝ) ≤ 1 + 1 / R := by linarith
  have hfarC : C₁ * (1 + 1 / R) ≤ (C₁ + C₂) * (1 + 1 / R) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hC1 hc0) (sub_nonneg.2 hc1),
      mul_nonneg hC2 (sq_nonneg (1 + 1 / R))]
  have hnearC : |N₁| * (1 + R) ≤ (|N₁| + |N₂|) * (1 + R) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg N₁) (by linarith : (0 : ℝ) ≤ 1 + R)) hR.le,
      mul_nonneg (abs_nonneg N₂) (sq_nonneg (1 + R))]
  refine ⟨max ((C₁ + C₂) * (1 + 1 / R) ^ 2) ((|N₁| + |N₂|) * (1 + R) ^ 2), fun ζ w hw => ?_⟩
  have hCa : (C₁ + C₂) * (1 + 1 / R) ^ 2 ≤
      max ((C₁ + C₂) * (1 + 1 / R) ^ 2) ((|N₁| + |N₂|) * (1 + R) ^ 2) := le_max_left _ _
  have hCb : (|N₁| + |N₂|) * (1 + R) ^ 2 ≤
      max ((C₁ + C₂) * (1 + 1 / R) ^ 2) ((|N₁| + |N₂|) * (1 + R) ^ 2) := le_max_right _ _
  generalize max ((C₁ + C₂) * (1 + 1 / R) ^ 2) ((|N₁| + |N₂|) * (1 + R) ^ 2) = C at hCa hCb
  have hC0 : 0 ≤ C := le_trans (by positivity) hCa
  have hW : ∀ h : ℂ × ℂ, 0 ≤ ‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖ := fun h => by positivity
  rcases le_or_gt R ‖ζ‖ with hζ | hζ
  · obtain ⟨f1, f2⟩ := far ζ w hζ hw
    have hn : 0 < ‖ζ‖ := lt_of_lt_of_le hR hζ
    constructor
    · intro h
      calc ‖fderiv ℝ F (ζ, w) h‖ ≤ C₁ * (‖h.1‖ / ‖ζ‖ + ‖h.2‖) := f1 h
        _ ≤ C₁ * ((1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) :=
            mul_le_mul_of_nonneg_left (wt_far hR hζ h) hC1
        _ = C₁ * (1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := by ring
        _ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) :=
            mul_le_mul_of_nonneg_right (hfarC.trans hCa) (hW h)
    · intro h k
      have p1 : 0 ≤ ‖k.1‖ / ‖ζ‖ + ‖k.2‖ := by positivity
      calc ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖
          ≤ (C₁ + C₂) * (‖h.1‖ / ‖ζ‖ + ‖h.2‖) * (‖k.1‖ / ‖ζ‖ + ‖k.2‖) := f2 h k
        _ ≤ (C₁ + C₂) * ((1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) *
              ((1 + 1 / R) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (wt_far hR hζ h) (by linarith))
              (wt_far hR hζ k) p1
              (mul_nonneg (by linarith) (mul_nonneg hc0 (hW h)))
        _ = (C₁ + C₂) * (1 + 1 / R) ^ 2 * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) *
              (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) := by ring
        _ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCa (hW h)) (hW k)
  · have hmem : (ζ, w) ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) ρ' :=
      ⟨mem_closedBall_zero_iff.2 hζ.le, hw⟩
    have n1 : ‖fderiv ℝ F (ζ, w)‖ ≤ |N₁| := (hN₁ _ hmem).trans (le_abs_self _)
    have n2 : ‖fderiv ℝ (fderiv ℝ F) (ζ, w)‖ ≤ |N₂| := by
      have h2' := hN₂ _ hmem
      rw [Real.norm_eq_abs] at h2'
      exact ((le_abs_self _).trans h2').trans (le_abs_self _)
    have hR1 : (0 : ℝ) ≤ 1 + R := by linarith
    constructor
    · intro h
      calc ‖fderiv ℝ F (ζ, w) h‖ ≤ ‖fderiv ℝ F (ζ, w)‖ * ‖h‖ := (fderiv ℝ F (ζ, w)).le_opNorm h
        _ ≤ |N₁| * ((1 + R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) :=
            mul_le_mul n1 (wt_near hζ.le h) (norm_nonneg _) (abs_nonneg _)
        _ = |N₁| * (1 + R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := by ring
        _ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) :=
            mul_le_mul_of_nonneg_right (hnearC.trans hCb) (hW h)
    · intro h k
      have hN12 : |N₂| ≤ |N₁| + |N₂| := by linarith [abs_nonneg N₁]
      calc ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖
          ≤ ‖fderiv ℝ (fderiv ℝ F) (ζ, w)‖ * ‖h‖ * ‖k‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ |N₂| * ((1 + R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) *
              ((1 + R) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖)) :=
            mul_le_mul (mul_le_mul n2 (wt_near hζ.le h) (norm_nonneg _) (abs_nonneg _))
              (wt_near hζ.le k) (norm_nonneg _)
              (mul_nonneg (abs_nonneg _) (mul_nonneg hR1 (hW h)))
        _ = |N₂| * (1 + R) ^ 2 * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) *
              (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) := by ring
        _ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              ((mul_le_mul_of_nonneg_right hN12 (sq_nonneg _)).trans hCb) (hW h)) (hW k)

end XT

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_cylindrical_bounds_of_expDecayCInftyTube_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ρ b ρ' : ℝ) (hb : 0 < b) (hρ' : 0 < ρ') (hρ : ρ' < ρ)
    (F : ℂ × ℂ → E) (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (ℓ : E)
    (M : ℝ × ℂ → E) (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hMper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w))
    (hdec : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) ρ b) :
    ∃ C : ℝ, ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' →
      (∀ h : ℂ × ℂ, ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) ∧
      ∀ h k : ℂ × ℂ, ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) :=
  XT.exists_cylBound ρ b ρ' hb hρ' hρ F hF ℓ M hM hMper hdec

end FiniteEnergyPlane

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
# S, child C6b (local proof): asymptotics of `aCoord` and `proj` on the tube.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SMF

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Tube decay only depends on the values on the tube. -/
lemma expDecayCInftyTube_congr {f f' : ℝ × ℝ × ℂ → F} {ρ b : ℝ} (h : ExpDecayCInftyTube f ρ b)
    (he : ∀ q : ℝ × ℝ × ℂ, q.2.2 ∈ ball (0 : ℂ) ρ → f q = f' q) :
    ExpDecayCInftyTube f' ρ b := by
  obtain ⟨⟨s₀, hs⟩, hl⟩ := h
  have hO : IsOpen (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℝ × ℂ)) :=
    isOpen_univ.prod (isOpen_univ.prod isOpen_ball)
  refine ⟨⟨s₀, hs.congr fun q hq => (he q hq.2.2).symm⟩, fun m => ?_⟩
  obtain ⟨C, s₁, hC⟩ := hl m
  refine ⟨C, s₁, fun s hs t w hw => ?_⟩
  have hev : f' =ᶠ[𝓝 (s, t, w)] f := by
    filter_upwards [hO.mem_nhds ⟨mem_univ _, mem_univ _, hw⟩] with q hq
    exact (he q hq.2.2).symm
  rw [(hev.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
  exact hC s hs t w hw

/-- `cToVec` as a continuous real-linear map. -/
def cToVecL : ℂ →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := cToVec
      map_add' := fun a b => by ext i; rcases i with i | i <;> simp [cToVec]
      map_smul' := fun c a => by ext i; rcases i with i | i <;> simp [cToVec] }

lemma contDiff_cToVec : ContDiff ℝ ∞ (fun w : ℂ => cToVec w) :=
  (cToVecL : ℂ →L[ℝ] _).contDiff

/-- Points of the energy surface: `proj` fixes them and `aCoord` vanishes. -/
lemma proj_aCoord_of_mem {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V 1}
    (hx : H x = 1) : proj H x = x ∧ aCoord H x = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx
    simp at this
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 x hx0
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := ⟨r, hr0, hr1⟩
  have h1 : scaleToS H x = 1 := by
    unfold scaleToS
    rw [dif_pos e1]
    have hc := Classical.choose_spec e1
    have a := hru _ hc
    have b := hru 1 ⟨one_pos, by simpa using hx⟩
    rw [a, b]
  refine ⟨by simp [proj, h1], by simp [aCoord, h1]⟩

end SMF

theorem exists_aCoord_proj_model_of_tubeMap_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hm : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → P.x (P.T * t) + M t (cToVec w) ≠ 0)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0) :
    ∃ (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
      ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
      (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t)) ∧
      ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
        aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - P.T * q.1 - d -
          α (q.2.1, q.2.2)) ρ b ∧
      ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
        proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - X (q.2.1, q.2.2)) ρ b := by
  set g : ℝ × ℂ → V 1 := fun p => P.x (P.T * p.1) + M p.1 (cToVec p.2) with hg
  have hcToVec : ContDiff ℝ ∞ (fun w : ℂ => cToVec w) := SMF.contDiff_cToVec
  have hgc : ContDiff ℝ ∞ g := by
    refine ((ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_fst)).add ?_
    exact (hM.1.comp contDiff_fst).clm_apply (hcToVec.comp contDiff_snd)
  have hgper : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w) := by
    intro t w
    simp only [hg, mul_add, mul_one, P.periodic, hM.2.1 t]
  have hgU : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → g (t, w) ∈ {y : V 1 | y ≠ 0} :=
    fun t w hw => hm t w hw
  have hUo : IsOpen {y : V 1 | y ≠ 0} := isOpen_ne
  have haC : ContDiffOn ℝ ∞ (aCoord H) {y : V 1 | y ≠ 0} :=
    fun y hy => ((contDiffAt_aCoord_proj H hH y hy).1).contDiffWithinAt
  have hpC : ContDiffOn ℝ ∞ (proj H) {y : V 1 | y ≠ 0} :=
    fun y hy => ((contDiffAt_aCoord_proj H hH y hy).2).contDiffWithinAt
  set f : ℝ × ℝ × ℂ → V 1 := fun q => Real.exp (-(2 * (P.T * q.1 + d))) •
    (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) with hf
  have h3 : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => f q - g (q.2.1, q.2.2)) ρ b :=
    expDecayCInftyTube_rescaled_sub_model H hH P u hu0 d b hb ha hw N M hNM ρ hρ
  have hρ2 : ball (0 : ℂ) ρ ⊆ closedBall 0 ρ := ball_subset_closedBall
  have hmaps : Set.MapsTo g (Set.univ ×ˢ ball (0 : ℂ) ρ) {y : V 1 | y ≠ 0} :=
    fun p hp => hm p.1 p.2 (hρ2 hp.2)
  -- rescaling identity on the tube
  have hscale : ∀ q : ℝ × ℝ × ℂ, q.2.2 ∈ ball (0 : ℂ) ρ →
      proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) = proj H (f q) ∧
      aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) =
        aCoord H (f q) + (P.T * q.1 + d) := by
    intro q hq
    have hy : u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2 ≠ 0 :=
      hΦ (cylInf q.1 q.2.1, q.2.2) ⟨mem_univ _, hq⟩
    have hfy : f q ≠ 0 := smul_ne_zero (Real.exp_pos _).ne' hy
    have e := proj_aCoord_exp_smul H hH (P.T * q.1 + d) (f q) hfy
    have e2 : Real.exp (2 * (P.T * q.1 + d)) • f q =
        u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2 := by
      simp only [hf, smul_smul, ← Real.exp_add]
      rw [show 2 * (P.T * q.1 + d) + -(2 * (P.T * q.1 + d)) = 0 by ring, Real.exp_zero, one_smul]
    rw [e2] at e
    exact e
  refine ⟨fun p => aCoord H (g p), fun p => proj H (g p), haC.comp hgc.contDiffOn hmaps, hpC.comp hgc.contDiffOn hmaps,
    fun t w => ⟨by simp only [hgper], by simp only [hgper]⟩, fun t => ?_, ?_, ?_⟩
  · have hx : H (P.x (P.T * t)) = 1 := P.mem _
    have h0 : g (t, 0) = P.x (P.T * t) := by
      simp only [hg]
      rw [show cToVec (0 : ℂ) = 0 by ext i; rcases i with i | i <;> simp [cToVec], map_zero,
        add_zero]
    show aCoord H (g (t, 0)) = 0 ∧ proj H (g (t, 0)) = P.x (P.T * t)
    rw [h0]
    exact ⟨(SMF.proj_aCoord_of_mem hH hx).2, (SMF.proj_aCoord_of_mem hH hx).1⟩
  · have key := expDecayCInftyTube_comp_sub (aCoord H) {y : V 1 | y ≠ 0} hUo haC ρ b hρ hb g
      hgc.contDiffOn hgper hgU f h3
    refine SMF.expDecayCInftyTube_congr key fun q hq => ?_
    rw [(hscale q hq).2]
    ring
  · have key := expDecayCInftyTube_comp_sub (proj H) {y : V 1 | y ≠ 0} hUo hpC ρ b hρ hb g
      hgc.contDiffOn hgper hgU f h3
    refine SMF.expDecayCInftyTube_congr key fun q hq => ?_
    rw [(hscale q hq).1]

end

end FiniteEnergyPlane

/-!
# A1, instance part 1: the model derivative in symplectization coordinates

`Ψ y = (aCoord y, proj y)`; the model `g(t, w) = x(T t) + M(t) w`; the model derivative
`Lm t = (T σ, 0) + DΨ(x)(Lx t 0 (i τ, ν))` at `(σ, τ, ν)` is injective, uniformly in `t`.
-/

namespace FiniteEnergyPlane

namespace DGA1

open Metric Set Filter Topology
open scoped ContDiff Real

noncomputable section

variable {H : V 1 → ℝ}

/-- Symplectization coordinates. -/
def Ψ (H : V 1 → ℝ) (y : V 1) : ℝ × V 1 := (aCoord H y, proj H y)

lemma contDiffAt_Ψ (hH : IsStrictlyStarShapedLevel H) {y : V 1} (hy : y ≠ 0) :
    ContDiffAt ℝ ∞ (Ψ H) y :=
  (contDiffAt_aCoord_proj H hH y hy).1.prodMk (contDiffAt_aCoord_proj H hH y hy).2

lemma Ψ_exp_smul (hH : IsStrictlyStarShapedLevel H) (c : ℝ) {y : V 1} (hy : y ≠ 0) :
    Ψ H (Real.exp (2 * c) • y) = Ψ H y + (c, 0) := by
  obtain ⟨h1, h2⟩ := proj_aCoord_exp_smul H hH c y hy
  simp [Ψ, h1, h2]

lemma injective_fderiv_Ψ (hH : IsStrictlyStarShapedLevel H) {y : V 1} (hy : y ≠ 0) :
    Function.Injective (fderiv ℝ (Ψ H) y) := by
  have h := (injective_fderiv_aCoord_proj_comp_iff H hH (fun w : V 1 => w) y
    differentiableAt_id hy).2 (by rw [fderiv_id']; exact Function.injective_id)
  exact h

lemma fderiv_Ψ_radial (hH : IsStrictlyStarShapedLevel H) {y : V 1} (hy : y ≠ 0) :
    fderiv ℝ (Ψ H) y ((2 : ℝ) • y) = (1, 0) := by
  have hγ : HasDerivAt (fun c : ℝ => Real.exp (2 * c) • y) ((2 : ℝ) • y) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul 2).exp).smul_const y
    simpa using h
  have h1 : HasDerivAt (fun c : ℝ => Ψ H (Real.exp (2 * c) • y))
      (fderiv ℝ (Ψ H) y ((2 : ℝ) • y)) 0 := by
    have hd := ((contDiffAt_Ψ hH hy).differentiableAt (by simp)).hasFDerivAt
    have e : Real.exp (2 * 0) • y = y := by simp
    rw [← e] at hd
    have := hd.comp_hasDerivAt (0 : ℝ) hγ
    rwa [e] at this
  have h2 : HasDerivAt (fun c : ℝ => Ψ H (Real.exp (2 * c) • y)) ((1 : ℝ), (0 : V 1)) 0 := by
    have e : (fun c : ℝ => Ψ H (Real.exp (2 * c) • y)) = fun c => Ψ H y + (c, 0) :=
      funext fun c => Ψ_exp_smul hH c hy
    rw [e]
    have := ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : V 1))).const_add
      (Ψ H y)
    simpa using this
  exact h1.unique h2

variable (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)

/-- The model loop of the tube. -/
def gm (p : ℝ × ℂ) : V 1 := P.x (P.T * p.1) + M p.1 (cToVec p.2)

/-- `(t, w) ↦ (i t, w)`. -/
def emb0L : ℝ × ℂ →L[ℝ] ℂ × ℂ :=
  ((Complex.I • Complex.ofRealCLM).comp (ContinuousLinearMap.fst ℝ ℝ ℂ)).prod
    (ContinuousLinearMap.snd ℝ ℝ ℂ)

lemma emb0L_apply (p : ℝ × ℂ) : emb0L p = ((p.1 : ℂ) * Complex.I, p.2) := by
  simp [emb0L, mul_comm]

lemma gm_eq_Y : gm P M = fun p => SM.Y P M (emb0L p) := by
  funext p
  simp [gm, SM.Y, SM.mm, emb0L_apply]

variable (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}

include hH in
lemma hasFDerivAt_gm (hMc : ContDiff ℝ ∞ M) (t : ℝ) (w : ℂ) :
    HasFDerivAt (gm P M) ((SM.Lx H P M t w).comp emb0L) (t, w) := by
  rw [gm_eq_Y]
  have h := SM.hasFDerivAt_Y P M hH hMc t w
  have e : (((t : ℂ) * Complex.I, w) : ℂ × ℂ) = emb0L (t, w) := (emb0L_apply (t, w)).symm
  rw [e] at h
  exact h.comp (t, w) emb0L.hasFDerivAt

lemma gm_zero (t : ℝ) : gm P M (t, 0) = P.x (P.T * t) := by
  simp [gm, show cToVec (0 : ℂ) = 0 by ext i; rcases i with i | i <;> simp [cToVec]]

include hH in
lemma x_ne_zero (t : ℝ) : P.x (P.T * t) ≠ 0 := fas_ne_zero_of_mem hH (P.mem _)

/-- The model derivative at `(s, t, 0)`. -/
def Lm (t : ℝ) : ℝ × ℝ × ℂ →L[ℝ] ℝ × V 1 :=
  (P.T • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).prod 0 +
    ((fderiv ℝ (Ψ H) (P.x (P.T * t))).comp ((SM.Lx H P M t 0).comp emb0L)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))

include hH in
lemma Lm_apply (t : ℝ) (k : ℝ × ℝ × ℂ) :
    Lm P M t k = fderiv ℝ (Ψ H) (P.x (P.T * t))
      (SM.Lx H P M t 0 ((k.1 : ℂ) + (k.2.1 : ℂ) * Complex.I, k.2.2)) := by
  have hx := x_ne_zero P hH t
  have hsplit : (((k.1 : ℂ) + (k.2.1 : ℂ) * Complex.I, k.2.2) : ℂ × ℂ) =
      ((k.1 : ℂ), 0) + emb0L k.2 := by
    rw [emb0L_apply]; ext <;> simp
  have hr : SM.Lx H P M t 0 ((k.1 : ℂ), 0) = (P.T * k.1) • ((2 : ℝ) • P.x (P.T * t)) := by
    rw [SM.Lx_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero, SM.mm, map_zero]
    rw [show cToVec (0 : ℂ) = 0 by ext i; rcases i with i | i <;> simp [cToVec], map_zero,
      add_zero, smul_smul]
    congr 1
    ring
  rw [hsplit, map_add, map_add, hr, map_smul, fderiv_Ψ_radial hH hx]
  simp [Lm, smul_eq_mul]

include hH in
lemma Lm_injective (hM : IsUnitaryXiFrame J P M) (t : ℝ) : Function.Injective (Lm P M t) := by
  rw [injective_iff_map_eq_zero]
  intro k hk
  rw [Lm_apply P M hH] at hk
  have h1 := (injective_iff_map_eq_zero _).1 (injective_fderiv_Ψ hH (x_ne_zero P hH t)) _ hk
  have h2 := (injective_iff_map_eq_zero _).1 (SM.Lx_zero_injective hH P hM t) _ h1
  have h3 := Prod.mk_eq_zero.1 h2
  have hre := congrArg Complex.re h3.1
  have him := congrArg Complex.im h3.1
  simp at hre him
  exact Prod.ext hre (Prod.ext him h3.2)

include hH in
lemma continuous_Lm (hMc : ContDiff ℝ ∞ M) : Continuous (Lm P M) := by
  have hx : Continuous (fun t : ℝ => P.x (P.T * t)) := (SM.contDiff_x P hH).continuous
  have hΨ : Continuous (fun t : ℝ => fderiv ℝ (Ψ H) (P.x (P.T * t))) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hc := (contDiffAt_Ψ hH (x_ne_zero P hH t)).fderiv_right (m := ∞) (by simp)
    exact ContinuousAt.comp (f := fun t : ℝ => P.x (P.T * t)) (x := t) hc.continuousAt
      hx.continuousAt
  have hL : Continuous (fun t : ℝ => SM.Lx H P M t 0) :=
    Continuous.comp (g := fun p : ℝ × ℂ => SM.Lx H P M p.1 p.2) (f := fun t : ℝ => (t, (0 : ℂ)))
      (SM.contDiff_Lx hH P M hMc).continuous (continuous_id.prodMk continuous_const)
  have e : Lm P M = fun t => (P.T • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).prod 0 +
      ((fderiv ℝ (Ψ H) (P.x (P.T * t))).comp ((SM.Lx H P M t 0).comp emb0L)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)) := rfl
  rw [e]
  refine continuous_const.add ?_
  refine Continuous.clm_comp ?_ continuous_const
  exact hΨ.clm_comp (hL.clm_comp continuous_const)

lemma Lm_periodic (hM : IsUnitaryXiFrame J P M) (t : ℝ) : Lm P M (t + 1) = Lm P M t := by
  have hx : P.x (P.T * (t + 1)) = P.x (P.T * t) := by rw [mul_add, mul_one, P.periodic]
  simp only [Lm, hx, SM.Lx_periodic P M hM]

include hH in
/-- Uniform lower bound for the model derivative. -/
lemma exists_Lm_lower (hM : IsUnitaryXiFrame J P M) :
    ∃ m > 0, ∀ (t : ℝ) (k : ℝ × ℝ × ℂ), m * ‖k‖ ≤ ‖Lm P M t k‖ := by
  have hMc : ContDiff ℝ ∞ M := hM.1
  set K : Set (ℝ × (ℝ × ℝ × ℂ)) := Icc (0 : ℝ) 1 ×ˢ sphere (0 : ℝ × ℝ × ℂ) 1
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_sphere _ _)
  have hne : K.Nonempty := by
    refine ⟨(0, (1, 0, 0)), ⟨left_mem_Icc.2 zero_le_one, ?_⟩⟩
    simp
  have hcont : ContinuousOn (fun p : ℝ × (ℝ × ℝ × ℂ) => ‖Lm P M p.1 p.2‖) K :=
    (((continuous_Lm P M hH hMc).comp continuous_fst).clm_apply continuous_snd).norm.continuousOn
  obtain ⟨⟨t₀, k₀⟩, hmem, hmin⟩ := hK.exists_isMinOn hne hcont
  have hk₀ : k₀ ≠ 0 := by
    intro h
    have := hmem.2
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  have hm : 0 < ‖Lm P M t₀ k₀‖ :=
    norm_pos_iff.2 fun h => hk₀ ((injective_iff_map_eq_zero _).1 (Lm_injective P M hH hM t₀) _ h)
  refine ⟨‖Lm P M t₀ k₀‖, hm, fun t k => ?_⟩
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hper : Function.Periodic (Lm P M) 1 := Lm_periodic P M hM
  have ht : Lm P M t = Lm P M (Int.fract t) := by
    have := hper.sub_int_mul_eq (x := t) ⌊t⌋
    simp only [mul_one] at this
    rw [Int.self_sub_floor] at this
    exact this.symm
  have hkn : 0 < ‖k‖ := norm_pos_iff.2 hk
  have hin : (Int.fract t, ‖k‖⁻¹ • k) ∈ K := by
    refine ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hkn.ne']
  have h : ‖Lm P M t₀ k₀‖ ≤ ‖k‖⁻¹ * ‖Lm P M (Int.fract t) k‖ := by
    have := isMinOn_iff.1 hmin _ hin
    simpa [map_smul, norm_smul] using this
  rw [ht]
  calc ‖Lm P M t₀ k₀‖ * ‖k‖ ≤ (‖k‖⁻¹ * ‖Lm P M (Int.fract t) k‖) * ‖k‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖Lm P M (Int.fract t) k‖ := by field_simp

end

end DGA1

end FiniteEnergyPlane

/-!
# A1, instance part 2: decay to the model and the far lower bound of `DF(ζ, 0)`
-/

namespace FiniteEnergyPlane

namespace DGA1

open Metric Set Filter Topology
open scoped ContDiff Real

noncomputable section

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)

include hH in
lemma contDiff_gm (hMc : ContDiff ℝ ∞ M) : ContDiff ℝ ∞ (gm P M) := by
  rw [gm_eq_Y]
  exact (SM.contDiff_Y P M hH hMc).comp emb0L.contDiff

lemma gm_periodic (hM : IsUnitaryXiFrame J P M) (t : ℝ) (w : ℂ) :
    gm P M (t + 1, w) = gm P M (t, w) := by
  simp only [gm, mul_add, mul_one, P.periodic, hM.2.1 t]

variable (u : ℂ → V 1) (N : ℂ → ℂ →L[ℝ] V 1)

/-- The rescaled tube map. -/
def fr (d : ℝ) (q : ℝ × ℝ × ℂ) : V 1 :=
  Real.exp (-(2 * (P.T * q.1 + d))) • (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2)

/-- The deviation from the model. -/
def Ed (d : ℝ) (q : ℝ × ℝ × ℂ) : ℝ × V 1 :=
  Ψ H (fr P u N d q) - Ψ H (gm P M (q.2.1, q.2.2))

include hH in
lemma Ed_decay (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ) (hg : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → gm P M (t, w) ≠ 0) :
    ExpDecayCInftyTube (Ed P M u N d) ρ b := by
  have h3 := expDecayCInftyTube_rescaled_sub_model H hH P u hu0 d b hb ha hw N M hNM ρ hρ
  exact expDecayCInftyTube_comp_sub (Ψ H) {y : V 1 | y ≠ 0} isOpen_ne
    (fun y hy => (contDiffAt_Ψ hH hy).contDiffWithinAt) ρ b hρ hb (gm P M)
    (contDiff_gm hH P M hM.1).contDiffOn (gm_periodic P M hM) hg (fr P u N d) h3

/-- The tube map in symplectization coordinates. -/
def Ft (H : V 1 → ℝ) (u : ℂ → V 1) (N : ℂ → ℂ →L[ℝ] V 1) (p : ℂ × ℂ) : ℝ × V 1 :=
  Ψ H (u p.1 + N p.1 p.2)

/-- The model in the cylinder chart. -/
def Gm (d : ℝ) (q : ℝ × ℝ × ℂ) : ℝ × V 1 := Ψ H (gm P M (q.2.1, q.2.2)) + (P.T * q.1 + d, 0)

include hH in
lemma Ft_Pc (d : ℝ) (q : ℝ × ℝ × ℂ) (h0 : u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2 ≠ 0) :
    Ft H u N (XT.Pc q) = Gm P M d q + Ed P M u N d q := by
  have hf : fr P u N d q ≠ 0 := smul_ne_zero (Real.exp_pos _).ne' h0
  have e2 : Real.exp (2 * (P.T * q.1 + d)) • fr P u N d q =
      u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2 := by
    simp only [fr, smul_smul, ← Real.exp_add]
    rw [show 2 * (P.T * q.1 + d) + -(2 * (P.T * q.1 + d)) = 0 by ring, Real.exp_zero, one_smul]
  have e := Ψ_exp_smul hH (P.T * q.1 + d) hf
  rw [e2] at e
  simp only [Ft, XT.Pc, Gm, Ed, e]
  abel

include hH in
lemma hasFDerivAt_Gm (hMc : ContDiff ℝ ∞ M) (d s t : ℝ) :
    HasFDerivAt (Gm P M d) (Lm P M t) (s, t, 0) := by
  have hg := hasFDerivAt_gm P M hH hMc t 0
  have hΨ := ((contDiffAt_Ψ hH (x_ne_zero P hH t)).differentiableAt (by simp)).hasFDerivAt
  rw [← gm_zero P M t] at hΨ
  have h1 : HasFDerivAt (fun q : ℝ × ℝ × ℂ => Ψ H (gm P M (q.2.1, q.2.2)))
      (((fderiv ℝ (Ψ H) (P.x (P.T * t))).comp ((SM.Lx H P M t 0).comp emb0L)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))) (s, t, 0) := by
    have := (hΨ.comp (t, (0 : ℂ)) hg).comp (s, t, (0 : ℂ))
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)).hasFDerivAt (x := ((s, t, (0 : ℂ)) : ℝ × ℝ × ℂ)))
    rw [gm_zero] at this
    exact this
  have h2 : HasFDerivAt (fun q : ℝ × ℝ × ℂ => ((P.T * q.1 + d, 0) : ℝ × V 1))
      ((P.T • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).prod 0) (s, t, 0) := by
    have := (((P.T • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).prod
      (0 : ℝ × ℝ × ℂ →L[ℝ] V 1)).hasFDerivAt (x := (s, t, (0 : ℂ)))).add_const
      ((d, 0) : ℝ × V 1)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    simp [smul_eq_mul]
  have h3 := h1.add h2
  have e : Gm P M d = fun q : ℝ × ℝ × ℂ =>
      Ψ H (gm P M (q.2.1, q.2.2)) + ((P.T * q.1 + d, 0) : ℝ × V 1) := rfl
  rw [e]
  refine h3.congr_fderiv ?_
  show _ = Lm P M t
  unfold Lm
  exact add_comm _ _

lemma norm_hsol_ge {ζ : ℂ} (hζ : ζ ≠ 0) (Δ o : ℂ) :
    (‖Δ‖ / (1 + ‖ζ‖) + ‖o‖) / (6 * π) ≤ ‖XT.hsol ζ Δ o‖ := by
  set x : ℂ := Δ / (((2 * π : ℝ) : ℂ) * ζ) with hx
  have hk1 : |x.re| ≤ ‖XT.hsol ζ Δ o‖ := by
    have := norm_fst_le (XT.hsol ζ Δ o)
    simpa [XT.hsol, hx] using this
  have hk2 : |x.im| ≤ ‖XT.hsol ζ Δ o‖ := by
    have := (norm_fst_le (XT.hsol ζ Δ o).2).trans (norm_snd_le (XT.hsol ζ Δ o))
    simpa [XT.hsol, hx] using this
  have hk3 : ‖o‖ ≤ ‖XT.hsol ζ Δ o‖ := by
    have := (norm_snd_le (XT.hsol ζ Δ o).2).trans (norm_snd_le (XT.hsol ζ Δ o))
    simpa [XT.hsol] using this
  have hxn : ‖x‖ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
  have hζn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  have hpi : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have hxe : ‖x‖ = ‖Δ‖ / (2 * π * ‖ζ‖) := by
    rw [hx, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have h1 : ‖Δ‖ / (1 + ‖ζ‖) ≤ 2 * π * ‖x‖ := by
    rw [hxe, mul_div_assoc', mul_div_mul_left _ _ (by positivity : (2 * π : ℝ) ≠ 0)]
    · exact div_le_div_of_nonneg_left (norm_nonneg _) hζn (by linarith)
  have h2 : ‖o‖ ≤ 2 * π * ‖o‖ := le_mul_of_one_le_left (norm_nonneg _) hpi
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg x, norm_nonneg o]

end

end DGA1

end FiniteEnergyPlane

/-!
# A1, instance part 3: the uniform weighted lower bound of `DF(ζ, 0)`
-/

namespace FiniteEnergyPlane

namespace DGA1

open Metric Set Filter Topology
open scoped ContDiff Real

noncomputable section

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (P : ReebOrbit H) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
  (u : ℂ → V 1) (N : ℂ → ℂ →L[ℝ] V 1)

lemma gm_eq_mm (t : ℝ) (w : ℂ) : gm P M (t, w) = SM.mm P M t w := by simp [gm, SM.mm]

include hH in
lemma contDiffOn_Ft (hu : ContDiff ℝ ∞ u) (hN : ContDiff ℝ ∞ N) (ρ : ℝ)
    (h0 : ∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0) :
    ContDiffOn ℝ ∞ (Ft H u N) ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ) := by
  have hΦ : ContDiff ℝ ∞ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) :=
    (hu.comp contDiff_fst).add ((hN.comp contDiff_fst).clm_apply contDiff_snd)
  intro p hp
  exact ((contDiffAt_Ψ hH (h0 p hp)).comp p hΦ.contDiffAt).contDiffWithinAt

include hH in
/-- Far part: the cylinder-chart derivative is bounded below. -/
lemma far_lower (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (hN : ContDiff ℝ ∞ N) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (h0 : ∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0)
    (hg : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → gm P M (t, w) ≠ 0) :
    ∃ m > 0, ∃ S : ℝ, ∀ s ≥ S, ∀ (t : ℝ) (k : ℝ × ℝ × ℂ),
      m * ‖k‖ ≤ ‖fderiv ℝ (Ft H u N) (cylInf s t, 0) (XT.Lc (s, t, 0) k)‖ := by
  have hMc : ContDiff ℝ ∞ M := hM.1
  obtain ⟨m, hm, hLm⟩ := exists_Lm_lower P M hH hM
  obtain ⟨⟨s₀, hs₀⟩, hdec⟩ := Ed_decay hH P M u N hu0 d b hb ha hw hM hNM ρ hρ hg
  obtain ⟨C₁, s₁, hC₁⟩ := hdec 1
  obtain ⟨S₁, hS₁⟩ := SME.eventually_const_mul_exp_lt C₁ b (m / 2) hb (by positivity)
  have hF := contDiffOn_Ft hH u N hu hN ρ h0
  refine ⟨m / 2, by positivity, max (max S₁ s₁) (s₀ + 1), fun s hs t k => ?_⟩
  have hsS : s ≥ S₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs1 : s ≥ s₁ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs0 : s₀ < s := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hs)
  set q : ℝ × ℝ × ℂ := (s, t, 0) with hq
  have hq0 : q.2.2 ∈ ball (0 : ℂ) ρ := by simp [hq, hρ]
  -- the chart derivative
  have hchart := XT.hasFDerivAt_comp_Pc hF hq0
  -- the decomposition near `q`
  have hO : {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} ∈ 𝓝 q := (XT.isOpen_tube ρ).mem_nhds hq0
  have hev : (fun q => Ft H u N (XT.Pc q)) =ᶠ[𝓝 q] fun q => Gm P M d q + Ed P M u N d q :=
    Filter.eventually_of_mem hO fun q' hq' => Ft_Pc hH P M u N d q' (h0 (cylInf q'.1 q'.2.1, q'.2.2) ⟨Set.mem_univ _, (show q'.2.2 ∈ ball (0 : ℂ) ρ from hq')⟩)
  have hEo : IsOpen (Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_Ioi.prod (isOpen_univ.prod isOpen_ball)
  have hEd : DifferentiableAt ℝ (Ed P M u N d) q :=
    ((hs₀.contDiffAt (hEo.mem_nhds (by
      refine ⟨?_, Set.mem_univ _, ?_⟩ <;> simp [hq, hρ, hs0]))).differentiableAt
      (by simp))
  have hsum : HasFDerivAt (fun q => Gm P M d q + Ed P M u N d q)
      (Lm P M t + fderiv ℝ (Ed P M u N d) q) q :=
    (hasFDerivAt_Gm hH P M hMc d s t).add hEd.hasFDerivAt
  have heq : (fderiv ℝ (Ft H u N) (XT.Pc q)).comp (XT.Lc q) = Lm P M t + fderiv ℝ (Ed P M u N d) q :=
    hchart.unique (hsum.congr_of_eventuallyEq hev)
  have hbd : ‖fderiv ℝ (Ed P M u N d) q‖ ≤ C₁ * Real.exp (-(b * s)) := by
    have := hC₁ s hs1 t 0 (by simp [hρ])
    rwa [norm_iteratedFDeriv_one] at this
  have hlt := hS₁ s hsS
  have hk : fderiv ℝ (Ft H u N) (cylInf s t, 0) (XT.Lc (s, t, 0) k) =
      Lm P M t k + fderiv ℝ (Ed P M u N d) q k := by
    have := congrArg (fun L => L k) heq
    simpa [XT.Pc, hq] using this
  rw [hk]
  have h1 := hLm t k
  have h2 : ‖fderiv ℝ (Ed P M u N d) q k‖ ≤ m / 2 * ‖k‖ :=
    ((fderiv ℝ (Ed P M u N d) q).le_opNorm k).trans
      (mul_le_mul_of_nonneg_right (hbd.trans hlt.le) (norm_nonneg _))
  have h3 := norm_sub_norm_le (Lm P M t k) (-(fderiv ℝ (Ed P M u N d) q k))
  rw [norm_neg, sub_neg_eq_add] at h3
  linarith

include hH in
/-- The uniform weighted lower bound of `DF(ζ, 0)`. -/
theorem exists_lower_fderiv_Ft (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ c₁ > 0, ∀ (ζ : ℂ) (h : ℂ × ℂ),
      c₁ * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) ≤ ‖fderiv ℝ (Ft H u N) (ζ, 0) h‖ := by
  have hMc : ContDiff ℝ ∞ M := hM.1
  obtain ⟨ρS, hρS, htube⟩ :=
    exists_ball_tubeMap_ne_zero_injective H hH J P u hu hu0 d b hb ha hw N hN hNinj M hM hNM
  obtain ⟨ρ₁, hρ₁, hgood⟩ := SM.goodSet_tube hH P M hM hMc
  set ρ : ℝ := min ρS ρ₁ / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρS' : ρ < ρS := by
    have := min_le_left ρS ρ₁; rw [hρdef]; linarith
  have hρ₁' : ρ < ρ₁ := by
    have := min_le_right ρS ρ₁; rw [hρdef]; linarith
  have h0 : ∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 := fun p hp =>
    (htube p ⟨Set.mem_univ _, ball_subset_ball hρS'.le hp.2⟩).1
  have hg : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → gm P M (t, w) ≠ 0 := fun t w hw => by
    rw [gm_eq_mm]
    exact (hgood t w (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ₁')).1
  obtain ⟨m, hm, S, hfar⟩ := far_lower hH P M u N hu hu0 d b hb ha hw hN hM hNM ρ hρ h0 hg
  have hF := contDiffOn_Ft hH u N hu hN ρ h0
  -- compact part
  set R := Real.exp (2 * π * S) with hR
  have hRpos : 0 < R := Real.exp_pos _
  set K : Set (ℂ × (ℂ × ℂ)) := closedBall (0 : ℂ) R ×ˢ sphere (0 : ℂ × ℂ) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hne : K.Nonempty := ⟨(0, (1, 0)), by simp [K, hRpos.le]⟩
  have hdF : ContinuousOn (fderiv ℝ (Ft H u N)) ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ) :=
    hF.continuousOn_fderiv_of_isOpen (isOpen_univ.prod isOpen_ball) (by simp)
  have hcont : ContinuousOn (fun p : ℂ × (ℂ × ℂ) => ‖fderiv ℝ (Ft H u N) (p.1, 0) p.2‖) K := by
    have hc : Continuous (fun p : ℂ × (ℂ × ℂ) => fderiv ℝ (Ft H u N) (p.1, 0)) := by
      have : Continuous (fun ζ : ℂ => fderiv ℝ (Ft H u N) (ζ, 0)) :=
        hdF.comp_continuous (continuous_id.prodMk continuous_const)
          (fun ζ => ⟨Set.mem_univ _, by simp [hρ]⟩)
      exact this.comp continuous_fst
    exact (hc.clm_apply continuous_snd).norm.continuousOn
  obtain ⟨⟨ζ₀, h₀⟩, hmem, hmin⟩ := hK.exists_isMinOn hne hcont
  have hinj : ∀ ζ : ℂ, Function.Injective (fderiv ℝ (Ft H u N) (ζ, 0)) := by
    intro ζ
    have hp : ((ζ, 0) : ℂ × ℂ) ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρS := ⟨Set.mem_univ _, by simp [hρS]⟩
    have hΦ : ContDiff ℝ ∞ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) :=
      (hu.comp contDiff_fst).add ((hN.comp contDiff_fst).clm_apply contDiff_snd)
    exact (injective_fderiv_aCoord_proj_comp_iff H hH (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (ζ, 0)
      (hΦ.differentiable (by simp) _) (htube _ hp).1).2 (htube _ hp).2
  have hh₀ : h₀ ≠ 0 := by
    intro h
    have := hmem.2
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  set m₂ := ‖fderiv ℝ (Ft H u N) (ζ₀, 0) h₀‖
  have hm₂ : 0 < m₂ := norm_pos_iff.2 fun h => hh₀ ((injective_iff_map_eq_zero _).1 (hinj ζ₀) _ h)
  refine ⟨min (m / (6 * π)) (m₂ / 2), lt_min (by positivity) (by positivity), fun ζ h => ?_⟩
  have hW0 : 0 ≤ ‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖ := by positivity
  rcases le_or_gt ‖ζ‖ R with hζ | hζ
  · -- compact part
    have hW : ‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖ ≤ 2 * ‖h‖ := by
      have k1 : ‖h.1‖ / (1 + ‖ζ‖) ≤ ‖h.1‖ :=
        div_le_self (norm_nonneg _) (by linarith [norm_nonneg ζ])
      have := norm_fst_le h
      have := norm_snd_le h
      linarith
    have hlow : m₂ * ‖h‖ ≤ ‖fderiv ℝ (Ft H u N) (ζ, 0) h‖ := by
      rcases eq_or_ne h 0 with rfl | hh
      · simp
      have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
      have hin : (ζ, ‖h‖⁻¹ • h) ∈ K := by
        refine ⟨mem_closedBall_zero_iff.2 hζ, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hhn.ne']
      have hle : m₂ ≤ ‖h‖⁻¹ * ‖fderiv ℝ (Ft H u N) (ζ, 0) h‖ := by
        have := isMinOn_iff.1 hmin _ hin
        simpa [map_smul, norm_smul] using this
      calc m₂ * ‖h‖ ≤ (‖h‖⁻¹ * ‖fderiv ℝ (Ft H u N) (ζ, 0) h‖) * ‖h‖ :=
            mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ = ‖fderiv ℝ (Ft H u N) (ζ, 0) h‖ := by field_simp
    calc min (m / (6 * π)) (m₂ / 2) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)
        ≤ m₂ / 2 * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hW0
      _ ≤ m₂ / 2 * (2 * ‖h‖) := mul_le_mul_of_nonneg_left hW (by positivity)
      _ = m₂ * ‖h‖ := by ring
      _ ≤ _ := hlow
  · -- far part
    obtain ⟨s, hs, t, hst⟩ := SME.exists_cylInf_of_lt S ζ hζ
    have hζ0 : ζ ≠ 0 := by
      intro h0'
      rw [h0', norm_zero] at hζ
      exact absurd hζ (not_lt.2 hRpos.le)
    have hk := hfar s hs t (XT.hsol ζ h.1 h.2)
    have hL : XT.Lc (s, t, 0) (XT.hsol ζ h.1 h.2) = h := by
      rw [XT.Lc_apply, XT.lc_hsol hζ0]
      simp only [hst]
      ext
      · simp only; field_simp
      · simp [XT.hsol]
    rw [hL, hst] at hk
    have hsol := norm_hsol_ge hζ0 h.1 h.2
    calc min (m / (6 * π)) (m₂ / 2) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)
        ≤ m / (6 * π) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hW0
      _ = m * ((‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) / (6 * π)) := by ring
      _ ≤ m * ‖XT.hsol ζ h.1 h.2‖ := mul_le_mul_of_nonneg_left hsol hm.le
      _ ≤ _ := hk

end

end DGA1

end FiniteEnergyPlane

/-!
# A1 `exists_mul_le_tubeMap_of_mul_le`: assembly
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_mul_le_tubeMap_of_mul_le_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hslice : ∀ z z' : ℂ, c₀ * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) *
      (|aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖)) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∃ c > 0, ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖ := by
  have hMc : ContDiff ℝ ∞ M := hM.1
  obtain ⟨ρS, hρS, htube⟩ :=
    exists_ball_tubeMap_ne_zero_injective H hH J P u hu hu0 d b hb ha hw N hN hNinj M hM hNM
  obtain ⟨ρ₁, hρ₁, hgood⟩ := SM.goodSet_tube hH P M hM hMc
  set ρm : ℝ := min ρS ρ₁ / 2 with hρdef
  have hρm : 0 < ρm := by positivity
  have hρS' : ρm < ρS := by
    have := min_le_left ρS ρ₁; rw [hρdef]; linarith
  have hρ₁' : ρm < ρ₁ := by
    have := min_le_right ρS ρ₁; rw [hρdef]; linarith
  have h0 : ∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρm, u p.1 + N p.1 p.2 ≠ 0 := fun p hp =>
    (htube p ⟨Set.mem_univ _, ball_subset_ball hρS'.le hp.2⟩).1
  have hg : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρm → DGA1.gm P M (t, w) ≠ 0 :=
    fun t w hw => by
      rw [DGA1.gm_eq_mm]
      exact (hgood t w (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ₁')).1
  have hF := DGA1.contDiffOn_Ft hH u N hu hN ρm h0
  have hdecE := DGA1.Ed_decay hH P M u N hu0 d b hb ha hw hM hNM ρm hρm hg
  set Mm : ℝ × ℂ → ℝ × V 1 := fun p => DGA1.Ψ H (DGA1.gm P M p) + (d, 0) with hMmdef
  have hMm : ContDiffOn ℝ ∞ Mm ((Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρm) := by
    intro p hp
    have hp0 : DGA1.gm P M p ≠ 0 := hg p.1 p.2 (ball_subset_closedBall hp.2)
    exact (((DGA1.contDiffAt_Ψ hH hp0).comp p
      (DGA1.contDiff_gm hH P M hMc).contDiffAt).add contDiffAt_const).contDiffWithinAt
  have hMper : ∀ (t : ℝ) (w : ℂ), Mm (t + 1, w) = Mm (t, w) := fun t w => by
    simp only [hMmdef, DGA1.gm_periodic P M hM]
  have hdec : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      DGA1.Ft H u N (cylInf q.1 q.2.1, q.2.2) - q.1 • ((P.T, 0) : ℝ × V 1) - Mm (q.2.1, q.2.2))
      ρm b := by
    refine SMF.expDecayCInftyTube_congr hdecE fun q hq => ?_
    have e := DGA1.Ft_Pc hH P M u N d q (h0 (cylInf q.1 q.2.1, q.2.2) ⟨Set.mem_univ _, hq⟩)
    simp only [XT.Pc] at e
    rw [e]
    simp only [DGA1.Gm, hMmdef]
    ext
    · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      ring
    · simp
  obtain ⟨C, hC⟩ := exists_cylindrical_bounds_of_expDecayCInftyTube ρm b (ρm / 2) hb
    (by positivity) (by linarith) (DGA1.Ft H u N) hF ((P.T, 0) : ℝ × V 1) Mm hMm hMper hdec
  obtain ⟨c₁, hc₁, hlow⟩ :=
    DGA1.exists_lower_fderiv_Ft hH P M u N hu hu0 d b hb ha hw hN hNinj hM hNM
  have hFz : ∀ z : ℂ, DGA1.Ft H u N (z, 0) = (aCoord H (u z), proj H (u z)) := fun z => by
    simp [DGA1.Ft, DGA1.Ψ]
  have hslice' : ∀ z z' : ℂ, c₀ / 2 * (‖z - z'‖ / (1 + ‖z‖ + ‖z'‖)) ≤
      ‖DGA1.Ft H u N (z, 0) - DGA1.Ft H u N (z', 0)‖ := by
    intro z z'
    rw [hFz, hFz, Prod.mk_sub_mk, Prod.norm_def, Real.norm_eq_abs]
    set A := |aCoord H (u z) - aCoord H (u z')|
    set B := ‖proj H (u z) - proj H (u z')‖
    have hAB : A + B ≤ 2 * max A B := by
      have := le_max_left A B; have := le_max_right A B; linarith
    have hS : 0 < 1 + ‖z‖ + ‖z'‖ := by positivity
    have e : c₀ / 2 * (‖z - z'‖ / (1 + ‖z‖ + ‖z'‖)) = c₀ * ‖z - z'‖ / (2 * (1 + ‖z‖ + ‖z'‖)) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h1 := hslice z z'
    have h2 := mul_le_mul_of_nonneg_left hAB hS.le
    linarith
  obtain ⟨ρ, hρ, c, hc, hmain⟩ := exists_mul_le_norm_sub_of_cylBounds (DGA1.Ft H u N) ρm (ρm / 2)
    (by positivity) (by linarith) hF C (fun ζ w hw h => (hC ζ w hw).1 h)
    (fun ζ w hw h k => (hC ζ w hw).2 h k) (c₀ / 2) (by positivity) hslice' c₁ hc₁ hlow
  refine ⟨ρ, hρ, c, hc, fun p hp q hq => (hmain p hp q hq).trans ?_⟩
  show ‖(aCoord H (u p.1 + N p.1 p.2), proj H (u p.1 + N p.1 p.2)) -
      (aCoord H (u q.1 + N q.1 q.2), proj H (u q.1 + N q.1 q.2))‖ ≤ _
  rw [Prod.mk_sub_mk, Prod.norm_def, Real.norm_eq_abs]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hslice : ∀ z z' : ℂ, c₀ * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) *
      (|aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖)) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∃ c > 0, ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖ :=
  exists_mul_le_tubeMap_of_mul_le_aux H hH J hJ P u hu hu0 c₀ hc₀ hslice d b hb ha hw N hN hNinj M hM hNM
