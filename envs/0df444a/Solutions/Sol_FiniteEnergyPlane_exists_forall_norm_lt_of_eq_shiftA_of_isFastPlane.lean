-- Prove2me | solution 1 for FiniteEnergyPlane.exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T23:49:36.92344+00:00
-- url     : https://prove2.me/submissions/ad4b0a44-6d03-4100-8326-35a761efd46f

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
import Theorems.Thm_FiniteEnergyPlane_isAsymptoticEigen_apply_ne_zero
import Theorems.Thm_FiniteEnergyPlane_exists_eq_add_int_mul_of_proj_add_eq_of_isPrime
import Theorems.Thm_FiniteEnergyPlane_isAsymptoticEigen_eq_smul_of_apply_eq_smul
import Theorems.Thm_FiniteEnergyPlane_exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_isBounded_preimage_proj_of_isNondegenerateEnd

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
# Distance to the orbit along an end with an asymptotic eigenvector

`w = proj (x(τ) + h)` with `‖h‖ ≤ (sup ‖v‖ + 1) e^{εμs}`; `proj` fixes `S` and is Lipschitz on a
uniform neighbourhood of the compact `S`, so `dist(w, x(τ)) ≤ D ‖h‖`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma idp_proj_of_mem {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : x ∈ energySurface H) : proj H x = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx
    simp at this
  have hx1 : H ((1 : ℝ) • x) = 1 := by rw [one_smul]; exact hx
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := ⟨1, one_pos, hx1⟩
  have hs : scaleToS H x = 1 := by
    unfold scaleToS
    rw [dif_pos hex]
    exact (hH.2.1 x hx0).unique (Classical.choose_spec hex) ⟨one_pos, hx1⟩
  simp [proj, hs]

lemma idp_ne_zero_of_mem {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : x ∈ energySurface H) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

theorem infDist_endW_le_of_hasAsymptoticEigenvector_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε μ : ℝ) (v : ℝ → V n)
    (hv : HasAsymptoticEigenvector H J u e P ε μ v) :
    ∃ C s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ,
      infDist (endW H u e (s, t)) (Set.range P.x) ≤ C * Real.exp (ε * μ * s) := by
  obtain ⟨hev, hεμ, c, τ, r, s₀, -, hr, hform⟩ := hv
  -- `v` is bounded
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1
    (hev.1.2.1.compact_of_continuous one_ne_zero hev.1.1.continuous).isBounded
  have hMv : ∀ y, ‖v y‖ ≤ M := fun y => hM _ ⟨y, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMv 0)
  -- `r` is eventually small
  obtain ⟨s₁, hs₁⟩ := hr.2 0 1 one_pos
  have hrb : ∀ s ≥ s₁, ∀ t, ‖r (s, t)‖ ≤ 1 := fun s hs t => by
    have := hs₁ s hs t
    rwa [norm_iteratedFDeriv_zero] at this
  -- `proj` is Lipschitz near `S`
  have hO : IsOpen {y : V n | y ≠ 0} := isOpen_ne
  have hf : ContDiffOn ℝ 1 (proj H) {y : V n | y ≠ 0} := fun y hy =>
    ((contDiffAt_aCoord_proj H hH y hy).2.of_le (by exact_mod_cast le_top)).contDiffWithinAt
  obtain ⟨δ₀, hδ₀, D, hD, hK⟩ := exists_lipschitz_near_compact hO hf
    (isCompact_energySurface H hH) (fun x hx => idp_ne_zero_of_mem H hH hx)
  -- `e^{εμs}` is eventually small
  have hlim : Tendsto (fun s : ℝ => Real.exp (ε * μ * s)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hεμ)
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1
    ((tendsto_order.1 hlim).2 (δ₀ / (M + 1)) (by positivity))
  refine ⟨D * (M + 1), max s₀ (max s₁ s₂), fun s hs t => ?_⟩
  have hs0 : s₀ ≤ s := le_trans (le_max_left _ _) hs
  have hs1 : s₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs2 : s₂ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  obtain ⟨-, heq⟩ := hform s hs0 t
  set h : V n := Real.exp (ε * μ * s) • (v (τ (s, t) / P.T) + r (s, t)) with hh
  have hhn : ‖h‖ ≤ Real.exp (ε * μ * s) * (M + 1) := by
    rw [hh, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hMv _) (hrb s hs1 t)))
      (Real.exp_pos _).le
  have hhδ : ‖h‖ ≤ δ₀ := by
    have h2 := (hs₂ s hs2).le
    have hM1 : 0 < M + 1 := by linarith
    calc ‖h‖ ≤ Real.exp (ε * μ * s) * (M + 1) := hhn
      _ ≤ δ₀ / (M + 1) * (M + 1) := mul_le_mul_of_nonneg_right h2 hM1.le
      _ = δ₀ := div_mul_cancel₀ _ hM1.ne'
  have hxS : P.x (τ (s, t)) ∈ energySurface H := P.mem _
  obtain ⟨-, hLip⟩ := hK _ hxS
  have hy : P.x (τ (s, t)) + h ∈ closedBall (P.x (τ (s, t))) δ₀ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hhδ
  have hLip' := (hLip _ hy).2 _ (mem_closedBall_self hδ₀.le)
  rw [idp_proj_of_mem H hH hxS, add_sub_cancel_left] at hLip'
  calc infDist (endW H u e (s, t)) (Set.range P.x)
      ≤ dist (endW H u e (s, t)) (P.x (τ (s, t))) := infDist_le_dist_of_mem ⟨_, rfl⟩
    _ = ‖proj H (P.x (τ (s, t)) + h) - P.x (τ (s, t))‖ := by rw [heq, dist_eq_norm]
    _ ≤ D * ‖h‖ := hLip'
    _ ≤ D * (Real.exp (ε * μ * s) * (M + 1)) := mul_le_mul_of_nonneg_left hhn hD
    _ = D * (M + 1) * Real.exp (ε * μ * s) := by ring

end FiniteEnergyPlane



/-!
# Far-field child, layer 2: the eigenvector relation at far coincidences

If `endW u (s, t) = endW v (s', t')` with `s, s'` large, the tube representations of both ends
agree (global tube injectivity), so the leading eigenvectors satisfy
`e₁(σ) + R₁ = e^{μ₂ s' - μ₁ s} (e₂(σ) + R₂)` with small remainders.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem rdf_rel (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (P : ReebOrbit H) (hP : P.IsPrime) (u v : ℂ → V 1) {μ₁ μ₂ : ℝ} {e₁ e₂ : ℝ → V 1}
    (hA₁ : HasAsymptoticEigenvector H J u cylInf P 1 μ₁ e₁)
    (hA₂ : HasAsymptoticEigenvector H J v cylInf P 1 μ₂ e₂) :
    ∀ η > 0, ∃ S : ℝ, ∀ s s' t t' : ℝ, S ≤ s → S ≤ s' →
      endW H u cylInf (s, t) = endW H v cylInf (s', t') →
      ∃ (σ : ℝ) (R₁ R₂ : V 1), ‖R₁‖ ≤ η ∧ ‖R₂‖ ≤ η ∧
        e₁ σ + R₁ = Real.exp (μ₂ * s' - μ₁ * s) • (e₂ σ + R₂) := by
  intro η hη
  obtain ⟨he₁, hμ₁, c₁, τ₁, r₁, s₁, -, hr₁, hrep₁⟩ := hA₁
  obtain ⟨he₂, hμ₂, c₂, τ₂, r₂, s₂, -, hr₂, hrep₂⟩ := hA₂
  have hμ₁' : μ₁ < 0 := by linarith
  have hμ₂' : μ₂ < 0 := by linarith
  have hT := P.T_pos
  obtain ⟨ρT, hρT, htube⟩ := exists_eq_add_int_mul_of_proj_add_eq_of_isPrime H hH P hP
  -- bounds on the eigenvectors
  have hbd : ∀ {μ : ℝ} {e : ℝ → V 1}, IsAsymptoticEigen J P μ e → ∃ M, ∀ θ, ‖e θ‖ ≤ M := by
    intro μ e he
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1
      (he.1.2.1.compact_of_continuous one_ne_zero he.1.1.continuous).isBounded
    exact ⟨M, fun y => hM _ ⟨y, rfl⟩⟩
  obtain ⟨M₁, hM₁⟩ := hbd he₁
  obtain ⟨M₂, hM₂⟩ := hbd he₂
  set η' : ℝ := min η 1 with hη'
  have hη'pos : 0 < η' := lt_min hη one_pos
  -- small remainders
  have hsmall : ∀ (r : ℝ × ℝ → V 1), TendstoZeroCInfty r → ∃ S, ∀ s ≥ S, ∀ t, ‖r (s, t)‖ ≤ η' := by
    intro r hr
    obtain ⟨S, hS⟩ := hr.2 0 η' hη'pos
    exact ⟨S, fun s hs t => by have := hS s hs t; rwa [norm_iteratedFDeriv_zero] at this⟩
  obtain ⟨Sr₁, hSr₁⟩ := hsmall r₁ hr₁
  obtain ⟨Sr₂, hSr₂⟩ := hsmall r₂ hr₂
  -- small tube vectors
  have hexp : ∀ {μ : ℝ}, μ < 0 → ∀ M : ℝ, ∃ S, ∀ s ≥ S, Real.exp (μ * s) * (M + 1) ≤ ρT := by
    intro μ hμ M
    have ht : Tendsto (fun s : ℝ => Real.exp (μ * s) * (M + 1)) atTop (𝓝 (0 * (M + 1))) :=
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hμ)).mul_const _
    rw [zero_mul] at ht
    obtain ⟨S, hS⟩ := eventually_atTop.1 (ht.eventually (ge_mem_nhds hρT))
    exact ⟨S, hS⟩
  obtain ⟨Sh₁, hSh₁⟩ := hexp hμ₁' M₁
  obtain ⟨Sh₂, hSh₂⟩ := hexp hμ₂' M₂
  refine ⟨max (max (max s₁ s₂) (max Sr₁ Sr₂)) (max Sh₁ Sh₂), fun s s' t t' hs hs' hW => ?_⟩
  have hs₁ : s₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hs)
  have hs₂ : s₂ ≤ s' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hs')
  have hr₁s : ‖r₁ (s, t)‖ ≤ η' :=
    hSr₁ s (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hs)) t
  have hr₂s : ‖r₂ (s', t')‖ ≤ η' :=
    hSr₂ s' (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hs')) t'
  have hh₁s := hSh₁ s (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hs))
  have hh₂s := hSh₂ s' (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hs'))
  obtain ⟨hξ₁, hW₁⟩ := hrep₁ s hs₁ t
  obtain ⟨hξ₂, hW₂⟩ := hrep₂ s' hs₂ t'
  have hnorm : ∀ (μ σ : ℝ) (a b : V 1) (M : ℝ), ‖a‖ ≤ M → ‖b‖ ≤ η' →
      Real.exp (μ * σ) * (M + 1) ≤ ρT → ‖Real.exp (1 * μ * σ) • (a + b)‖ ≤ ρT := by
    intro μ σ a b M ha hb hh
    rw [one_mul, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine le_trans (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ha
      (hb.trans (min_le_right _ _)))) (Real.exp_pos _).le) hh
  obtain ⟨j, hj, hh⟩ := htube (τ₁ (s, t)) (τ₂ (s', t')) _ _ hξ₁ hξ₂
    (hnorm μ₁ s _ _ M₁ (hM₁ _) hr₁s hh₁s) (hnorm μ₂ s' _ _ M₂ (hM₂ _) hr₂s hh₂s)
    (by rw [← hW₁, ← hW₂]; exact hW)
  set σ : ℝ := τ₁ (s, t) / P.T with hσ
  have hσ2 : τ₂ (s', t') / P.T + j * 1 = σ := by
    rw [hσ, hj]; field_simp
  have he₂σ : e₂ (τ₂ (s', t') / P.T) = e₂ σ := by
    rw [← hσ2]; exact (he₂.1.2.1.int_mul j (τ₂ (s', t') / P.T)).symm
  rw [he₂σ, one_mul, one_mul] at hh
  refine ⟨σ, r₁ (s, t), r₂ (s', t'), hr₁s.trans (min_le_left _ _),
    hr₂s.trans (min_le_left _ _), ?_⟩
  have := congrArg (fun x => Real.exp (-(μ₁ * s)) • x) hh
  simp only [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul] at this
  rw [this, show -(μ₁ * s) + μ₂ * s' = μ₂ * s' - μ₁ * s by ring]

end FiniteEnergyPlane

/-!
# Far-field child, layer 3: the exceptional level

Leading eigenvectors `e₁` (of `u`) and `e₂` (of `v`), both of winding `1`.
* If `e₁ = b e₂` with `b > 0`, far coincidences force `e^{μ(s' - s)} → b`, hence
  `τ = a_u - a_v → τ₀ = d₁ - d₂ - (T/μ) log b`.
* Otherwise `‖e₁(σ) - c e₂(σ)‖ ≥ κ > 0` on the relevant compact range of `c`, so there are no far
  coincidences at all.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem rdf_mM (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) {μ : ℝ} {e : ℝ → V 1}
    (he : IsAsymptoticEigen J P μ e) : ∃ m > 0, ∃ M, ∀ θ, m ≤ ‖e θ‖ ∧ ‖e θ‖ ≤ M := by
  have hvc : Continuous e := he.1.1.continuous
  have hvper : Function.Periodic e 1 := he.1.2.1
  obtain ⟨x₀, -, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (Set.nonempty_Icc.2 zero_le_one) (hvc.norm.continuousOn)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hvc.continuousOn
  refine ⟨‖e x₀‖, norm_pos_iff.2 (isAsymptoticEigen_apply_ne_zero H hH J hJ P μ e he x₀), C,
    fun θ => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hvper.exists_mem_Ico₀ one_pos θ
  rw [hfy]
  exact ⟨hmin (Set.Ico_subset_Icc_self hy), hC y (Set.Ico_subset_Icc_self hy)⟩

theorem rdf_nb {a r : V 1} {m M η : ℝ} (ha : m ≤ ‖a‖) (ha' : ‖a‖ ≤ M) (hr : ‖r‖ ≤ η)
    (hηm : η ≤ m / 2) (hη1 : η ≤ 1) : m / 2 ≤ ‖a + r‖ ∧ ‖a + r‖ ≤ M + 1 := by
  have h1 := norm_sub_le (a + r) r
  rw [add_sub_cancel_right] at h1
  exact ⟨by linarith, (norm_add_le _ _).trans (by linarith)⟩

theorem rdf_diff {e₁ e₂ R₁ R₂ : V 1} {ρ : ℝ} (h : e₁ + R₁ = ρ • (e₂ + R₂)) :
    e₁ - ρ • e₂ = ρ • R₂ - R₁ := by
  calc e₁ - ρ • e₂ = (e₁ + R₁) - R₁ - ρ • e₂ := by abel
    _ = ρ • (e₂ + R₂) - R₁ - ρ • e₂ := by rw [h]
    _ = ρ • R₂ - R₁ := by rw [smul_add]; abel

theorem rdf_far (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1) :
    ∃ τ₀ : ℝ, ∀ ε > 0, ∃ S : ℝ, ∀ s s' t t' τ : ℝ, S ≤ s → S ≤ s' →
      endW H u cylInf (s, t) = endW H v cylInf (s', t') →
      endA H u cylInf (s, t) = τ + endA H v cylInf (s', t') → |τ - τ₀| < ε := by
  classical
  have hP := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP
  obtain ⟨μ₁, e₁, hA₁, hk₁⟩ :=
    exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane H hH J hJ P u hu huP
  obtain ⟨μ₂, e₂, hA₂, hk₂⟩ :=
    exists_hasAsymptoticEigenvector_hasXiLoopWind_one_of_isFastPlane H hH J hJ P v hv hvP
  have hrel := rdf_rel H hH J P hP u v hA₁ hA₂
  have he₁ := hA₁.1
  have he₂ := hA₂.1
  have hμ₁ : μ₁ < 0 := by have := hA₁.2.1; linarith
  obtain ⟨m₁, hm₁, M₁, hmM₁⟩ := rdf_mM H hH J hJ P he₁
  obtain ⟨m₂, hm₂, M₂, hmM₂⟩ := rdf_mM H hH J hJ P he₂
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hmM₁ 0).2
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hmM₂ 0).2
  obtain ⟨d₁, -, -, -, hd₁, -⟩ := huP
  obtain ⟨d₂, -, -, -, hd₂, -⟩ := hvP
  have hT := P.T_pos
  by_cases hB : ∃ b : ℝ, b > 0 ∧ ∀ σ, e₁ σ = b • e₂ σ
  · obtain ⟨b, hb, hbe⟩ := hB
    have hμ : μ₁ = μ₂ := (isAsymptoticEigen_eq_smul_of_apply_eq_smul H hH J hJ P he₁ he₂ hk₁ hk₂ (hbe 0)).1
    subst hμ
    refine ⟨d₁ - d₂ - P.T / μ₁ * Real.log b, fun ε hε => ?_⟩
    have hnμ : 0 < -μ₁ := by linarith
    set εl : ℝ := ε * (-μ₁) / (2 * P.T) with hεl
    have hεlpos : 0 < εl := by positivity
    obtain ⟨δl, hδl, hlog⟩ := Metric.continuousAt_iff.1 (Real.continuousAt_log hb.ne') εl hεlpos
    set ρmax : ℝ := 2 * (b * M₂ + 1) / m₂ with hρmax
    have hρmax0 : 0 ≤ ρmax := by positivity
    set η : ℝ := min (min (ε / 8) 1) (min (m₂ / 2) (δl * m₂ / (2 * (ρmax + 1)))) with hη
    have hηpos : 0 < η := lt_min (lt_min (by linarith) one_pos) (lt_min (by linarith) (by positivity))
    have hη8 : η ≤ ε / 8 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hη1 : η ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hηm : η ≤ m₂ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hηδ : η ≤ δl * m₂ / (2 * (ρmax + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    obtain ⟨S₀, hS₀⟩ := hrel η hηpos
    obtain ⟨Sd₁, hSd₁⟩ := hd₁ η hηpos
    obtain ⟨Sd₂, hSd₂⟩ := hd₂ η hηpos
    refine ⟨max S₀ (max Sd₁ Sd₂), fun s s' t t' τ hs hs' hW ha => ?_⟩
    obtain ⟨σ, R₁, R₂, hR₁, hR₂, heq⟩ :=
      hS₀ s s' t t' (le_trans (le_max_left _ _) hs) (le_trans (le_max_left _ _) hs') hW
    set ρ : ℝ := Real.exp (μ₁ * s' - μ₁ * s) with hρ
    have hρpos : 0 < ρ := Real.exp_pos _
    rw [hbe σ] at heq
    obtain ⟨hl₂, -⟩ := rdf_nb (hmM₂ σ).1 (hmM₂ σ).2 hR₂ hηm hη1
    have hnorm : ‖b • e₂ σ + R₁‖ = ρ * ‖e₂ σ + R₂‖ := by
      rw [heq, norm_smul, Real.norm_of_nonneg hρpos.le]
    have hup : ‖b • e₂ σ + R₁‖ ≤ b * M₂ + 1 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hb.le]
      nlinarith [(hmM₂ σ).2]
    have hρle : ρ ≤ ρmax := by
      rw [hρmax, le_div_iff₀ hm₂]
      nlinarith
    have hdiff := rdf_diff heq
    rw [← sub_smul] at hdiff
    have hbρ : |b - ρ| * m₂ ≤ (ρmax + 1) * η := by
      have h1 : |b - ρ| * m₂ ≤ ‖(b - ρ) • e₂ σ‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hmM₂ σ).1 (abs_nonneg _)
      have h2 : ‖ρ • R₂ - R₁‖ ≤ ρ * η + η := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ hR₁)
        rw [norm_smul, Real.norm_of_nonneg hρpos.le]
        exact mul_le_mul_of_nonneg_left hR₂ hρpos.le
      rw [hdiff] at h1
      nlinarith
    have hδ : dist ρ b < δl := by
      rw [Real.dist_eq, abs_sub_comm]
      have h3 : (ρmax + 1) * η ≤ δl * m₂ / 2 := by
        rw [le_div_iff₀ (by positivity)] at hηδ; nlinarith
      have h4 : |b - ρ| * m₂ < δl * m₂ := by nlinarith
      exact lt_of_mul_lt_mul_right h4 hm₂.le
    have hl := hlog hδ
    rw [hρ, Real.log_exp, Real.dist_eq] at hl
    have ha₁ : |endA H u cylInf (s, t) - 1 * P.T * s - d₁| ≤ η := by
      have := hSd₁ s (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs) t
      simpa [Real.norm_eq_abs] using this
    have ha₂ : |endA H v cylInf (s', t') - 1 * P.T * s' - d₂| ≤ η := by
      have := hSd₂ s' (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs') t'
      simpa [Real.norm_eq_abs] using this
    have hkey : τ - (d₁ - d₂ - P.T / μ₁ * Real.log b) =
        (endA H u cylInf (s, t) - 1 * P.T * s - d₁) - (endA H v cylInf (s', t') - 1 * P.T * s' - d₂)
          + P.T / μ₁ * (Real.log b - (μ₁ * s' - μ₁ * s)) := by
      have hm : P.T / μ₁ * μ₁ = P.T := div_mul_cancel₀ _ hμ₁.ne
      rw [show P.T / μ₁ * (Real.log b - (μ₁ * s' - μ₁ * s)) =
        P.T / μ₁ * Real.log b - (P.T / μ₁ * μ₁) * s' + (P.T / μ₁ * μ₁) * s by ring, hm]
      linarith
    have hlast : |P.T / μ₁ * (Real.log b - (μ₁ * s' - μ₁ * s))| < ε / 2 := by
      rw [abs_mul, abs_div, abs_of_pos hT, abs_of_neg hμ₁, abs_sub_comm]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hnμ]
      have : P.T * |μ₁ * s' - μ₁ * s - Real.log b| < P.T * εl := mul_lt_mul_of_pos_left hl hT
      rw [hεl] at this
      have e : P.T * (ε * -μ₁ / (2 * P.T)) = ε / 2 * -μ₁ := by field_simp
      linarith
    rw [hkey]
    calc |(endA H u cylInf (s, t) - 1 * P.T * s - d₁) - (endA H v cylInf (s', t') - 1 * P.T * s' - d₂)
          + P.T / μ₁ * (Real.log b - (μ₁ * s' - μ₁ * s))|
        ≤ |endA H u cylInf (s, t) - 1 * P.T * s - d₁| + |endA H v cylInf (s', t') - 1 * P.T * s' - d₂|
          + |P.T / μ₁ * (Real.log b - (μ₁ * s' - μ₁ * s))| :=
          le_trans (abs_add_le _ _) (add_le_add (abs_sub _ _) le_rfl)
      _ < ε := by linarith
  · refine ⟨0, fun ε hε => ?_⟩
    set ρmin : ℝ := m₁ / (2 * (M₂ + 1)) with hρmin
    set ρmax : ℝ := 2 * (M₁ + 1) / m₂ with hρmax
    have hρmin0 : 0 < ρmin := by positivity
    have hρmax0 : 0 ≤ ρmax := by positivity
    set K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc ρmin ρmax with hK
    have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
    have hfc : Continuous (fun p : ℝ × ℝ => ‖e₁ p.1 - p.2 • e₂ p.1‖) :=
      ((he₁.1.1.continuous.comp continuous_fst).sub
        (continuous_snd.smul (he₂.1.1.continuous.comp continuous_fst))).norm
    have hfpos : ∀ p ∈ K, 0 < ‖e₁ p.1 - p.2 • e₂ p.1‖ := by
      intro p hp
      rw [norm_pos_iff]
      intro h0
      have h1 : e₁ p.1 = p.2 • e₂ p.1 := sub_eq_zero.1 h0
      exact hB ⟨p.2, lt_of_lt_of_le hρmin0 hp.2.1,
        (isAsymptoticEigen_eq_smul_of_apply_eq_smul H hH J hJ P he₁ he₂ hk₁ hk₂ h1).2⟩
    obtain ⟨κ, hκ, hκK⟩ : ∃ κ > 0, ∀ p ∈ K, κ ≤ ‖e₁ p.1 - p.2 • e₂ p.1‖ := by
      rcases K.eq_empty_or_nonempty with hKe | hKne
      · exact ⟨1, one_pos, fun p hp => by rw [hKe] at hp; exact hp.elim⟩
      · obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKne hfc.continuousOn
        exact ⟨_, hfpos p₀ hp₀, fun p hp => hmin hp⟩
    set η : ℝ := min (min 1 (m₁ / 2)) (min (m₂ / 2) (κ / (2 * (ρmax + 1)))) with hη
    have hηpos : 0 < η := lt_min (lt_min one_pos (by linarith)) (lt_min (by linarith) (by positivity))
    have hη1 : η ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hηm₁ : η ≤ m₁ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hηm₂ : η ≤ m₂ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hηκ : η ≤ κ / (2 * (ρmax + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    obtain ⟨S₀, hS₀⟩ := hrel η hηpos
    refine ⟨S₀, fun s s' t t' τ hs hs' hW _ => ?_⟩
    exfalso
    obtain ⟨σ, R₁, R₂, hR₁, hR₂, heq⟩ := hS₀ s s' t t' hs hs' hW
    set ρ : ℝ := Real.exp (μ₂ * s' - μ₁ * s) with hρ
    have hρpos : 0 < ρ := Real.exp_pos _
    obtain ⟨hl₁, hu₁⟩ := rdf_nb (hmM₁ σ).1 (hmM₁ σ).2 hR₁ hηm₁ hη1
    obtain ⟨hl₂, hu₂⟩ := rdf_nb (hmM₂ σ).1 (hmM₂ σ).2 hR₂ hηm₂ hη1
    have hnorm : ‖e₁ σ + R₁‖ = ρ * ‖e₂ σ + R₂‖ := by
      rw [heq, norm_smul, Real.norm_of_nonneg hρpos.le]
    have hρle : ρ ≤ ρmax := by
      rw [hρmax, le_div_iff₀ hm₂]
      have := mul_le_mul_of_nonneg_left hl₂ hρpos.le
      linarith
    have hρge : ρmin ≤ ρ := by
      rw [hρmin, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hu₂ hρpos.le
      linarith
    set σ' : ℝ := Int.fract σ with hσ'
    have hper : ∀ {μ : ℝ} {e : ℝ → V 1}, IsAsymptoticEigen J P μ e → e σ' = e σ := by
      intro μ e he
      have := he.1.2.1.sub_int_mul_eq (x := σ) ⌊σ⌋
      rw [mul_one] at this
      rw [hσ', Int.fract]; exact this
    have hmem : (σ', ρ) ∈ K :=
      ⟨⟨Int.fract_nonneg σ, (Int.fract_lt_one σ).le⟩, ⟨hρge, hρle⟩⟩
    have h1 := hκK _ hmem
    simp only at h1
    rw [hper he₁, hper he₂, rdf_diff heq] at h1
    have h2 : ‖ρ • R₂ - R₁‖ ≤ ρ * η + η := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ hR₁)
      rw [norm_smul, Real.norm_of_nonneg hρpos.le]
      exact mul_le_mul_of_nonneg_left hR₂ hρpos.le
    have h3 : (ρmax + 1) * η ≤ κ / 2 := by
      rw [le_div_iff₀ (by positivity)] at hηκ; linarith
    have h4 : ρ * η ≤ ρmax * η := mul_le_mul_of_nonneg_right hρle hηpos.le
    linarith

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open scoped Real

theorem emb_exists_cylInf_eq (z : ℂ) (hz : z ≠ 0) :
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
# Far-field child: assembly

Near/far: if `|z|` is bounded, `proj v(w) = proj u(z)` lies in a compact set off `x(ℝ)`, so `w` is
bounded (properness), uniformly in the translation; symmetrically. Far/far: cylinder coordinates
and the exceptional level of layer 3.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem rdfx_swap {n : ℕ} {f g : ℂ → V n} {τ : ℝ} {z w : ℂ} (h : f z = shiftA τ g w) :
    g w = shiftA (-τ) f z := by
  show g w = Real.exp (2 * -τ) • f z
  rw [h]
  simp only [shiftA]
  rw [smul_smul, ← Real.exp_add, show 2 * -τ + 2 * τ = 0 by ring, Real.exp_zero, one_smul]

theorem rdfx_mix (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (f g : ℂ → V 1) (hf0 : ∀ z, f z ≠ 0) (hg0 : ∀ w, g w ≠ 0) (hfc : Continuous f)
    (hgP : IsNondegenerateEnd H g cylInf P 1) (hfmiss : ∀ z, proj H (f z) ∉ Set.range P.x)
    (R : ℝ) : ∃ R' : ℝ, ∀ (τ : ℝ) (z w : ℂ), ‖z‖ ≤ R → f z = shiftA τ g w → ‖w‖ ≤ R' := by
  set K : Set (V 1) := (proj H ∘ f) '' closedBall (0 : ℂ) R with hK
  have hpc : Continuous (proj H ∘ f) := (continuous_aCoord_proj_comp_aux H hH f hf0 hfc).2
  have hKc : IsCompact K := (isCompact_closedBall _ _).image hpc
  have hKP : Disjoint K (Set.range P.x) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, -, rfl⟩
    exact hfmiss z
  obtain ⟨R', hR'⟩ := isBounded_iff_forall_norm_le.1
    (isBounded_preimage_proj_of_isNondegenerateEnd H hH P g hgP K hKc hKP)
  refine ⟨R', fun τ z w hz h => hR' w ?_⟩
  show proj H (g w) ∈ K
  refine ⟨z, mem_closedBall_zero_iff.2 hz, ?_⟩
  show proj H (f z) = proj H (g w)
  rw [h]
  exact (proj_aCoord_exp_smul_aux H hH τ (g w) (hg0 w)).1

theorem rdfx_cyl {R₀ S : ℝ} (hR₀ : R₀ = Real.exp (2 * π * S)) {z : ℂ} (hz : R₀ < ‖z‖) :
    ∃ s t : ℝ, S ≤ s ∧ cylInf s t = z := by
  have hpos : 0 < R₀ := by rw [hR₀]; exact Real.exp_pos _
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  obtain ⟨t, ht⟩ := emb_exists_cylInf_eq z hz0
  refine ⟨_, t, ?_, ht⟩
  rw [le_div_iff₀ (by positivity)]
  have := Real.log_lt_log hpos hz
  rw [hR₀, Real.log_exp] at this
  linarith

theorem exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1)
    (humiss : ∀ z, proj H (u z) ∉ Set.range P.x) (hvmiss : ∀ z, proj H (v z) ∉ Set.range P.x) :
    ∃ τ₀ : ℝ, ∀ ε > 0, ∃ R : ℝ, ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ v w → ε ≤ |τ - τ₀| →
      ‖z‖ < R ∧ ‖w‖ < R := by
  obtain ⟨τ₀, hfar⟩ := rdf_far H hH J hJ P u v hu huP hv hvP
  refine ⟨τ₀, fun ε hε => ?_⟩
  obtain ⟨S, hS⟩ := hfar ε hε
  have hfu := hu.1
  have hfv := hv.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfu.2.1 z trivial
  have hv0 : ∀ z, v z ≠ 0 := fun z => hfv.2.1 z trivial
  have hcu : Continuous u := (contDiffOn_univ.1 hfu.1).continuous
  have hcv : Continuous v := (contDiffOn_univ.1 hfv.1).continuous
  set R₀ : ℝ := Real.exp (2 * π * S) with hR₀
  have hR₀pos : 0 < R₀ := Real.exp_pos _
  obtain ⟨R₁, hR₁⟩ := rdfx_mix H hH P u v hu0 hv0 hcu hvP humiss R₀
  obtain ⟨R₂, hR₂⟩ := rdfx_mix H hH P v u hv0 hu0 hcv huP hvmiss R₀
  set R : ℝ := max (max R₀ R₁) R₂ + 1 with hR
  have h0 : R₀ < R := by
    have := le_max_left R₀ R₁; have := le_max_left (max R₀ R₁) R₂; linarith
  have h1 : R₁ < R := by
    have := le_max_right R₀ R₁; have := le_max_left (max R₀ R₁) R₂; linarith
  have h2 : R₂ < R := by have := le_max_right (max R₀ R₁) R₂; linarith
  refine ⟨R, fun τ z w h hτ => ?_⟩
  by_cases hz : ‖z‖ ≤ R₀
  · exact ⟨by linarith, lt_of_le_of_lt (hR₁ τ z w hz h) h1⟩
  by_cases hw : ‖w‖ ≤ R₀
  · exact ⟨lt_of_le_of_lt (hR₂ (-τ) w z hw (rdfx_swap h)) h2, by linarith⟩
  exfalso
  push_neg at hz hw
  obtain ⟨s, t, hs, hst⟩ := rdfx_cyl hR₀ hz
  obtain ⟨s', t', hs', hst'⟩ := rdfx_cyl hR₀ hw
  have hpr := proj_aCoord_exp_smul_aux H hH τ (v w) (hv0 w)
  have hh : u z = Real.exp (2 * τ) • v w := h
  have hW : endW H u cylInf (s, t) = endW H v cylInf (s', t') := by
    simp only [endW]; rw [hst, hst', hh, hpr.1]
  have hA : endA H u cylInf (s, t) = τ + endA H v cylInf (s', t') := by
    simp only [endA]; rw [hst, hst', hh, hpr.2, add_comm]
  have := hS s s' t t' τ hs hs' hW hA
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1)
    (humiss : ∀ z, proj H (u z) ∉ Set.range P.x) (hvmiss : ∀ z, proj H (v z) ∉ Set.range P.x) :
    ∃ τ₀ : ℝ, ∀ ε > 0, ∃ R : ℝ, ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ v w → ε ≤ |τ - τ₀| →
      ‖z‖ < R ∧ ‖w‖ < R :=
  FiniteEnergyPlane.exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane_aux H hH J hJ P u v hu huP hv hvP humiss hvmiss
