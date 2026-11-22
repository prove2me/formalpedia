-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tubeCoords_of_isUnitaryXiFrame
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T15:51:51.743806+00:00
-- url     : https://prove2.me/submissions/a5f5ef59-eddb-4ad2-b0aa-0d24a3aa7c15

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_exists_smooth_periodic_root_family
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_mul_norm_of_periodic

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open scoped ContDiff Topology
open Set Metric Filter Topology

/-! Algebra helpers for the tube coordinates (copied from Scratch/ZC_L0 `kta_*`). -/




set_option linter.unusedSimpArgs false

def kta_sig {n : ℕ} (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

def kta_sgn {n : ℕ} (k : Fin (2 * (n + 1))) : ℝ := if (k : ℕ) % 2 = 0 then -1 else 1

theorem kta_sig_val {n : ℕ} (k : Fin (2 * (n + 1))) :
    ((kta_sig k : Fin (2 * (n + 1))) : ℕ) = if (k : ℕ) % 2 = 0 then (k : ℕ) + 1 else (k : ℕ) - 1 := by
  unfold kta_sig; split_ifs <;> rfl

theorem kta_sig_sig {n : ℕ} (k : Fin (2 * (n + 1))) : kta_sig (kta_sig k) = k := by
  ext
  rw [kta_sig_val, kta_sig_val]
  split_ifs <;> omega

theorem kta_sgn_sig {n : ℕ} (k : Fin (2 * (n + 1))) : kta_sgn (kta_sig k) = - kta_sgn k := by
  unfold kta_sgn
  rw [kta_sig_val]
  split_ifs <;> (try norm_num) <;> omega

theorem kta_sgn_sq {n : ℕ} (k : Fin (2 * (n + 1))) : kta_sgn k * kta_sgn k = 1 := by
  unfold kta_sgn; split_ifs <;> norm_num

def kta_sigE (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) :=
  Function.Involutive.toPerm kta_sig kta_sig_sig

theorem kta_sigE_apply {n : ℕ} (k : Fin (2 * (n + 1))) : kta_sigE n k = kta_sig k := rfl

theorem kta_j0_apply {n : ℕ} (v : V n) (k : Fin (2 * (n + 1))) :
    j0 v k = kta_sgn k * v (kta_sig k) := by
  unfold j0 kta_sgn kta_sig
  split_ifs <;> simp

theorem kta_j0_j0 {n : ℕ} (v : V n) : j0 (j0 v) = -v := by
  funext k
  rw [kta_j0_apply, kta_j0_apply, kta_sig_sig, kta_sgn_sig]
  simp only [Pi.neg_apply]
  have := kta_sgn_sq k
  linear_combination (-(v k)) * this

theorem kta_j0_smul {n : ℕ} (a : ℝ) (v : V n) : j0 (a • v) = a • j0 v := by
  funext k; simp only [kta_j0_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem kta_j0_add {n : ℕ} (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [kta_j0_apply, Pi.add_apply]; ring

theorem kta_j0_sub {n : ℕ} (u v : V n) : j0 (u - v) = j0 u - j0 v := by
  funext k; simp only [kta_j0_apply, Pi.sub_apply]; ring

theorem kta_dot_comm {n : ℕ} (u v : V n) : dot u v = dot v u := by
  unfold dot; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem kta_dot_smul_right {n : ℕ} (a : ℝ) (u v : V n) : dot u (a • v) = a * dot u v := by
  unfold dot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem kta_dot_smul_left {n : ℕ} (a : ℝ) (u v : V n) : dot (a • u) v = a * dot u v := by
  rw [kta_dot_comm, kta_dot_smul_right, kta_dot_comm]

theorem kta_dot_add_right {n : ℕ} (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem kta_dot_add_left {n : ℕ} (u v w : V n) : dot (v + w) u = dot v u + dot w u := by
  rw [kta_dot_comm, kta_dot_add_right, kta_dot_comm, kta_dot_comm u]

theorem kta_dot_sub_right {n : ℕ} (u v w : V n) : dot u (v - w) = dot u v - dot u w := by
  unfold dot; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem kta_dot_sub_left {n : ℕ} (u v w : V n) : dot (v - w) u = dot v u - dot w u := by
  rw [kta_dot_comm, kta_dot_sub_right, kta_dot_comm, kta_dot_comm u]

theorem kta_dot_neg_right {n : ℕ} (u v : V n) : dot u (-v) = - dot u v := by
  unfold dot; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp)

theorem kta_dot_neg_left {n : ℕ} (u v : V n) : dot (-u) v = - dot u v := by
  rw [kta_dot_comm, kta_dot_neg_right, kta_dot_comm]

theorem kta_dot_j0_left {n : ℕ} (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (kta_sigE n)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [kta_sigE_apply, kta_j0_apply, kta_sig_sig, kta_sgn_sig]
  ring

theorem kta_dot_j0_j0 {n : ℕ} (u v : V n) : dot (j0 u) (j0 v) = dot u v := by
  rw [kta_dot_j0_left, kta_j0_j0, kta_dot_neg_right, neg_neg]

theorem kta_dot_self_j0 {n : ℕ} (u : V n) : dot u (j0 u) = 0 := by
  have := kta_dot_j0_left u u
  rw [kta_dot_comm] at this
  linarith

theorem kta_clm_apply {n : ℕ} (L : V n →L[ℝ] ℝ) (v : V n) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (v k) : V n) = v k • Pi.single k 1 by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul]

theorem kta_fderiv_eq_dot {n : ℕ} (H : V n → ℝ) (x v : V n) :
    fderiv ℝ H x v = dot (grad H x) v := by
  rw [kta_clm_apply]; unfold dot grad
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem kta_liouville_ham {n : ℕ} (H : V n → ℝ) (x : V n) :
    liouville x (hamVF H x) = fderiv ℝ H x x / 2 := by
  unfold liouville omega0 hamVF
  rw [kta_dot_j0_j0, kta_fderiv_eq_dot, kta_dot_comm]

theorem kta_reeb_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  have hpos : 0 < liouville x (hamVF H x) := by
    rw [kta_liouville_ham]; have := hH.2.2 x hx; linarith
  refine ⟨hpos, ?_, ?_, ?_⟩
  · unfold reeb
    have : liouville x ((liouville x (hamVF H x))⁻¹ • hamVF H x) =
        (liouville x (hamVF H x))⁻¹ * liouville x (hamVF H x) := by
      unfold liouville omega0; rw [kta_dot_smul_right]; ring
    rw [this, inv_mul_cancel₀ hpos.ne']
  · unfold reeb hamVF
    rw [map_smul, kta_fderiv_eq_dot, kta_dot_self_j0, smul_zero]
  · intro w hw
    unfold reeb hamVF omega0
    rw [kta_j0_smul, kta_j0_j0, kta_dot_smul_left, kta_dot_neg_left,
      ← kta_fderiv_eq_dot, hw]; ring

theorem kta_om_add_left {n : ℕ} (u v w : V n) : omega0 (u + v) w = omega0 u w + omega0 v w := by
  unfold omega0; rw [kta_j0_add, kta_dot_add_left]
theorem kta_om_add_right {n : ℕ} (u v w : V n) : omega0 w (u + v) = omega0 w u + omega0 w v := by
  unfold omega0; rw [kta_dot_add_right]
theorem kta_om_sub_left {n : ℕ} (u v w : V n) : omega0 (u - v) w = omega0 u w - omega0 v w := by
  unfold omega0; rw [kta_j0_sub, kta_dot_sub_left]
theorem kta_om_sub_right {n : ℕ} (u v w : V n) : omega0 w (u - v) = omega0 w u - omega0 w v := by
  unfold omega0; rw [kta_dot_sub_right]
theorem kta_om_smul_left {n : ℕ} (a : ℝ) (u w : V n) : omega0 (a • u) w = a * omega0 u w := by
  unfold omega0; rw [kta_j0_smul, kta_dot_smul_left]
theorem kta_om_smul_right {n : ℕ} (a : ℝ) (u w : V n) : omega0 w (a • u) = a * omega0 w u := by
  unfold omega0; rw [kta_dot_smul_right]
theorem kta_om_anti {n : ℕ} (u v : V n) : omega0 u v = - omega0 v u := by
  unfold omega0; rw [kta_dot_j0_left, kta_dot_comm]
theorem kta_om_self {n : ℕ} (u : V n) : omega0 u u = 0 := by
  have := kta_om_anti u u; linarith

theorem kta_liouvilleCLM_apply {n : ℕ} (x v : V n) : liouvilleCLM x v = liouville x v := by
  unfold liouvilleCLM liouville omega0 dot
  simp [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem kta_scale_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem kta_scale_unique {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (t : ℝ) (ht : 0 < t) (hHt : H (t • y) = 1) : scaleToS H y = t := by
  obtain ⟨r, _, hu⟩ := hH.2.1 y hy
  have h1 := hu t ⟨ht, hHt⟩
  have h2 := hu (scaleToS H y) (kta_scale_spec H hH y hy)
  rw [h1, h2]



theorem kta_j0_contDiff {n : ℕ} : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 (fun k => ?_)
  have : (fun v : V n => j0 v k) = fun v => kta_sgn k * v (kta_sig k) := by
    funext v; exact kta_j0_apply v k
  rw [this]
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (kta_sig k))

theorem kta_dH_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)

theorem kta_grad_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (grad H) := by
  refine contDiff_pi.2 (fun k => ?_)
  exact (kta_dH_contDiff H hH).clm_apply contDiff_const

theorem kta_hamVF_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamVF H) := kta_j0_contDiff.comp (kta_grad_contDiff H hH)

theorem kta_liouvilleCLM_contDiff {n : ℕ} : ContDiff ℝ ∞ (liouvilleCLM : V n → V n →L[ℝ] ℝ) := by
  unfold liouvilleCLM
  refine ContDiff.const_smul _ (ContDiff.sum (fun k _ => ?_))
  exact ((contDiff_apply ℝ ℝ k).comp kta_j0_contDiff).smul contDiff_const

theorem kta_reeb_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContDiffAt ℝ ∞ (reeb H) x := by
  have hpos := (kta_reeb_spec H hH x hx).1
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [kta_liouvilleCLM_apply]
  have hc : ContDiff ℝ ∞ (fun x => liouville x (hamVF H x)) := by
    rw [hL]; exact kta_liouvilleCLM_contDiff.clm_apply (kta_hamVF_contDiff H hH.1)
  unfold reeb
  exact (hc.contDiffAt.inv hpos.ne').smul (kta_hamVF_contDiff H hH.1).contDiffAt

theorem kta_scale_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y₀ : V n)
    (hy₀ : y₀ ≠ 0) : ContDiffAt ℝ ∞ (scaleToS H) y₀ := by
  obtain ⟨hr, hHx⟩ := kta_scale_spec H hH y₀ hy₀
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
    exact (kta_scale_unique H hH y h3 (ψ y) h2 h1').symm
  exact hψc.congr_of_eventuallyEq hev.symm

/-! Generic analytic helpers for `exists_tubeCoords_near_linearized` (leaf B of K 138fff41). -/


namespace TCBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `(ε/K)(e^{Kx} - 1) ≤ ε x e^{Kx}`, packaged as a bound on `gronwallBound`. -/
lemma gronwallBound_le {δ K ε x : ℝ} (hδ : 0 ≤ δ) (hK : 0 < K) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
    have := Real.add_one_le_exp (-(K * x))
    have hE := Real.exp_pos (K * x)
    have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  have h3 : ε / K * (Real.exp (K * x) - 1) ≤ ε * x * Real.exp (K * x) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    nlinarith [mul_le_mul_of_nonneg_left h1 hε]
  nlinarith

/-- Forward Grönwall on `[0, L]` with an everywhere-derivative hypothesis. -/
lemma gronwall_fwd {f f' : ℝ → E} {L K ε : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc (-L) L, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc (-L) L, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc 0 L, ‖f t‖ ≤ (‖f 0‖ + ε * L) * Real.exp (K * L) := by
  have hsub : Icc 0 L ⊆ Icc (-L) L := Icc_subset_Icc (by linarith) le_rfl
  have hcont : ContinuousOn f (Icc 0 L) := fun t ht =>
    (hf t (hsub ht)).continuousAt.continuousWithinAt
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := f') (δ := ‖f 0‖)
    (K := K) (ε := ε) (a := 0) (b := L) hcont
    (fun t ht => (hf t (hsub (Ico_subset_Icc_self ht))).hasDerivWithinAt) le_rfl
    (fun t ht => hb t (hsub (Ico_subset_Icc_self ht)))
  intro t ht
  refine (key t ht).trans ?_
  rw [sub_zero]
  refine (gronwallBound_le (norm_nonneg _) hK hε ht.1).trans ?_
  have h1 : ‖f 0‖ + ε * t ≤ ‖f 0‖ + ε * L := by nlinarith [ht.2]
  have h2 : Real.exp (K * t) ≤ Real.exp (K * L) := Real.exp_le_exp.2 (by nlinarith [ht.2])
  have h3 : 0 ≤ ‖f 0‖ + ε * t := by nlinarith [norm_nonneg (f 0), ht.1]
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by linarith)

/-- Two-sided Grönwall on `[-L, L]`, centred at `0`. -/
lemma gronwall_two {f f' : ℝ → E} {L K ε : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc (-L) L, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc (-L) L, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc (-L) L, ‖f t‖ ≤ (‖f 0‖ + ε * L) * Real.exp (K * L) := by
  intro t ht
  rcases le_total 0 t with h0 | h0
  · exact gronwall_fwd hK hε hL hf hb t ⟨h0, ht.2⟩
  · have hg : ∀ s ∈ Icc (-L) L, HasDerivAt (fun s => f (-s)) (-f' (-s)) s := by
      intro s hs
      have hs' : -s ∈ Icc (-L) L := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      exact ((hf (-s) hs').scomp s (hasDerivAt_neg s)).congr_deriv (by simp)
    have hgb : ∀ s ∈ Icc (-L) L, ‖-f' (-s)‖ ≤ K * ‖f (-s)‖ + ε := by
      intro s hs
      rw [norm_neg]
      exact hb (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := gronwall_fwd (f := fun s => f (-s)) hK hε hL hg hgb (-t) ⟨by linarith, by linarith [ht.1]⟩
    simpa using this

/-- Gronwall with bootstrap (copied from `ROFCore.traj_close`). -/
lemma traj_close {R : E → E} {x Q : ℝ → E} {K : NNReal} {δ : ℝ}
    (hL : ∀ t, LipschitzOnWith K R (ball (x t) δ))
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hQ : ∀ t, HasDerivAt Q (R (Q t)) t)
    {a b ε : ℝ} (h0 : dist (Q a) (x a) ≤ ε) (hε : ε * Real.exp (K * (b - a)) < δ) :
    ∀ t ∈ Icc a b, dist (Q t) (x t) ≤ ε * Real.exp (K * (t - a)) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hQc : Continuous Q := continuous_iff_continuousAt.2 fun t => (hQ t).continuousAt
  have gron : ∀ c ∈ Icc a b, (∀ t ∈ Ico a c, dist (Q t) (x t) < δ) →
      ∀ t ∈ Icc a c, dist (Q t) (x t) ≤ ε * Real.exp (K * (t - a)) := by
    intro c hc hin
    have hδ : 0 < δ := lt_of_le_of_lt (le_trans dist_nonneg h0 |> fun h =>
      mul_nonneg h (Real.exp_pos _).le) hε
    exact dist_le_of_trajectories_ODE_of_mem (v := fun _ => R) (s := fun t => ball (x t) δ)
      (fun t _ => hL t) hQc.continuousOn (fun t _ => (hQ t).hasDerivWithinAt)
      (fun t ht => mem_ball.2 (hin t ht)) hxc.continuousOn (fun t _ => (hx t).hasDerivWithinAt)
      (fun t _ => mem_ball_self hδ) h0
  have mono : ∀ t ∈ Icc a b, ε * Real.exp (K * (t - a)) < δ := by
    intro t ht
    refine lt_of_le_of_lt ?_ hε
    have hε0 : 0 ≤ ε := le_trans dist_nonneg h0
    gcongr
    exact ht.2
  by_cases hS : ∃ t ∈ Icc a b, δ ≤ dist (Q t) (x t)
  · exfalso
    set S := Icc a b ∩ {t | δ ≤ dist (Q t) (x t)} with hSdef
    have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const (hQc.dist hxc))
    have hSne : S.Nonempty := by obtain ⟨t, ht, h⟩ := hS; exact ⟨t, ht, h⟩
    have hSb : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
    have hmem := hSc.csInf_mem hSne hSb
    set c := sInf S
    have hc : c ∈ Icc a b := hmem.1
    have hin : ∀ t ∈ Ico a c, dist (Q t) (x t) < δ := by
      intro t ht
      by_contra hcon
      push Not at hcon
      have : c ≤ t := csInf_le hSb ⟨⟨ht.1, ht.2.le.trans hc.2⟩, hcon⟩
      exact absurd ht.2 (not_lt.2 this)
    have := gron c hc hin c ⟨hc.1, le_rfl⟩
    have h2 := mono c hc
    exact absurd hmem.2 (not_le.2 (lt_of_le_of_lt this h2))
  · push Not at hS
    intro t ht
    exact gron b ⟨ht.1.trans ht.2, le_rfl⟩ (fun t ht => hS t ⟨ht.1, ht.2.le⟩) t ht

/-- Two-sided version of `traj_close` on `[-L, L]` for trajectories compared with `x(c + ·)`. -/
lemma traj_close_two {R : E → E} {x Q : ℝ → E} {K : NNReal} {δ : ℝ}
    (hL : ∀ t, LipschitzOnWith K R (ball (x t) δ))
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hQ : ∀ t, HasDerivAt Q (R (Q t)) t)
    {c L ε : ℝ} (h0 : dist (Q 0) (x c) ≤ ε) (hε : ε * Real.exp (K * L) < δ) :
    ∀ t ∈ Icc (-L) L, dist (Q t) (x (c + t)) ≤ ε * Real.exp (K * L) := by
  have hε0 : 0 ≤ ε := le_trans dist_nonneg h0
  intro t ht
  rcases le_total 0 t with h0t | h0t
  · have hx' : ∀ s, HasDerivAt (fun s => x (c + s)) (R (x (c + s))) s := fun s =>
      (hx (c + s)).comp_const_add c s
    have hL' : ∀ s, LipschitzOnWith K R (ball (x (c + s)) δ) := fun s => hL (c + s)
    have key := traj_close (x := fun s => x (c + s)) hL' hx' hQ (a := 0) (b := L)
      (by simpa using h0) (by simpa using hε) t ⟨h0t, ht.2⟩
    refine key.trans ?_
    gcongr
    · linarith [ht.2]
  · have hx' : ∀ s, HasDerivAt (fun s => x (c - s)) ((-R) (x (c - s))) s := fun s => by
      exact ((hx (c - s)).scomp s ((hasDerivAt_id s).const_sub c)).congr_deriv (by simp)
    have hQ' : ∀ s, HasDerivAt (fun s => Q (-s)) ((-R) (Q (-s))) s := fun s => by
      exact ((hQ (-s)).scomp s (hasDerivAt_neg s)).congr_deriv (by simp)
    have hL' : ∀ s, LipschitzOnWith K (-R) (ball (x (c - s)) δ) := fun s => by
      have := (hL (c - s))
      intro a ha b hb
      have h := this ha hb
      simpa [edist_neg_neg] using h
    have key := traj_close (x := fun s => x (c - s)) (Q := fun s => Q (-s)) hL' hx' hQ'
      (a := 0) (b := L) (by simpa using h0) (by simpa using hε) (-t) ⟨by linarith, by linarith [ht.1]⟩
    have e : c - -t = c + t := by ring
    simp only [neg_neg, e] at key
    refine key.trans ?_
    gcongr
    · linarith [ht.1]

/-- A `C²` map near a compact set: uniform Lipschitz bound and quadratic Taylor remainder. -/
lemma C2_near_compact [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {O : Set E} (hO : IsOpen O) (hf : ContDiffOn ℝ 2 f O)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ δ > 0, ∃ D, 0 ≤ D ∧ ∀ p ∈ K, closedBall p δ ⊆ O ∧
      (∀ y ∈ closedBall p δ, ∀ y' ∈ closedBall p δ, ‖f y - f y'‖ ≤ D * ‖y - y'‖) ∧
      ∀ y ∈ closedBall p δ, ‖f y - f p - fderiv ℝ f p (y - p)‖ ≤ D * ‖y - p‖ ^ 2 := by
  have hf1 : ContDiffOn ℝ 1 f O := hf.of_le (by norm_num)
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ f) O := hf.fderiv_of_isOpen hO (by norm_num)
  obtain ⟨δ₁, hδ₁, D₁, hD₁, h₁⟩ := FiniteEnergyPlane.exists_lipschitz_near_compact hO hf1 hK hKO
  obtain ⟨δ₂, hδ₂, D₂, hD₂, h₂⟩ := FiniteEnergyPlane.exists_lipschitz_near_compact hO hdf hK hKO
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max D₁ D₂, le_max_of_le_left hD₁, ?_⟩
  intro p hp
  have hb1 : closedBall p (min δ₁ δ₂) ⊆ closedBall p δ₁ := closedBall_subset_closedBall (min_le_left _ _)
  have hb2 : closedBall p (min δ₁ δ₂) ⊆ closedBall p δ₂ := closedBall_subset_closedBall (min_le_right _ _)
  obtain ⟨hO1, hL1⟩ := h₁ p hp
  obtain ⟨-, hL2⟩ := h₂ p hp
  refine ⟨hb1.trans hO1, ?_, ?_⟩
  · intro y hy y' hy'
    refine ((hL1 y (hb1 hy)).2 y' (hb1 hy')).trans ?_
    gcongr
    exact le_max_left _ _
  · intro y hy
    have hdiff : ∀ z ∈ O, DifferentiableAt ℝ f z := fun z hz =>
      (hf1.differentiableOn one_ne_zero z hz).differentiableAt (hO.mem_nhds hz)
    set s := closedBall p ‖y - p‖ with hs
    have hsb : s ⊆ closedBall p (min δ₁ δ₂) :=
      closedBall_subset_closedBall (by simpa [dist_eq_norm] using hy)
    have hp0 : p ∈ closedBall p (min δ₁ δ₂) := mem_closedBall_self (lt_min hδ₁ hδ₂).le
    have key := (convex_closedBall p ‖y - p‖).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := fun z => f z - fderiv ℝ f p z) (C := max D₁ D₂ * ‖y - p‖) (x := p) (y := y)
      (fun z hz => (hdiff z (hO1 (hb1 (hsb hz)))).sub (fderiv ℝ f p).differentiableAt)
      (fun z hz => by
        rw [fderiv_fun_sub (hdiff z (hO1 (hb1 (hsb hz)))) (fderiv ℝ f p).differentiableAt,
          ContinuousLinearMap.fderiv]
        have h3 := (hL2 z (hb2 (hsb hz))).2 p (hb2 hp0)
        have hz' : ‖z - p‖ ≤ ‖y - p‖ := by
          rw [hs, mem_closedBall, dist_eq_norm] at hz; exact hz
        calc ‖fderiv ℝ f z - fderiv ℝ f p‖ ≤ D₂ * ‖z - p‖ := h3
          _ ≤ max D₁ D₂ * ‖y - p‖ := mul_le_mul (le_max_right _ _) hz' (norm_nonneg _)
              (le_max_of_le_left hD₁))
      (mem_closedBall_self (norm_nonneg _)) (by simp [hs, dist_eq_norm])
    have e : f y - fderiv ℝ f p y - (f p - fderiv ℝ f p p) = f y - f p - fderiv ℝ f p (y - p) := by
      rw [map_sub]; abel
    rw [e] at key
    calc _ ≤ max D₁ D₂ * ‖y - p‖ * ‖y - p‖ := key
      _ = max D₁ D₂ * ‖y - p‖ ^ 2 := by ring

/-- A `C¹` map on `ℝ × ball`, periodic in the first variable, is uniformly Lipschitz in the
second variable on `ℝ × closedBall (r/2)`, for small increments. -/
lemma periodic_lipschitz_snd [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (Φ : ℝ × E → F) {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ 1 Φ (univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (u : E), Φ (φ + T, u) = Φ (φ, u)) :
    ∃ δ > 0, ∃ D, 0 ≤ D ∧ ∀ (φ : ℝ) (u u' : E), ‖u‖ ≤ r / 2 → ‖u' - u‖ ≤ δ →
      ‖Φ (φ, u') - Φ (φ, u)‖ ≤ D * ‖u' - u‖ := by
  have hO : IsOpen ((univ : Set ℝ) ×ˢ ball (0 : E) r) := isOpen_univ.prod isOpen_ball
  have hK : IsCompact (Icc (0 : ℝ) T ×ˢ closedBall (0 : E) (r / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKO : Icc (0 : ℝ) T ×ˢ closedBall (0 : E) (r / 2) ⊆ (univ : Set ℝ) ×ˢ ball (0 : E) r :=
    prod_mono (subset_univ _) (closedBall_subset_ball (by linarith))
  obtain ⟨δ, hδ, D, hD, h⟩ := FiniteEnergyPlane.exists_lipschitz_near_compact hO hΦ hK hKO
  refine ⟨δ, hδ, D, hD, ?_⟩
  intro φ u u' hu hu'
  have hp : Function.Periodic (fun φ => (Φ (φ, u), Φ (φ, u'))) T := fun φ => by
    simp only [hper]
  obtain ⟨φ', hφ', he⟩ := hp.exists_mem_Ico₀ hT φ
  simp only [Prod.mk.injEq] at he
  rw [he.1, he.2]
  have hpK : (φ', u) ∈ Icc (0 : ℝ) T ×ˢ closedBall (0 : E) (r / 2) :=
    ⟨Ico_subset_Icc_self hφ', by simpa using hu⟩
  obtain ⟨-, hL⟩ := h _ hpK
  have hm1 : (φ', u') ∈ closedBall (φ', u) δ := by
    rw [mem_closedBall, Prod.dist_eq]; simp [dist_eq_norm, hu', hδ.le]
  have hm2 : (φ', u) ∈ closedBall (φ', u) δ := mem_closedBall_self hδ.le
  have := (hL _ hm1).2 _ hm2
  have hn : ‖((φ', u') : ℝ × E) - (φ', u)‖ = ‖u' - u‖ := by
    rw [Prod.norm_def]; simp
  rwa [hn] at this

/-- A continuous periodic function is bounded. -/
lemma periodic_bdd {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {T : ℝ} (hT : 0 < T)
    (hf : Continuous f) (hper : Function.Periodic f T) : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  obtain ⟨t', ht', he⟩ := hper.exists_mem_Ico₀ hT t
  rw [he]
  exact (hM t' (Ico_subset_Icc_self ht')).trans (le_max_left _ _)

end TCBase

/-! Tube coordinates `y = proj (x τ + Z(τ/T) a)` near a periodic Reeb orbit, with an explicit
inverse of the unitary frame. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

noncomputable section

/-- The inverse of the unitary frame on `ξ`, `w ↦ J₀ (ω₀(Z eᵢ, w))ᵢ`. -/
@[irreducible] def tcZinv (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (t : ℝ) (w : V 1) :
    CauchyRiemannIndex.Vec 1 :=
  Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1)
    ((EuclideanSpace.equiv (Fin 1 ⊕ Fin 1) ℝ).symm
      (fun i => omega0 (Z t (EuclideanSpace.single i 1)) w))

theorem tc_omega0_contDiff : ContDiff ℝ ∞ (fun p : V 1 × V 1 => omega0 p.1 p.2) := by
  unfold omega0 dot
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_apply ℝ ℝ k).comp (kta_j0_contDiff.comp contDiff_fst)).mul
    ((contDiff_apply ℝ ℝ k).comp contDiff_snd)

theorem tcZinv_contDiff {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hZ : ContDiff ℝ ∞ Z) :
    ContDiff ℝ ∞ (fun p : ℝ × V 1 => tcZinv Z p.1 p.2) := by
  unfold tcZinv
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × V 1 =>
      (fun i => omega0 (Z p.1 (EuclideanSpace.single i 1)) p.2 : Fin 1 ⊕ Fin 1 → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    exact tc_omega0_contDiff.comp
      (((hZ.comp contDiff_fst).clm_apply contDiff_const).prodMk contDiff_snd)
  have h2 := (EuclideanSpace.equiv (Fin 1 ⊕ Fin 1) ℝ).symm.contDiff.comp h1
  exact (LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1))).contDiff.comp h2

theorem tcZinv_apply_Z {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hZ : IsUnitaryXiFrame J P Z) (t : ℝ)
    (a : CauchyRiemannIndex.Vec 1) : tcZinv Z t (Z t a) = a := by
  have hω := (hZ.2.2 t).2.2.2
  unfold tcZinv
  simp_rw [hω]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.toEuclideanLin, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.fromBlocks] <;> ring

theorem tc_Z_tcZinv {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hZ : IsUnitaryXiFrame J P Z) (t : ℝ)
    (w : V 1) (hw : IsInXi H (P.x (P.T * t)) w) : Z t (tcZinv Z t w) = w := by
  obtain ⟨a, rfl⟩ := (hZ.2.2 t).2.1 w hw
  rw [tcZinv_apply_Z hZ]

lemma tc_periodic_lb {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : Continuous f)
    (hper : Function.Periodic f T) (hpos : ∀ x, 0 < f x) : ∃ m > 0, ∀ x, m ≤ f x := by
  obtain ⟨x₀, -, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hT.le) hf.continuousOn
  refine ⟨f x₀, hpos x₀, fun x => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico₀ hT x
  rw [hfy]
  exact hmin (Set.Ico_subset_Icc_self hy)

lemma tc_liouville_self {n : ℕ} (y : V n) : liouville y y = 0 := by
  unfold liouville; rw [kta_om_self]; simp

lemma tc_liouville_anti {n : ℕ} (a b : V n) : liouville a b = -liouville b a := by
  unfold liouville; rw [kta_om_anti]; ring

lemma tc_ne_zero_of_mem {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : H y = 1) : y ≠ 0 := by
  intro h
  have := hH.2.2 y hy
  rw [h, map_zero] at this
  exact lt_irrefl _ this

lemma tc_proj_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : H y = 1) {ρ : ℝ} (hρ : 0 < ρ) : proj H (ρ • y) = y := by
  have hy0 := tc_ne_zero_of_mem hH hy
  have hne : ρ • y ≠ 0 := smul_ne_zero hρ.ne' hy0
  have hs : scaleToS H (ρ • y) = ρ⁻¹ :=
    kta_scale_unique H hH _ hne ρ⁻¹ (inv_pos.2 hρ) (by rw [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul, hy])
  unfold proj; rw [hs, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

/-- Tube coordinates near a periodic Reeb orbit, in a unitary frame. -/
theorem tc_tube (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (P : ReebOrbit H) (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hZ : IsUnitaryXiFrame J P Z) :
    ∃ r > 0, ∃ m > 0, ∃ (θ : ℝ × V 1 → ℝ) (A : ℝ × V 1 → CauchyRiemannIndex.Vec 1)
      (ρ : ℝ × V 1 → ℝ),
      ContDiffOn ℝ 1 (fun q => (θ q, A q)) (univ ×ˢ ball (0 : V 1) r) ∧
      (∀ φ u, θ (φ + P.T, u) = θ (φ, u) ∧ A (φ + P.T, u) = A (φ, u)) ∧
      (∀ φ u, ‖u‖ < r → 0 < ρ (φ, u) ∧
        ρ (φ, u) • (P.x φ + u) = P.x (φ + θ (φ, u)) + Z ((φ + θ (φ, u)) / P.T) (A (φ, u)) ∧
        |ρ (φ, u) - 1| ≤
          (2 / m) * |fderiv ℝ H (P.x (φ + θ (φ, u))) (P.x φ + u - P.x (φ + θ (φ, u)))|) ∧
      (∀ φ b, ‖Z (φ / P.T) b‖ < r → θ (φ, Z (φ / P.T) b) = 0 ∧ A (φ, Z (φ / P.T) b) = b) := by
  classical
  have hT : 0 < P.T := P.T_pos
  have hxs : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  have hxper : Function.Periodic P.x P.T := P.periodic
  have hxS : ∀ τ, H (P.x τ) = 1 := P.mem
  have hxd : ∀ τ, HasDerivAt P.x (reeb H (P.x τ)) τ := P.hasDerivAt
  have hdH : ContDiff ℝ ∞ (fderiv ℝ H) := kta_dH_contDiff H hH.1
  set x := P.x with hxdef
  set T := P.T with hTdef
  obtain ⟨G, hG_def⟩ : ∃ G : (ℝ × V 1) × ℝ → ℝ,
      ∀ q, G q = liouvilleCLM (x q.1.1 + q.1.2) (x (q.1.1 + q.2)) := ⟨_, fun _ => rfl⟩
  have hGs : ContDiff ℝ ∞ G := by
    have h1 : ContDiff ℝ ∞ (fun q : (ℝ × V 1) × ℝ => x q.1.1 + q.1.2) :=
      (hxs.comp (contDiff_fst.comp contDiff_fst)).add (contDiff_snd.comp contDiff_fst)
    have h2 : ContDiff ℝ ∞ (fun q : (ℝ × V 1) × ℝ => x (q.1.1 + q.2)) :=
      hxs.comp ((contDiff_fst.comp contDiff_fst).add contDiff_snd)
    have : G = fun q => liouvilleCLM (x q.1.1 + q.1.2) (x (q.1.1 + q.2)) := funext hG_def
    rw [this]
    exact (kta_liouvilleCLM_contDiff.comp h1).clm_apply h2
  have hGper : ∀ (φ : ℝ) (u : V 1) (σ : ℝ), G ((φ + T, u), σ) = G ((φ, u), σ) := by
    intro φ u σ
    rw [hG_def, hG_def]
    simp only
    rw [hxper φ, show φ + T + σ = (φ + σ) + T by ring, hxper]
  have hG0 : ∀ φ : ℝ, G ((φ, 0), 0) = 0 := by
    intro φ
    rw [hG_def]; simp only [add_zero, kta_liouvilleCLM_apply]
    exact tc_liouville_self _
  have hGd : ∀ φ : ℝ, deriv (fun σ : ℝ => G ((φ, 0), σ)) 0 ≠ 0 := by
    intro φ
    have hx' : HasDerivAt (fun σ : ℝ => x (φ + σ)) (reeb H (x φ)) 0 :=
      HasDerivAt.comp_const_add φ 0 (by rw [add_zero]; exact hxd φ)
    have hd : HasDerivAt (fun σ : ℝ => G ((φ, 0), σ)) (liouvilleCLM (x φ) (reeb H (x φ))) 0 := by
      have : (fun σ : ℝ => G ((φ, 0), σ)) = fun σ => liouvilleCLM (x φ) (x (φ + σ)) := by
        funext σ; rw [hG_def]; simp
      rw [this]
      exact (liouvilleCLM (x φ)).hasFDerivAt.comp_hasDerivAt 0 hx'
    rw [hd.deriv, kta_liouvilleCLM_apply, (kta_reeb_spec H hH (x φ) (hxS φ)).2.1]
    exact one_ne_zero
  obtain ⟨δ, r, hδ, -, hr, g, hgs, hgper, hg0, hgroot⟩ :=
    exists_smooth_periodic_root_family G hGs T hT hGper hG0 hGd 1 one_pos
  have hNc : Continuous fun τ => fderiv ℝ H (x τ) (x τ) :=
    (hdH.continuous.comp hxs.continuous).clm_apply hxs.continuous
  obtain ⟨m, hm, hmN⟩ := tc_periodic_lb hT hNc
    (fun τ => by show fderiv ℝ H (x (τ + T)) (x (τ + T)) = _; rw [hxper])
    (fun τ => hH.2.2 _ (hxS τ))
  set S := (Set.univ : Set ℝ) ×ˢ ball (0 : V 1) r with hS
  have hτs : ContDiffOn ℝ ∞ (fun q : ℝ × V 1 => x (q.1 + g q)) S :=
    hxs.comp_contDiffOn (contDiff_fst.contDiffOn.add hgs)
  have hdens : ContDiffOn ℝ ∞ (fun q : ℝ × V 1 => fderiv ℝ H (x (q.1 + g q)) (x q.1 + q.2)) S :=
    (hdH.comp_contDiffOn hτs).clm_apply
      ((hxs.comp contDiff_fst).add contDiff_snd).contDiffOn
  have hNs : ContDiffOn ℝ ∞
      (fun q : ℝ × V 1 => fderiv ℝ H (x (q.1 + g q)) (x (q.1 + g q))) S :=
    (hdH.comp_contDiffOn hτs).clm_apply hτs
  obtain ⟨LD, hLD0, hLD⟩ := exists_norm_le_mul_norm_of_periodic
    (fun q : ℝ × V 1 => fderiv ℝ H (x (q.1 + g q)) (x q.1 + q.2) -
      fderiv ℝ H (x (q.1 + g q)) (x (q.1 + g q))) T r hT hr
    ((hdens.sub hNs).of_le (by simp))
    (fun φ u _ => by
      simp only
      rw [hgper, show φ + T + g (φ, u) = (φ + g (φ, u)) + T by ring, hxper, hxper])
    (fun φ => by simp [hg0])
  set r' := min (r / 2) (m / (2 * (LD + 1))) with hr'
  have hr'pos : 0 < r' := lt_min (by linarith) (div_pos hm (by linarith))
  have hr'r : r' ≤ r / 2 := min_le_left _ _
  have hden : ∀ φ (u : V 1), ‖u‖ < r' → m / 2 ≤ fderiv ℝ H (x (φ + g (φ, u))) (x φ + u) := by
    intro φ u hu
    have h1 := hLD φ u (by linarith)
    rw [Real.norm_eq_abs] at h1
    have h2 : LD * ‖u‖ ≤ m / 2 := by
      have hu' : ‖u‖ ≤ m / (2 * (LD + 1)) := hu.le.trans (min_le_right _ _)
      have h3 : LD * ‖u‖ ≤ (LD + 1) * ‖u‖ := by nlinarith [norm_nonneg u]
      have h4 : (LD + 1) * ‖u‖ ≤ (LD + 1) * (m / (2 * (LD + 1))) :=
        mul_le_mul_of_nonneg_left hu' (by linarith)
      have h5 : (LD + 1) * (m / (2 * (LD + 1))) = m / 2 := by field_simp
      linarith
    have h6 := hmN (φ + g (φ, u))
    have h7 := (abs_le.1 (h1.trans h2)).1
    beta_reduce at h6 h7
    linarith
  obtain ⟨Hf, hHf⟩ : ∃ Hf : ℝ × V 1 → V 1, ∀ q, Hf q =
      (fderiv ℝ H (x (q.1 + g q)) (x (q.1 + g q)) /
        fderiv ℝ H (x (q.1 + g q)) (x q.1 + q.2)) • (x q.1 + q.2) - x (q.1 + g q) :=
    ⟨_, fun _ => rfl⟩
  have hS' : (Set.univ : Set ℝ) ×ˢ ball (0 : V 1) r' ⊆ S :=
    Set.prod_mono le_rfl (ball_subset_ball (by linarith))
  have hHfs : ContDiffOn ℝ ∞ Hf ((Set.univ : Set ℝ) ×ˢ ball (0 : V 1) r') := by
    have : Hf = fun q => (fderiv ℝ H (x (q.1 + g q)) (x (q.1 + g q)) /
        fderiv ℝ H (x (q.1 + g q)) (x q.1 + q.2)) • (x q.1 + q.2) - x (q.1 + g q) := funext hHf
    rw [this]
    refine ((((hNs.mono hS').div (hdens.mono hS') ?_).smul
      ((hxs.comp contDiff_fst).add contDiff_snd).contDiffOn)).sub (hτs.mono hS')
    rintro ⟨φ, u⟩ ⟨-, hu⟩
    rw [mem_ball_zero_iff] at hu
    have := hden φ u hu
    exact (by linarith : (0 : ℝ) < _).ne'
  have hHfper : ∀ φ u, Hf (φ + T, u) = Hf (φ, u) := by
    intro φ u
    rw [hHf, hHf]; simp only
    rw [hgper, show φ + T + g (φ, u) = (φ + g (φ, u)) + T by ring, hxper, hxper]
  have hZper : ∀ t, Z (t + 1) = Z t := hZ.2.1
  refine ⟨r', hr'pos, m, hm, g, fun q => tcZinv Z ((q.1 + g q) / T) (Hf q),
    fun q => fderiv ℝ H (x (q.1 + g q)) (x (q.1 + g q)) /
        fderiv ℝ H (x (q.1 + g q)) (x q.1 + q.2), ?_, ?_, ?_, ?_⟩
  · have hτT : ContDiffOn ℝ ∞ (fun q : ℝ × V 1 => (q.1 + g q) / T)
        ((Set.univ : Set ℝ) ×ˢ ball (0 : V 1) r') :=
      (contDiff_fst.contDiffOn.add (hgs.mono hS')).div_const T
    have hpair : ContDiffOn ℝ ∞ (fun q : ℝ × V 1 => (((q.1 + g q) / T, Hf q) : ℝ × V 1))
        ((Set.univ : Set ℝ) ×ˢ ball (0 : V 1) r') := hτT.prodMk hHfs
    have hZi : ContDiff ℝ ∞ (fun p : ℝ × V 1 => tcZinv Z p.1 p.2) := tcZinv_contDiff hZ.1
    have hA : ContDiffOn ℝ ∞ (fun q : ℝ × V 1 => tcZinv Z ((q.1 + g q) / T) (Hf q))
        ((Set.univ : Set ℝ) ×ˢ ball (0 : V 1) r') := hZi.comp_contDiffOn hpair
    exact ((hgs.mono hS').prodMk hA).of_le (by simp)
  · intro φ u
    refine ⟨hgper φ u, ?_⟩
    simp only
    rw [hgper, hHfper, show (φ + T + g (φ, u)) / T = (φ + g (φ, u)) / T + 1 by
      field_simp; ring, tcZinv, tcZinv, hZper]
  · intro φ u hu
    have hur : ‖u‖ < r := by linarith
    obtain ⟨-, hgG, -⟩ := hgroot φ u hur
    set τ0 := φ + g (φ, u) with hτ0
    set den := fderiv ℝ H (x τ0) (x φ + u) with hden_def
    set N := fderiv ℝ H (x τ0) (x τ0) with hN_def
    have hdenpos : m / 2 ≤ den := hden φ u hu
    have hdenpos' : 0 < den := by linarith
    have hNpos : 0 < N := lt_of_lt_of_le hm (hmN τ0)
    have hHfu : Hf (φ, u) = (N / den) • (x φ + u) - x τ0 := by rw [hHf]
    have hxi : IsInXi H (x τ0) (Hf (φ, u)) := by
      constructor
      · rw [hHfu, ← kta_liouvilleCLM_apply, map_sub, map_smul, kta_liouvilleCLM_apply,
          kta_liouvilleCLM_apply, tc_liouville_self, tc_liouville_anti]
        have : liouville (x φ + u) (x τ0) = 0 := by
          rw [← kta_liouvilleCLM_apply, ← hgG, hG_def]
        rw [this]; simp
      · rw [hHfu, map_sub, map_smul, smul_eq_mul, ← hden_def, ← hN_def]
        field_simp
        ring
    have hxi' : IsInXi H (P.x (P.T * (τ0 / T))) (Hf (φ, u)) := by
      rw [← hTdef, mul_div_cancel₀ _ hT.ne']; exact hxi
    have hZZ := tc_Z_tcZinv hZ (τ0 / T) _ hxi'
    refine ⟨div_pos hNpos hdenpos', ?_, ?_⟩
    · simp only
      rw [← hτ0, hZZ, hHfu]; abel
    · simp only
      rw [← hτ0, ← hden_def, ← hN_def]
      have e : N / den - 1 = -(fderiv ℝ H (x τ0) (x φ + u - x τ0)) / den := by
        rw [map_sub, ← hden_def, ← hN_def]; field_simp; ring
      rw [e, abs_div, abs_neg, abs_of_pos hdenpos', div_le_iff₀ hdenpos']
      have h0 : 0 ≤ |fderiv ℝ H (x τ0) (x φ + u - x τ0)| := abs_nonneg _
      have h2 : 1 ≤ (2 / m) * den := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hm]; linarith
      have h3 := mul_le_mul_of_nonneg_right h2 h0
      linarith
  · intro φ b hb
    set u := Z (φ / T) b with hu
    have hur : ‖u‖ < r := by linarith
    have hxi : IsInXi H (x φ) u := by
      have := (hZ.2.2 (φ / T)).1 b
      rwa [← hTdef, mul_div_cancel₀ _ hT.ne'] at this
    have hG00 : G ((φ, u), 0) = 0 := by
      rw [hG_def]; simp only [add_zero, kta_liouvilleCLM_apply]
      unfold liouville
      rw [kta_om_add_left, kta_om_self, kta_om_anti, show omega0 (x φ) u = 2 * liouville (x φ) u by
        unfold liouville; ring, hxi.1]
      simp
    have hg00 : g (φ, u) = 0 := ((hgroot φ u hur).2.2 0 (by simpa using hδ) hG00).symm
    refine ⟨hg00, ?_⟩
    simp only
    have hden1 : fderiv ℝ H (x φ) (x φ + u) = fderiv ℝ H (x φ) (x φ) := by
      rw [map_add, hxi.2, add_zero]
    have hNpos : 0 < fderiv ℝ H (x φ) (x φ) := lt_of_lt_of_le hm (hmN φ)
    have hHfu : Hf (φ, u) = u := by
      rw [hHf]; simp only [hg00, add_zero]
      rw [hden1, div_self hNpos.ne', one_smul]; abel
    rw [hg00, add_zero, hHfu, hu, tcZinv_apply_Z hZ]

end

end FiniteEnergyPlane

/-! Quantitative tube coordinates near a periodic Reeb orbit in a unitary frame. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem exists_tubeCoords_of_isUnitaryXiFrame_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hZ : IsUnitaryXiFrame J P Z) :
    ∃ r > 0, ∃ K, 0 ≤ K ∧ ∃ δ > 0, ∃ (θ : ℝ × V 1 → ℝ) (A : ℝ × V 1 → CauchyRiemannIndex.Vec 1)
      (ρ : ℝ × V 1 → ℝ),
      ContinuousOn θ (univ ×ˢ ball (0 : V 1) r) ∧ ContinuousOn A (univ ×ˢ ball (0 : V 1) r) ∧
      (∀ φ u, ‖u‖ < r → 0 < ρ (φ, u) ∧
        ρ (φ, u) • (P.x φ + u) = P.x (φ + θ (φ, u)) + Z ((φ + θ (φ, u)) / P.T) (A (φ, u))) ∧
      (∀ φ u, ‖u‖ < r → H (P.x φ + u) = 1 →
        ‖P.x φ + u - P.x (φ + θ (φ, u))‖ ≤ K * ‖A (φ, u)‖ ∧ |ρ (φ, u) - 1| ≤ K * ‖A (φ, u)‖ ^ 2) ∧
      (∀ φ b, ‖Z (φ / P.T) b‖ < r → θ (φ, Z (φ / P.T) b) = 0 ∧ A (φ, Z (φ / P.T) b) = b) ∧
      (∀ φ (u u' : V 1), ‖u‖ < r → ‖u' - u‖ ≤ δ →
        |θ (φ, u') - θ (φ, u)| ≤ K * ‖u' - u‖ ∧ ‖A (φ, u') - A (φ, u)‖ ≤ K * ‖u' - u‖) := by
  classical
  have hT : 0 < P.T := P.T_pos
  have hxs : ContDiff ℝ ∞ P.x := ReebOrbit.contDiff_x H hH P
  have hxc : Continuous P.x := hxs.continuous
  have hxS : ∀ τ, H (P.x τ) = 1 := P.mem
  have hxper : Function.Periodic P.x P.T := P.periodic
  have hKc : IsCompact (range P.x) := by
    have : range P.x = P.x '' Icc 0 P.T := by
      apply subset_antisymm
      · rintro _ ⟨t, rfl⟩
        obtain ⟨y, hy, hxy⟩ := hxper.exists_mem_Ico₀ hT t
        exact ⟨y, Ico_subset_Icc_self hy, hxy.symm⟩
      · exact image_subset_range _ _
    rw [this]; exact isCompact_Icc.image hxc
  obtain ⟨δH, hδH, DH, hDH, hHb⟩ := TCBase.C2_near_compact isOpen_univ
    (hH.1.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top)) hKc (subset_univ _)
  obtain ⟨r, hr, m, hm, θ, A, ρ, hθA, hper, hcoord, hlin⟩ := tc_tube H hH J P Z hZ
  obtain ⟨δL, hδL, DL, hDL, hLip⟩ := TCBase.periodic_lipschitz_snd (fun q => (θ q, A q)) hT hr hθA
    (fun φ u => by simp only [(hper φ u).1, (hper φ u).2])
  have hLθ : ∀ φ (u u' : V 1), ‖u‖ ≤ r / 2 → ‖u' - u‖ ≤ δL →
      |θ (φ, u') - θ (φ, u)| ≤ DL * ‖u' - u‖ := fun φ u u' hu hu' => by
    refine le_trans ?_ (hLip φ u u' hu hu')
    have := norm_fst_le ((θ (φ, u'), A (φ, u')) - (θ (φ, u), A (φ, u)))
    simpa [Real.norm_eq_abs] using this
  have hLA : ∀ φ (u u' : V 1), ‖u‖ ≤ r / 2 → ‖u' - u‖ ≤ δL →
      ‖A (φ, u') - A (φ, u)‖ ≤ DL * ‖u' - u‖ := fun φ u u' hu hu' => by
    refine le_trans ?_ (hLip φ u u' hu hu')
    have := norm_snd_le ((θ (φ, u'), A (φ, u')) - (θ (φ, u), A (φ, u)))
    simpa using this
  have hθ0 : ∀ φ, θ (φ, 0) = 0 := fun φ => by
    have := (hlin φ 0 (by simpa using hr)).1; simpa using this
  have hA0 : ∀ φ, A (φ, 0) = 0 := fun φ => by
    have := (hlin φ 0 (by simpa using hr)).2; simpa using this
  obtain ⟨MZ, hMZ0, hMZ⟩ := TCBase.periodic_bdd one_pos hZ.1.continuous hZ.2.1
  obtain ⟨Mx, hMx0, hMx⟩ := TCBase.periodic_bdd hT hxc hxper
  have hderiv : deriv P.x = fun τ => reeb H (P.x τ) := funext fun τ => (P.hasDerivAt τ).deriv
  obtain ⟨Lx, hLx0, hLxb⟩ := TCBase.periodic_bdd hT (hxs.continuous_deriv (by simp))
    (fun τ => by rw [hderiv]; simp only [hxper τ])
  have hxLip : ∀ a b, ‖P.x a - P.x b‖ ≤ Lx * |a - b| := by
    have hl := lipschitzWith_of_nnnorm_deriv_le (C := Lx.toNNReal) (hxs.differentiable (by simp))
      (fun τ => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hLx0]; exact hLxb τ)
    intro a b
    have := hl.dist_le_mul a b
    rwa [dist_eq_norm, Real.coe_toNNReal _ hLx0, Real.dist_eq] at this
  set c0 := 2 / m * DH * (Mx + 1) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  set r1 := min (min (r / 2) δL) (min 1 (min δH (1 / (2 * c0 + 1)) / (1 + Lx * DL + 1))) with hr1
  have hr1pos : 0 < r1 := by
    simp only [hr1, lt_min_iff]
    exact ⟨⟨by linarith, hδL⟩, one_pos, div_pos (lt_min hδH (by positivity)) (by positivity)⟩
  have hr1r : r1 ≤ r / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr1L : r1 ≤ δL := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr11 : r1 ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr1d : r1 ≤ min δH (1 / (2 * c0 + 1)) / (1 + Lx * DL + 1) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨r1, hr1pos, max (max DL (2 * MZ)) (2 / m * DH * (2 * MZ) ^ 2), le_max_of_le_left
    (le_max_of_le_left hDL), δL, hδL, θ, A, ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_fst.comp_continuousOn hθA.continuousOn).mono
      (prod_mono le_rfl (ball_subset_ball (by linarith)))
  · exact (continuous_snd.comp_continuousOn hθA.continuousOn).mono
      (prod_mono le_rfl (ball_subset_ball (by linarith)))
  · intro φ u hu
    obtain ⟨h1, h2, -⟩ := hcoord φ u (by linarith)
    exact ⟨h1, h2⟩
  · intro φ u hu hw
    set K := max (max DL (2 * MZ)) (2 / m * DH * (2 * MZ) ^ 2) with hK
    obtain ⟨hρpos, hρeq, hρb⟩ := hcoord φ u (by linarith)
    set τ₀ := φ + θ (φ, u) with hτ₀
    set w := P.x φ + u with hw'
    set d := ‖w - P.x τ₀‖ with hd
    set α := ‖A (φ, u)‖ with hα
    have hθu : |θ (φ, u)| ≤ DL * ‖u‖ := by
      have := hLθ φ 0 u (by simp; positivity) (by simpa using hu.le.trans hr1L)
      simpa [hθ0] using this
    have hdu : d ≤ (1 + Lx * DL) * ‖u‖ := by
      have h1 : ‖w - P.x τ₀‖ ≤ ‖w - P.x φ‖ + ‖P.x φ - P.x τ₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h2 := hxLip φ τ₀
      have h3 : |φ - τ₀| = |θ (φ, u)| := by
        rw [hτ₀, show φ - (φ + θ (φ, u)) = -θ (φ, u) by ring, abs_neg]
      rw [h3] at h2
      have h5 : ‖w - P.x φ‖ = ‖u‖ := by rw [hw', add_sub_cancel_left]
      have h4 := mul_le_mul_of_nonneg_left hθu hLx0
      have h6 : (1 + Lx * DL) * ‖u‖ = ‖u‖ + Lx * (DL * ‖u‖) := by ring
      rw [hd, h6]; linarith
    have hdsmall : d ≤ min δH (1 / (2 * c0 + 1)) := by
      have h3 : ‖u‖ * (1 + Lx * DL + 1) ≤ min δH (1 / (2 * c0 + 1)) :=
        (le_div_iff₀ (by positivity : (0:ℝ) < 1 + Lx * DL + 1)).1 (le_trans hu.le hr1d)
      have h4 : 0 ≤ ‖u‖ := norm_nonneg u
      have h5 : (1 + Lx * DL) * ‖u‖ ≤ ‖u‖ * (1 + Lx * DL + 1) := by nlinarith
      linarith
    have hdH : d ≤ δH := le_trans hdsmall (min_le_left _ _)
    have hdc : c0 * d ≤ 1 / 2 := by
      have h1 : d ≤ 1 / (2 * c0 + 1) := le_trans hdsmall (min_le_right _ _)
      have h2 : d * (2 * c0 + 1) ≤ 1 :=
        (le_div_iff₀ (by positivity : (0:ℝ) < 2 * c0 + 1)).1 h1
      have h0 : 0 ≤ d := norm_nonneg _
      nlinarith
    have hHtay : |fderiv ℝ H (P.x τ₀) (w - P.x τ₀)| ≤ DH * d ^ 2 := by
      have := (hHb _ (mem_range_self τ₀)).2.2 w (by rw [mem_closedBall, dist_eq_norm]; exact hdH)
      rw [hw, hxS τ₀, sub_self, zero_sub, norm_neg, Real.norm_eq_abs] at this
      exact this
    have hwn : ‖w‖ ≤ Mx + 1 := by
      have h1 : ‖w‖ ≤ ‖P.x φ‖ + ‖u‖ := norm_add_le _ _
      linarith [hMx φ, hu.le.trans hr11]
    have hρ1 : |ρ (φ, u) - 1| ≤ (2 / m) * DH * d ^ 2 := by
      calc |ρ (φ, u) - 1| ≤ (2 / m) * |fderiv ℝ H (P.x τ₀) (w - P.x τ₀)| := hρb
        _ ≤ (2 / m) * (DH * d ^ 2) := by gcongr
        _ = _ := by ring
    have hdα : d ≤ 2 * MZ * α := by
      have heq : w - P.x τ₀ = (1 - ρ (φ, u)) • w + Z (τ₀ / P.T) (A (φ, u)) := by
        rw [sub_smul, one_smul, hρeq]; abel
      have h1 : d ≤ |1 - ρ (φ, u)| * ‖w‖ + MZ * α := by
        rw [hd, heq]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hMZ _)
      have h2 : |1 - ρ (φ, u)| * ‖w‖ ≤ c0 * d * d := by
        rw [abs_sub_comm]
        calc |ρ (φ, u) - 1| * ‖w‖ ≤ (2 / m) * DH * d ^ 2 * (Mx + 1) :=
              mul_le_mul hρ1 hwn (norm_nonneg _) (by positivity)
          _ = c0 * d * d := by rw [hc0]; ring
      have h0 : 0 ≤ d := norm_nonneg _
      have h3 : c0 * d * d ≤ d / 2 := by nlinarith
      linarith
    have hK1 : 2 * MZ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
    have hK2 : 2 / m * DH * (2 * MZ) ^ 2 ≤ K := le_max_right _ _
    have hα0 : 0 ≤ α := norm_nonneg _
    refine ⟨hdα.trans (mul_le_mul_of_nonneg_right hK1 hα0), ?_⟩
    have hd2 : d ^ 2 ≤ (2 * MZ * α) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdα 2
    calc |ρ (φ, u) - 1| ≤ (2 / m) * DH * d ^ 2 := hρ1
      _ ≤ (2 / m) * DH * (2 * MZ * α) ^ 2 := by gcongr
      _ = (2 / m * DH * (2 * MZ) ^ 2) * α ^ 2 := by ring
      _ ≤ K * α ^ 2 := mul_le_mul_of_nonneg_right hK2 (sq_nonneg _)
  · intro φ b hb
    exact hlin φ b (by linarith)
  · intro φ u u' hu hu'
    have hu2 : ‖u‖ ≤ r / 2 := by linarith
    have hK : DL ≤ max (max DL (2 * MZ)) (2 / m * DH * (2 * MZ) ^ 2) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    exact ⟨(hLθ φ u u' hu2 hu').trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _)),
      (hLA φ u u' hu2 hu').trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Set

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hZ : IsUnitaryXiFrame J P Z) :
    ∃ r > 0, ∃ K, 0 ≤ K ∧ ∃ δ > 0, ∃ (θ : ℝ × V 1 → ℝ) (A : ℝ × V 1 → CauchyRiemannIndex.Vec 1)
      (ρ : ℝ × V 1 → ℝ),
      ContinuousOn θ (univ ×ˢ ball (0 : V 1) r) ∧ ContinuousOn A (univ ×ˢ ball (0 : V 1) r) ∧
      (∀ φ u, ‖u‖ < r → 0 < ρ (φ, u) ∧
        ρ (φ, u) • (P.x φ + u) = P.x (φ + θ (φ, u)) + Z ((φ + θ (φ, u)) / P.T) (A (φ, u))) ∧
      (∀ φ u, ‖u‖ < r → H (P.x φ + u) = 1 →
        ‖P.x φ + u - P.x (φ + θ (φ, u))‖ ≤ K * ‖A (φ, u)‖ ∧ |ρ (φ, u) - 1| ≤ K * ‖A (φ, u)‖ ^ 2) ∧
      (∀ φ b, ‖Z (φ / P.T) b‖ < r → θ (φ, Z (φ / P.T) b) = 0 ∧ A (φ, Z (φ / P.T) b) = b) ∧
      (∀ φ (u u' : V 1), ‖u‖ < r → ‖u' - u‖ ≤ δ →
        |θ (φ, u') - θ (φ, u)| ≤ K * ‖u' - u‖ ∧ ‖A (φ, u') - A (φ, u)‖ ≤ K * ‖u' - u‖) :=
  exists_tubeCoords_of_isUnitaryXiFrame_aux H hH J P Z hZ
