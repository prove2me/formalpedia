-- Prove2me | solution 1 for FiniteEnergyPlane.exists_pos_le_lintegral_energyDensity_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T21:29:35.878615+00:00
-- url     : https://prove2.me/submissions/ab3355db-61fe-492f-9ac7-273240356ab3

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_omega0_tames_jtilde
import Theorems.Thm_FiniteEnergyPlane_exists_extension_of_energy_lt_top
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_isJHolomorphicOn_comp_mul
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_energy_ge_of_mapsTo_ball
import Theorems.Thm_FiniteEnergyPlane_isCompact_aCoord_slab

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open scoped ContDiff Topology in
open scoped ContDiff Topology

/-! Helpers copied verbatim from fizzyinc3's accepted solution a386257a (isRemovablePuncture_of_abs_aCoord_le):
the `g69s_*` CR/tameness lemmas, the `FEPA3` Stokes helpers, `FEPA3R.proj_bounds`,
`uniform_tame` and `logistic_bounds`. -/



set_option linter.unusedSimpArgs false

def g69s_sig {n : ℕ} (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

def g69s_sgn {n : ℕ} (k : Fin (2 * (n + 1))) : ℝ := if (k : ℕ) % 2 = 0 then -1 else 1

theorem g69s_sig_val {n : ℕ} (k : Fin (2 * (n + 1))) :
    ((g69s_sig k : Fin (2 * (n + 1))) : ℕ) = if (k : ℕ) % 2 = 0 then (k : ℕ) + 1 else (k : ℕ) - 1 := by
  unfold g69s_sig; split_ifs <;> rfl

theorem g69s_sig_sig {n : ℕ} (k : Fin (2 * (n + 1))) : g69s_sig (g69s_sig k) = k := by
  ext
  rw [g69s_sig_val, g69s_sig_val]
  split_ifs <;> omega

theorem g69s_sgn_sig {n : ℕ} (k : Fin (2 * (n + 1))) : g69s_sgn (g69s_sig k) = - g69s_sgn k := by
  unfold g69s_sgn
  rw [g69s_sig_val]
  split_ifs <;> (try norm_num) <;> omega

theorem g69s_sgn_sq {n : ℕ} (k : Fin (2 * (n + 1))) : g69s_sgn k * g69s_sgn k = 1 := by
  unfold g69s_sgn; split_ifs <;> norm_num

def g69s_sigE (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) :=
  Function.Involutive.toPerm g69s_sig g69s_sig_sig

theorem g69s_sigE_apply {n : ℕ} (k : Fin (2 * (n + 1))) : g69s_sigE n k = g69s_sig k := rfl

theorem g69s_j0_apply {n : ℕ} (v : V n) (k : Fin (2 * (n + 1))) :
    j0 v k = g69s_sgn k * v (g69s_sig k) := by
  unfold j0 g69s_sgn g69s_sig
  split_ifs <;> simp

theorem g69s_j0_j0 {n : ℕ} (v : V n) : j0 (j0 v) = -v := by
  funext k
  rw [g69s_j0_apply, g69s_j0_apply, g69s_sig_sig, g69s_sgn_sig]
  simp only [Pi.neg_apply]
  have := g69s_sgn_sq k
  linear_combination (-(v k)) * this

theorem g69s_j0_smul {n : ℕ} (a : ℝ) (v : V n) : j0 (a • v) = a • j0 v := by
  funext k; simp only [g69s_j0_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem g69s_j0_add {n : ℕ} (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [g69s_j0_apply, Pi.add_apply]; ring

theorem g69s_j0_sub {n : ℕ} (u v : V n) : j0 (u - v) = j0 u - j0 v := by
  funext k; simp only [g69s_j0_apply, Pi.sub_apply]; ring

theorem g69s_dot_comm {n : ℕ} (u v : V n) : dot u v = dot v u := by
  unfold dot; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem g69s_dot_smul_right {n : ℕ} (a : ℝ) (u v : V n) : dot u (a • v) = a * dot u v := by
  unfold dot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem g69s_dot_smul_left {n : ℕ} (a : ℝ) (u v : V n) : dot (a • u) v = a * dot u v := by
  rw [g69s_dot_comm, g69s_dot_smul_right, g69s_dot_comm]

theorem g69s_dot_add_right {n : ℕ} (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem g69s_dot_add_left {n : ℕ} (u v w : V n) : dot (v + w) u = dot v u + dot w u := by
  rw [g69s_dot_comm, g69s_dot_add_right, g69s_dot_comm, g69s_dot_comm u]

theorem g69s_dot_sub_right {n : ℕ} (u v w : V n) : dot u (v - w) = dot u v - dot u w := by
  unfold dot; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem g69s_dot_sub_left {n : ℕ} (u v w : V n) : dot (v - w) u = dot v u - dot w u := by
  rw [g69s_dot_comm, g69s_dot_sub_right, g69s_dot_comm, g69s_dot_comm u]

theorem g69s_dot_neg_right {n : ℕ} (u v : V n) : dot u (-v) = - dot u v := by
  unfold dot; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp)

theorem g69s_dot_neg_left {n : ℕ} (u v : V n) : dot (-u) v = - dot u v := by
  rw [g69s_dot_comm, g69s_dot_neg_right, g69s_dot_comm]

theorem g69s_dot_j0_left {n : ℕ} (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (g69s_sigE n)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [g69s_sigE_apply, g69s_j0_apply, g69s_sig_sig, g69s_sgn_sig]
  ring

theorem g69s_dot_j0_j0 {n : ℕ} (u v : V n) : dot (j0 u) (j0 v) = dot u v := by
  rw [g69s_dot_j0_left, g69s_j0_j0, g69s_dot_neg_right, neg_neg]

theorem g69s_dot_self_j0 {n : ℕ} (u : V n) : dot u (j0 u) = 0 := by
  have := g69s_dot_j0_left u u
  rw [g69s_dot_comm] at this
  linarith

theorem g69s_clm_apply {n : ℕ} (L : V n →L[ℝ] ℝ) (v : V n) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (v k) : V n) = v k • Pi.single k 1 by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul]

theorem g69s_fderiv_eq_dot {n : ℕ} (H : V n → ℝ) (x v : V n) :
    fderiv ℝ H x v = dot (grad H x) v := by
  rw [g69s_clm_apply]; unfold dot grad
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem g69s_liouville_ham {n : ℕ} (H : V n → ℝ) (x : V n) :
    liouville x (hamVF H x) = fderiv ℝ H x x / 2 := by
  unfold liouville omega0 hamVF
  rw [g69s_dot_j0_j0, g69s_fderiv_eq_dot, g69s_dot_comm]

theorem g69s_reeb_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  have hpos : 0 < liouville x (hamVF H x) := by
    rw [g69s_liouville_ham]; have := hH.2.2 x hx; linarith
  refine ⟨hpos, ?_, ?_, ?_⟩
  · unfold reeb
    have : liouville x ((liouville x (hamVF H x))⁻¹ • hamVF H x) =
        (liouville x (hamVF H x))⁻¹ * liouville x (hamVF H x) := by
      unfold liouville omega0; rw [g69s_dot_smul_right]; ring
    rw [this, inv_mul_cancel₀ hpos.ne']
  · unfold reeb hamVF
    rw [map_smul, g69s_fderiv_eq_dot, g69s_dot_self_j0, smul_zero]
  · intro w hw
    unfold reeb hamVF omega0
    rw [g69s_j0_smul, g69s_j0_j0, g69s_dot_smul_left, g69s_dot_neg_left,
      ← g69s_fderiv_eq_dot, hw]; ring

theorem g69s_om_add_left {n : ℕ} (u v w : V n) : omega0 (u + v) w = omega0 u w + omega0 v w := by
  unfold omega0; rw [g69s_j0_add, g69s_dot_add_left]
theorem g69s_om_add_right {n : ℕ} (u v w : V n) : omega0 w (u + v) = omega0 w u + omega0 w v := by
  unfold omega0; rw [g69s_dot_add_right]
theorem g69s_om_sub_left {n : ℕ} (u v w : V n) : omega0 (u - v) w = omega0 u w - omega0 v w := by
  unfold omega0; rw [g69s_j0_sub, g69s_dot_sub_left]
theorem g69s_om_sub_right {n : ℕ} (u v w : V n) : omega0 w (u - v) = omega0 w u - omega0 w v := by
  unfold omega0; rw [g69s_dot_sub_right]
theorem g69s_om_smul_left {n : ℕ} (a : ℝ) (u w : V n) : omega0 (a • u) w = a * omega0 u w := by
  unfold omega0; rw [g69s_j0_smul, g69s_dot_smul_left]
theorem g69s_om_smul_right {n : ℕ} (a : ℝ) (u w : V n) : omega0 w (a • u) = a * omega0 w u := by
  unfold omega0; rw [g69s_dot_smul_right]
theorem g69s_om_anti {n : ℕ} (u v : V n) : omega0 u v = - omega0 v u := by
  unfold omega0; rw [g69s_dot_j0_left, g69s_dot_comm]
theorem g69s_om_self {n : ℕ} (u : V n) : omega0 u u = 0 := by
  have := g69s_om_anti u u; linarith

theorem g69s_tame_abstract {n : ℕ} (A B : V n) (P : V n → Prop) (J' : V n → V n)
    (α β : V n → ℝ)
    (hW : ∀ v, P (v - α v • A - β v • B))
    (hJP : ∀ w, P w → P (J' w)) (hpos : ∀ w, P w → w ≠ 0 → 0 < omega0 w (J' w))
    (hinv : ∀ w w', P w → P w' → omega0 (J' w) (J' w') = omega0 w w')
    (hA : ∀ w, P w → omega0 A w = 0) (hB : ∀ w, P w → omega0 B w = 0)
    (hK : 0 < omega0 A B) :
    (∀ v, v ≠ 0 → 0 < omega0 v (α v • B - β v • A + J' (v - α v • A - β v • B))) ∧
    ∀ v u, omega0 (α v • B - β v • A + J' (v - α v • A - β v • B))
      (α u • B - β u • A + J' (u - α u • A - β u • B)) = omega0 v u := by
  have hBA : omega0 B A = - omega0 A B := g69s_om_anti _ _
  have hwA : ∀ w, P w → omega0 w A = 0 := fun w hw => by rw [g69s_om_anti, hA w hw, neg_zero]
  have hwB : ∀ w, P w → omega0 w B = 0 := fun w hw => by rw [g69s_om_anti, hB w hw, neg_zero]
  constructor
  · intro v hv
    have hPw := hW v
    have hv' : v = α v • A + β v • B + (v - α v • A - β v • B) := by abel
    generalize v - α v • A - β v • B = w at hPw hv'
    generalize α v = a at hv'
    generalize β v = b at hv'
    subst hv'
    have hJw := hJP w hPw
    simp only [g69s_om_add_left, g69s_om_add_right, g69s_om_sub_right, g69s_om_smul_left,
      g69s_om_smul_right, hA w hPw, hB w hPw, hA _ hJw, hB _ hJw, hwA w hPw, hwB w hPw, hBA,
      g69s_om_self]
    by_cases hw0 : w = 0
    · subst hw0
      have hab : a ≠ 0 ∨ b ≠ 0 := by
        by_contra h; push Not at h; apply hv; rw [h.1, h.2]; simp
      have h0 : omega0 (0 : V n) (J' 0) = 0 := by
        rw [show (0 : V n) = (0 : ℝ) • (0 : V n) by simp, g69s_om_smul_left]; ring
      rw [h0]
      rcases hab with h | h
      · have := mul_self_pos.mpr h; nlinarith [mul_self_nonneg b]
      · have := mul_self_pos.mpr h; nlinarith [mul_self_nonneg a]
    · have := hpos w hPw hw0
      nlinarith [mul_self_nonneg a, mul_self_nonneg b]
  · intro v u
    have hPw := hW v
    have hPw' := hW u
    have hv' : v = α v • A + β v • B + (v - α v • A - β v • B) := by abel
    have hu' : u = α u • A + β u • B + (u - α u • A - β u • B) := by abel
    generalize v - α v • A - β v • B = w at hPw hv'
    generalize u - α u • A - β u • B = w' at hPw' hu'
    generalize α v = a at hv'
    generalize β v = b at hv'
    generalize α u = a' at hu'
    generalize β u = b' at hu'
    subst hv' hu'
    have hJw := hJP w hPw
    have hJw' := hJP w' hPw'
    have hJJ := hinv w w' hPw hPw'
    simp only [g69s_om_add_left, g69s_om_add_right, g69s_om_sub_right, g69s_om_sub_left,
      g69s_om_smul_left,
      g69s_om_smul_right, hA w hPw, hB w hPw, hA _ hJw, hB _ hJw, hwA w hPw, hwB w hPw,
      hA w' hPw', hB w' hPw', hA _ hJw', hB _ hJw', hwA _ hJw, hwB _ hJw, hwA w' hPw', hwB w' hPw',
      hBA, g69s_om_self, hJJ]
    ring

theorem g69s_liouvilleCLM_apply {n : ℕ} (x v : V n) : liouvilleCLM x v = liouville x v := by
  unfold liouvilleCLM liouville omega0 dot
  simp [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem g69s_scale_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem g69s_omega0_tames {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (y : V n) (hy : y ≠ 0) :
    (∀ v : V n, v ≠ 0 → 0 < omega0 v (Jtilde H J y v)) ∧
      ∀ v w : V n, omega0 (Jtilde H J y v) (Jtilde H J y w) = omega0 v w := by
  obtain ⟨hr, hHx⟩ := g69s_scale_spec H hH y hy
  set r := scaleToS H y with hrdef
  set x := proj H y with hxdef
  have hxr : x = r • y := rfl
  have hx : x ∈ energySurface H := hHx
  have hyx : y = r⁻¹ • x := by rw [hxr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨hc, hR1, hRH, hRw⟩ := g69s_reeb_spec H hH x hx
  set R := reeb H x
  set D := fderiv ℝ H x x
  have hD : 0 < D := hH.2.2 x hx
  have hLxx : liouville x x = 0 := by
    unfold liouville; rw [g69s_om_self]; ring
  have hJt : ∀ v, Jtilde H J y v =
      ((r / (2 * D)) * fderiv ℝ H x v) • (r⁻¹ • R) - (r * liouville x v) • ((2:ℝ) • y) +
        J x (v - ((r / (2 * D)) * fderiv ℝ H x v) • ((2:ℝ) • y) -
          (r * liouville x v) • (r⁻¹ • R)) := by
    intro v
    simp only [Jtilde, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      g69s_liouvilleCLM_apply]
    rfl
  have key := g69s_tame_abstract (n := n) ((2:ℝ) • y) (r⁻¹ • R) (IsInXi H x) (J x)
    (fun v => (r / (2 * D)) * fderiv ℝ H x v) (fun v => r * liouville x v)
    (by
      intro v
      constructor
      · unfold liouville
        rw [g69s_om_sub_right, g69s_om_sub_right, hyx]
        simp only [g69s_om_smul_right]
        have h1 : omega0 x x = 0 := g69s_om_self x
        have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
        rw [h1, h2]; field_simp; ring
      · simp only [map_sub, map_smul, smul_eq_mul, hRH, hyx]
        field_simp; ring)
    (fun w hw => (hJ.2 x hx w w hw hw).1)
    (fun w hw hw0 => (hJ.2 x hx w w hw hw).2.2.1 hw0)
    (fun w w' hw hw' => (hJ.2 x hx w w' hw hw').2.2.2)
    (by
      intro w hw
      rw [hyx, smul_smul, g69s_om_smul_left]
      have := hw.1; unfold liouville at this
      rw [show omega0 x w = 0 by linarith]; ring)
    (by
      intro w hw
      rw [g69s_om_smul_left, hRw w hw.2]; ring)
    (by
      rw [hyx, smul_smul, g69s_om_smul_left, g69s_om_smul_right]
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h2]; positivity)
  refine ⟨fun v hv => ?_, fun v w => ?_⟩
  · rw [hJt]; exact key.1 v hv
  · rw [hJt, hJt]; exact key.2 v w

theorem g69s_scale_unique {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (t : ℝ) (ht : 0 < t) (hHt : H (t • y) = 1) : scaleToS H y = t := by
  obtain ⟨r, _, hu⟩ := hH.2.1 y hy
  have h1 := hu t ⟨ht, hHt⟩
  have h2 := hu (scaleToS H y) (g69s_scale_spec H hH y hy)
  rw [h1, h2]

theorem g69s_scale_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y₀ : V n)
    (hy₀ : y₀ ≠ 0) : ContDiffAt ℝ ∞ (scaleToS H) y₀ := by
  obtain ⟨hr, hHx⟩ := g69s_scale_spec H hH y₀ hy₀
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
    exact (g69s_scale_unique H hH y h3 (ψ y) h2 h1').symm
  exact hψc.congr_of_eventuallyEq hev.symm


theorem g69s_j0_contDiff {n : ℕ} : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 (fun k => ?_)
  have : (fun v : V n => j0 v k) = fun v => g69s_sgn k * v (g69s_sig k) := by
    funext v; exact g69s_j0_apply v k
  rw [this]
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (g69s_sig k))

theorem g69s_dH_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)

theorem g69s_grad_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (grad H) := by
  refine contDiff_pi.2 (fun k => ?_)
  exact (g69s_dH_contDiff H hH).clm_apply contDiff_const

theorem g69s_hamVF_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamVF H) := g69s_j0_contDiff.comp (g69s_grad_contDiff H hH)

theorem g69s_liouvilleCLM_contDiff {n : ℕ} : ContDiff ℝ ∞ (liouvilleCLM : V n → V n →L[ℝ] ℝ) := by
  unfold liouvilleCLM
  refine ContDiff.const_smul _ (ContDiff.sum (fun k _ => ?_))
  exact ((contDiff_apply ℝ ℝ k).comp g69s_j0_contDiff).smul contDiff_const

theorem g69s_reeb_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContDiffAt ℝ ∞ (reeb H) x := by
  have hpos := (g69s_reeb_spec H hH x hx).1
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [g69s_liouvilleCLM_apply]
  have hc : ContDiff ℝ ∞ (fun x => liouville x (hamVF H x)) := by
    rw [hL]; exact g69s_liouvilleCLM_contDiff.clm_apply (g69s_hamVF_contDiff H hH.1)
  unfold reeb
  exact (hc.contDiffAt.inv hpos.ne').smul (g69s_hamVF_contDiff H hH.1).contDiffAt

theorem g69s_jtilde_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (y₀ : V n) (hy₀ : y₀ ≠ 0) :
    ContDiffAt ℝ ∞ (Jtilde H J) y₀ := by
  obtain ⟨hr, hHx⟩ := g69s_scale_spec H hH y₀ hy₀
  have hS := g69s_scale_contDiffAt H hH y₀ hy₀
  have hP : ContDiffAt ℝ ∞ (proj H) y₀ := hS.smul contDiffAt_id
  have hdH := g69s_dH_contDiff H hH.1
  have hdHx : ContDiffAt ℝ ∞ (fun y => fderiv ℝ H (proj H y)) y₀ := hdH.contDiffAt.comp y₀ hP
  have hD : ContDiffAt ℝ ∞ (fun y => fderiv ℝ H (proj H y) (proj H y)) y₀ := hdHx.clm_apply hP
  have hDpos : 0 < fderiv ℝ H (proj H y₀) (proj H y₀) := hH.2.2 _ hHx
  have hR : ContDiffAt ℝ ∞ (fun y => reeb H (proj H y)) y₀ :=
    (g69s_reeb_contDiffAt H hH (proj H y₀) hHx).comp y₀ hP
  have hLc : ContDiffAt ℝ ∞ (fun y => liouvilleCLM (proj H y)) y₀ :=
    g69s_liouvilleCLM_contDiff.contDiffAt.comp y₀ hP
  have hJc : ContDiffAt ℝ ∞ (fun y => J (proj H y)) y₀ := hJ.1.contDiffAt.comp y₀ hP
  have hα : ContDiffAt ℝ ∞ (fun y => (scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y))) •
      fderiv ℝ H (proj H y)) y₀ :=
    (hS.div (contDiffAt_const.mul hD) (by positivity)).smul hdHx
  have hβ : ContDiffAt ℝ ∞ (fun y => scaleToS H y • liouvilleCLM (proj H y)) y₀ := hS.smul hLc
  have hRl : ContDiffAt ℝ ∞ (fun y => (scaleToS H y)⁻¹ • reeb H (proj H y)) y₀ :=
    (hS.inv hr.ne').smul hR
  have hy2 : ContDiffAt ℝ ∞ (fun y : V n => (2:ℝ) • y) y₀ := contDiffAt_id.const_smul _
  have heq : Jtilde H J = fun y =>
      ((scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)).smulRight
        ((scaleToS H y)⁻¹ • reeb H (proj H y)) -
      (scaleToS H y • liouvilleCLM (proj H y)).smulRight ((2:ℝ) • y) +
      (J (proj H y)).comp (ContinuousLinearMap.id ℝ (V n) -
        ((scaleToS H y / (2 * fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)).smulRight
          ((2:ℝ) • y) -
        (scaleToS H y • liouvilleCLM (proj H y)).smulRight ((scaleToS H y)⁻¹ • reeb H (proj H y))) := by
    funext y; rfl
  rw [heq]
  exact ((hα.smulRight hRl).sub (hβ.smulRight hy2)).add
    (hJc.clm_comp ((contDiffAt_const.sub (hα.smulRight hy2)).sub (hβ.smulRight hRl)))

theorem g69s_sq_abstract {n : ℕ} (A B : V n) (P : V n → Prop) (J' : V n →L[ℝ] V n)
    (α β : V n →L[ℝ] ℝ)
    (hW : ∀ v, P (v - α v • A - β v • B)) (hJP : ∀ w, P w → P (J' w))
    (hJJ : ∀ w, P w → J' (J' w) = -w)
    (hαA : α A = 1) (hαB : α B = 0) (hβA : β A = 0) (hβB : β B = 1)
    (hαP : ∀ w, P w → α w = 0) (hβP : ∀ w, P w → β w = 0) (v : V n) :
    let T : V n → V n := fun v => α v • B - β v • A + J' (v - α v • A - β v • B)
    T (T v) = -v := by
  intro T
  have hPw := hW v
  have hPJw := hJP _ hPw
  have e1 : α (T v) = - β v := by
    simp only [T]; rw [map_add, hαP _ hPJw]
    simp only [map_sub, map_smul, hαA, hαB, smul_eq_mul]; ring
  have e2 : β (T v) = α v := by
    simp only [T]; rw [map_add, hβP _ hPJw]
    simp only [map_sub, map_smul, hβA, hβB, smul_eq_mul]; ring
  have e3 : T v - α (T v) • A - β (T v) • B = J' (v - α v • A - β v • B) := by
    rw [e1, e2]; simp only [T]; module
  show α (T v) • B - β (T v) • A + J' (T v - α (T v) • A - β (T v) • B) = -v
  rw [e3, hJJ _ hPw, e1, e2]
  module

theorem g69s_jtilde_sq {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (y : V n) (hy : y ≠ 0) :
    (Jtilde H J y).comp (Jtilde H J y) = -ContinuousLinearMap.id ℝ (V n) := by
  obtain ⟨hr, hHx⟩ := g69s_scale_spec H hH y hy
  set r := scaleToS H y with hrdef
  set x := proj H y with hxdef
  have hxr : x = r • y := rfl
  have hx : x ∈ energySurface H := hHx
  have hyx : y = r⁻¹ • x := by rw [hxr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨hc, hR1, hRH, hRw⟩ := g69s_reeb_spec H hH x hx
  set R := reeb H x
  set D := fderiv ℝ H x x
  have hD : 0 < D := hH.2.2 x hx
  have hLxx : liouville x x = 0 := by unfold liouville; rw [g69s_om_self]; ring
  ext1 v
  have key := g69s_sq_abstract ((2:ℝ) • y) (r⁻¹ • R) (IsInXi H x) (J x)
    ((r / (2 * D)) • fderiv ℝ H x) (r • liouvilleCLM x)
    (by
      intro v
      simp only [ContinuousLinearMap.smul_apply, g69s_liouvilleCLM_apply, smul_eq_mul]
      constructor
      · unfold liouville
        rw [g69s_om_sub_right, g69s_om_sub_right, hyx]
        simp only [g69s_om_smul_right]
        have h1 : omega0 x x = 0 := g69s_om_self x
        have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
        rw [h1, h2]; field_simp; ring
      · simp only [map_sub, map_smul, smul_eq_mul, hRH, hyx]
        field_simp; ring)
    (fun w hw => (hJ.2 x hx w w hw hw).1)
    (fun w hw => (hJ.2 x hx w w hw hw).2.1)
    (by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hyx]
      field_simp
      rfl)
    (by simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hRH]; ring)
    (by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, g69s_liouvilleCLM_apply, hyx]
      unfold liouville; simp only [g69s_om_smul_right, g69s_om_self]; ring)
    (by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, g69s_liouvilleCLM_apply]
      unfold liouville; simp only [g69s_om_smul_right]
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h2]; field_simp)
    (fun w hw => by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hw.2]; ring)
    (fun w hw => by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, g69s_liouvilleCLM_apply, hw.1]; ring)
    v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
  exact key

theorem g69s_jtilde_all {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) :
    JHolomorphic.IsAlmostComplexOn (Jtilde H J) {y | y ≠ 0} ∧
      ContDiffOn ℝ ∞ (proj H) {y | y ≠ 0} ∧ ContDiffOn ℝ ∞ (aCoord H) {y | y ≠ 0} ∧
      (∀ y : V n, y ≠ 0 → H (proj H y) = 1 ∧ y = Real.exp (2 * aCoord H y) • proj H y) ∧
      ∀ y : V n, y ≠ 0 → ∀ c : ℝ, 0 < c → Jtilde H J (c • y) = Jtilde H J y := by
  refine ⟨⟨isOpen_ne, fun y hy => (g69s_jtilde_contDiffAt H hH J hJ y hy).contDiffWithinAt,
    fun y hy => g69s_jtilde_sq H hH J hJ y hy⟩, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun y hy c hc => ?_⟩
  · exact ((g69s_scale_contDiffAt H hH y hy).smul contDiffAt_id).contDiffWithinAt
  · obtain ⟨hr, _⟩ := g69s_scale_spec H hH y hy
    exact ((((g69s_scale_contDiffAt H hH y hy).log hr.ne').neg).div_const 2).contDiffWithinAt
  · obtain ⟨hr, hHx⟩ := g69s_scale_spec H hH y hy
    refine ⟨hHx, ?_⟩
    unfold aCoord proj
    rw [smul_smul, show 2 * (-Real.log (scaleToS H y) / 2) = -Real.log (scaleToS H y) by ring,
      Real.exp_neg, Real.exp_log hr, inv_mul_cancel₀ hr.ne', one_smul]
  · obtain ⟨hr, hHx⟩ := g69s_scale_spec H hH y hy
    have hcy : c • y ≠ 0 := smul_ne_zero hc.ne' hy
    have hsc : scaleToS H (c • y) = scaleToS H y / c := by
      apply g69s_scale_unique H hH _ hcy _ (div_pos hr hc)
      rw [smul_smul, div_mul_cancel₀ _ hc.ne']; exact hHx
    have hpr : proj H (c • y) = proj H y := by
      unfold proj; rw [hsc, smul_smul, div_mul_cancel₀ _ hc.ne']
    ext1 v
    have hform : ∀ z : V n, Jtilde H J z v =
        ((scaleToS H z / (2 * fderiv ℝ H (proj H z) (proj H z))) * fderiv ℝ H (proj H z) v) •
          ((scaleToS H z)⁻¹ • reeb H (proj H z)) -
        (scaleToS H z * liouvilleCLM (proj H z) v) • ((2:ℝ) • z) +
        J (proj H z) (v -
          ((scaleToS H z / (2 * fderiv ℝ H (proj H z) (proj H z))) * fderiv ℝ H (proj H z) v) •
            ((2:ℝ) • z) -
          (scaleToS H z * liouvilleCLM (proj H z) v) • ((scaleToS H z)⁻¹ • reeb H (proj H z))) :=
      fun z => rfl
    rw [hform, hform, hpr, hsc]
    set r := scaleToS H y
    set D := fderiv ℝ H (proj H y) (proj H y)
    set R := reeb H (proj H y)
    have k1 : ∀ a : ℝ, (r / c / (2 * D) * a) • ((r / c)⁻¹ • R) = (r / (2 * D) * a) • (r⁻¹ • R) := by
      intro a; rw [smul_smul, smul_smul]; congr 1; field_simp
    have k2 : ∀ a : ℝ, (r / c * a) • ((2:ℝ) • (c • y)) = (r * a) • ((2:ℝ) • y) := by
      intro a; simp only [smul_smul]; congr 1; field_simp
    have k3 : ∀ a : ℝ, (r / c / (2 * D) * a) • ((2:ℝ) • (c • y)) = (r / (2 * D) * a) • ((2:ℝ) • y) := by
      intro a; simp only [smul_smul]; congr 1; field_simp
    have k4 : ∀ a : ℝ, (r / c * a) • ((r / c)⁻¹ • R) = (r * a) • (r⁻¹ • R) := by
      intro a; rw [smul_smul, smul_smul]; congr 1; field_simp
    rw [k1, k2, k3, k4]

theorem g69s_scale_hasFDerivAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) :
    HasFDerivAt (scaleToS H)
      ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)) y := by
  obtain ⟨hr, hHx⟩ := g69s_scale_spec H hH y hy
  have hd : DifferentiableAt ℝ (scaleToS H) y :=
    (g69s_scale_contDiffAt H hH y hy).differentiableAt (by simp)
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
    exact (g69s_scale_spec H hH y' hy').2
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

theorem g69s_hol_abstract {n : ℕ} (A B : V n) (P : V n → Prop) (J' : V n →L[ℝ] V n)
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
  have hBB : omega0 B B = 0 := g69s_om_self B
  have hJwB : omega0 (J' w) B = 0 := by rw [g69s_om_anti, hB _ hPJw, neg_zero]
  refine ⟨e1, by linarith, ?_, ?_⟩
  · rw [hus, hut]
    simp only [g69s_om_add_right, g69s_om_sub_left, g69s_om_smul_left, g69s_om_smul_right,
      hBB, hB _ hPw, hJwB]
    rw [g69s_om_anti (J' w) w]; ring
  · intro h1 h2 h3
    have hw0 : w = 0 := h3
    have hα : α ut = 0 := by linarith
    have hJ0 : J' w = 0 := by rw [hw0, map_zero]
    constructor
    · rw [hs, hJ0, h2, hα]; simp
    · have : ut = α ut • A + β ut • B + w := by rw [hwdef]; module
      rw [this, hα, h2, hw0]; simp

theorem g69s_clm_complex_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) (h1 : L 1 = 0) (hI : L Complex.I = 0) : L = 0 := by
  ext1 z
  have : z = z.re • (1:ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [this, map_add, map_smul, map_smul, h1, hI]; simp

theorem g69s_cr {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
    dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  set y := u z with hydef
  obtain ⟨hr, hHx⟩ := g69s_scale_spec H hH y hz
  set r := scaleToS H y with hrdef
  set x := proj H y with hxdef
  have hxr : x = r • y := rfl
  have hx : x ∈ energySurface H := hHx
  have hyx : y = r⁻¹ • x := by rw [hxr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨hc, hR1, hRH, hRw⟩ := g69s_reeb_spec H hH x hx
  set R := reeb H x
  set D := fderiv ℝ H x x
  have hD : 0 < D := hH.2.2 x hx
  set α : V n →L[ℝ] ℝ := (r / (2 * D)) • fderiv ℝ H x with hαdef
  set β : V n →L[ℝ] ℝ := r • liouvilleCLM x with hβdef
  set A : V n := (2:ℝ) • y
  set B : V n := r⁻¹ • R
  have hLA : liouvilleCLM x A = 0 := by
    simp only [A, hyx, g69s_liouvilleCLM_apply]
    unfold liouville; simp only [g69s_om_smul_right, g69s_om_self]; ring
  -- derivatives
  have hS' := g69s_scale_hasFDerivAt H hH y hz
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
    simp only [hαdef, hβdef, ContinuousLinearMap.smul_apply, g69s_liouvilleCLM_apply, smul_eq_mul]
    constructor
    · unfold liouville
      rw [g69s_om_sub_right, g69s_om_sub_right]
      simp only [A, B, hyx, g69s_om_smul_right]
      have h1 : omega0 x x = 0 := g69s_om_self x
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h1, h2]; field_simp; ring
    · simp only [A, B, map_sub, map_smul, smul_eq_mul, hRH, hyx]
      field_simp; ring
  have key := g69s_hol_abstract A B (IsInXi H x) (J x) α β hWgen
    (fun w hw => (hJ.2 x hx w w hw hw).1)
    (by
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hyx]
      field_simp
      rfl)
    (by simp only [hαdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hRH]; ring)
    (by
      simp only [hβdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, g69s_liouvilleCLM_apply, hyx]
      unfold liouville; simp only [g69s_om_smul_right, g69s_om_self]; ring)
    (by
      simp only [hβdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, g69s_liouvilleCLM_apply]
      unfold liouville; simp only [g69s_om_smul_right]
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h2]; field_simp)
    (fun w hw => by
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, hw.2]; ring)
    (fun w hw => by
      simp only [hβdef, ContinuousLinearMap.smul_apply, smul_eq_mul, g69s_liouvilleCLM_apply, hw.1]; ring)
    (fun w hw => by simp only [B]; rw [g69s_om_smul_left, hRw w hw.2]; ring)
    us ut hhol
  obtain ⟨e1, e2, e3, e4⟩ := key
  set W := ut - α ut • A - β ut • B
  have hPW : IsInXi H x W := hWgen ut
  have hm : 0 ≤ omega0 W (J x W) := by
    by_cases h0 : W = 0
    · rw [h0, map_zero, g69s_om_self]
    · exact ((hJ.2 x hx W W hPW hPW).2.2.1 h0).le
  have hLs : liouville x (r • (us - α us • A)) = β us := by
    rw [← g69s_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  have hLt : liouville x (r • (ut - α ut • A)) = β ut := by
    rw [← g69s_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  refine ⟨?_, ?_⟩
  · rw [hdsa, hdtw, hLt, e1]
  · rw [hdta, hdsw, hLs, e2]


theorem g69s_pointwise {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0) (φ : ℝ → ℝ) :
    ∃ p q m : ℝ, 0 ≤ m ∧
      energyDensity H φ u z = deriv φ (aCoord H (u z)) * (p ^ 2 + q ^ 2) + φ (aCoord H (u z)) * m ∧
      dlambdaDensity H u z = m ∧ (p = 0 → q = 0 → m = 0 → fderiv ℝ u z = 0) := by
  set y := u z with hydef
  obtain ⟨hr, hHx⟩ := g69s_scale_spec H hH y hz
  set r := scaleToS H y with hrdef
  set x := proj H y with hxdef
  have hxr : x = r • y := rfl
  have hx : x ∈ energySurface H := hHx
  have hyx : y = r⁻¹ • x := by rw [hxr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨hc, hR1, hRH, hRw⟩ := g69s_reeb_spec H hH x hx
  set R := reeb H x
  set D := fderiv ℝ H x x
  have hD : 0 < D := hH.2.2 x hx
  set α : V n →L[ℝ] ℝ := (r / (2 * D)) • fderiv ℝ H x with hαdef
  set β : V n →L[ℝ] ℝ := r • liouvilleCLM x with hβdef
  set A : V n := (2:ℝ) • y
  set B : V n := r⁻¹ • R
  have hLA : liouvilleCLM x A = 0 := by
    simp only [A, hyx, g69s_liouvilleCLM_apply]
    unfold liouville; simp only [g69s_om_smul_right, g69s_om_self]; ring
  -- derivatives
  have hS' := g69s_scale_hasFDerivAt H hH y hz
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
    simp only [hαdef, hβdef, ContinuousLinearMap.smul_apply, g69s_liouvilleCLM_apply, smul_eq_mul]
    constructor
    · unfold liouville
      rw [g69s_om_sub_right, g69s_om_sub_right]
      simp only [A, B, hyx, g69s_om_smul_right]
      have h1 : omega0 x x = 0 := g69s_om_self x
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h1, h2]; field_simp; ring
    · simp only [A, B, map_sub, map_smul, smul_eq_mul, hRH, hyx]
      field_simp; ring
  have key := g69s_hol_abstract A B (IsInXi H x) (J x) α β hWgen
    (fun w hw => (hJ.2 x hx w w hw hw).1)
    (by
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hyx]
      field_simp
      rfl)
    (by simp only [hαdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hRH]; ring)
    (by
      simp only [hβdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, g69s_liouvilleCLM_apply, hyx]
      unfold liouville; simp only [g69s_om_smul_right, g69s_om_self]; ring)
    (by
      simp only [hβdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, g69s_liouvilleCLM_apply]
      unfold liouville; simp only [g69s_om_smul_right]
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h2]; field_simp)
    (fun w hw => by
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, hw.2]; ring)
    (fun w hw => by
      simp only [hβdef, ContinuousLinearMap.smul_apply, smul_eq_mul, g69s_liouvilleCLM_apply, hw.1]; ring)
    (fun w hw => by simp only [B]; rw [g69s_om_smul_left, hRw w hw.2]; ring)
    us ut hhol
  obtain ⟨e1, e2, e3, e4⟩ := key
  set W := ut - α ut • A - β ut • B
  have hPW : IsInXi H x W := hWgen ut
  have hm : 0 ≤ omega0 W (J x W) := by
    by_cases h0 : W = 0
    · rw [h0, map_zero, g69s_om_self]
    · exact ((hJ.2 x hx W W hPW hPW).2.2.1 h0).le
  have hLs : liouville x (r • (us - α us • A)) = β us := by
    rw [← g69s_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  have hLt : liouville x (r • (ut - α ut • A)) = β ut := by
    rw [← g69s_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  refine ⟨β us, β ut, r ^ 2 * omega0 W (J x W), by positivity, ?_, ?_, ?_⟩
  · unfold energyDensity
    simp only []
    rw [hdsa, hdta, hdsw, hdtw, hLs, hLt, g69s_om_smul_left, g69s_om_smul_right, e3, e1, e2]
    ring
  · unfold dlambdaDensity
    rw [hdsw, hdtw, g69s_om_smul_left, g69s_om_smul_right, e3]; ring
  · intro hp hq hm0
    have hW0 : W = 0 := by
      by_contra h0
      have := (hJ.2 x hx W W hPW hPW).2.2.1 h0
      have : 0 < r ^ 2 * omega0 W (J x W) := by positivity
      linarith
    obtain ⟨h1, h2⟩ := e4 hp hq hW0
    exact g69s_clm_complex_eq_zero _ h1 h2


namespace FEPA3

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

variable {n : ℕ}

/-- The partner index `2i ↔ 2i+1`. -/
def pairIdx (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

theorem pairIdx_involutive : Function.Involutive (pairIdx (n := n)) := by
  intro k
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [pairIdx, h, h', dite_true, dite_false]
    ext; simp
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [pairIdx, h, h', dite_true, dite_false]
    ext; simp; omega

theorem j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring

theorem j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; simp only [j0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- `j0` as a continuous linear map. -/
noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := j0_add, map_smul' := j0_smul }

@[simp] theorem j0L_apply (u : V n) : j0L u = j0 u := rfl

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def omegaL : V n →L[ℝ] V n →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k)

theorem omegaL_apply (u v : V n) : omegaL u v = omega0 u v := by
  simp [omegaL, omega0, dot, ContinuousLinearMap.sum_apply]

theorem omega0_antisymm (u v : V n) : omega0 u v = -omega0 v u := by
  have e := Equiv.sum_comp (Function.Involutive.toPerm _ (pairIdx_involutive (n := n)))
    (fun k => j0 u k * v k)
  simp only [omega0, dot]
  rw [← e, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.Involutive.coe_toPerm, pairIdx, j0]
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false, dite_true, dite_false]
    have : (⟨(k : ℕ) + 1 - 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp
    rw [this]; ring
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false, dite_true, dite_false]
    have : (⟨(k : ℕ) - 1 + 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp; omega
    rw [this]; ring


/-- The boundary term of a map `w` on the circle of radius `r`. -/
noncomputable def bdryTerm {n : ℕ} (w : ℂ → V n) (r : ℝ) : ℝ :=
  (1 / 2) * ∫ θ in (0 : ℝ)..2 * π,
    omegaL (w (circleMap 0 r θ)) (fderiv ℝ w (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))

theorem continuousOn_dens {n : ℕ} (w : ℂ → V n) {U : Set ℂ} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) :
    ContinuousOn (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I)) U := by
  have hd : ContinuousOn (fderiv ℝ w) U := hw.continuousOn_fderiv_of_isOpen hU (by simp)
  simp_rw [← omegaL_apply]
  exact ((omegaL.continuous.comp_continuousOn (hd.clm_apply continuousOn_const)).clm_apply
    (hd.clm_apply continuousOn_const))

/-- Stokes on an annulus inside an open set. -/
theorem annulus_eq {n : ℕ} (w : ℂ → V n) {U : Set ℂ} (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hsub : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → z ∈ U) :
    ∫ z in ball 0 b \ ball 0 a, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      bdryTerm w b - bdryTerm w a := by
  have hc : ContinuousOn (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I))
      (closedBall 0 b \ ball 0 a) := by
    refine (continuousOn_dens w hU hw).mono ?_
    intro z hz
    refine hsub z ?_ ?_
    · simpa using hz.2
    · simpa using hz.1
  rw [setIntegral_annulus_eq_integral_circleMap ha hab hc]
  have hS := integral_mul_integral_bilin_circleMap_eq (omegaL (n := n))
    (fun x y => by rw [omegaL_apply, omegaL_apply, omega0_antisymm]) hU
    (hw.of_le (WithTop.coe_le_coe.2 le_top)) ha hab hsub 0
  simp only [sub_zero, omegaL_apply] at hS
  simp only [smul_eq_mul, bdryTerm, omegaL_apply]
  exact hS

/-- The action of the clockwise loop is minus the boundary term. -/
theorem loopAction_cw_eq {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) {U : Set ℂ} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ (fun z => proj H (u z)) U) (ρ : ℝ) (hρ : ∀ θ, circleMap 0 ρ θ ∈ U) :
    loopAction H u (cwLoop 0 ρ) = -bdryTerm (fun z => proj H (u z)) ρ := by
  set w := fun z => proj H (u z) with hwdef
  have hcm : ∀ t : ℝ, cwLoop 0 ρ t = circleMap 0 ρ (-(2 * π) * t) := by
    intro t; simp [cwLoop, circleMap]
  have hloop : loopInS H u (cwLoop 0 ρ) = fun t => w (circleMap 0 ρ (-(2 * π) * t)) := by
    funext t; simp [loopInS, hwdef, hcm]
  have hder : ∀ t : ℝ, deriv (loopInS H u (cwLoop 0 ρ)) t =
      (-(2 * π)) • fderiv ℝ w (circleMap 0 ρ (-(2 * π) * t))
        (circleMap 0 ρ (-(2 * π) * t) * Complex.I) := by
    intro t
    rw [hloop]
    have hh : HasDerivAt (fun t : ℝ => -(2 * π) * t) (-(2 * π)) t := by
      simpa using (hasDerivAt_id t).const_mul (-(2 * π))
    have h1 := (hasDerivAt_circleMap 0 ρ (-(2 * π) * t)).scomp t hh
    have h2 : HasFDerivAt w (fderiv ℝ w (circleMap 0 ρ (-(2 * π) * t))) (circleMap 0 ρ (-(2 * π) * t)) :=
      ((hw.contDiffAt (hU.mem_nhds (hρ _))).differentiableAt (by simp)).hasFDerivAt
    have := h2.comp_hasDerivAt t h1
    rw [show (fun t => w (circleMap 0 ρ (-(2 * π) * t))) =
      w ∘ (circleMap 0 ρ ∘ fun t => -(2 * π) * t) from rfl, this.deriv, ← map_smul]
  set f : ℝ → ℝ := fun θ => omegaL (w (circleMap 0 ρ θ))
      (fderiv ℝ w (circleMap 0 ρ θ) (circleMap 0 ρ θ * Complex.I)) with hfdef
  have hper : Function.Periodic f (2 * π) := by
    intro θ; simp only [hfdef, periodic_circleMap 0 ρ θ]
  unfold loopAction
  simp_rw [hder, hloop]
  simp only [liouville, map_smul, smul_eq_mul]
  have e : ∀ t : ℝ, omega0 (w (circleMap 0 ρ (-(2 * π) * t)))
      ((-(2 * π)) • fderiv ℝ w (circleMap 0 ρ (-(2 * π) * t))
        (circleMap 0 ρ (-(2 * π) * t) * Complex.I)) / 2 = (-π) * f (-(2 * π) * t) := by
    intro t
    simp only [hfdef, ← omegaL_apply, map_smul, smul_eq_mul]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left f (by have := Real.pi_pos; intro h; linarith : (-(2 * π) : ℝ) ≠ 0),
    mul_one, mul_zero, intervalIntegral.integral_symm]
  have hp := hper.intervalIntegral_add_eq (-(2 * π)) 0
  simp only [mul_zero, mul_one, neg_add_cancel, zero_add] at hp
  rw [hp, bdryTerm, smul_eq_mul]
  field_simp
  ring

end FEPA3

namespace FEPA3R

open FiniteEnergyPlane FEPA3
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- The level `S` is bounded and bounded away from `0`. -/
theorem proj_bounds {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) :
    ∃ d₀ M₀ : ℝ, 0 < d₀ ∧ ∀ y : V n, y ≠ 0 → d₀ ≤ ‖proj H y‖ ∧ ‖proj H y‖ ≤ M₀ := by
  obtain ⟨-, hprojs, -, hrep, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hH0 : H 0 ≠ 1 := by
    intro h
    have := hH.2.2 0 h
    simp at this
  have hopen : IsOpen {x : V n | H x ≠ 1} := isOpen_ne_fun hH.1.continuous continuous_const
  obtain ⟨d₀, hd₀, hball⟩ := Metric.isOpen_iff.1 hopen 0 hH0
  obtain ⟨M₀, hM₀⟩ := (isCompact_sphere (0 : V n) 1).exists_bound_of_continuousOn
    (hprojs.continuousOn.mono (fun y hy => by
      rw [mem_sphere_zero_iff_norm] at hy
      intro h; rw [h, norm_zero] at hy; norm_num at hy))
  refine ⟨d₀, M₀, hd₀, fun y hy => ⟨?_, ?_⟩⟩
  · by_contra hlt
    push_neg at hlt
    have : proj H y ∈ ball (0 : V n) d₀ := by rw [mem_ball_zero_iff]; exact hlt
    exact hball this (hrep y hy).1
  · have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
    set e : V n := ‖y‖⁻¹ • y with hedef
    have he : e ∈ sphere (0 : V n) 1 := by
      rw [mem_sphere_zero_iff_norm, hedef, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hny.ne']
    have he0 : e ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at he; norm_num at he
    obtain ⟨hs, hHs⟩ := g69s_scale_spec H hH y hy
    have hsc : scaleToS H e = scaleToS H y * ‖y‖ := by
      apply g69s_scale_unique H hH e he0 _ (mul_pos hs hny)
      rw [hedef, smul_smul, mul_assoc, mul_inv_cancel₀ hny.ne', mul_one]
      exact hHs
    have hpe : proj H e = proj H y := by
      unfold proj
      rw [hsc, hedef, smul_smul, mul_assoc, mul_inv_cancel₀ hny.ne', mul_one]
    rw [← hpe]
    exact hM₀ e he

/-- Uniform taming of `J̃` on a compact set avoiding `0`. -/
theorem uniform_tame {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (K : Set (V n))
    (hK : IsCompact K) (hKO : K ⊆ {y | y ≠ 0}) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K, ∀ v : V n, c * ‖v‖ ^ 2 ≤ omega0 v (Jtilde H J y v) := by
  obtain ⟨hJa, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hJc : ContinuousOn (Jtilde H J) K := hJa.2.1.continuousOn.mono hKO
  rcases K.eq_empty_or_nonempty with hKe | hKe
  · exact ⟨1, one_pos, fun y hy => by rw [hKe] at hy; exact absurd hy (Set.notMem_empty y)⟩
  set f : V n × V n → ℝ := fun p => omegaL p.2 (Jtilde H J p.1 p.2) with hfdef
  have hfc : ContinuousOn f (K ×ˢ sphere (0 : V n) 1) := by
    have h1 : ContinuousOn (fun p : V n × V n => Jtilde H J p.1) (K ×ˢ sphere (0 : V n) 1) :=
      hJc.comp continuousOn_fst (fun p hp => hp.1)
    exact (omegaL.continuous.comp_continuousOn continuousOn_snd).clm_apply
      (h1.clm_apply continuousOn_snd)
  have hSne : (sphere (0 : V n) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨p₀, hp₀, hmin⟩ := (hK.prod (isCompact_sphere 0 1)).exists_isMinOn
    (hKe.prod hSne) hfc
  have hp₀2 : p₀.2 ≠ 0 := by
    intro h; have := hp₀.2; rw [h, mem_sphere_zero_iff_norm, norm_zero] at this; norm_num at this
  have hc : 0 < f p₀ := by
    simp only [hfdef, omegaL_apply]
    exact (omega0_tames_jtilde H hH J hJ p₀.1 (hKO hp₀.1)).1 _ hp₀2
  refine ⟨f p₀, hc, fun y hy v => ?_⟩
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp [omega0, dot]
  · have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
    set e : V n := ‖v‖⁻¹ • v with hedef
    have he : e ∈ sphere (0 : V n) 1 := by
      rw [mem_sphere_zero_iff_norm, hedef, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hnv.ne']
    have hm := hmin (show (y, e) ∈ K ×ˢ sphere (0 : V n) 1 from ⟨hy, he⟩)
    simp only [hfdef, omegaL_apply] at hm
    have hve : v = ‖v‖ • e := by
      rw [hedef, smul_smul, mul_inv_cancel₀ hnv.ne', one_smul]
    have : omega0 v (Jtilde H J y v) = ‖v‖ ^ 2 * omega0 e (Jtilde H J y e) := by
      conv_lhs => rw [hve]
      rw [map_smul, ← omegaL_apply, ← omegaL_apply, map_smul, map_smul]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [this]
    have h2 : 0 ≤ ‖v‖ ^ 2 := by positivity
    simp only [hfdef, omegaL_apply] at hc ⊢
    have hm' : omega0 p₀.2 ((Jtilde H J p₀.1) p₀.2) ≤ omega0 e ((Jtilde H J y) e) := hm
    nlinarith

end FEPA3R

namespace FEPA3R

open FiniteEnergyPlane FEPA3
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem g69s_logistic_hasDerivAt (s : ℝ) :
    HasDerivAt (fun s : ℝ => (1 + Real.exp (-s))⁻¹)
      (Real.exp (-s) / (1 + Real.exp (-s)) ^ 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + Real.exp (-s)) (-Real.exp (-s)) s := by
    have := ((hasDerivAt_neg s).exp).const_add 1
    simpa using this
  have h2 := h1.inv (by positivity)
  rw [neg_neg] at h2
  exact h2

theorem g69s_logistic_admissible : Admissible (fun s : ℝ => (1 + Real.exp (-s))⁻¹) := by
  refine ⟨?_, ?_, fun s => ⟨by positivity, ?_⟩⟩
  · exact (contDiff_const.add (Real.contDiff_exp.comp contDiff_neg)).inv
      (fun s => by have := Real.exp_pos (-s); simp only [Function.comp]; linarith)
  · intro a b hab
    simp only
    apply inv_anti₀ (by positivity)
    have : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
    linarith
  · apply inv_le_one_of_one_le₀
    have := Real.exp_pos (-s); linarith

theorem logistic_bounds {A s : ℝ} (hs : |s| ≤ A) :
    Real.exp (-A) / (1 + Real.exp A) ^ 2 ≤
        deriv (fun s : ℝ => (1 + Real.exp (-s))⁻¹) s ∧
      Real.exp (-A) / (1 + Real.exp A) ^ 2 ≤ (1 + Real.exp (-s))⁻¹ := by
  rw [(g69s_logistic_hasDerivAt s).deriv]
  have hA : 0 ≤ A := (abs_nonneg s).trans hs
  rw [abs_le] at hs
  have h1 : Real.exp (-A) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-s) ≤ Real.exp A := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-A) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hp1 := Real.exp_pos (-A)
  have hp2 := Real.exp_pos (-s)
  have hp3 := Real.exp_pos A
  constructor
  · apply div_le_div₀ hp2.le h1 (by positivity)
    have : 1 + Real.exp (-s) ≤ 1 + Real.exp A := by linarith
    gcongr
  · rw [div_le_iff₀ (by positivity)]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul h3 (show 1 + Real.exp (-s) ≤ (1 + Real.exp A) ^ 2 by nlinarith)
      (by positivity) (by norm_num)]

end FEPA3R

namespace FEPA3R

open FiniteEnergyPlane FEPA3
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Pointwise bound of the Dirichlet density by Hofer's energy density, for any `φ` whose value
and derivative are at least `c₀` at the point, uniformly over curves with values in a compact
`K ⊆ {y ≠ 0}` below a fixed level. (A variant of fizzyinc3's `dirichlet_pt`.) -/
theorem zc_dirichlet_pt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (K : Set (V n))
    (hK : IsCompact K) (hKO : K ⊆ {y | y ≠ 0}) (A c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : Set ℂ, IsOpen U → ∀ u : ℂ → V n, ContDiffOn ℝ ∞ u U →
      (∀ z ∈ U, u z ≠ 0) → JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u → ∀ φ : ℝ → ℝ,
      ∀ z ∈ U, u z ∈ K → aCoord H (u z) ≤ A → c₀ ≤ deriv φ (aCoord H (u z)) →
      c₀ ≤ φ (aCoord H (u z)) → ‖fderiv ℝ u z‖ ^ 2 ≤ C * energyDensity H φ u z := by
  obtain ⟨hJa, hprojs, haCs, hrep, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨c, hc, htame⟩ := uniform_tame H hH J hJ K hK hKO
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hJa.2.1.continuousOn.mono hKO)
  set M' := max M 0 with hM'def
  refine ⟨(1 + M') ^ 2 / c * (4 * Real.exp (4 * A) / c₀), by positivity, ?_⟩
  intro U hU u hu1 hu2 hu3 φ z hz hzK haA hb1 hb2
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  have hdu := (hu3 z hz).1
  have hhol := (hu3 z hz).2
  have huz := hu2 z hz
  set us := fderiv ℝ u z 1 with husdef
  set ut := fderiv ℝ u z Complex.I with hutdef
  set Jy := Jtilde H J (u z) with hJydef
  have hJJ : ∀ v, Jy (Jy v) = -v := by
    intro v
    have := congrArg (fun L : V n →L[ℝ] V n => L v) (hJa.2.2 (u z) huz)
    simpa using this
  have hut : Jy us = ut := by
    have h0 : us + Jy ut = 0 := hhol
    have : us = -Jy ut := eq_neg_of_add_eq_zero_left h0
    rw [this, map_neg, hJJ, neg_neg]
  have hDu : ‖fderiv ℝ u z‖ ≤ ‖us‖ + ‖ut‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ζ => ?_
    have hζ : ζ = ζ.re • (1 : ℂ) + ζ.im • Complex.I := by apply Complex.ext <;> simp
    rw [hζ, map_add, map_smul, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← hζ]
    have := Complex.abs_re_le_norm ζ
    have := Complex.abs_im_le_norm ζ
    nlinarith [norm_nonneg us, norm_nonneg ut]
  have hutn : ‖ut‖ ≤ M' * ‖us‖ := by
    rw [← hut]
    refine (Jy.le_opNorm us).trans ?_
    exact mul_le_mul_of_nonneg_right ((hM _ hzK).trans (le_max_left _ _)) (norm_nonneg _)
  have htm : c * ‖us‖ ^ 2 ≤ omega0 us ut := by
    have := htame (u z) hzK us
    rwa [hut] at this
  have hda : DifferentiableAt ℝ a z :=
    (haCs.comp hu1 (fun z hz => hu2 z hz)).differentiableOn (by simp) z hz
      |>.differentiableAt (hU.mem_nhds hz)
  have hdw : DifferentiableAt ℝ w z :=
    (hprojs.comp hu1 (fun z hz => hu2 z hz)).differentiableOn (by simp) z hz
      |>.differentiableAt (hU.mem_nhds hz)
  set E := Real.exp (2 * a z) with hEdef
  have hexp : HasFDerivAt (fun y => Real.exp (2 * a y)) (E • ((2 : ℝ) • fderiv ℝ a z)) z :=
    (hda.hasFDerivAt.const_mul 2).exp
  have hF := hexp.smul hdw.hasFDerivAt
  have hev : u =ᶠ[𝓝 z] (fun y => Real.exp (2 * a y)) • w := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact (hrep (u y) (hu2 y hy)).2
  have hfd : fderiv ℝ u z = E • fderiv ℝ w z + (E • ((2 : ℝ) • fderiv ℝ a z)).smulRight (w z) :=
    (hF.congr_of_eventuallyEq hev).fderiv
  set as := fderiv ℝ a z 1
  set at' := fderiv ℝ a z Complex.I
  set ws := fderiv ℝ w z 1
  set wt := fderiv ℝ w z Complex.I
  have hus : us = E • ws + (E * (2 * as)) • w z := by
    rw [husdef, hfd]; simp [smul_eq_mul]; rfl
  have hut' : ut = E • wt + (E * (2 * at')) • w z := by
    rw [hutdef, hfd]; simp [smul_eq_mul]; rfl
  set X := ds a z * liouville (w z) (dt w z) - dt a z * liouville (w z) (ds w z) with hXdef
  set Y := omega0 (ds w z) (dt w z) with hYdef
  have hid : omega0 us ut = E ^ 2 * (4 * X + Y) := by
    rw [hus, hut']
    simp only [g69s_om_add_left, g69s_om_add_right, g69s_om_smul_left, g69s_om_smul_right,
      g69s_om_self, hXdef, hYdef, ds, dt, liouville]
    rw [g69s_om_anti ws (w z)]
    ring
  obtain ⟨p, q, m, hm, he, hd, -⟩ := g69s_pointwise H hH J hJ u z hdu huz hhol (fun s => s)
  have hY : Y = m := hd
  have hX : X = p ^ 2 + q ^ 2 := by
    have he' : energyDensity H (fun s => s) u z = 1 * X + a z * Y := by
      simp only [energyDensity, deriv_id'']; rfl
    rw [he', deriv_id'', hY] at he
    linarith
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hY0 : 0 ≤ Y := by rw [hY]; exact hm
  have hED : energyDensity H φ u z = deriv φ (a z) * X + φ (a z) * Y := rfl
  have hEDl : c₀ * (X + Y) ≤ energyDensity H φ u z := by
    rw [hED]; nlinarith
  have hE2 : E ^ 2 ≤ Real.exp (4 * A) := by
    rw [hEdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast
    have : a z ≤ A := haA
    linarith
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have step1 : ‖fderiv ℝ u z‖ ^ 2 ≤ (1 + M') ^ 2 * ‖us‖ ^ 2 := by
    have : ‖fderiv ℝ u z‖ ≤ (1 + M') * ‖us‖ := by linarith
    have h0 := norm_nonneg (fderiv ℝ u z)
    calc ‖fderiv ℝ u z‖ ^ 2 ≤ ((1 + M') * ‖us‖) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = (1 + M') ^ 2 * ‖us‖ ^ 2 := by ring
  have step2 : ‖us‖ ^ 2 ≤ omega0 us ut / c := by rw [le_div_iff₀ hc]; linarith
  have step3 : omega0 us ut ≤ Real.exp (4 * A) * 4 * (X + Y) := by
    rw [hid]; nlinarith
  have step4 : X + Y ≤ energyDensity H φ u z / c₀ := by
    rw [le_div_iff₀ hc₀]; linarith
  have hpos1 : 0 ≤ (1 + M') ^ 2 := by positivity
  calc ‖fderiv ℝ u z‖ ^ 2 ≤ (1 + M') ^ 2 * (omega0 us ut / c) :=
        step1.trans (mul_le_mul_of_nonneg_left step2 hpos1)
    _ ≤ (1 + M') ^ 2 * (Real.exp (4 * A) * 4 * (energyDensity H φ u z / c₀) / c) := by
        apply mul_le_mul_of_nonneg_left _ hpos1
        apply div_le_div_of_nonneg_right _ hc.le
        exact step3.trans (mul_le_mul_of_nonneg_left step4 (by positivity))
    _ = (1 + M') ^ 2 / c * (4 * Real.exp (4 * A) / c₀) * energyDensity H φ u z := by
        field_simp

end FEPA3R

namespace FEPA3R

open FiniteEnergyPlane FEPA3
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Positive rescaling shifts `aCoord` by `log c / 2` and fixes `proj`. -/
theorem zc_aCoord_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (c : ℝ) (hc : 0 < c) :
    aCoord H (c • y) = aCoord H y + Real.log c / 2 ∧ proj H (c • y) = proj H y := by
  obtain ⟨hs, hHs⟩ := g69s_scale_spec H hH y hy
  have hcy : c • y ≠ 0 := smul_ne_zero hc.ne' hy
  have hsc : scaleToS H (c • y) = scaleToS H y / c := by
    refine g69s_scale_unique H hH (c • y) hcy _ (div_pos hs hc) ?_
    rw [smul_smul, div_mul_cancel₀ _ hc.ne']; exact hHs
  constructor
  · unfold aCoord
    rw [hsc, Real.log_div hs.ne' hc.ne']
    ring
  · unfold proj
    rw [hsc, smul_smul, div_mul_cancel₀ _ hc.ne']

/-- The energy density of the rescaled curve `e^{-2A} u` for `φ` is that of `u` for `φ(· - A)`. -/
theorem zc_energyDensity_smul_exp {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (u : ℂ → V n) (U : Set ℂ) (hU : IsOpen U) (hu2 : ∀ z ∈ U, u z ≠ 0) (A : ℝ) (φ : ℝ → ℝ)
    (z : ℂ) (hz : z ∈ U) :
    energyDensity H φ (fun z => Real.exp (-2 * A) • u z) z =
      energyDensity H (fun s => φ (s - A)) u z := by
  have hc := Real.exp_pos (-2 * A)
  have hlog : Real.log (Real.exp (-2 * A)) / 2 = -A := by rw [Real.log_exp]; ring
  have ha_ev : (fun z => aCoord H (Real.exp (-2 * A) • u z)) =ᶠ[𝓝 z]
      fun z => aCoord H (u z) - A := by
    filter_upwards [hU.mem_nhds hz] with y hy
    rw [(zc_aCoord_smul H hH (u y) (hu2 y hy) _ hc).1, hlog]; ring
  have hw_ev : (fun z => proj H (Real.exp (-2 * A) • u z)) =ᶠ[𝓝 z]
      fun z => proj H (u z) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact (zc_aCoord_smul H hH (u y) (hu2 y hy) _ hc).2
  have hderiv : deriv (fun s => φ (s - A)) (aCoord H (u z)) = deriv φ (aCoord H (u z) - A) :=
    deriv_comp_sub_const _ _ _
  simp only [energyDensity, ds, dt]
  rw [ha_ev.fderiv_eq, hw_ev.fderiv_eq, ha_ev.eq_of_nhds, hw_ev.eq_of_nhds, fderiv_sub_const,
    hderiv]

/-- A level `s₀ ∈ (0, 1)` and a window `[s₀ - δ, s₀ + δ] ⊆ (0, 1)` on which
`φ₀ = smoothTransition²` and its derivative are bounded below by `c₀ > 0`. -/
theorem zc_select :
    ∃ s₀ δ c₀ : ℝ, 0 < δ ∧ 0 < s₀ - δ ∧ s₀ + δ < 1 ∧ 0 < c₀ ∧ ∀ s : ℝ, |s - s₀| ≤ δ →
      c₀ ≤ deriv (fun s => Real.smoothTransition s ^ 2) s ∧
        c₀ ≤ Real.smoothTransition s ^ 2 := by
  set φ₀ : ℝ → ℝ := fun s => Real.smoothTransition s ^ 2 with hφ₀
  have hφc : ContDiff ℝ ∞ φ₀ := (Real.smoothTransition.contDiff (n := ⊤)).pow 2
  obtain ⟨s₀, hs₀, hd⟩ := exists_deriv_eq_slope φ₀ zero_lt_one hφc.continuous.continuousOn
    (hφc.differentiable (by simp)).differentiableOn
  have h10 : (φ₀ 1 - φ₀ 0) / (1 - 0) = 1 := by
    simp [hφ₀, Real.smoothTransition.one, Real.smoothTransition.zero]
  rw [h10] at hd
  have hpos : 0 < φ₀ s₀ := by
    have := Real.smoothTransition.pos_of_pos hs₀.1; simp only [hφ₀]; positivity
  have hdc : Continuous (deriv φ₀) := hφc.continuous_deriv (by simp)
  have e1 : ∀ᶠ s in 𝓝 s₀, 1 / 2 < deriv φ₀ s :=
    hdc.continuousAt.eventually (lt_mem_nhds (by rw [hd]; norm_num))
  have e2 : ∀ᶠ s in 𝓝 s₀, φ₀ s₀ / 2 < φ₀ s :=
    hφc.continuous.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  set δ := min (ε / 2) (min (s₀ / 2) ((1 - s₀) / 2)) with hδdef
  have hδ : 0 < δ := by
    have := hs₀.1; have := hs₀.2
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ s₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ (1 - s₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨s₀, δ, min (1 / 2) (φ₀ s₀ / 2), hδ, by linarith [hs₀.1], by linarith [hs₀.2],
    lt_min (by norm_num) (by linarith), fun s hs => ?_⟩
  have hdist : dist s s₀ < ε := by rw [Real.dist_eq]; linarith
  obtain ⟨h1, h2⟩ := hεs hdist
  exact ⟨(min_le_left _ _).trans h1.le, (min_le_right _ _).trans h2.le⟩

end FEPA3R

namespace FiniteEnergyPlane

open FEPA3 FEPA3R
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem exists_pos_le_lintegral_energyDensity_annulus_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ∃ c : ℝ, 0 < c ∧ ∀ A ρ₁ ρ₂ : ℝ, 0 < ρ₂ → ρ₂ < ρ₁ → ρ₁ < 1 →
      (((∀ z : ℂ, ‖z‖ = ρ₁ → aCoord H (u z) ≤ A) ∧
          ∀ z : ℂ, ‖z‖ = ρ₂ → A + 1 ≤ aCoord H (u z)) ∨
        ((∀ z : ℂ, ‖z‖ = ρ₁ → A + 1 ≤ aCoord H (u z)) ∧
          ∀ z : ℂ, ‖z‖ = ρ₂ → aCoord H (u z) ≤ A)) →
      ENNReal.ofReal c ≤ ∫⁻ z in ball 0 ρ₁ \ ball 0 ρ₂,
        ENNReal.ofReal (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) := by
  obtain ⟨hJa, hprojs, haCs, hrep, hscale⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set φ₀ : ℝ → ℝ := fun s => Real.smoothTransition s ^ 2 with hφ₀
  obtain ⟨s₀, δ, c₀, hδ, hs₀l, hs₀u, hc₀, hφb⟩ := zc_select
  have hO : IsOpen {y : V n | y ≠ 0} := isOpen_ne
  -- compact sets
  set slab : Set (V n) := {y | y ≠ 0 ∧ |aCoord H y| ≤ |s₀| + 1} with hslabdef
  have hslab : IsCompact slab := isCompact_aCoord_slab H hH J hJ _
  have hslabO : slab ⊆ {y | y ≠ 0} := fun y hy => hy.1
  set K : Set (V n) := {y | y ≠ 0 ∧ aCoord H y = s₀} with hKdef
  have hKeq : K = slab ∩ aCoord H ⁻¹' {s₀} := by
    ext y
    simp only [hKdef, hslabdef, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [h2]; linarith⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  have hK : IsCompact K := by
    rw [hKeq]
    exact hslab.of_isClosed_subset ((haCs.continuousOn.mono hslabO).preimage_isClosed_of_isClosed
      hslab.isClosed isClosed_singleton) inter_subset_left
  have hKO : K ⊆ {y | y ≠ 0} := fun y hy => hy.1
  -- the open window around `K`
  set O' : Set (V n) := {y | y ≠ 0} ∩ aCoord H ⁻¹' Ioo (s₀ - δ) (s₀ + δ) with hO'def
  have hO' : IsOpen O' := haCs.continuousOn.isOpen_inter_preimage hO isOpen_Ioo
  have hKO' : K ⊆ O' := fun y hy => ⟨hy.1, by
    simp only [mem_preimage, mem_Ioo, hy.2]; constructor <;> linarith⟩
  obtain ⟨r₁, hr₁, hthick⟩ := hK.exists_thickening_subset_open hO' hKO'
  obtain ⟨r₀, hr₀, cm, hcm, hmono⟩ :=
    energy_ge_of_mapsTo_ball (Jtilde H J) {y | y ≠ 0} hJa K hK hKO
  set r := min r₀ r₁ with hrdef
  have hr : 0 < r := lt_min hr₀ hr₁
  obtain ⟨Cd, hCd0, hdir⟩ := zc_dirichlet_pt H hH J hJ slab hslab hslabO (|s₀| + 1) c₀ hc₀
  refine ⟨cm * r ^ 2 / (Cd + 1), by positivity, ?_⟩
  intro A ρ₁ ρ₂ h₂ h₂₁ h₁ hcases
  -- the rescaled curve
  set U₀ : Set ℂ := ball 0 1 \ {0} with hU₀def
  have hU₀ : IsOpen U₀ := isOpen_ball.sdiff isClosed_singleton
  set e : ℝ := Real.exp (-2 * A) with hedef
  have he : 0 < e := Real.exp_pos _
  set v : ℂ → V n := fun z => e • u z with hvdef
  have hv1 : ContDiffOn ℝ ∞ v U₀ := hu.1.const_smul e
  have hv2 : ∀ z ∈ U₀, v z ≠ 0 := fun z hz => smul_ne_zero he.ne' (hu.2.1 z hz)
  have hv3 : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U₀ v := by
    intro z hz
    obtain ⟨hd, hdb⟩ := hu.2.2.1 z hz
    refine ⟨hd.const_smul e, ?_⟩
    have hfd : fderiv ℝ v z = e • fderiv ℝ u z := fderiv_const_smul hd e
    unfold JHolomorphic.dbarJ at hdb ⊢
    rw [hfd, hscale (u z) (hu.2.1 z hz) e he]
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    rw [← smul_add, hdb, smul_zero]
  have hav : ∀ z ∈ U₀, aCoord H (v z) = aCoord H (u z) - A := by
    intro z hz
    rw [(zc_aCoord_smul H hH (u z) (hu.2.1 z hz) e he).1, hedef, Real.log_exp]; ring
  have hmemU : ∀ z : ℂ, ρ₂ ≤ ‖z‖ → ‖z‖ ≤ ρ₁ → z ∈ U₀ := by
    intro z hz1 hz2
    refine ⟨by rw [mem_ball_zero_iff]; linarith, ?_⟩
    intro h; rw [mem_singleton_iff] at h; rw [h, norm_zero] at hz1; linarith
  -- a point of the open annulus at level `A + s₀`
  obtain ⟨z₀, hz₀l, hz₀u, hz₀a⟩ : ∃ z₀ : ℂ, ρ₂ < ‖z₀‖ ∧ ‖z₀‖ < ρ₁ ∧
      aCoord H (u z₀) = A + s₀ := by
    set f : ℝ → ℝ := fun t => aCoord H (u (t : ℂ)) with hfdef
    have hnt : ∀ t : ℝ, 0 ≤ t → ‖(t : ℂ)‖ = t := fun t ht => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    have hfc : ContinuousOn f (Icc ρ₂ ρ₁) := by
      have hc : ContinuousOn (fun z => aCoord H (u z)) U₀ :=
        (haCs.comp hu.1 (fun z hz => hu.2.1 z hz)).continuousOn
      refine hc.comp Complex.continuous_ofReal.continuousOn fun t ht => ?_
      exact hmemU _ (by rw [hnt t (h₂.le.trans ht.1)]; exact ht.1)
        (by rw [hnt t (h₂.le.trans ht.1)]; exact ht.2)
    have hf₁ := hnt ρ₁ (h₂.trans h₂₁).le
    have hf₂ := hnt ρ₂ h₂.le
    have hmem : A + s₀ ∈ f '' Icc ρ₂ ρ₁ := by
      rcases hcases with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · refine intermediate_value_Icc' h₂₁.le hfc ⟨?_, ?_⟩
        · have := hc1 _ hf₁; simp only [hfdef]; linarith
        · have := hc2 _ hf₂; simp only [hfdef]; linarith
      · refine intermediate_value_Icc h₂₁.le hfc ⟨?_, ?_⟩
        · have := hc2 _ hf₂; simp only [hfdef]; linarith
        · have := hc1 _ hf₁; simp only [hfdef]; linarith
    obtain ⟨t, ht, hft⟩ := hmem
    have htn := hnt t (h₂.le.trans ht.1)
    refine ⟨(t : ℂ), ?_, ?_, hft⟩
    · rw [htn]
      refine lt_of_le_of_ne ht.1 fun h => ?_
      rw [← h] at hft
      rcases hcases with ⟨-, hc2⟩ | ⟨-, hc2⟩
      · have := hc2 _ hf₂; simp only [hfdef] at hft; linarith
      · have := hc2 _ hf₂; simp only [hfdef] at hft; linarith
    · rw [htn]
      refine lt_of_le_of_ne ht.2 fun h => ?_
      rw [h] at hft
      rcases hcases with ⟨hc1, -⟩ | ⟨hc1, -⟩
      · have := hc1 _ hf₁; simp only [hfdef] at hft; linarith
      · have := hc1 _ hf₁; simp only [hfdef] at hft; linarith
  have hz₀U : z₀ ∈ U₀ := hmemU z₀ hz₀l.le hz₀u.le
  set p : V n := v z₀ with hpdef
  have hpK : p ∈ K := ⟨hv2 z₀ hz₀U, by rw [hpdef, hav z₀ hz₀U, hz₀a]; ring⟩
  -- the ball lies in the window
  have hball : ∀ z ∈ U₀, v z ∈ ball p r →
      s₀ - δ < aCoord H (v z) ∧ aCoord H (v z) < s₀ + δ := by
    intro z hz hb
    have : v z ∈ O' :=
      hthick (ball_subset_thickening hpK r₁ (ball_subset_ball (min_le_right r₀ r₁) hb))
    exact this.2
  have hcirc : ∀ z : ℂ, (‖z‖ = ρ₁ ∨ ‖z‖ = ρ₂) → v z ∉ ball p r := by
    intro z hz hb
    have hzU : z ∈ U₀ := by
      rcases hz with h | h
      · exact hmemU z (by rw [h]; exact h₂₁.le) h.le
      · exact hmemU z h.ge (by rw [h]; exact h₂₁.le)
    obtain ⟨hl, hu'⟩ := hball z hzU hb
    rw [hav z hzU] at hl hu'
    rcases hcases with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ <;> rcases hz with h | h
    · have := hc1 z h; linarith
    · have := hc2 z h; linarith
    · have := hc1 z h; linarith
    · have := hc2 z h; linarith
  -- the domain for the monotonicity lemma
  set Ann : Set ℂ := {z | ρ₂ < ‖z‖ ∧ ‖z‖ < ρ₁} with hAnndef
  have hAnn : IsOpen Ann :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAnnU : Ann ⊆ U₀ := fun z hz => hmemU z hz.1.le hz.2.le
  set Uo : Set ℂ := Ann ∩ v ⁻¹' ball p r with hUodef
  have hUo : IsOpen Uo := (hv1.continuousOn.mono hAnnU).isOpen_inter_preimage hAnn isOpen_ball
  have hUoU : Uo ⊆ U₀ := fun z hz => hAnnU hz.1
  have hmaps : MapsTo v Uo (ball p r) := fun z hz => hz.2
  have hprop : ∀ L : Set (V n), IsCompact L → L ⊆ ball p r → IsCompact (Uo ∩ v ⁻¹' L) := by
    intro L hL hLb
    set CA : Set ℂ := closedBall 0 ρ₁ \ ball 0 ρ₂ with hCAdef
    have hCA : IsCompact CA := (isCompact_closedBall 0 ρ₁).diff isOpen_ball
    have hCAU : CA ⊆ U₀ := fun z hz =>
      hmemU z (by simpa using hz.2) (by simpa using hz.1)
    have heq : Uo ∩ v ⁻¹' L = CA ∩ v ⁻¹' L := by
      ext z
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, -⟩, hL'⟩
        exact ⟨⟨by simpa using h2.le, by simpa using h1.le⟩, hL'⟩
      · rintro ⟨⟨h1, h2⟩, hL'⟩
        have hb := hLb hL'
        have h1' : ‖z‖ ≤ ρ₁ := by simpa using h1
        have h2' : ρ₂ ≤ ‖z‖ := by simpa using h2
        refine ⟨⟨⟨lt_of_le_of_ne h2' fun h => hcirc z (Or.inr h.symm) hb,
          lt_of_le_of_ne h1' fun h => hcirc z (Or.inl h) hb⟩, hb⟩, hL'⟩
    rw [heq]
    exact hCA.of_isClosed_subset ((hv1.continuousOn.mono hCAU).preimage_isClosed_of_isClosed
      hCA.isClosed hL.isClosed) inter_subset_left
  have hpim : p ∈ v '' Uo := ⟨z₀, ⟨⟨hz₀l, hz₀u⟩, mem_ball_self hr⟩, rfl⟩
  have hM := hmono p hpK r hr (min_le_left _ _) Uo hUo v (hv1.mono hUoU)
    (fun z hz => hv3 z (hUoU hz)) hmaps hprop hpim
  -- pointwise comparison on `Uo`
  set I := ∫⁻ z in ball 0 ρ₁ \ ball 0 ρ₂,
    ENNReal.ofReal (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) with hIdef
  have hpt : ∀ z ∈ Uo, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) ≤ ENNReal.ofReal Cd *
      ENNReal.ofReal (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) := by
    intro z hz
    have hzU := hUoU hz
    obtain ⟨hl, hu'⟩ := hball z hzU hz.2
    have hw : |aCoord H (v z) - s₀| ≤ δ := by rw [abs_le]; constructor <;> linarith
    obtain ⟨hb1, hb2⟩ := hφb _ hw
    have hvs : v z ∈ slab := ⟨hv2 z hzU, by
      rw [abs_le]; constructor <;> linarith [neg_abs_le s₀, le_abs_self s₀]⟩
    have h := hdir U₀ hU₀ v hv1 hv2 hv3 φ₀ z hzU hvs
      (by linarith [le_abs_self s₀]) hb1 hb2
    rw [zc_energyDensity_smul_exp H hH u U₀ hU₀ (fun z hz => hu.2.1 z hz) A φ₀ z hzU] at h
    rw [← ENNReal.ofReal_mul hCd0]
    exact ENNReal.ofReal_le_ofReal h
  have hchain : ENNReal.ofReal (cm * r ^ 2) ≤ ENNReal.ofReal Cd * I := by
    refine hM.trans ?_
    calc ∫⁻ z in Uo, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2)
        ≤ ∫⁻ z in Uo, ENNReal.ofReal Cd * ENNReal.ofReal
            (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) :=
          setLIntegral_mono' hUo.measurableSet hpt
      _ = ENNReal.ofReal Cd * ∫⁻ z in Uo, ENNReal.ofReal
            (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Cd * I := by
          gcongr
          refine lintegral_mono_set fun z hz => ⟨mem_ball_zero_iff.2 hz.1.2, ?_⟩
          rw [mem_ball_zero_iff, not_lt]; exact hz.1.1.le
  have hCd1 : ENNReal.ofReal Cd * I ≤ ENNReal.ofReal (Cd + 1) * I := by
    gcongr; linarith
  rw [ENNReal.ofReal_div_of_pos (by linarith)]
  exact ENNReal.div_le_of_le_mul' (hchain.trans hCd1)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ∃ c : ℝ, 0 < c ∧ ∀ A ρ₁ ρ₂ : ℝ, 0 < ρ₂ → ρ₂ < ρ₁ → ρ₁ < 1 →
      (((∀ z : ℂ, ‖z‖ = ρ₁ → aCoord H (u z) ≤ A) ∧
          ∀ z : ℂ, ‖z‖ = ρ₂ → A + 1 ≤ aCoord H (u z)) ∨
        ((∀ z : ℂ, ‖z‖ = ρ₁ → A + 1 ≤ aCoord H (u z)) ∧
          ∀ z : ℂ, ‖z‖ = ρ₂ → aCoord H (u z) ≤ A)) →
      ENNReal.ofReal c ≤ ∫⁻ z in ball 0 ρ₁ \ ball 0 ρ₂,
        ENNReal.ofReal (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) :=
  FiniteEnergyPlane.exists_pos_le_lintegral_energyDensity_annulus_aux H hH J hJ u hu
