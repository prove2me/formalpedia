-- Prove2me | solution 1 for FiniteEnergyPlane.ReebOrbit.contDiff_x
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T21:17:16.678304+00:00
-- url     : https://prove2.me/submissions/054e102e-220d-460c-a5a1-e880b439b99e

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_omega0_tames_jtilde
import Theorems.Thm_FiniteEnergyPlane_exists_extension_of_energy_lt_top
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_isJHolomorphicOn_comp_mul
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn

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

namespace FiniteEnergyPlane

open scoped ContDiff

/-- The parametrization `x` of a periodic Reeb orbit on a strictly star-shaped level is `C^∞`. -/
theorem ReebOrbit.contDiff_x_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) : ContDiff ℝ ∞ P.x := by
  have hd : deriv P.x = fun τ => reeb H (P.x τ) := funext fun τ => (P.hasDerivAt τ).deriv
  have hdiff : Differentiable ℝ P.x := fun τ => (P.hasDerivAt τ).differentiableAt
  have key : ∀ k : ℕ, ContDiff ℝ k P.x := by
    intro k
    induction k with
    | zero => exact contDiff_zero.2 hdiff.continuous
    | succ k ih =>
      have : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [this]
      refine contDiff_succ_iff_deriv.2 ⟨hdiff, by simp, ?_⟩
      rw [hd]
      exact contDiff_iff_contDiffAt.2 fun τ =>
        ((g69s_reeb_contDiffAt H hH _ (P.mem τ)).of_le (by exact_mod_cast le_top)).comp τ
          ih.contDiffAt
  exact contDiff_infty.2 key

end FiniteEnergyPlane

open FiniteEnergyPlane FiniteEnergyPlane.ReebOrbit

open scoped ContDiff

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) : ContDiff ℝ ∞ P.x :=
  ReebOrbit.contDiff_x_aux H hH P
