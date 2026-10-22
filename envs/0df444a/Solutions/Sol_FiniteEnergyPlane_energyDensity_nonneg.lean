-- Prove2me | solution 1 for FiniteEnergyPlane.energyDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:23:25.481387+00:00
-- url     : https://prove2.me/submissions/1d70861b-b8c2-44c3-91e0-0130e67972ea

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

open FiniteEnergyPlane
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

open scoped ContDiff Topology in
theorem g69s_scale_unique {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (t : ℝ) (ht : 0 < t) (hHt : H (t • y) = 1) : scaleToS H y = t := by
  obtain ⟨r, _, hu⟩ := hH.2.1 y hy
  have h1 := hu t ⟨ht, hHt⟩
  have h2 := hu (scaleToS H y) (g69s_scale_spec H hH y hy)
  rw [h1, h2]

open scoped ContDiff Topology in
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

open scoped ContDiff Topology

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

theorem g69s_energyDensity_nonneg {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) :
    (∀ φ : ℝ → ℝ, Admissible φ → ∀ z ∈ U, 0 ≤ energyDensity H φ u z) ∧
      (∀ z ∈ U, 0 ≤ dlambdaDensity H u z) ∧ dlambdaEnergy H U u ≤ energy H U u ∧
      (IsPreconnected U → energy H U u = 0 → ∃ c : V n, ∀ z ∈ U, u z = c) := by
  obtain ⟨hsm, hne, hhol, hfin⟩ := hu
  have hpt : ∀ φ : ℝ → ℝ, ∀ z ∈ U, ∃ p q m : ℝ, 0 ≤ m ∧
      energyDensity H φ u z = deriv φ (aCoord H (u z)) * (p ^ 2 + q ^ 2) + φ (aCoord H (u z)) * m ∧
      dlambdaDensity H u z = m ∧ (p = 0 → q = 0 → m = 0 → fderiv ℝ u z = 0) :=
    fun φ z hz => g69s_pointwise H hH J hJ u z (hhol z hz).1 (hne z hz) (hhol z hz).2 φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ hφ z hz
    obtain ⟨p, q, m, hm, he, -, -⟩ := hpt φ z hz
    rw [he]
    have h1 : 0 ≤ deriv φ (aCoord H (u z)) := hφ.2.1.deriv_nonneg
    have h2 := (hφ.2.2 (aCoord H (u z))).1
    positivity
  · intro z hz
    obtain ⟨p, q, m, hm, -, hd, -⟩ := hpt (fun _ => 1) z hz
    rw [hd]; exact hm
  · have hadm : Admissible (fun _ : ℝ => (1:ℝ)) :=
      ⟨contDiff_const, monotone_const, fun _ => ⟨by norm_num, le_rfl⟩⟩
    refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (φ : ℝ → ℝ) (_ : Admissible φ) =>
      ∫⁻ z in U, ENNReal.ofReal (energyDensity H φ u z)) (fun _ => 1) hadm)
    unfold dlambdaEnergy
    congr 1; funext z
    simp [energyDensity, dlambdaDensity]
  · intro hpc h0
    set φL : ℝ → ℝ := fun s => (1 + Real.exp (-s))⁻¹ with hφL
    have hadm := g69s_logistic_admissible
    have hint : ∫⁻ z in U, ENNReal.ofReal (energyDensity H φL u z) = 0 := by
      apply le_antisymm _ (zero_le')
      rw [← h0]
      exact le_iSup₂ (f := fun (φ : ℝ → ℝ) (_ : Admissible φ) =>
        ∫⁻ z in U, ENNReal.ofReal (energyDensity H φ u z)) φL hadm
    -- continuity of the density
    have hmaps : Set.MapsTo u U {y | y ≠ 0} := fun z hz => hne z hz
    obtain ⟨-, hP, hA, -, -⟩ := g69s_jtilde_all H hH J hJ
    have ha : ContDiffOn ℝ ∞ (fun z => aCoord H (u z)) U := hA.comp hsm hmaps
    have hw : ContDiffOn ℝ ∞ (fun z => proj H (u z)) U := hP.comp hsm hmaps
    have hfa := ha.continuousOn_fderiv_of_isOpen hU (by simp)
    have hfw := hw.continuousOn_fderiv_of_isOpen hU (by simp)
    have hdsa : ContinuousOn (ds fun z => aCoord H (u z)) U := hfa.clm_apply continuousOn_const
    have hdta : ContinuousOn (dt fun z => aCoord H (u z)) U := hfa.clm_apply continuousOn_const
    have hdsw : ContinuousOn (ds fun z => proj H (u z)) U := hfw.clm_apply continuousOn_const
    have hdtw : ContinuousOn (dt fun z => proj H (u z)) U := hfw.clm_apply continuousOn_const
    have hLc := g69s_liouvilleCLM_contDiff (n := n)
    have hliou : ∀ f g : ℂ → V n, ContinuousOn f U → ContinuousOn g U →
        ContinuousOn (fun z => liouville (f z) (g z)) U := by
      intro f g hf hg
      have : (fun z => liouville (f z) (g z)) = fun z => liouvilleCLM (f z) (g z) := by
        funext z; rw [g69s_liouvilleCLM_apply]
      rw [this]
      exact (hLc.continuous.comp_continuousOn hf).clm_apply hg
    have hom : ∀ f g : ℂ → V n, ContinuousOn f U → ContinuousOn g U →
        ContinuousOn (fun z => omega0 (f z) (g z)) U := by
      intro f g hf hg
      have : (fun z => omega0 (f z) (g z)) = fun z => 2 * liouville (f z) (g z) := by
        funext z; unfold liouville; ring
      rw [this]; exact continuousOn_const.mul (hliou f g hf hg)
    have hφc : Continuous (deriv φL) := hadm.1.continuous_deriv (by simp)
    have hcont : ContinuousOn (energyDensity H φL u) U := by
      unfold energyDensity
      simp only []
      refine ContinuousOn.add (ContinuousOn.mul (hφc.comp_continuousOn ha.continuousOn) ?_)
        (ContinuousOn.mul (hadm.1.continuous.comp_continuousOn ha.continuousOn)
          (hom _ _ hdsw hdtw))
      exact (hdsa.mul (hliou _ _ hw.continuousOn hdtw)).sub
        (hdta.mul (hliou _ _ hw.continuousOn hdsw))
    have hmeas : AEMeasurable (fun z => ENNReal.ofReal (energyDensity H φL u z))
        (MeasureTheory.volume.restrict U) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hcont.aemeasurable hU.measurableSet)
    have hae := (MeasureTheory.lintegral_eq_zero_iff' hmeas).1 hint
    have hae2 : (energyDensity H φL u) =ᵐ[MeasureTheory.volume.restrict U] (fun _ => (0:ℝ)) := by
      filter_upwards [hae, MeasureTheory.ae_restrict_mem hU.measurableSet] with z hz hzU
      have h1 : energyDensity H φL u z ≤ 0 := ENNReal.ofReal_eq_zero.1 hz
      obtain ⟨p, q, m, hm, he, -, -⟩ := hpt φL z hzU
      have hd : 0 ≤ deriv φL (aCoord H (u z)) := hadm.2.1.deriv_nonneg
      have h2 := (hadm.2.2 (aCoord H (u z))).1
      have : 0 ≤ energyDensity H φL u z := by rw [he]; positivity
      exact le_antisymm h1 this
    have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae2 hU hcont continuousOn_const
    have hfd : Set.EqOn (fderiv ℝ u) 0 U := by
      intro z hz
      obtain ⟨p, q, m, hm, he, -, himp⟩ := hpt φL z hz
      have hz0 : energyDensity H φL u z = 0 := heq hz
      have hd : 0 < deriv φL (aCoord H (u z)) := by
        rw [(g69s_logistic_hasDerivAt _).deriv]; positivity
      have hφp : 0 < φL (aCoord H (u z)) := by simp only [hφL]; positivity
      rw [he] at hz0
      have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
      have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
      have hA0 : deriv φL (aCoord H (u z)) * (p ^ 2 + q ^ 2) = 0 := by
        have := mul_nonneg hφp.le hm
        have := mul_nonneg hd.le (add_nonneg hp2 hq2)
        linarith
      have hB0 : φL (aCoord H (u z)) * m = 0 := by
        have := mul_nonneg hφp.le hm
        have := mul_nonneg hd.le (add_nonneg hp2 hq2)
        linarith
      have hpq : p ^ 2 + q ^ 2 = 0 := (mul_eq_zero.1 hA0).resolve_left hd.ne'
      have hm0 : m = 0 := (mul_eq_zero.1 hB0).resolve_left hφp.ne'
      have hp : p = 0 := by nlinarith
      have hq : q = 0 := by nlinarith
      exact himp hp hq hm0
    exact hU.exists_is_const_of_fderiv_eq_zero hpc (hsm.differentiableOn (by simp)) hfd

/-- Hryniewicz 2014, § 2.2.1 and (17); Hofer 1993, (42). For a finite-energy `J̃`-holomorphic
curve on an open set `U ⊆ ℂ`, the integrand of `u*d(φ(a) λ)` is nonnegative for every admissible
`φ`, so is the integrand of `u*dλ`, and the `dλ`-energy is at most the Hofer energy. If `U` is
preconnected and the Hofer energy vanishes, `u` is constant on `U`. -/
theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) :
    (∀ φ : ℝ → ℝ, Admissible φ → ∀ z ∈ U, 0 ≤ energyDensity H φ u z) ∧
      (∀ z ∈ U, 0 ≤ dlambdaDensity H u z) ∧ dlambdaEnergy H U u ≤ energy H U u ∧
      (IsPreconnected U → energy H U u = 0 → ∃ c : V n, ∀ z ∈ U, u z = c) := by
  exact g69s_energyDensity_nonneg H hH J hJ U hU u hu

