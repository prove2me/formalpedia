-- Prove2me | solution 1 for FiniteEnergyPlane.exists_period_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:06:29.430568+00:00
-- url     : https://prove2.me/submissions/c4c1d250-ecb9-4813-ab30-24a143f55198

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
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

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem g70p_compact {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    IsCompact (energySurface H) := by
  have hcont : ContinuousOn (fun y : V n => scaleToS H y • y) (sphere 0 1) := by
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy; exact zero_ne_one hy
    exact ((g69s_scale_contDiffAt H hH y hy0).continuousAt.smul continuousAt_id).continuousWithinAt
  refine (isCompact_sphere (0 : V n) 1 |>.image_of_continuousOn hcont).of_isClosed_subset
    (isClosed_eq hH.1.continuous continuous_const) ?_
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    have := hH.2.2 x hx
    rw [h, map_zero] at this; exact lt_irrefl _ this
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · have hu : ‖x‖⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hn.ne') hx0
    have hs : scaleToS H (‖x‖⁻¹ • x) = ‖x‖ := by
      apply g69s_scale_unique H hH _ hu _ hn
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]; exact hx
    simp only; rw [hs, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ P : ReebOrbit H, T₀ ≤ P.T := by
  set S := energySurface H
  rcases (energySurface H).eq_empty_or_nonempty with hE | hne
  · exact ⟨1, one_pos, fun P => absurd (P.mem 0) (by rw [hE]; exact Set.notMem_empty _)⟩
  have hK := g70p_compact H hH
  have hRc : ContinuousOn (reeb H) S := fun x hx =>
    (g69s_reeb_contDiffAt H hH x hx).continuousAt.continuousWithinAt
  have hR0 : ∀ x ∈ S, reeb H x ≠ 0 := by
    intro x hx h
    have := (g69s_reeb_spec H hH x hx).2.1
    rw [h] at this
    simp [liouville, omega0, dot] at this
  obtain ⟨x₁, hx₁, hmin⟩ := hK.exists_isMinOn hne hRc.norm
  obtain ⟨x₂, hx₂, hmax⟩ := hK.exists_isMaxOn hne hRc.norm
  set m := ‖reeb H x₁‖
  set M := ‖reeb H x₂‖
  have hm : 0 < m := norm_pos_iff.2 (hR0 x₁ hx₁)
  have hM : 0 < M := lt_of_lt_of_le hm (hmax hx₁)
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hRc) (m / 2) (by positivity)
  refine ⟨δ / M, by positivity, fun P => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hxc : Continuous P.x := continuous_iff_continuousAt.2 fun t => (P.hasDerivAt t).continuousAt
  have hRxc : Continuous (fun t => reeb H (P.x t)) := hRc.comp_continuous hxc P.mem
  -- ‖x t - x 0‖ ≤ M t
  have hmv : ∀ t ∈ Set.Icc (0:ℝ) P.T, ‖P.x t - P.x 0‖ ≤ M * (t - 0) := by
    apply norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun t => reeb H (P.x t))
    · exact fun t _ => (P.hasDerivAt t).hasDerivWithinAt
    · exact fun t _ => hmax (P.mem t)
  have hclose : ∀ t ∈ Set.Icc (0:ℝ) P.T, ‖reeb H (P.x 0) - reeb H (P.x t)‖ ≤ m / 2 := by
    intro t ht
    have h1 := hmv t ht
    have h2 : M * t < δ := by
      calc M * t ≤ M * P.T := mul_le_mul_of_nonneg_left ht.2 hM.le
        _ < M * (δ / M) := mul_lt_mul_of_pos_left hlt hM
        _ = δ := by field_simp
    have := hU (P.x t) (P.mem t) (P.x 0) (P.mem 0) (by rw [dist_eq_norm]; linarith)
    rw [dist_eq_norm, norm_sub_rev] at this; exact this.le
  have hint : ∫ t in (0:ℝ)..P.T, reeb H (P.x t) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => P.hasDerivAt t)
      (hRxc.intervalIntegrable _ _)]
    have := P.periodic 0
    rw [zero_add] at this
    rw [this, sub_self]
  have hbound : ‖∫ t in (0:ℝ)..P.T, (reeb H (P.x 0) - reeb H (P.x t))‖ ≤ m / 2 * |P.T - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le P.T_pos.le] at ht
    exact hclose t ⟨ht.1.le, ht.2⟩
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hRxc.intervalIntegrable _ _), hint,
    sub_zero, intervalIntegral.integral_const, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos P.T_pos] at hbound
  have := hmin (P.mem 0)
  simp only [Set.mem_setOf_eq] at this
  nlinarith [P.T_pos]
