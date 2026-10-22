-- Prove2me | solution 1 for FiniteEnergyPlane.reeb_spec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:50:30.939154+00:00
-- url     : https://prove2.me/submissions/b593ce46-2e6b-46da-8ba8-2f2f2bfcc305

import Definitions.Def_FiniteEnergyPlane_Setting
open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

open FiniteEnergyPlane

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

/-- The Reeb field of `λ₀|S` (Hofer 1993, § 1; Hryniewicz 2014, § 2.1). On a strictly
star-shaped level `S`, `λ₀(X_H) > 0`, and `R = X_H / λ₀(X_H)` is tangent to `S`, satisfies
`λ₀(R) = 1`, and `ω₀(R, w) = 0` for every `w ∈ T_x S`. -/
theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  exact g69s_reeb_spec H hH x hx

