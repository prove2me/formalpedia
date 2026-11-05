-- Prove2me | solution 1 for FiniteEnergyPlane.eventually_liouville_deriv_nonneg_of_tendstoCInfty
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T18:35:27.209813+00:00
-- url     : https://prove2.me/submissions/b4ef6e60-aa98-494b-9b1e-f39df3747f19

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reeb



namespace FiniteEnergyPlane

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

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Along the loops of a `C^∞`-converging family, the action integrand is eventually nonnegative. -/
theorem bu_eventually_nonneg {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (l : ℕ → ℝ → V n) (Q : ReebOrbit H) (hT : 0 < Q.T) (c : ℝ)
    (hconv : TendstoCInfty l (fun t => Q.x (Q.T * t + c))) :
    ∀ᶠ k in atTop, ∀ t, 0 ≤ liouville (l k t) (deriv (l k) t) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_reeb H hH
  have hcpt := isCompact_energySurface H hH
  obtain ⟨A, hA⟩ := hcpt.exists_bound_of_continuousOn (f := fun x : V n => x) continuousOn_id
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuousOn hK.continuousOn
  set Λ := ‖(omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)‖ with hΛ
  have hΛn : 0 ≤ Λ := norm_nonneg (omegaL (n := n))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (Q.mem 0))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ (Q.mem 0))
  have hder : ∀ t, deriv (fun t => Q.x (Q.T * t + c)) t = Q.T • reeb H (Q.x (Q.T * t + c)) := by
    intro t
    have hin : HasDerivAt (fun t : ℝ => Q.T * t + c) Q.T t := by
      simpa using ((hasDerivAt_id t).const_mul Q.T).add_const c
    exact ((Q.hasDerivAt (Q.T * t + c)).scomp t hin).deriv
  -- `L` is the constant `‖T • reeb‖` bound
  set L := Q.T * B with hL
  have hL0 : 0 ≤ L := mul_nonneg hT.le hB0
  -- choose the tolerance
  obtain ⟨ε, hε, hεs⟩ : ∃ ε > 0, Λ * ε * (L + ε) + Λ * A * ε < 2 * Q.T := by
    have hc : Continuous (fun ε : ℝ => Λ * ε * (L + ε) + Λ * A * ε) := by fun_prop
    have h0 : (fun ε : ℝ => Λ * ε * (L + ε) + Λ * A * ε) 0 < 2 * Q.T := by simpa using hT
    have hev := hc.continuousAt.eventually (gt_mem_nhds h0)
    obtain ⟨ε, hε1, hε2⟩ := (hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))) |>.exists
    exact ⟨ε, hε2, hε1⟩
  have h0 := Metric.tendstoUniformly_iff.1 (hconv 0) ε hε
  have h1 := Metric.tendstoUniformly_iff.1 (hconv 1) ε hε
  filter_upwards [h0, h1] with k hk0 hk1 t
  have ht0 := hk0 t
  have ht1 := hk1 t
  simp only [iteratedDeriv_zero, iteratedDeriv_one, hder] at ht0 ht1
  rw [dist_comm, dist_eq_norm] at ht0 ht1
  set x := Q.x (Q.T * t + c) with hx
  have hxS : x ∈ energySurface H := Q.mem _
  have hR := (reeb_spec H hH x hxS).2.1
  have hR2 : omegaL x (Q.T • reeb H x) = 2 * Q.T := by
    have h := hR
    rw [liouville, ← omegaL_apply] at h
    rw [map_smul, smul_eq_mul]
    have : omegaL x (reeb H x) = 2 := by linarith
    rw [this]; ring
  set a := l k t with ha
  set b := deriv (l k) t with hb
  set y := Q.T • reeb H x with hy
  have hby : ‖y‖ ≤ L := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_pos hT, hL]
    exact mul_le_mul_of_nonneg_left (hB _ hxS) hT.le
  have hbb : ‖b‖ ≤ L + ε := by
    have : b = y + (b - y) := by abel
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add hby ht1.le)
  have hsplit : omegaL a b = omegaL x y + (omegaL (a - x) b + omegaL x (b - y)) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    ring
  have he1 : |omegaL (a - x) b| ≤ Λ * ε * (L + ε) := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht0.le hΛn) hbb (norm_nonneg _)
      (mul_nonneg hΛn hε.le)
  have he2 : |omegaL x (b - y)| ≤ Λ * A * ε := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hA _ hxS) hΛn) ht1.le (norm_nonneg _)
      (mul_nonneg hΛn hA0)
  have hfin : 0 ≤ omegaL a b := by
    rw [hsplit, hR2]
    have := neg_abs_le (omegaL (a - x) b)
    have := neg_abs_le (omegaL x (b - y))
    linarith
  rw [liouville, ← omegaL_apply]
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (l : ℕ → ℝ → V n) (Q : ReebOrbit H) (c : ℝ)
    (hconv : TendstoCInfty l (fun t => Q.x (Q.T * t + c))) :
    ∀ᶠ k in atTop, ∀ t, 0 ≤ liouville (l k t) (deriv (l k) t) :=
  bu_eventually_nonneg H hH l Q Q.T_pos c hconv
