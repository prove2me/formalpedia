-- Prove2me | solution 1 for ContWeatherall.homotopy_formula
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-18T21:30:43.206303+00:00
-- url     : https://prove2.me/submissions/21b59485-4ac6-4523-be88-7415ef74cb35

import Mathlib
import Definitions.Def_ContWeatherall_defs
import Theorems.Thm_ContWeatherall_fderiv_homotopyOp
import Theorems.Thm_ContWeatherall_integral_radial
import Theorems.Thm_ContWeatherall_alternating_sum_cons_removeNth
import Theorems.Thm_ContWeatherall_alternatizeUncurryFin_apply_cons

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- Evaluating an interval integral of a continuous family of alternating maps at a tuple. -/
theorem hf_integral_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {n : ℕ}
    {f : ℝ → E [⋀^Fin n]→L[ℝ] F} (hf : Continuous f) (u : Fin n → E) :
    (∫ t in (0 : ℝ)..1, f t) u = ∫ t in (0 : ℝ)..1, f t u :=
  ((ContinuousAlternatingMap.apply ℝ E F u).intervalIntegral_comp_comm
    (hf.intervalIntegrable 0 1)).symm

theorem hf_main {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) : extDeriv (homotopyOp w) + homotopyOp (extDeriv w) = w := by
  funext x
  ext v
  have hsm : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
  have c1 : Continuous fun t : ℝ => w (t • x) := hw.continuous.comp hsm
  have c2 : Continuous fun t : ℝ => fderiv ℝ w (t • x) :=
    (hw.continuous_fderiv (by simp)).comp hsm
  have c3 : Continuous fun t : ℝ => extDeriv w (t • x) :=
    (extDeriv_contDiff hw).continuous.comp hsm
  have cL : ∀ {n : ℕ} {g : ℝ → E [⋀^Fin (n + 1)]→L[ℝ] F}, Continuous g → ∀ y : E,
      Continuous fun t => (g t).curryLeft y := by
    intro n g hg y
    exact ((curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := n)).continuous.comp hg).clm_apply
      continuous_const
  have cA : ∀ {n : ℕ} {g : ℝ → E [⋀^Fin n]→L[ℝ] F}, Continuous g → ∀ u : Fin n → E,
      Continuous fun t => g t u := by
    intro n g hg u
    exact (ContinuousAlternatingMap.apply ℝ E F u).continuous.comp hg
  set D : Fin (k + 1) → ℝ → F := fun i t =>
    fderiv ℝ w (t • x) (v i) (Fin.cons x (i.removeNth v)) with hD
  set W : Fin (k + 1) → ℝ → F := fun i t => w (t • x) (Fin.cons (v i) (i.removeNth v)) with hW
  set X : ℝ → F := fun t => fderiv ℝ w (t • x) x v with hX
  have cD : ∀ i, Continuous (D i) := fun i => cA (c2.clm_apply continuous_const) _
  have cW : ∀ i, Continuous (W i) := fun i => cA c1 _
  have cX : Continuous X := cA (c2.clm_apply continuous_const) _
  have i1 : ∀ i : Fin (k + 1), Continuous fun t : ℝ =>
      (-1 : ℤ) ^ (i : ℕ) • (t ^ k • (t • D i t + W i t)) := fun i => by
    have := cD i; have := cW i; fun_prop
  have i2 : Continuous fun t : ℝ =>
      t ^ (k + 1) • (X t - ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • D i t) := by
    have := cD; fun_prop
  have h1 : extDeriv (homotopyOp w) x v =
      ∫ t in (0 : ℝ)..1, ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • (t ^ k • (t • D i t + W i t)) := by
    rw [extDeriv, alternatizeUncurryFin_apply, intervalIntegral.integral_finsetSum
      (fun i _ => (i1 i).intervalIntegrable 0 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have j1 : Continuous fun t : ℝ =>
        t ^ k • (t • (fderiv ℝ w (t • x) (v i)).curryLeft x + (w (t • x)).curryLeft (v i)) :=
      (continuous_pow k).smul
        ((continuous_id.smul (cL (c2.clm_apply continuous_const) x)).add (cL c1 (v i)))
    rw [fderiv_homotopyOp hw, hf_integral_apply j1,
      ← Int.cast_smul_eq_zsmul ℝ, ← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hD, hW, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, curryLeft_apply_apply,
      Int.cast_smul_eq_zsmul]
    rfl
  have h2 : homotopyOp (extDeriv w) x v =
      ∫ t in (0 : ℝ)..1, t ^ (k + 1) • (X t - ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • D i t) := by
    have j2 : Continuous fun t : ℝ => t ^ (k + 1) • (extDeriv w (t • x)).curryLeft x :=
      (continuous_pow (k + 1)).smul (cL c3 x)
    rw [homotopyOp, hf_integral_apply j2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hD, hX, ContinuousAlternatingMap.smul_apply, curryLeft_apply_apply, extDeriv]
    congr 1
    exact alternatizeUncurryFin_apply_cons _ x v
  have hs : ∀ t : ℝ, ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • W i t = (k + 1) • w (t • x) v := fun t => by
    simpa using alternating_sum_cons_removeNth (w (t • x)).toAlternatingMap v
  have hg : ContDiff ℝ 1 (fun y => w y v) :=
    ((ContinuousAlternatingMap.apply ℝ E F v).contDiff.comp hw).of_le (by simp)
  have hfg : ∀ y, fderiv ℝ (fun y => w y v) y x = fderiv ℝ w y x v := fun y =>
    fderiv_continuousAlternatingMap_apply_const_apply (hw.differentiable (by simp) y) v x
  rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, h1, h2,
    ← intervalIntegral.integral_add ((continuous_finsetSum _ fun i _ => i1 i).intervalIntegrable 0 1)
      (i2.intervalIntegrable 0 1), ← integral_radial k hg x]
  refine intervalIntegral.integral_congr fun t _ => ?_
  try dsimp only
  have e1 : ∀ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • (t ^ k • (t • D i t + W i t)) =
      t ^ (k + 1) • ((-1 : ℤ) ^ (i : ℕ) • D i t) + t ^ k • ((-1 : ℤ) ^ (i : ℕ) • W i t) :=
    fun i => by module
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, ← Finset.smul_sum,
    ← Finset.smul_sum, hs, hfg]
  simp only [hX]
  module

end ContWeatherall

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) :
    extDeriv (ContWeatherall.homotopyOp w) + ContWeatherall.homotopyOp (extDeriv w) = w :=
  ContWeatherall.hf_main hw
