-- Prove2me | solution 1 for BianchiIX.normalized_partialCore_energy_band_improves
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:30:01.907302+00:00
-- url     : https://prove2.me/submissions/66b70320-3bac-4028-b3cc-9149609bfbed

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_exists_normalized_coreAngle_reparametrization
import Theorems.Thm_BianchiIX_exists_normalized_core_regular_interval
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_partialCoreAngle_radius_drift
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partial_core_radius_energy_improvement {k r u p : ℝ} (hk : 6 ≤ k)
    (hr : 0 ≤ r) (hrhi : r ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hp : 0 ≤ p ∧ p ≤ (1 / 10000) / k)
    (hR : |r - k| ≤ 16 * (u + p ^ 2 / k)) : |r ^ 2 - k ^ 2| < 1 / 16 := by
  have hk0 : 0 < k := by linarith only [hk]
  have hku : k * u ≤ 1 / 10000 := by
    have H := (le_div_iff₀ hk0).mp hu.2
    linarith only [H]
  have hp' := coreBootstrap_wall_bound hk hp.2
  have hp2 := (sq_le_sq₀ hp.1 (by norm_num : (0 : ℝ) ≤ 1 / 60000)).mpr hp'
  have hnonneg : 0 ≤ 16 * (u + p ^ 2 / k) :=
    mul_nonneg (by norm_num) (add_nonneg hu.1 (div_nonneg (sq_nonneg p) hk0.le))
  calc
    |r ^ 2 - k ^ 2| = |r - k| * (r + k) := by
      rw [show r ^ 2 - k ^ 2 = (r - k) * (r + k) by ring, abs_mul,
        abs_of_nonneg (by linarith only [hr, hk] : 0 ≤ r + k)]
    _ ≤ (16 * (u + p ^ 2 / k)) * (201 / 100 * k) :=
      mul_le_mul hR (by linarith only [hrhi]) (by linarith only [hr, hk]) hnonneg
    _ = (804 / 25) * (k * u + p ^ 2) := by field_simp; ring
    _ < 1 / 16 := by nlinarith only [hku, hp2]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.partialCoreAngle_radius_drift_shifted {Y : ℝ → CoreAngleState} {a b k z₀ : ℝ}
    (hab : a ≤ b) (hk : 6 ≤ k)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (coreAngleField (z + z₀) (Y z)) z)
    (hinit : Y a 0 = k)
    (hr : ∀ z ∈ Icc a b, 99 / 100 * k ≤ Y z 0 ∧ Y z 0 ≤ 101 / 100 * k)
    (hv : ∀ z ∈ Icc a b, 1 ≤ Y z 0 / Real.cosh (z + z₀))
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ (1 / 10000) / k)
    (hp : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ (1 / 10000) / k) :
    |Y b 0 - k| ≤ 16 * (Y a 1 + (Y a 2) ^ 2 / k) := by
  have hmem (z : ℝ) (hz : z ∈ Icc (a + z₀) (b + z₀)) : z - z₀ ∈ Icc a b := by
    constructor <;> linarith only [hz.1, hz.2]
  have hsol (z : ℝ) (hz : z ∈ Icc (a + z₀) (b + z₀)) :
      HasDerivAt (fun u => Y (u - z₀)) (coreAngleField z (Y (z - z₀))) z := by
    have H := (hY (z - z₀) (hmem z hz)).scomp z ((hasDerivAt_id z).sub_const z₀)
    simp only [sub_add_cancel, one_smul] at H
    convert! H using 1
  have H := partialCoreAngle_radius_drift (Y := fun z => Y (z - z₀))
    (by linarith only [hab] : a + z₀ ≤ b + z₀) hk hsol
    (by simpa only [add_sub_cancel_right] using hinit)
    (fun z hz => hr _ (hmem z hz))
    (fun z hz => by simpa only [sub_add_cancel] using hv _ (hmem z hz))
    (fun z hz => hu _ (hmem z hz)) (fun z hz => hp _ (hmem z hz))
  simpa only [add_sub_cancel_right] using H

end
end


/-- The strict energy improvement holds on actual closed Einstein-flow prefixes, with no extra clock assumptions. -/
theorem solution {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k →
    (∀ u ∈ Icc s t, |coreRadius (β u 0) (β u 2) ^ 2 - k ^ 2| ≤ 1 / 8) →
    (∀ u ∈ Icc s t, 1 ≤ β u 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ Icc s t, 0 ≤ β u 2 * β u 3 ∧ β u 2 * β u 3 ≤ (1 / 10000) / k) →
    |coreRadius (β t 0) (β t 2) - k| ≤ 16 * (β s 1 + (β s 2 * β s 3) ^ 2 / k) ∧
      |coreRadius (β t 0) (β t 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro β hinit hband hv hu hp
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have htm : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hdom (u : ℝ) (hh : u ∈ Icc s t) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh.1)
  have hvpos (u : ℝ) (hh : u ∈ Icc s t) : 0 < β u 2 := lt_of_lt_of_le zero_lt_one (hv u hh)
  have hr (u : ℝ) (hh : u ∈ Icc s t) :
      99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧ coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k :=
    coreBootstrap_radius_closed hk (coreRadius_pos (hvpos u hh)).le (hband u hh)
  have hw (u : ℝ) (hh : u ∈ Icc s t) : 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k := by
    have hnonneg : 0 ≤ β u 3 := (mul_nonneg_iff_of_pos_left (hvpos u hh)).mp (hp u hh).1
    exact ⟨hnonneg, (le_mul_of_one_le_left hnonneg (hv u hh)).trans (hp u hh).2⟩
  have hd (u : ℝ) (hh : u ∈ Icc s t) :
      0 < coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000)
      (coreBootstrap_clock_bounds hk (hr u hh).1 (hu u hh) (hw u hh)).1
  obtain ⟨l, r, hls, htr, hregular⟩ := exists_normalized_core_regular_interval hst
    (fun _ hh => hdom _ hh) hA hvpos hd
  have hcover : Icc s t ⊆ Ioo l r := fun u hh => ⟨hls.trans_le hh.1, hh.2.trans_lt htr⟩
  have hsI := hcover hsm
  have htI := hcover htm
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_coreAngle_reparametrization (convex_Ioo l r) isOpen_Ioo hsI
      (fun u hh => (hregular u hh).1) hc
      (fun u hh => (hregular u hh).2.1) (fun u hh => (hregular u hh).2.2.1)
      (fun u hh => (hregular u hh).2.2.2)
  have htE : t ∈ e.source := by rwa [hsrc]
  have hes : e s = 0 := by rw [heq s hsI]; exact sub_self _
  have hbt : 0 ≤ e t := by simpa only [hes] using hmono.monotoneOn hsI htI hst
  have hzt (z : ℝ) (hz : z ∈ Icc 0 (e t)) : z ∈ e.target :=
    htarget.ordConnected.out hzero (e.map_source htE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 (e t)) : e.symm z ∈ Icc s t := by
    have hzT := hzt z hz
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target hzT
    constructor
    · apply (hmono.le_iff_le hsI hxI).mp
      rw [hes, e.right_inv hzT]
      exact hz.1
    · apply (hmono.le_iff_le hxI htI).mp
      rw [e.right_inv hzT]
      exact hz.2
  let Y := fun z => toCoreAngleState (β (e.symm z))
  let z₀ := coreAngle (β s 0) (β s 2)
  have hY (z : ℝ) (hz : z ∈ Icc 0 (e t)) : HasDerivAt Y (coreAngleField (z + z₀) (Y z)) z :=
    (hflow z (hzt z hz)).2.1
  have hvY (z : ℝ) (hz : z ∈ Icc 0 (e t)) : Y z 0 / Real.cosh (z + z₀) = β (e.symm z) 2 := by
    have he := (hflow z (hzt z hz)).1
    change coreRadius (β (e.symm z) 0) (β (e.symm z) 2) / Real.cosh (z + z₀) = _
    rw [← he]
    exact (coreAngle_coordinates (hvpos _ (hinv z hz))).1
  have hY0 : Y 0 0 = k := by change coreRadius (β (e.symm 0) 0) (β (e.symm 0) 2) = k; rwa [hinv0]
  have H := partialCoreAngle_radius_drift_shifted hbt hk hY hY0
    (fun z hz => hr _ (hinv z hz))
    (fun z hz => by rw [hvY z hz]; exact hv _ (hinv z hz))
    (fun z hz => hu _ (hinv z hz)) (fun z hz => hp _ (hinv z hz))
  have hinvt : e.symm (e t) = t := e.left_inv htE
  change |coreRadius (β (e.symm (e t)) 0) (β (e.symm (e t)) 2) - k| ≤
    16 * (β (e.symm 0) 1 + (β (e.symm 0) 2 * β (e.symm 0) 3) ^ 2 / k) at H
  rw [hinvt, hinv0] at H
  exact ⟨H, partial_core_radius_energy_improvement hk (coreRadius_pos (hvpos t htm)).le (hr t htm).2
    (hu s hsm) (hp s hsm) H⟩
