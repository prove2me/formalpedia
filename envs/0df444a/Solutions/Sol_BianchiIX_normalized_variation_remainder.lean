-- Prove2me | solution 1 for BianchiIX.normalized_variation_remainder
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:21:01.811635+00:00
-- url     : https://prove2.me/submissions/e5325141-371c-4d73-990a-42dc55e0884a

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Theorems.Thm_BianchiIX_norm_le_gronwall_uIcc
import Theorems.Thm_BianchiIX_normalizedField_quadratic_remainder
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal


/-- The actual solution error satisfies a quadratic bound once the linear variational equation holds. -/
theorem solution {α β : ℝ → NormalizedState}
    {J : ℝ → NormalizedVariation} {t₀ t : ℝ} {S : Set NormalizedState}
    (hS : Convex ℝ S) {K L : ℝ} {C : ℝ≥0}
    (hD : LipschitzOnWith C normalizedDifferential S)
    (hα : ∀ u ∈ uIcc t₀ t, HasDerivAt α (normalizedField (α u)) u)
    (hβ : ∀ u ∈ uIcc t₀ t, HasDerivAt β (normalizedField (β u)) u)
    (hαS : ∀ u ∈ uIcc t₀ t, α u ∈ S) (hβS : ∀ u ∈ uIcc t₀ t, β u ∈ S)
    (hJ : ∀ u ∈ uIcc t₀ t, HasDerivAt J ((normalizedDifferential (α u)).comp (J u)) u)
    (hJinit : J t₀ = ContinuousLinearMap.id ℝ NormalizedState)
    (hDnorm : ∀ u ∈ uIcc t₀ t, ‖normalizedDifferential (α u)‖ ≤ K)
    (hclose : ∀ u ∈ uIcc t₀ t, ‖β u - α u‖ ≤ L * ‖β t₀ - α t₀‖) :
    ‖β t - α t - J t (β t₀ - α t₀)‖ ≤
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖β t₀ - α t₀‖ ^ 2 := by
  let h := β t₀ - α t₀
  let e := fun u => β u - α u - J u h
  let de := fun u => normalizedField (β u) - normalizedField (α u) -
    normalizedDifferential (α u) (J u h)
  have he (u : ℝ) (hu : u ∈ uIcc t₀ t) : HasDerivAt e (de u) u := by
    have hJh := (hJ u hu).clm_apply (hasDerivAt_const u h)
    convert! ((hβ u hu).sub (hα u hu)).sub hJh using 1
    simp [de]
  have hb (u : ℝ) (hu : u ∈ uIcc t₀ t) :
      ‖de u‖ ≤ K * ‖e u‖ + C * L ^ 2 * ‖h‖ ^ 2 := by
    have hde : de u = normalizedDifferential (α u) (e u) +
        (normalizedField (β u) - normalizedField (α u) -
          normalizedDifferential (α u) (β u - α u)) := by
      simp only [de, e, map_sub]
      abel
    rw [hde]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact ((normalizedDifferential (α u)).le_opNorm (e u)).trans
        (mul_le_mul_of_nonneg_right (hDnorm u hu) (norm_nonneg _))
    · apply (normalizedField_quadratic_remainder hS hD (hαS u hu) (hβS u hu)).trans
      calc
        (C : ℝ) * ‖β u - α u‖ ^ 2 ≤ C * (L * ‖h‖) ^ 2 := by
          gcongr
          exact hclose u hu
        _ = C * L ^ 2 * ‖h‖ ^ 2 := by ring
  have H := norm_le_gronwall_uIcc he (δ := 0) (by simp [e, h, hJinit]) hb
  have hscale : gronwallBound 0 K (C * L ^ 2 * ‖h‖ ^ 2) |t - t₀| =
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖h‖ ^ 2 := by
    unfold gronwallBound
    split_ifs <;> ring
  simpa only [hscale, e, h] using H
