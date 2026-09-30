-- Prove2me | solution 1 for CalamaiMore.ActiveSet.tangentCone_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:46:48.36838+00:00
-- url     : https://prove2.me/submissions/2e22e0c4-2d4b-46e9-ae13-351e41dc93de

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Definitions.Def_CalamaiMore_Shared_tangentCone
import Definitions.Def_CalamaiMore_ActiveSet_polyhedron
open scoped InnerProductSpace Topology
open Filter CalamaiMore.Shared
noncomputable section


namespace CalamaiMore.ActiveSet

/-- Calamai–Moré, §4, p. 105 (display after (4.2)): for the polyhedral set
`Ω = {x : ⟨c_j, x⟩ ≥ δ_j}` and `x ∈ Ω`, the tangent cone is
`T(x) = {v : ⟨c_j, v⟩ ≥ 0, j ∈ A(x)}`. -/
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ)
    (x : E) (hx : x ∈ polyhedron c δ) :
    CalamaiMore.Shared.tangentCone (polyhedron c δ) x =
      {v | ∀ j ∈ activeSet c δ x, 0 ≤ inner ℝ (c j) v} := by
  classical
  let T : Set E := {v | ∀ j ∈ activeSet c δ x, 0 ≤ inner ℝ (c j) v}
  have heq : CalamaiMore.Shared.feasibleDirections (polyhedron c δ) x = T := by
    ext v
    constructor
    · intro hv j hj
      change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ polyhedron c δ at hv
      have ht := hv.and (eventually_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)
      obtain ⟨t, htΩ, ht⟩ := ht.exists
      have hactive : inner ℝ (c j) x = δ j := by simpa [activeSet] using hj
      have hh := htΩ j
      simp only [inner_add_right, inner_smul_right, hactive] at hh
      have : 0 ≤ t * inner ℝ (c j) v := by linarith
      exact (mul_nonneg_iff_of_pos_left ht).mp this
    · intro hv
      have hj (j : Fin m) : ∀ᶠ t : ℝ in 𝓝[>] 0, δ j ≤ inner ℝ (c j) (x + t • v) := by
        by_cases hact : inner ℝ (c j) x = δ j
        · have hmem : j ∈ activeSet c δ x := by simp [activeSet, hact]
          have hvj := hv j hmem
          filter_upwards [eventually_mem_nhdsWithin] with t ht
          simp only [inner_add_right, inner_smul_right, hact]
          exact le_add_of_nonneg_right (mul_nonneg (le_of_lt ht) hvj)
        · have hstrict : δ j < inner ℝ (c j) x := lt_of_le_of_ne (hx j) (Ne.symm hact)
          have hcont : ContinuousAt (fun t : ℝ => inner ℝ (c j) (x + t • v)) 0 := by fun_prop
          have hstrict' : δ j < inner ℝ (c j) (x + (0 : ℝ) • v) := by simpa using hstrict
          have hh := hcont.eventually (eventually_gt_nhds hstrict')
          exact (hh.filter_mono nhdsWithin_le_nhds).mono (fun t ht => ht.le)
      exact Filter.eventually_all.mpr hj
  have hclosed : IsClosed T := by
    have he : T = (⋂ j, ⋂ (_ : j ∈ activeSet c δ x), {v : E | 0 ≤ inner ℝ (c j) v}) := by
      ext v
      simp [T]
    rw [he]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro hj
    exact isClosed_le continuous_const (by fun_prop)
  change closure (CalamaiMore.Shared.feasibleDirections (polyhedron c δ) x) = T
  rw [heq, hclosed.closure_eq]


end CalamaiMore.ActiveSet
