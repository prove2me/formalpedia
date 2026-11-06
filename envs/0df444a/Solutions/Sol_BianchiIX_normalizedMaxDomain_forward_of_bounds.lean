-- Prove2me | solution 1 for BianchiIX.normalizedMaxDomain_forward_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:01:39.27817+00:00
-- url     : https://prove2.me/submissions/2a20f758-9fb5-4834-9ecd-93cb8c7b8e50

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_exists_normalized_solution_uniform
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_extension
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
open scoped Topology

private theorem BianchiIX.lt_csSup_of_mem_open {I : Set ℝ} (ho : IsOpen I) (hb : BddAbove I)
    {t : ℝ} (ht : t ∈ I) : t < sSup I := by
  obtain ⟨l, u, htu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds ht)
  have hmid : (t + u) / 2 ∈ I := hsub ⟨by linarith [htu.1, htu.2], by linarith [htu.2]⟩
  exact (show t < (t + u) / 2 by linarith [htu.2]).trans_le (le_csSup hb hmid)

/-- Bounds on each finite forward interval exclude a finite maximal right endpoint. -/
theorem solution {x₀ : NormalizedState} {t₀ : ℝ}
    (hbound : ∀ T : ℝ, ∃ R ≥ (0 : ℝ), ∀ t ∈ normalizedMaxDomain x₀ t₀,
      t ∈ Icc t₀ T → ‖normalizedMaxCurve x₀ t₀ t‖ ≤ R) :
    Ici t₀ ⊆ normalizedMaxDomain x₀ t₀ := by
  let S := maximalNormalizedSolution x₀ t₀
  have hunbounded : ¬ BddAbove S.domain := by
    intro hb
    let b := sSup S.domain
    have ht₀b : t₀ < b := lt_csSup_of_mem_open S.isOpen_domain hb S.initial_mem
    obtain ⟨R, hR, hboundR⟩ := hbound b
    obtain ⟨ε, hε, hlocal⟩ := exists_normalized_solution_uniform R hR
    have hmax : max t₀ (b - ε) < b := max_lt ht₀b (by linarith)
    obtain ⟨s, hs, hclose⟩ := exists_lt_of_lt_csSup ⟨t₀, S.initial_mem⟩ hmax
    have hsbound := hboundR s hs ⟨(le_max_left _ _).trans hclose.le, le_csSup hb hs⟩
    obtain ⟨β, hinit, hβ⟩ := hlocal (S.curve s) hsbound s
    have hsJ : s ∈ Ioo (s - ε) (s + ε) := by constructor <;> linarith
    have hbJ : b ∈ Ioo (s - ε) (s + ε) := by
      have hsb : s ≤ b := le_csSup hb hs
      have hbs : b - ε < s := (le_max_right _ _).trans_lt hclose
      constructor <;> linarith
    have hbmem := normalizedMaxDomain_contains_extension (convex_Ioo _ _) isOpen_Ioo
      hβ hs hsJ hinit.symm hbJ
    exact (lt_irrefl b) (lt_csSup_of_mem_open S.isOpen_domain hb hbmem)
  intro t ht
  obtain ⟨u, hu, htu⟩ := not_bddAbove_iff.mp hunbounded t
  exact S.convex_domain.ordConnected.out S.initial_mem hu ⟨ht, htu.le⟩
