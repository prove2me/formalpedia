-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.isIdMod2_genLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:18.858037+00:00
-- url     : https://prove2.me/submissions/493370ec-ea6e-46f4-af92-69eef56f6f1f

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff low_P)
variable {K : Type u} [Field K] {τ : Type v} [DecidableEq τ]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (p : τ → τ) :
    Formalism.FG.IsIdMod2 (genLog (K := K) l p) := by
  have hl0 : 0 < l := by omega
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show (∑ e ∈ Finset.range ((0 : τ →₀ ℕ).degree + 1),
      if (0 : τ →₀ ℕ) = Finsupp.single (p^[e] j) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = 0
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    intro h
    have hd := congrArg Finsupp.degree h
    rw [map_zero, Finsupp.degree_single] at hd
    have := pow_pos (pow_pos hl0 2) e
    omega
  · show (∑ e ∈ Finset.range ((Finsupp.single i 1 : τ →₀ ℕ).degree + 1),
      if Finsupp.single i 1 = Finsupp.single (p^[e] j) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = _
    rw [Finsupp.degree_single, Finset.sum_range_succ, Finset.sum_range_one]
    have h1 : ¬ Finsupp.single i 1 = Finsupp.single (p^[1] j) ((l ^ 2) ^ 1) := by
      intro h
      have hd := congrArg Finsupp.degree h
      rw [Finsupp.degree_single, Finsupp.degree_single] at hd
      nlinarith
    rw [if_neg h1, add_zero]
    simp only [Function.iterate_zero, id, pow_zero, inv_one]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Finsupp.single_left_inj one_ne_zero]
end Formalism.DworkPowerSeriesWeights
