-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.coeff_genLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:53.54981+00:00
-- url     : https://prove2.me/submissions/a7ea6266-96cf-4972-9d0a-75b96b8886a1

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lt_sq_pow
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
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (p : τ → τ) (x : τ) (n : τ →₀ ℕ) {M : ℕ}
    (hM : n.degree < M) :
    coeff n (genLog (K := K) l p x) = ∑ e ∈ Finset.range M,
      if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  show (∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = _
  apply Finset.sum_subset (fun e he => by simp only [Finset.mem_range] at he ⊢; omega)
  intro e _ hne
  rw [if_neg]
  intro h
  apply hne
  rw [Finset.mem_range]
  have hd := congrArg Finsupp.degree h
  rw [Finsupp.degree_single] at hd
  have := lt_sq_pow hl e
  omega
end Formalism.DworkPowerSeriesWeights
