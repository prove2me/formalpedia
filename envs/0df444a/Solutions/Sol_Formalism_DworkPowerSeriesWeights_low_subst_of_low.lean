-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.low_subst_of_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:46.134845+00:00
-- url     : https://prove2.me/submissions/2e1960f9-12fb-4dc3-a453-85cbda761e4a

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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {ι : Type v} [Finite ι] {τ : Type w}
    {k : ι → MvPowerSeries τ K} (hk : ∀ i, constantCoeff (k i) = 0) {m : ℕ}
    {f : MvPowerSeries ι K} (hf : Low m f) : Low m (subst k f) := by
  intro d hd
  have hs : HasSubst k := hasSubst_of_constantCoeff_zero hk
  rw [coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rcases lt_or_ge e.degree m with he | he
  · rw [hf e he, zero_smul]
  · have := low_P (fun i => (low_one_iff _).2 (hk i)) e d (lt_of_lt_of_le hd he)
    simp only [Formalism.FG.SolveVAux.P] at this
    rw [this, smul_zero]
end Formalism.DworkPowerSeriesWeights
