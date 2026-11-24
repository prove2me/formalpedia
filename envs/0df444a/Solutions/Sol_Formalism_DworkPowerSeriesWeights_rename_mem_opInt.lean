-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.rename_mem_opInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:54:35.845792+00:00
-- url     : https://prove2.me/submissions/5d78f9b6-7362-4a09-9c7c-5cbd228ada7f

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {H : Type} {N0 : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {σ ρ : Type} (f : σ → ρ) (P : MvPolynomial σ K)
    (hP : P ∈ opInt K σ) : rename f P ∈ opInt K ρ := by
  classical
  rw [P.as_sum, map_sum]
  refine Subring.sum_mem _ fun μ _ => ?_
  rw [rename_monomial]
  intro κ
  rw [coeff_monomial]
  split_ifs
  · exact hP μ
  · simp
end Formalism.DworkPowerSeriesWeights
