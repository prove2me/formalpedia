-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.count_pred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:59.310722+00:00
-- url     : https://prove2.me/submissions/1865b12c-fb29-480e-955f-0849465803fa

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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {J : Type} [Fintype J] [DecidableEq J] {N1 p : ℕ} (τ : Fin p → J)
    (I : Fin p → Fin N1) (Pr : J → Prop) [DecidablePred Pr] :
    (∑ y ∈ Finset.univ.filter (fun y : J × Fin N1 => Pr y.1),
      (∑ i, Finsupp.single (τ i, I i) 1 : J × Fin N1 →₀ ℕ) y) =
      (Finset.univ.filter (fun i => Pr (τ i))).card := by
  classical
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_comm, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter, Finset.sum_eq_single (τ i, I i)]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.DworkPowerSeriesWeights
