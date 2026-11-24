-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.aa_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:08:25.0688+00:00
-- url     : https://prove2.me/submissions/12a4c1e3-7c88-43e8-ba9f-35df97942298

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_block_slice
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_bE

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
variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution [Fintype H] [DecidableEq H] {N1 : ℕ} (x : Bool × H → Matrix (Fin N0) (Fin N0) K)
    (z : (Bool × H) × Fin N0 × Fin N1) :
    (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
      MvPowerSeries (Bool × H × Fin N0 × Fin N1) K) =
      ∑ i, MvPowerSeries.C (bM x z.1 i z.2.1) * MvPowerSeries.X (z.1.1, z.1.2, i, z.2.2) := by
  rw [sum_bE, sum_block_slice z.1 z.2.2]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [bA, bE]
  · intro w hw
    have : ¬ (z.1 = (w.1.1, w.1.2) ∧ z.2.2 = w.2.2) := fun h => hw ⟨h.1.symm, h.2.symm⟩
    simp [bA, bE, this]
end Formalism.DworkPowerSeriesWeights
