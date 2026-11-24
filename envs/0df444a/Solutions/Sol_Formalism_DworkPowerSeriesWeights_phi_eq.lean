-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:08:28.121969+00:00
-- url     : https://prove2.me/submissions/0309e057-77f8-45df-b8d6-7730165f4923

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_block_slice

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
    (τ : Bool × H) (k : Fin N0) (b : Fin N1) :
    (∑ z, C (bA x (bE H N0 N1 (τ, k, b)) z) * X z :
      MvPolynomial ((Bool × H) × Fin N0 × Fin N1) K) =
      ∑ a, C (bM x τ k a) * X (τ, a, b) := by
  rw [sum_block_slice τ b]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [bA, bE]
  · intro w hw
    have : ¬ (w.1 = (τ.1, τ.2) ∧ w.2.2 = b) := hw
    simp [bA, bE, this]
end Formalism.DworkPowerSeriesWeights
