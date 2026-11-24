-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bT_mul_bM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:56:00.651202+00:00
-- url     : https://prove2.me/submissions/147e1abd-6ebc-4105-af8a-76451adcf08c

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
variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ, (x τ).det ≠ 0)
    (τ : Bool × H) : bT x τ * bM x τ = x τ := by
  obtain ⟨e, t⟩ := τ
  cases e
  · simp [bT, bM]
  · simp only [bT, bM, if_true]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hx (false, t))), Matrix.transpose_one,
      Matrix.mul_one]
end Formalism.DworkPowerSeriesWeights
