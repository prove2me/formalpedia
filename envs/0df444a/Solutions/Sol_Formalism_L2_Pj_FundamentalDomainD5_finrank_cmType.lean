-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.finrank_cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:15:48.771391+00:00
-- url     : https://prove2.me/submissions/9e9a7091-e1ba-4455-9198-f7304f70173d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinrankCmType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix
open scoped ComplexConjugate
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    Module.finrank ℚ K = 2 * Fintype.card ι := by
  rw [← NumberField.Embeddings.card K ℂ, ← Fintype.card_congr (cmEquiv σ hinj hcm), Fintype.card_sum]
  ring
end Formalism.L2.Pj.FundamentalDomainD5
