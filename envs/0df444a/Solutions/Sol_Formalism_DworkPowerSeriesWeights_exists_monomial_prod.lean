-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.exists_monomial_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:46.716502+00:00
-- url     : https://prove2.me/submissions/d73632db-aa27-4ad0-82d2-8769c23ac273

import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership

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
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R ι α : Type} [CommSemiring R] (s : Finset α)
    (f : α → MvPolynomial ι R) (hf : ∀ i ∈ s, ∃ e, f i = monomial e 1) :
    ∃ e, ∏ i ∈ s, f i = monomial e 1 := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => ⟨0, ?_⟩) ?_
  · rw [Finset.prod_empty, ← MvPolynomial.C_1, MvPolynomial.C_apply]
  intro a s ha ih hf
  obtain ⟨e1, h1⟩ := hf a (Finset.mem_insert_self a s)
  obtain ⟨e2, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
  exact ⟨e1 + e2, by rw [Finset.prod_insert ha, h1, h2, MvPolynomial.monomial_mul, mul_one]⟩
end Formalism.DworkPowerSeriesWeights
