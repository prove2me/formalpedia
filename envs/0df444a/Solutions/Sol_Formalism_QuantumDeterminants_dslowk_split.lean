-- Prove2me | solution 1 for Formalism.QuantumDeterminants.dslowk_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:12:44.322786+00:00
-- url     : https://prove2.me/submissions/02087924-1047-4ca7-99bc-11b3b2e6441f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution {α : Type*} (s : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    (s.filter p).card =
      (s.filter fun x => p x ∧ q x).card + (s.filter fun x => p x ∧ ¬ q x).card := by
  have hd : Disjoint (s.filter fun x => p x ∧ q x) (s.filter fun x => p x ∧ ¬ q x) :=
    Finset.disjoint_filter.2 fun x _ h1 h2 => h2.2 h1.2
  rw [← Finset.card_disjUnion _ _ hd]
  congr 1
  ext x
  simp only [Finset.mem_disjUnion, Finset.mem_filter]
  tauto
end Formalism.QuantumDeterminants
