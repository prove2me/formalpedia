-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.finite_words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:11.653721+00:00
-- url     : https://prove2.me/submissions/8964bfbc-fdeb-42af-8850-88b1030e478b

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx2
theorem _root_.solution {α : Type*} (A : Set α) (hA : A.Finite) (N : ℕ) :
    {w : List α | w.length ≤ N ∧ ∀ l ∈ w, l ∈ A}.Finite := by
  have : Finite A := hA.to_subtype
  refine ((List.finite_length_le A N).image (List.map Subtype.val)).subset ?_
  rintro w ⟨hw, hwA⟩
  refine ⟨w.attach.map (fun x => (⟨x.1, hwA x.1 x.2⟩ : A)), ?_, ?_⟩
  · simpa using hw
  · simp
end Formalism.FourierDecayAlt.P.TBBx2
