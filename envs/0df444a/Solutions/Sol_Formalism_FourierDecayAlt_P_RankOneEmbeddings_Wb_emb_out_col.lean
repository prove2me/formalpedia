-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb.emb_out_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:51.348457+00:00
-- url     : https://prove2.me/submissions/ddea2504-63b0-4914-9632-3cda56375067

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  have hj' : ¬ (r ≤ j.val ∧ j.val ≤ r + k) := hj
  simp only [embWb]
  rw [dif_neg (fun h => hj' h.2)]
  by_cases hqj : q = j
  · subst hqj
    rw [if_pos ⟨rfl, hj'⟩, if_pos rfl]
  · rw [if_neg (fun h => hqj h.1), if_neg hqj]
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
