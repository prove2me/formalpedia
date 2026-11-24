-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.uwb_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:20.67793+00:00
-- url     : https://prove2.me/submissions/10a65c1a-f485-4962-98cd-6709ad56fc2a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_not_mid_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_not_mid_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_uwb_eq_emb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_fix

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution (g : Mat k r) : g ∈ UWb k r ↔ ∃ a, aᴴ * Hb k * a = Hb k ∧ embWb k r a = g := by
  constructor
  · intro hg
    have h := uwb_eq_emb hg
    refine ⟨_, ?_, h.symm⟩
    rw [← emb_mem (r := r), ← h]
    exact hg.1
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(emb_mem a).mpr ha, fun b => ⟨emb_fix a _ (not_mid_e b), emb_fix a _ (not_mid_es b)⟩⟩
end Formalism.FourierDecayAlt.P.B2x3
