-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.emb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:00.426531+00:00
-- url     : https://prove2.me/submissions/213d4446-1d33-4f6a-8db1-4fc56203a390

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hpk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_sand_inj
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq


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
theorem _root_.solution (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r a ∈ GV k r ↔ aᴴ * Hb k * a = Hb k := by
  show (embWb k r a)ᴴ * Hpk k r * embWb k r a = Hpk k r ↔ _
  rw [emb_form]
  constructor
  · intro h
    exact sand_inj (add_right_cancel (h.trans (Hpk_eq (k := k) (r := r))))
  · intro h
    rw [h]
    exact Hpk_eq.symm
end Formalism.FourierDecayAlt.P.B2x3
