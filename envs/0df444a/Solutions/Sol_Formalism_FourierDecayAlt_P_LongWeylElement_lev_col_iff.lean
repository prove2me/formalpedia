-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.lev_col_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:30.084852+00:00
-- url     : https://prove2.me/submissions/df97f657-6b96-4ca8-a10f-ea5ea2abce99

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mid_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_levPos_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_levPos_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mid_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_levPos_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_levPos_inj


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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (g : Mat k r') (t : Fin (2 * r' + k + 1)) :
    (∀ p, ιLev k 1 r' g p (levPos k 1 r' t) = if p = levPos k 1 r' t then 1 else 0) ↔
      ∀ s, g s t = if s = t then 1 else 0 := by
  constructor
  · intro h s
    have := h (levPos k 1 r' s)
    rw [lev_mm] at this
    rw [this]
    exact if_congr (levPos_inj k r').eq_iff rfl rfl
  · intro h p
    by_cases hp : mid k r' p
    · obtain ⟨s, rfl⟩ := (mid_iff k r' p).1 hp
      rw [lev_mm, h s]
      exact if_congr (levPos_inj k r').eq_iff.symm rfl rfl
    · exact lev_n k r' g p _ hp
end Formalism.FourierDecayAlt.P.LongWeylElement
