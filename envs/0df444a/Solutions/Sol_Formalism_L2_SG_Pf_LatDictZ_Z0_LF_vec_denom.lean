-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.LF.vec_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:32.988148+00:00
-- url     : https://prove2.me/submissions/d58c7338-a0e6-4fa4-8357-019fd7288221

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Lemmata_Denominators_Denom
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_LocFin
import Theorems.Thm_Bl_DenominatorsAlt_goal1
import Theorems.Thm_Bl_NearbyExistence_goal1
import Theorems.Thm_Bl_VolumeRatioCancellation_goal1
import Theorems.Thm_Bl_general_b_fact_second_rest_goal1
import Theorems.Thm_P2M_Bl_general_b_fact_second______goal1_b283150bff17


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.LF
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.LF
theorem _root_.solution (M : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (M : Set (Fin n → E)) = ⊤)
    (v : Fin n → E) : ∃ m : ℕ, 0 < m ∧ (m : 𝓞 E) • v ∈ M := by
  first | exact Bl.DenominatorsAlt.goal1 .. | (apply Bl.DenominatorsAlt.goal1 <;> assumption) | (intros; apply Bl.DenominatorsAlt.goal1 <;> assumption)
end Formalism.L2.SG.Pf.LatDictZ.Z0.LF
