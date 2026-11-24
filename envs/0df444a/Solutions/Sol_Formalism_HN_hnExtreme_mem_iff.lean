-- Prove2me | solution 1 for Formalism.HN.hnExtreme_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:26.272322+00:00
-- url     : https://prove2.me/submissions/02f4a6a2-feee-44bb-9faf-d48be738166b

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Lemmata_GeneralBFactLeftForm_Imports
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNExtreme
import Theorems.Thm_Bl_general_b_fact_left_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w
namespace Formalism.HN
theorem _root_.solution {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (θ : ℝ) (j : Fin n) :
    θ ≤ f j ↔ (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ f i)).card := by
  first | exact Bl.general_b_fact_left_form.goal1 .. | (apply Bl.general_b_fact_left_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_form.goal1 <;> first | assumption | infer_instance)
end Formalism.HN
