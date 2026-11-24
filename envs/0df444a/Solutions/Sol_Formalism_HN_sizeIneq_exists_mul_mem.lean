-- Prove2me | solution 1 for Formalism.HN.sizeIneq_exists_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:29.751977+00:00
-- url     : https://prove2.me/submissions/05df8c02-a02e-41ee-9879-bff01d1f9c4f

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Lemmata_GeneralBFactSecondTail_Imports
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
import Theorems.Thm_P2M_Bl_general_b_fact_second_______goal1_d3261d09d138


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type*} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
namespace Formalism.HN
theorem _root_.solution (A : Submodule (𝓞 K) V) (x : V)
    (hx : x ∈ Submodule.span K (A : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first | exact Bl.general_b_fact_second''''''.goal1 .. | (apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> first | assumption | infer_instance)
end Formalism.HN
