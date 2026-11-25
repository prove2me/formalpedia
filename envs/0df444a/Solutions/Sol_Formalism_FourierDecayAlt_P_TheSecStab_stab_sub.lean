-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSecStab.stab_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:50.898803+00:00
-- url     : https://prove2.me/submissions/c7da7b02-3c0d-4ffc-bb2b-44aecaf2b255

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_block_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_uwset_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSecStab_emb_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TheSecStab
theorem _root_.solution (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ ζ' : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    (hζ' : Tz k r z * Tz k r z' < Complex.normSq ζ') (p : Mat k r × Mat k r)
    (hp : p ∈ NF.Stab k r z z' (theSection k r z z') ζ) : p ∈ NF.Stab k r z z' (theSection k r z z') ζ' := by
  obtain ⟨h1, h2, heq⟩ := hp
  obtain ⟨μ, hμ, hp1, hμa⟩ := uwset_block hz h1
  obtain ⟨μ', hμ', hp2, hμb⟩ := uwset_block hz' h2
  refine ⟨h1, h2, ?_⟩
  have ha := herm_self k r z hz
  have hb := herm_self k r z' hz'
  have hblock : μ * theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') ζ * μ' =
      theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') ζ := by
    apply emb_inj (r := r)
    rw [emb_mul, emb_mul, ← hp1, ← hp2]
    exact heq
  have hc := (block_iff hk hT hT' ha hb hζ hμ hμ' hμa hμb).1 hblock
  have hblock' := (block_iff hk hT hT' ha hb hζ' hμ hμ' hμa hμb).2 hc
  show p.1 * embWb k r (theSection k r z z' ζ') * p.2 = embWb k r (theSection k r z z' ζ')
  rw [hp1, hp2, ← emb_mul, ← emb_mul]
  exact congrArg (embWb k r) hblock'
end Formalism.FourierDecayAlt.P.TheSecStab
