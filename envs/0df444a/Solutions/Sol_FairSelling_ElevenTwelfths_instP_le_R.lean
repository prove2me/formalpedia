-- Prove2me | solution 1 for FairSelling.ElevenTwelfths.instP_le_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:13.09796+00:00
-- url     : https://prove2.me/submissions/3cf407b2-0e97-418c-8695-6105c4f49147

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ElevenTwelfths
open FeigeNorkin
namespace FairSelling.ElevenTwelfths
theorem _root_.solution {δ : ℝ} (hδ : δ ≤ 1/12) (g : Fin 8) :
    instP δ g ≤ instV 0 g := by
  fin_cases g <;>
    simp only [instP, instV, fnR, fnU, Matrix.cons_val_zero] <;> norm_num <;> linarith
end FairSelling.ElevenTwelfths
