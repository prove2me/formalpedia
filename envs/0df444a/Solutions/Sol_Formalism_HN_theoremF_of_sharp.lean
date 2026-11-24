-- Prove2me | solution 1 for Formalism.HN.theoremF_of_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:02.745501+00:00
-- url     : https://prove2.me/submissions/bbe2c4f3-a906-4eea-895b-92070eee6511

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TheoremFSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (H : TheoremFSharp) : TheoremF := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ
    s u HH e η δ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    h23 h24 h25 h26
  have := H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26
  have hI : (1 : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hl : 0 ≤ Real.log (Fintype.card I : ℝ) := Real.log_nonneg hI
  linarith
end Formalism.HN
