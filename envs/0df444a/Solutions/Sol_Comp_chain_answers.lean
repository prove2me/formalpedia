-- Prove2me | solution 1 for Comp.chain_answers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:34:12.523827+00:00
-- url     : https://prove2.me/submissions/10eb8e05-f417-4306-b5a7-4c2b589bd1ef

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_chain_G

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution :
    chainGame.Answers chainGame_wf (Objective.sureSafe chainSafe) (Answer.region chainGood) :=
  .sureSafe chain_G
end Comp
