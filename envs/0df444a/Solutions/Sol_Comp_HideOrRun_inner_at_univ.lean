-- Prove2me | solution 1 for Comp.HideOrRun.inner_at_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:53:46.751917+00:00
-- url     : https://prove2.me/submissions/923a7b6e-e8a5-4bcf-8088-34b4b164fa3c

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_mid_eq

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution :
    ((game.toCSG game_wf).LFInner ↑target ↑(Finset.univ : Finset HR)).lfp =
      (↑winning : Set HR) :=
  mid_eq target Finset.univ winning 2 (by decide) (by decide)
end Comp.HideOrRun
