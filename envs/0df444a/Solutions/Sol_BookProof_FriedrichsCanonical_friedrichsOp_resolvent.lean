-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.friedrichsOp_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T14:49:26.989203+00:00
-- url     : https://prove2.me/submissions/5dc65019-b5cb-4e8e-b4bd-a3b2bfce0b38

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.friedrichsOp_resolvent
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_apply
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHashimotoShiftInvert
import Theorems.Thm_BookProof_FriedrichsCanonical_resolvent_mem_friedrichsDomain
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.QgOuterFockFL

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) (u : F) :
    friedrichsOp P hdense ⟨friedrichsResolvent P u, resolvent_mem_friedrichsDomain P u⟩
      = u - friedrichsResolvent P u := by

  have hpre : preim (friedrichsResolvent P)
      ⟨friedrichsResolvent P u, resolvent_mem_friedrichsDomain P u⟩ = u :=
    preim_eq _ (friedrichsResolvent_injective P hdense) _ rfl
  rw [friedrichsOp_apply]
  erw [hpre]
  push_cast
  module
