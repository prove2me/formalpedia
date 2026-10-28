-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.esa_on_core
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:30:45.233819+00:00
-- url     : https://prove2.me/submissions/7db87062-8231-4963-8f00-3c9197d9d3fd

-- Generated from ChapterFarisLavineOnly.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.esa_on_core
import Theorems.Thm_BookProof_QgTruncationResolvent_esa_core_of_ext
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_essentiallySelfAdjointOn
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterFarisLavineOnly
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterLeafGaps
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL


open scoped ENNReal

noncomputable section


open BookProof.FarisLavine


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


variable (d : CoreData F)
open BookProof.QgOuterFockCoreFL.CoreData in
theorem solution (hsym : SymmetricOn d.C₀ d.H₀) {c : ℝ} (hc : 0 ≤ c)
    (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p) :
    EssentiallySelfAdjointOn d.C₀ d.H₀ := by
  exact BookProof.QgTruncationResolvent.esa_core_of_ext d (d.ext_essentiallySelfAdjointOn hsym hc hcomm)
