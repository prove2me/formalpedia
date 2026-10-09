-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.ext_essentiallySelfAdjointOn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:52:17.80804+00:00
-- url     : https://prove2.me/submissions/e56d0bfd-c83a-4055-be35-e6d86479766c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQgOuterFockCoreFL.lean — solution of BookProof.QgOuterFockCoreFL.CoreData.ext_essentiallySelfAdjointOn
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_symmetricOn
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_commForm_le
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_essentiallySelfAdjointOn
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData




open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs
open BookProof.EsaClosure
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore
open Filter Topology

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (d : CoreData F)

set_option maxHeartbeats 1000000 in
theorem solution (hsym : SymmetricOn d.C₀ d.H₀) {c : ℝ} (hc : 0 ≤ c)
    (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p) :
    EssentiallySelfAdjointOn d.C.dom d.ext := d.C.essentiallySelfAdjointOn d.ext (d.ext_symmetricOn hsym) c hc (d.ext_commForm_le hcomm)
