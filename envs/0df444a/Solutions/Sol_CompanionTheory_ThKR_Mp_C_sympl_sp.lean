-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.C.sympl_sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:28.080683+00:00
-- url     : https://prove2.me/submissions/3bb90463-1f04-42f0-86ef-9dbaa6b19801

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MapOfRealMul
import Theorems.Thm_CompanionTheory_ThKF_E_sympl_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.C
namespace CompanionTheory.ThKR.Mp.C
theorem _root_.solution (s : Sp l) (w w' : l ⊕ l → ℝ) : sympl (s.1 *ᵥ w) (s.1 *ᵥ w') = sympl w w' := by
  have h2 : s.1ᵀ * (Matrix.J l ℝ * s.1) = Matrix.J l ℝ := by
    have := SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem s.2)
    rwa [transpose_transpose, Matrix.mul_assoc] at this
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]
end CompanionTheory.ThKR.Mp.C
