-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.upperUni_blk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:05.694013+00:00
-- url     : https://prove2.me/submissions/1cd507cb-e409-4833-b7b5-0013e1dcdb1d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_ll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    IsUpperUni (blk A b a e) ↔ IsUpperUni A ∧ a = 0 ∧ e = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_, ?_⟩
    · rw [← blk_cc A b a e]; exact h1 _
    · rw [← blk_cc A b a e]; exact h2 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)
    · ext j
      rw [← blk_lc A b a e]; exact h2 _ _ (Fin.castSucc_lt_last j)
    · rw [← blk_ll A b a e]; exact h1 _
  · rintro ⟨⟨h1, h2⟩, rfl, rfl⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · induction i using Fin.lastCases with
      | last => rw [blk_ll]
      | cast i => rw [blk_cc]; exact h1 i
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => rw [blk_lc]; rfl
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j => rw [blk_cc]; exact h2 _ _ (Fin.castSucc_lt_castSucc_iff.1 hij)
end Formalism.FourierDecayAlt.P.G4
