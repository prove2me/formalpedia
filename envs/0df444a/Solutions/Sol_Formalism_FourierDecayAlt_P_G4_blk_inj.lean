-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.blk_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:34.327948+00:00
-- url     : https://prove2.me/submissions/f4070373-84e2-483b-ac62-e3439246005b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_cl
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
theorem _root_.solution {n : ℕ} {A A' : Matrix (Fin n) (Fin n) ℂ} {b a b' a' : Fin n → ℂ} {e e' : ℂ} :
    blk A b a e = blk A' b' a' e' ↔ A = A' ∧ b = b' ∧ a = a' ∧ e = e' := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i j
      have := congrFun (congrFun h i.castSucc) j.castSucc
      simpa only [blk_cc] using this
    · ext i
      have := congrFun (congrFun h i.castSucc) (Fin.last n)
      simpa only [blk_cl] using this
    · ext j
      have := congrFun (congrFun h (Fin.last n)) j.castSucc
      simpa only [blk_lc] using this
    · have := congrFun (congrFun h (Fin.last n)) (Fin.last n)
      simpa only [blk_ll] using this
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl
end Formalism.FourierDecayAlt.P.G4
