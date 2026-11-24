-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.det_ptMatN_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:41.224866+00:00
-- url     : https://prove2.me/submissions/605217b0-aed2-4a97-8c78-9af703b6c0b4

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_ptEntry_app_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_ptEntry_app_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_ptEntry_app_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (c : ℂ) (H : C.LPt) (n : ℕ) (hn : D.ptSize H = n) :
    (D.ptMatN (H ++ [(1, c)]) (n + 1)).det = c * (D.ptMatN H n).det ∧
      D.ptMatN (H ++ [(1, c)]) n = D.ptMatN H n := by
  subst hn
  have hsub : (D.ptMatN (H ++ [(1, c)]) (D.ptSize H + 1)).submatrix Fin.castSucc Fin.castSucc =
      D.ptMatN H (D.ptSize H) := by
    ext a b
    simp only [Matrix.submatrix_apply, D.ptMatN, Fin.coe_castSucc]
    exact ptEntry_app_lt c H a b a.isLt b.isLt
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_succ_row _ (Fin.last _), Finset.sum_eq_single (Fin.last _)]
    · simp only [Fin.val_last, Fin.succAbove_last]
      rw [hsub]
      simp only [D.ptMatN, Fin.val_last, ptEntry_app_last]
      simp
    · intro j _ hj
      have hj' : (j : ℕ) < D.ptSize H := by
        have := j.isLt
        have : (j : ℕ) ≠ D.ptSize H := fun h => hj (Fin.ext (by simp [h]))
        omega
      simp [D.ptMatN, ptEntry_app_row c H j hj']
    · simp
  · ext a b
    simp only [D.ptMatN]
    exact ptEntry_app_lt c H a b a.isLt b.isLt
end Formalism.FourierDecayAlt.P.PBD
