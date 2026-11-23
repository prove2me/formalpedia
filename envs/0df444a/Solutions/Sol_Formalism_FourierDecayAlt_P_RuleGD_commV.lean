-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.commV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:20.901826+00:00
-- url     : https://prove2.me/submissions/284fec11-3d40-466a-a91f-c6698f4055b9

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_alg
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_comm_of_cj
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_cb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_cbi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleGD_m___020c678e767a
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_GG
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_GGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_keyV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.RuleGD
theorem _root_.solution (L : LevelData A r) (x xi : A) (h : x * xi = 1) (h' : xi * x = 1)
    (hp : ∀ m, L.pb m * x = x * L.pb m) (hfn : ∀ y ∈ L.fns, y * x = x * y)
    (hn : L.nabs * x = x * L.nabs) (Y : ℂ) :
    x * L.Ahatv Y = L.Ahatv Y * x ∧ x * L.R0v Y = L.R0v Y * x := by
  have hf : ∀ y ∈ L.fns, cj x xi h h' y = y := fun y hy => cj_fix x xi h h' (hfn y hy)
  obtain ⟨a1, a2⟩ := keyV L (cj x xi h h') 0 0 (cj_alg x xi h h')
    (fun m => by rw [map_zero, add_zero]; exact cj_fix x xi h h' (hp m))
    (fun l => hf _ (m_cb L l)) (fun l => hf _ (m_cbi L l)) (fun l => hf _ (m_c L l))
    (hf _ (m_GG L)) (hf _ (m_ζ L)) (hf _ (m_GGi L))
    (by rw [map_zero, zero_mul, sub_zero, sub_zero]; exact cj_fix x xi h h' hn) Y
  rw [sub_zero] at a1 a2
  rw [mul_zero, zero_mul, add_zero] at a2
  exact ⟨comm_of_cj x xi h h' a1, comm_of_cj x xi h h' a2⟩
end Formalism.FourierDecayAlt.P.RuleGD
