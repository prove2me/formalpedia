-- Prove2me | solution 1 for Formalism.UG.P.split_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:52:57.875453+00:00
-- url     : https://prove2.me/submissions/e888227d-c56d-4394-bf60-ca0060a6efa8

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso
import Theorems.Thm_Formalism_UG_P_split_mat_ext
import Theorems.Thm_Formalism_UG_P_split_map_fst_mul
import Theorems.Thm_Formalism_UG_P_split_map_snd_mul
import Theorems.Thm_Formalism_UG_P_split_cT_fst
import Theorems.Thm_Formalism_UG_P_split_cT_snd
import Theorems.Thm_Formalism_UG_P_splitJ_fst
import Theorems.Thm_Formalism_UG_P_splitJ_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (J₁ : Matrix n n R) (g : GL n (R × R)) :
    g ∈ UJ (swapR R) (splitJ J₁) ↔
      ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * (g : Matrix n n (R × R)).map Prod.fst
        = J₁ := by
  constructor
  · intro h
    have h' := congrArg (fun M : Matrix n n (R × R) => M.map Prod.fst)
      (show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁ from h)
    simpa only [split_map_fst_mul, split_cT_fst, splitJ_fst] using h'
  · intro h
    show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁
    apply split_mat_ext
    · rw [split_map_fst_mul, split_map_fst_mul, split_cT_fst, splitJ_fst, h]
    · rw [split_map_snd_mul, split_map_snd_mul, split_cT_snd, splitJ_snd]
      have h' := congrArg Matrix.transpose h
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h'
      rw [← Matrix.mul_assoc] at h'
      exact h'
end Formalism.UG.P
