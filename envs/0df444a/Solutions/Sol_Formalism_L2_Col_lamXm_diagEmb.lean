-- Prove2me | solution 1 for Formalism.L2.Col.lamXm_diagEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:51.259591+00:00
-- url     : https://prove2.me/submissions/97d3c479-d574-4c2a-8f07-051045c2b1f4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_blkIdx_replicate_of_le
import Theorems.Thm_Formalism_L2_Col_lamGen_diagEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (r t m : ℕ) (g : ↥(HJ κ (r + m * t) r t m)) :
    lamXm ψ χ (r + m * t + 1) r t m
      ⟨diagEmb κ (Nat.le_succ (r + m * t)) g.1, ⟨diagEmb_mem_uniUT _ g.2, diagEmb_mem_fixCol _ le_rfl g.1⟩⟩ =
      lamJ ψ χ (r + m * t) r t m g := by
  unfold lamXm lamJ
  rw [MonoidHom.comp_apply]
  refine lamGen_diagEmb ψ χ (Nat.le_succ _) (by omega) _ _ (fun i hi => ?_) g
  have h1 : coarse r (List.replicate m t) i = m + 1 := by
    unfold coarse
    simp only [blkIdx]
    rw [if_neg (by omega), blkIdx_replicate_of_le t m (i - r) (by omega)]
  rw [h1, List.length_replicate]
  omega
end Formalism.L2.Col
