-- Prove2me | solution 1 for Formalism.L2.Col.card_HPsym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:03:15.135987+00:00
-- url     : https://prove2.me/submissions/bbc11b1b-a4cf-40fb-ac7d-2d4ae091fca0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_HPsym_eq
import Theorems.Thm_Formalism_L2_Col_card_sym_pairs

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
variable {n : ℕ} {κ : Type} [CommRing κ]
namespace Formalism.L2.Col
theorem _root_.solution (κ : Type) [CommRing κ] (n k rS : ℕ) (hn : rS + k < n) :
    Nat.card ↥(HPsym κ n k rS) = Nat.card κ ^ (n * (n - 1) / 2 - k) := by
  have h1 : Nat.card ↥(HPsym κ n k rS) =
      Nat.card ↥(uSet κ (fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k))) := by
    rw [← HPsym_eq]; rfl
  rw [h1, card_uSet (P := fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k)) (fun _ _ h => h.1)]
  congr 1
  exact card_sym_pairs k rS hn
end Formalism.L2.Col
