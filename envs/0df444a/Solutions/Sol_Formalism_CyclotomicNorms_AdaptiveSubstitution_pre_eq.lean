-- Prove2me | solution 1 for Formalism.CyclotomicNorms.AdaptiveSubstitution.pre_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:25.968446+00:00
-- url     : https://prove2.me/submissions/28a371af-3207-4046-ac7e-f2c221c57811

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_AdaptiveSubstitutionBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.AdaptiveSubstitution
namespace Formalism.CyclotomicNorms.AdaptiveSubstitution
theorem _root_.solution (ℓ A : ℕ) (B : List ℕ → ℕ) (n : ℕ) :
    pre ℓ A B n = List.ofFn (fun i : Fin n => step ℓ A B (pre ℓ A B i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    rfl
end Formalism.CyclotomicNorms.AdaptiveSubstitution
