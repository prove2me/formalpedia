-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.PInv.prod_mul_prod_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:03:46.278444+00:00
-- url     : https://prove2.me/submissions/c7564605-a8db-4787-bc3e-52dbb2d68dbe

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.R.PInv
theorem _root_.solution : ∀ (n : ℕ) (f g : Fin n → A), (∀ i, f i * g i = 1) →
    (∀ i j, Commute (f i) (g j)) → (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h1, hc => by
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
      have hP : Commute (List.ofFn fun i => f i.succ).prod (g 0) :=
        Commute.list_prod_left _ _ (by
          intro a ha
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
          exact hc _ _)
      have ih := solution n (fun i => f i.succ) (fun i => g i.succ)
        (fun i => h1 _) (fun i j => hc _ _)
      calc f 0 * (List.ofFn fun i => f i.succ).prod * (g 0 * (List.ofFn fun i => g i.succ).prod)
          = f 0 * ((List.ofFn fun i => f i.succ).prod * g 0) * (List.ofFn fun i => g i.succ).prod := by
            noncomm_ring
        _ = f 0 * g 0 * ((List.ofFn fun i => f i.succ).prod * (List.ofFn fun i => g i.succ).prod) := by
            rw [hP.eq]; noncomm_ring
        _ = 1 := by rw [h1, ih, one_mul]
end Formalism.FourierDecayAlt.R.PInv
