-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickExists.map_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:32.248577+00:00
-- url     : https://prove2.me/submissions/f551dba7-2d63-49fb-a99b-cc44b90fbe87

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists

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
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists
namespace Formalism.FrobeniusOrbits.ThickExists
theorem _root_.solution (B : ℕ) : ∀ {S : ℕ} (v : Fin S → ℕ), (∀ m, v m < B) → Behrend.map B v < B ^ S := by
  intro S
  induction S with
  | zero => intro v _; simp [Behrend.map_apply]
  | succ S ih =>
    intro v hv
    have h1 := ih (fun m => v m.succ) (fun m => hv _)
    have hsplit : Behrend.map B v = v 0 + B * Behrend.map B (fun m : Fin S => v m.succ) := by
      simp only [Behrend.map_apply]
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      congr 1
      · simp
      · refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Fin.val_succ, pow_succ]
        ring
    rw [hsplit, pow_succ]
    have h2 : B * (Behrend.map B (fun m : Fin S => v m.succ) + 1) ≤ B * B ^ S :=
      Nat.mul_le_mul_left B h1
    have h3 := hv 0
    nlinarith
end Formalism.FrobeniusOrbits.ThickExists
