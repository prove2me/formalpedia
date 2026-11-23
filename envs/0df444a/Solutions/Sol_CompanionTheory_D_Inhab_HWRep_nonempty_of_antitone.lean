-- Prove2me | solution 1 for CompanionTheory.D.Inhab.HWRep.nonempty_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:56.624242+00:00
-- url     : https://prove2.me/submissions/3f635762-9f26-4e0d-aded-b2f0bc58f5e9

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab
attribute [instance] HWRep.fin HWRep.dec
open CompanionTheory.D.Inhab.HWRep
variable {k : ℕ}
namespace CompanionTheory.D.Inhab.HWRep
theorem _root_.solution (ν : Fin k → ℤ) (hν : Antitone ν) : Nonempty (HWRep k ν) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ∀ a, m ≤ ν a := by
    obtain ⟨m, hm⟩ := (Set.finite_range ν).bddBelow
    exact ⟨m, fun a => hm ⟨a, rfl⟩⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ a, ν a ≤ m + N := by
    obtain ⟨M, hM⟩ := (Set.finite_range ν).bddAbove
    exact ⟨(M - m).toNat, fun a => by have := hM ⟨a, rfl⟩; omega⟩
  induction N generalizing ν with
  | zero =>
    have : ν = fun _ => m := funext fun a => le_antisymm (by simpa using hN a) (hm a)
    exact this ▸ ⟨detPow k m⟩
  | succ N ih =>
    let p : Fin k → Prop := fun a => m < ν a
    have hp : ∀ a b, a ≤ b → p b → p a := fun a b hab hb => lt_of_lt_of_le hb (hν hab)
    obtain ⟨R⟩ := ih (fun a => ν a - if p a then 1 else 0)
      (fun a b hab => by
        have h1 := hν hab; have h2 := hm b; have h3 := hm a
        simp only [p]; split_ifs <;> omega)
      (fun a => by have := hm a; simp only [p]; split_ifs <;> omega)
      (fun a => by have := hm a; have := hN a; simp only [p]; push_cast at *; split_ifs <;> omega)
    have e : ν = (fun a => ν a - if p a then 1 else 0) + fun a => if p a then 1 else 0 := by
      funext a; simp
    exact e ▸ ⟨R.tensor (wedge p hp)⟩
end CompanionTheory.D.Inhab.HWRep
