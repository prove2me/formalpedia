-- Prove2me | solution 1 for FongoSync.length_filter_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:20.6198+00:00
-- url     : https://prove2.me/submissions/1a8e8a08-9fc1-4fde-bb61-3473f6ccf3d9

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_length_filter_mono
import Theorems.Thm_FongoSync_Connected_nil


set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution {l : List Gid} {p q : Gid → Bool} (hpq : ∀ x ∈ l, p x → q x)
    (hx : ∃ x ∈ l, q x ∧ ¬ p x) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := hx; cases hx
  | cons a t ih =>
    have hpq' : ∀ x ∈ t, p x → q x := fun x hx => hpq x (.tail _ hx)
    have hle := length_filter_mono hpq'
    obtain ⟨x, hxl, hqx, hpx⟩ := hx
    rcases List.mem_cons.mp hxl with rfl | hxt
    · simp only [List.filter_cons, hqx, Bool.not_eq_true] at hpx ⊢
      simp only [hpx]
      simp; omega
    · have := ih hpq' ⟨x, hxt, hqx, hpx⟩
      have ha := hpq a (.head _)
      cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega
end FongoSync
