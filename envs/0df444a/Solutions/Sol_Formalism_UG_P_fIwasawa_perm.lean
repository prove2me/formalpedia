-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:36:48.257081+00:00
-- url     : https://prove2.me/submissions/b58e1ee6-a3af-4b16-b64c-0d2b70acacad

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (ρ a : Fin n) (hρ : ρ < Fin.rev ρ) (ha1 : ρ ≤ a) (ha2 : a ≤ Fin.rev ρ)
    (haa : a ≠ Fin.rev a) :
    ∃ π : Equiv.Perm (Fin n), π ρ = a ∧ (∀ i, π (Fin.rev i) = Fin.rev (π i)) ∧
      (∀ i, (i < ρ ∨ Fin.rev ρ < i) → π i = i) := by
  have hρn := ρ.isLt
  have han := a.isLt
  by_cases haρ : a = Fin.rev ρ
  · subst haρ
    refine ⟨Equiv.swap ρ (Fin.rev ρ), Equiv.swap_apply_left _ _, fun i => ?_, fun i hi => ?_⟩
    · have hin := i.isLt
      simp only [Equiv.swap_apply_def]
      split_ifs <;> ((try simp only [Fin.lt_def, Fin.le_def, Fin.val_rev, Fin.ext_iff,
    ne_eq, not_true_eq_false] at *) <;> omega)
    · have hin := i.isLt
      simp only [Equiv.swap_apply_def]
      split_ifs <;> ((try simp only [Fin.lt_def, Fin.le_def, Fin.val_rev, Fin.ext_iff,
    ne_eq, not_true_eq_false] at *) <;> omega)
  · refine ⟨Equiv.swap ρ a * Equiv.swap (Fin.rev ρ) (Fin.rev a), ?_, fun i => ?_, fun i hi => ?_⟩
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> ((try simp only [Fin.lt_def, Fin.le_def, Fin.val_rev, Fin.ext_iff,
    ne_eq, not_true_eq_false] at *) <;> omega)
    · have hin := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> ((try simp only [Fin.lt_def, Fin.le_def, Fin.val_rev, Fin.ext_iff,
    ne_eq, not_true_eq_false] at *) <;> omega)
    · have hin := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> ((try simp only [Fin.lt_def, Fin.le_def, Fin.val_rev, Fin.ext_iff,
    ne_eq, not_true_eq_false] at *) <;> omega)
end Formalism.UG.P
