-- Prove2me | solution 1 for FiniteMagmaE677.no_left_period_four_of_fixer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:58:08.948102+00:00
-- url     : https://prove2.me/submissions/629e4b71-f695-4693-b1aa-fc14aa1b20da

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

namespace Magma677Work

open FiniteMagmaE677

universe u
variable {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op)
include h

theorem left_injective (a : α) : Function.Injective (op a) := by
  apply (Finite.injective_iff_surjective (f := op a)).2
  intro b
  exact ⟨op b (op (op a b) a), (h b a).symm⟩

theorem backwards (a b : α) : a = op (op b a) (op (op b (op b a)) b) := by
  apply left_injective op h b
  exact h (op b a) b

theorem fixer_determined (a b : α) (hf : op b a = a) :
    b = op (op a a) a := by
  have hab : op a (op a b) = a := by
    apply left_injective op h b
    simpa only [hf] using (h a b).symm
  apply left_injective op h a
  apply left_injective op h a
  exact hab.trans (h a a)

theorem second_successor_fixer (a : α)
    (hf : op (op a (op a a)) a = a) : op a (op a a) = a := by
  have hs : op (op a a) a = a := by
    apply left_injective op h a
    simpa only [hf] using (h (op a a) a).symm
  exact (fixer_determined op h a (op a (op a a)) hf).trans hs

theorem no_four_cycle_with_fixer (a : α)
    (hfour : op a (op a (op a (op a a))) = a)
    (hf : HasFixerAt op a) : op a (op a a) = a := by
  obtain ⟨w, hw⟩ := hf
  have hw' := fixer_determined op h a w hw
  have hcan : op (op a a) a = op a (op a a) := by
    apply left_injective op h a
    apply left_injective op h a
    exact (h a a).symm.trans hfour.symm
  apply second_successor_fixer op h a
  rw [← hcan, ← hw']
  exact hw

theorem no_two_cycle (a : α) (hper : op a (op a a) = a) : op a a = a := by
  have hr : op (op a a) a = a := by
    apply left_injective op h a
    apply left_injective op h a
    exact (h a a).symm.trans hper.symm
  exact (fixer_determined op h a (op a a) hr).trans hr

theorem four_cycle_fixer_idempotent (a : α)
    (hfour : op a (op a (op a (op a a))) = a)
    (hf : HasFixerAt op a) : op a a = a := by
  exact no_two_cycle op h a (no_four_cycle_with_fixer op h a hfour hf)

theorem third_successor_fixer (a b c d : α)
    (hab : op a a = b) (hac : op a b = c) (had : op a c = d)
    (hf : op d a = a) : op a a = a := by
  have hca : op c a = b := by
    apply left_injective op h a
    simpa only [had, hf, hac] using (h c a).symm
  have hba : op b a = d := by
    simpa only [hab] using (fixer_determined op h a d hf).symm
  have hbb : op b b = a := by
    simpa only [hab, hac, hca] using (backwards op h a a).symm
  have hdb : op d b = a := by
    apply left_injective op h a
    simpa only [hbb, hba, hab] using (backwards op h b b).symm
  exact hab.trans (left_injective op h d (hdb.trans hf.symm))

theorem five_cycle_fixer_idempotent (a : α)
    (hfive : op a (op a (op a (op a (op a a)))) = a)
    (hf : HasFixerAt op a) : op a a = a := by
  obtain ⟨w, hw⟩ := hf
  have hw' := fixer_determined op h a w hw
  have hcan : op (op a a) a = op a (op a (op a a)) := by
    apply left_injective op h a
    apply left_injective op h a
    exact (h a a).symm.trans hfive.symm
  apply third_successor_fixer op h a (op a a) (op a (op a a))
    (op a (op a (op a a))) rfl rfl rfl
  rw [← hcan, ← hw']
  exact hw

end Magma677Work


universe u

theorem solution {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (x : α)
    (hper : op x (op x (op x (op x (x)))) = x)
    (hfix : FiniteMagmaE677.HasFixerAt op x) : op x x = x := by
  exact Magma677Work.four_cycle_fixer_idempotent op h x hper hfix

#print axioms solution
