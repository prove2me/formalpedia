-- Prove2me | solution 1 for FiniteMagmaE677.period_four_r_second_step_seed_structure
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:06:49.552949+00:00
-- url     : https://prove2.me/submissions/e0c6ffe6-48d2-48fc-8477-b56e28f828d4

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_FiniteMagmaE677_d4_first_return
import Theorems.Thm_FiniteMagmaE677_no_left_period_three
import Theorems.Thm_FiniteMagmaE677_no_left_period_four_of_fixer
import Theorems.Thm_FiniteMagmaE677_no_left_period_five_of_fixer


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


namespace Magma677Work

open FiniteMagmaE677 FiniteMagmaE677.FirstReturn

universe u
variable {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op)
include h

theorem base_right (x c1 c2 c3 : α)
    (packet : D4Distinguished op x c1 c2 c3) : op c1 x = c2 := by
  apply left_injective op h x
  apply left_injective op h x
  simpa only [packet.orbit_c1, packet.orbit_c3, packet.orbit_closes] using (h x x).symm

theorem packet_no_fixer (x c1 c2 c3 : α)
    (packet : D4Distinguished op x c1 c2 c3) : ¬ HasFixerAt op x := by
  rintro ⟨y, hy⟩
  have he := fixer_determined op h x y hy
  rw [packet.orbit_c1, base_right op h x c1 c2 c3 packet] at he
  exact packet.q_ne_x (he ▸ hy)

theorem fixed_seed_data (x c1 c2 c3 : α)
    (packet : D4Distinguished op x c1 c2 c3)
    (q_to_r : op x (op c2 x) = op c1 c2) :
    op (op c2 x) (op x (op c2 x)) = x ∧
    op (op (op c2 x) x) (op c2 x) = op c2 x ∧
    op (op c2 x) (op c2 x) ≠ op c2 x := by
  let q := op c2 x
  have hqr : op q (op x q) = x := by
    simpa only [q, packet.q_packet_return, q_to_r] using (backwards op h x c2).symm
  have hf : op (op q x) q = q := by
    apply left_injective op h x
    apply left_injective op h q
    exact (h x q).symm.trans hqr.symm
  refine ⟨hqr, hf, ?_⟩
  intro hidem
  change op q q = q at hidem
  have hh : op q x = q := by
    simpa only [hidem] using fixer_determined op h q (op q x) hf
  have hxq : x = q := left_injective op h q (hh.trans hidem.symm)
  exact packet.q_ne_x hxq.symm

end Magma677Work


namespace Magma677Work

open FiniteMagmaE677 FiniteMagmaE677.FirstReturn

universe u
variable {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op)
include h

theorem fixer_period_at_least_six (x : α) (hfix : HasFixerAt op x)
    (hne : op x x ≠ x) : 6 ≤ Function.minimalPeriod (op x) x := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts
    ((left_injective op h x).mem_periodicPts x)
  have hr := Function.isPeriodicPt_minimalPeriod (op x) x
  change (op x)^[Function.minimalPeriod (op x) x] x = x at hr
  generalize hd : Function.minimalPeriod (op x) x = d at hp hr ⊢
  by_contra hlt
  have hc : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  apply hne
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hr
  · exact no_two_cycle op h x
      (by simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hr)
  · exact FiniteMagmaE677.no_left_period_three op h x
      (by simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hr)
  · exact FiniteMagmaE677.no_left_period_four_of_fixer op h x
      (by simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hr) hfix
  · exact FiniteMagmaE677.no_left_period_five_of_fixer op h x
      (by simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hr) hfix

theorem fixed_seed_period_bound (x c1 c2 c3 : α)
    (packet : D4Distinguished op x c1 c2 c3)
    (q_to_r : op x (op c2 x) = op c1 c2) :
    6 ≤ Function.minimalPeriod (op (op c2 x)) (op c2 x) := by
  obtain ⟨_, hf, hn⟩ := fixed_seed_data op h x c1 c2 c3 packet q_to_r
  exact fixer_period_at_least_six op h (op c2 x) ⟨op (op c2 x) x, hf⟩ hn

end Magma677Work

universe u

theorem solution {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (x c1 c2 c3 : α)
    (packet : FiniteMagmaE677.FirstReturn.D4Distinguished op x c1 c2 c3)
    (q_to_r : op x (op c2 x) = op c1 c2) :
    op (op (op c2 x) x) (op c2 x) = op c2 x ∧
    op (op c2 x) (op c2 x) ≠ op c2 x ∧
    6 ≤ Function.minimalPeriod (op (op c2 x)) (op c2 x) := by
  obtain ⟨_, hf, hn⟩ := Magma677Work.fixed_seed_data op h x c1 c2 c3 packet q_to_r
  exact ⟨hf, hn, Magma677Work.fixed_seed_period_bound op h x c1 c2 c3 packet q_to_r⟩
