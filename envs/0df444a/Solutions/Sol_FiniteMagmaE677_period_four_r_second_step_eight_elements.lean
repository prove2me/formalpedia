-- Prove2me | solution 1 for FiniteMagmaE677.period_four_r_second_step_eight_elements
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T08:22:06.506534+00:00
-- url     : https://prove2.me/submissions/33763e7c-74eb-4cca-9638-ead4db7f4589

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_FiniteMagmaE677_d4_first_return
import Theorems.Thm_FiniteMagmaE677_no_left_period_three
import Theorems.Thm_FiniteMagmaE677_no_left_period_four_of_fixer
import Theorems.Thm_FiniteMagmaE677_no_left_period_five_of_fixer
import Mathlib.Data.List.OfFn


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


namespace Magma677Work

open FiniteMagmaE677 FiniteMagmaE677.FirstReturn

universe u

private theorem six_chain_nodup {α : Type u} [Fintype α]
    (f : α → α) (hinj : Function.Injective f)
    (a b c d e g : α)
    (h0 : f a = b) (h1 : f b = c) (h2 : f c = d)
    (h3 : f d = e) (h4 : f e = g)
    (hper : 6 ≤ Function.minimalPeriod f e) :
    [a, b, c, d, e, g].Nodup := by
  have hret : (f^[4]) a = e := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      h0, h1, h2, h3]
  have hper' : 6 ≤ Function.minimalPeriod f a := by
    rw [← Function.minimalPeriod_apply_iterate (hinj.mem_periodicPts a) 4, hret]
    exact hper
  have hi : Function.Injective (fun i : Fin 6 => (f^[i.val]) a) := by
    intro i j he
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod
      (by change i.val < Function.minimalPeriod f a; omega)
      (by change j.val < Function.minimalPeriod f a; omega) he
  have hn := List.nodup_ofFn.mpr hi
  simpa [List.ofFn_succ, Function.iterate_succ_apply', h0, h1, h2, h3, h4] using hn

theorem fixed_seed_eight_elements {α : Type u} [Fintype α]
    (op : α → α → α) (h : E677 op) (x c1 c2 c3 : α)
    (packet : D4Distinguished op x c1 c2 c3)
    (start : RTaggedStart op x c1 c2 c3)
    (q_to_r : op x (op c2 x) = op c1 c2) :
    8 ≤ Fintype.card α := by
  let q := op c2 x
  let r := op c1 c2
  let w := op q x
  let p := op q w
  let v := op q q
  have cancel := left_injective op h
  have hbq : op c1 q = x := packet.q_packet_preimage
  have hcq : op c2 q = c1 := packet.q_packet_return
  have hdq : op c3 x = q := packet.q_collision.symm
  obtain ⟨hqr, hf, hnon⟩ := fixed_seed_data op h x c1 c2 c3 packet q_to_r
  change op q (op x q) = x at hqr
  rw [q_to_r] at hqr
  change op q r = x at hqr
  change op w q = q at hf
  have hqp : op q p = q := by
    apply cancel w
    simpa only [hf] using (h q w).symm
  have hw : w = op v q := fixer_determined op h q w hf
  have chain : [r, x, w, p, q, v].Nodup :=
    six_chain_nodup (op q) (cancel q) r x w p q v hqr rfl rfl hqp rfl
      (fixed_seed_period_bound op h x c1 c2 c3 packet q_to_r)
  have hwb : w ≠ c1 := by
    intro e
    have hxq : x = q := by simpa only [e, hbq] using hf
    exact packet.q_ne_x hxq.symm
  have hwc : w ≠ c2 := by
    intro e
    have hbq' : c1 = q := by simpa only [e, hcq] using hf
    exact packet.q_ne_c1 hbq'.symm
  have hwd : w ≠ c3 := by
    intro e
    have hdq : op c3 q = q := e ▸ hf
    have hdx : op c3 x = q := packet.q_collision.symm
    exact packet.q_ne_x (cancel c3 (hdq.trans hdx.symm))
  have hpc : p ≠ c2 := by
    intro e
    have hqc : op q c2 = q := e ▸ hqp
    have hxq : x = q := by
      simpa only [hbq, packet.orbit_c2, hqc] using (h q c1).symm
    exact packet.q_ne_x hxq.symm
  have hvb : v ≠ c1 := by
    intro e
    have hwx : w = x := by simpa only [e, hbq] using hw
    have : ¬ [r, x, x, p, q, v].Nodup := by simp
    exact this (hwx ▸ chain)
  have hvc : v ≠ c2 := by
    intro e
    exact hwb (by simpa only [e, hcq] using hw)
  have hrx : r ≠ x := start.r_ne_x
  have hrb : r ≠ c1 := start.r_ne_c1
  have hrc : r ≠ c2 := start.r_ne_c2
  have hrd : r ≠ c3 := start.r_ne_c3
  have hrq : r ≠ q := start.r_ne_q
  have hqx : q ≠ x := packet.q_ne_x
  have hqb : q ≠ c1 := packet.q_ne_c1
  have hqc : q ≠ c2 := packet.q_ne_c2
  have hqd : q ≠ c3 := packet.q_ne_c3
  have hxb := packet.x_ne_c1
  have hxc := packet.x_ne_c2
  have hxd := packet.x_ne_c3
  have hbc := packet.c1_ne_c2
  have hbd := packet.c1_ne_c3
  have hcd := packet.c2_ne_c3
  have chain' := chain
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    and_true, not_or, not_false_eq_true] at chain'
  rcases chain' with ⟨⟨_, hrw, hrp, _, hrv⟩, ⟨hxw, hxp, hxq, hxv⟩,
    ⟨hwp, hwq, hwv⟩, ⟨hpq, hpv⟩, hqv⟩
  have base : [c1, c2, c3, r, x, w, q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or, not_false_eq_true]
    exact ⟨⟨hbc, hbd, hrb.symm, hxb.symm, hwb.symm, hqb.symm⟩,
      ⟨hcd, hrc.symm, hxc.symm, hwc.symm, hqc.symm⟩,
      ⟨hrd.symm, hxd.symm, hwd.symm, hqd.symm⟩,
      ⟨hrx, hrw, hrq⟩, ⟨hxw, hxq⟩, hwq⟩
  by_cases hvd : v = c3
  · by_cases hpb : p = c1
    · have hqc_ne : op q c2 ≠ c2 := by
        intro e
        have hrq : r = q := by
          simpa only [hbq, packet.orbit_c2, e] using (h q c1).symm
        exact start.r_ne_q hrq
      have hqd_ne : op q v ≠ c2 := by
        intro e
        have hqdc : op q c3 = c2 := hvd ▸ e
        have hdd : op c3 c3 = x := by
          simpa only [hdq, hqdc, packet.orbit_c3] using (h x c3).symm
        have hdq' : op c3 q = c3 := by
          simpa only [hdd, packet.orbit_closes, hdq] using (h c3 c3).symm
        exact hwd (hw.trans (by simpa only [hvd] using hdq'))
      have images : [x, w, p, q, v, op q v].Nodup := by
        simpa only [List.map_cons, List.map_nil, hqr, hqp] using chain.map (cancel q)
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        and_true, not_or, not_false_eq_true] at images
      rcases images with ⟨⟨_, _, _, _, hxz⟩, ⟨_, _, _, hwz⟩,
        ⟨_, _, hpz⟩, ⟨_, hqz⟩, hvz⟩
      by_cases hvr : op q v = r
      · have extra : op q c2 ∉ [c1, c2, c3, r, x, w, q] := by
          have n0 : op q c2 ≠ x := fun e => hrc (cancel q (hqr.trans e.symm))
          have n1 : op q c2 ≠ w := fun e => hxc (cancel q e.symm)
          have n2 : op q c2 ≠ c1 := by
            intro e
            exact hwc (cancel q ((show op q w = p from rfl).trans (hpb.trans e.symm)))
          have n3 : op q c2 ≠ q := by
            intro e
            have : p = c2 := cancel q (hqp.trans e.symm)
            exact hpc this
          have n4 : op q c2 ≠ c3 := by
            intro e
            exact hqc (cancel q ((show op q q = v from rfl).trans (hvd.trans e.symm)))
          have n5 : op q c2 ≠ r := by
            intro e
            have : v = c2 := cancel q (hvr.trans e.symm)
            exact hvc this
          simpa only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]
            using And.intro n2 (And.intro hqc_ne (And.intro n4 (And.intro n5
              (And.intro n0 (And.intro n1 n3)))))
        exact (List.nodup_cons.mpr ⟨extra, base⟩).length_le_card
      · have extra : op q v ∉ [c1, c2, c3, r, x, w, q] := by
          simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]
          exact ⟨hpb ▸ (Ne.symm hpz), hqd_ne, hvd ▸ (Ne.symm hvz),
            hvr, Ne.symm hxz, Ne.symm hwz, Ne.symm hqz⟩
        exact (List.nodup_cons.mpr ⟨extra, base⟩).length_le_card
    · have extra : p ∉ [c1, c2, c3, r, x, w, q] := by
        simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]
        exact ⟨hpb, hpc, hvd ▸ hpv, Ne.symm hrp, Ne.symm hxp, Ne.symm hwp, hpq⟩
      have hn : (p :: [c1, c2, c3, r, x, w, q]).Nodup := List.nodup_cons.mpr ⟨extra, base⟩
      exact hn.length_le_card
  · have extra : v ∉ [c1, c2, c3, r, x, w, q] := by
      simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]
      exact ⟨hvb, hvc, hvd, Ne.symm hrv, Ne.symm hxv, Ne.symm hwv, Ne.symm hqv⟩
    have hn : (v :: [c1, c2, c3, r, x, w, q]).Nodup := List.nodup_cons.mpr ⟨extra, base⟩
    exact hn.length_le_card

end Magma677Work

universe u

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x c1 c2 c3 : α)
    (packet : FiniteMagmaE677.FirstReturn.D4Distinguished op x c1 c2 c3)
    (start : FiniteMagmaE677.FirstReturn.RTaggedStart op x c1 c2 c3)
    (q_to_r : op x (op c2 x) = op c1 c2) :
    8 ≤ Fintype.card α := by
  exact Magma677Work.fixed_seed_eight_elements op h x c1 c2 c3 packet start q_to_r
