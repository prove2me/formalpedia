-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.copy_gadget_correct
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T07:34:27.146125+00:00
-- url     : https://prove2.me/submissions/63a9338d-b2c3-4a1b-bdca-2f735bf6da41

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools
import Theorems.Thm_CorrelatedAuctionComplexity_Main_binary_deviation_inequalities
import Theorems.Thm_CorrelatedAuctionComplexity_Main_singleton_payoff_difference
import Theorems.Thm_CorrelatedAuctionComplexity_Main_anchored_payoff_difference
import Theorems.Thm_CorrelatedAuctionComplexity_Main_outside_perturbation_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open CorrelatedAuctionComplexity.Main

namespace CorrelatedAuctionComplexity.Main

private lemma delta_filter_incident {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (p : N → ℝ) (R : Finset (Fin H.edges.length)) (i : N) :
    H.delta p R i = H.delta p (R.filter (fun e => i ∈ (H.edge e).participants)) i := by
  classical
  symm
  unfold HDFPA.delta
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro e heR hef
  have hi : i ∉ (H.edge e).participants := by
    simpa only [Finset.mem_filter, heR, true_and, not_not] using hef
  simp [HDFPA.binaryEdgePure, expectation, singlePayoff, hi]

private lemma totalDelta_split {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (p : N → ℝ) (R : Finset (Fin H.edges.length)) (i : N) :
    H.totalDelta p i = H.delta p R i + H.delta p (Finset.univ \ R) i := by
  classical
  unfold HDFPA.totalDelta HDFPA.delta
  rw [← Finset.sum_sdiff (Finset.subset_univ R)]
  ring

private lemma incidentWeight_split {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (R : Finset (Fin H.edges.length)) (i : N) :
    H.incidentWeight i =
      (∑ e ∈ R, if i ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) +
      ∑ e ∈ Finset.univ \ R,
        if i ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0 := by
  classical
  unfold HDFPA.incidentWeight
  rw [← Finset.sum_sdiff (Finset.subset_univ R)]
  ring

private lemma copy_bookkeeping {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (y x h : N) (z : Fin 3 → N) (hnod : (y :: x :: h :: List.ofFn z).Nodup)
    (hvx : H.value x = 2) (Λ : ℝ) (hΛ : 0 < Λ)
    (ids : Fin 7 → Fin H.edges.length) (hocc : Occurs H (copyGadget y x h z) ids Λ)
    (hout : (∑ e ∈ Finset.univ \ gadgetEdges H (copyGadget y x h z) ids,
      if x ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) ≤ Λ/2)
    (p : N → ℝ) (hp : H.LegalBinary p) :
    H.incidentWeight h = 72*Λ ∧ H.incidentWeight x ≤ 30*Λ ∧
      |H.delta p (Finset.univ \ gadgetEdges H (copyGadget y x h z) ids) x| ≤ Λ/2 ∧
      H.delta p (Finset.univ \ gadgetEdges H (copyGadget y x h z) ids) h = 0 := by
  classical
  have hydis : ∀ a ∈ x :: h :: List.ofFn z, y ≠ a := (List.pairwise_cons.mp hnod).1
  have hxnod := (List.pairwise_cons.mp hnod).2
  have hxdis : ∀ a ∈ h :: List.ofFn z, x ≠ a := (List.pairwise_cons.mp hxnod).1
  have hyx : y ≠ x := hydis x (by simp)
  have hyh : y ≠ h := hydis h (by simp)
  have hxh : x ≠ h := hxdis h (by simp)
  have hxz (j : Fin 3) : x ≠ z j := hxdis (z j) (by fin_cases j <;> simp)
  let R := gadgetEdges H (copyGadget y x h z) ids
  have he (j : Fin 7) := (hocc.2.1 j).1
  have hw (j : Fin 7) := (hocc.2.1 j).2
  have hR (i : N) :
      (∑ e ∈ R, if i ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) =
      ∑ j : Fin 7, if i ∈ (H.edge (ids j)).participants then ((H.edge (ids j)).weight : ℝ) else 0 := by
    dsimp [R, gadgetEdges]
    rw [Finset.sum_image (fun a _ b _ hh => hocc.1 hh)]
    rfl
  have hhnot (e : Fin H.edges.length) (heR : e ∉ R) : h ∉ (H.edge e).participants := by
    apply hocc.2.2 e
    · rintro ⟨j, rfl⟩
      apply heR
      change ids j ∈ Finset.univ.image ids
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · simp [copyGadget]
  have houtzero : (∑ e ∈ Finset.univ \ R,
      if h ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e he'
    have heR : e ∉ R := (Finset.mem_sdiff.mp he').2
    simp [hhnot e heR]
  have hweightR (i : N) :
      (∑ e ∈ R, if i ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) =
      ∑ j : Fin 7, if i ∈ (copyGadget y x h z).auctions[j].participants then
        (((copyGadget y x h z).auctions[j].weight : ℚ) : ℝ) * Λ else 0 := by
    rw [hR]
    apply Finset.sum_congr rfl
    intro j hj
    rw [he, hw]
    rfl
  have hweightRh : (∑ e ∈ R,
      if h ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) = 72*Λ := by
    rw [hweightR, Fin.sum_univ_seven]
    norm_num [copyGadget, hyh, hyh.symm, hxh, hxh.symm]
    ring
  have hweightRx : (∑ e ∈ R,
      if x ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) = 29*Λ := by
    rw [hweightR, Fin.sum_univ_seven]
    norm_num [copyGadget, hyx, hyx.symm, hxh, hxh.symm, hxz]
    ring
  have hwh : H.incidentWeight h = 72*Λ := by
    rw [incidentWeight_split H R h, hweightRh, houtzero, add_zero]
  have hwx : H.incidentWeight x ≤ 30*Λ := by
    rw [incidentWeight_split H R x, hweightRx]
    change 29*Λ + _ ≤ 30*Λ
    have hout' : (∑ e ∈ Finset.univ \ R,
      if x ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) ≤ Λ/2 := hout
    linarith
  let S := (Finset.univ \ R).filter (fun e => x ∈ (H.edge e).participants)
  have hS : ∀ e ∈ S, x ∈ (H.edge e).participants := by
    intro e heS
    exact (Finset.mem_filter.mp heS).2
  have hb := outside_perturbation_bound H hH hB x hvx p hp S hS
  have hdelta : H.delta p (Finset.univ \ R) x = H.delta p S x :=
    delta_filter_incident H p (Finset.univ \ R) x
  have hweights : (∑ e ∈ S, ((H.edge e).weight : ℝ)) =
      ∑ e ∈ Finset.univ \ R,
        if x ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0 := by
    dsimp [S]
    rw [Finset.sum_filter]
  rw [← hdelta, hweights] at hb
  have hb' : |H.delta p (Finset.univ \ R) x| ≤ Λ/2 := hb.trans hout
  have hdeltah : H.delta p (Finset.univ \ R) h = 0 := by
    unfold HDFPA.delta
    apply Finset.sum_eq_zero
    intro e he'
    have hi := hhnot e (Finset.mem_sdiff.mp he').2
    simp [HDFPA.binaryEdgePure, expectation, singlePayoff, hi]
  exact ⟨hwh, hwx, hb', hdeltah⟩

private lemma delta_singleton_eq_zero {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (p : N → ℝ) (e : Fin H.edges.length) (i : N)
    (hi : i ∉ (H.edge e).participants) : H.delta p {e} i = 0 := by
  unfold HDFPA.delta
  simp [HDFPA.binaryEdgePure, expectation, singlePayoff, hi]

private lemma copy_delta_identities {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (y x h : N) (z : Fin 3 → N) (hroles : CopyRoles H y x h z)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (ids : Fin 7 → Fin H.edges.length)
    (hocc : Occurs H (copyGadget y x h z) ids Λ)
    (p : N → ℝ) (hp : H.LegalBinary p) :
    H.delta p (gadgetEdges H (copyGadget y x h z) ids) y = 0 ∧
    H.delta p (gadgetEdges H (copyGadget y x h z) ids) x = 2*Λ*(p h - 1/2) ∧
    H.delta p (gadgetEdges H (copyGadget y x h z) ids) h = 2*Λ*(p y - p x) := by
  classical
  rcases hroles with ⟨hnod, hvy, hvx, hvh, hvz⟩
  have hydis : ∀ a ∈ x :: h :: List.ofFn z, y ≠ a := (List.pairwise_cons.mp hnod).1
  have hxnod := (List.pairwise_cons.mp hnod).2
  have hxdis : ∀ a ∈ h :: List.ofFn z, x ≠ a := (List.pairwise_cons.mp hxnod).1
  have hhnod := (List.pairwise_cons.mp hxnod).2
  have hhdis : ∀ a ∈ List.ofFn z, h ≠ a := (List.pairwise_cons.mp hhnod).1
  have hyx : y ≠ x := hydis x (by simp)
  have hyh : y ≠ h := hydis h (by simp)
  have hxh : x ≠ h := hxdis h (by simp)
  have hyz (j : Fin 3) : y ≠ z j := hydis (z j) (by fin_cases j <;> simp)
  have hxz (j : Fin 3) : x ≠ z j := hxdis (z j) (by fin_cases j <;> simp)
  have hhz (j : Fin 3) : h ≠ z j := hhdis (z j) (by fin_cases j <;> simp)
  have hznod : (List.ofFn z).Nodup := (List.pairwise_cons.mp hhnod).2
  have hzy (j : Fin 3) : z j ≠ y := (hyz j).symm
  have hzx (j : Fin 3) : z j ≠ x := (hxz j).symm
  have hzh (j : Fin 3) : z j ≠ h := (hhz j).symm
  have hz12 : z 1 ≠ z 2 := by
    intro hh
    have hi := List.nodup_ofFn.mp hznod
    have heq : (1 : Fin 3) = 2 := hi hh
    have hv := congrArg Fin.val heq
    norm_num at hv
  let R := gadgetEdges H (copyGadget y x h z) ids
  have hsum (i : N) : H.delta p R i =
      ∑ j : Fin 7, H.delta p {ids j} i := by
    dsimp [R, gadgetEdges]
    unfold HDFPA.delta
    rw [Finset.sum_image (fun a _ b _ hh => hocc.1 hh)]
    apply Finset.sum_congr rfl
    intro j hj
    simp [HDFPA.delta]
  have he (j : Fin 7) := (hocc.2.1 j).1
  have hw (j : Fin 7) := (hocc.2.1 j).2
  have hw0' : ((H.edge (ids (0 : Fin 7))).weight : ℝ) = 4*Λ := by
    calc
      ((H.edge (ids (0 : Fin 7))).weight : ℝ) =
          (((copyGadget y x h z).auctions[(0 : Fin 7)].weight : ℚ) : ℝ)*Λ := hw 0
      _ = 4*Λ := by norm_num [copyGadget]
  have hw1' : ((H.edge (ids (1 : Fin 7))).weight : ℝ) = 12*Λ := by
    calc
      ((H.edge (ids (1 : Fin 7))).weight : ℝ) =
          (((copyGadget y x h z).auctions[(1 : Fin 7)].weight : ℚ) : ℝ)*Λ := hw 1
      _ = 12*Λ := by norm_num [copyGadget]
  have hw2' : ((H.edge (ids (2 : Fin 7))).weight : ℝ) = 24*Λ := by
    calc
      ((H.edge (ids (2 : Fin 7))).weight : ℝ) =
          (((copyGadget y x h z).auctions[(2 : Fin 7)].weight : ℚ) : ℝ)*Λ := hw 2
      _ = 24*Λ := by norm_num [copyGadget]
  have hw3' : ((H.edge (ids (3 : Fin 7))).weight : ℝ) = 4*Λ := by
    calc
      ((H.edge (ids (3 : Fin 7))).weight : ℝ) =
          (((copyGadget y x h z).auctions[(3 : Fin 7)].weight : ℚ) : ℝ)*Λ := hw 3
      _ = 4*Λ := by norm_num [copyGadget]
  have hw4' : ((H.edge (ids (4 : Fin 7))).weight : ℝ) = 16*Λ := by
    calc
      ((H.edge (ids (4 : Fin 7))).weight : ℝ) =
          (((copyGadget y x h z).auctions[(4 : Fin 7)].weight : ℚ) : ℝ)*Λ := hw 4
      _ = 16*Λ := by norm_num [copyGadget]
  have hw5' : ((H.edge (ids (5 : Fin 7))).weight : ℝ) = 36*Λ := by
    calc
      ((H.edge (ids (5 : Fin 7))).weight : ℝ) =
          (((copyGadget y x h z).auctions[(5 : Fin 7)].weight : ℚ) : ℝ)*Λ := hw 5
      _ = 36*Λ := by norm_num [copyGadget]
  have hw6' : ((H.edge (ids (6 : Fin 7))).weight : ℝ) = 9*Λ := by
    calc
      ((H.edge (ids (6 : Fin 7))).weight : ℝ) =
          (((copyGadget y x h z).auctions[(6 : Fin 7)].weight : ℚ) : ℝ)*Λ := hw 6
      _ = 9*Λ := by norm_num [copyGadget]
  have hy0 : H.delta p {ids 0} y = (4*Λ)*(p h/2 + 1) := by
    have hd := anchored_payoff_difference H hH hB 0 y h hyh (fun j => Fin.elim0 j)
      (by simp) (fun j => Fin.elim0 j) (by simp [hvy]) (by simp [hvh])
      (fun j => Fin.elim0 j) (ids 0) (by simpa [copyGadget] using he 0) p hp
    rw [hd, hw0', hvy]
    norm_num
    ring_nf <;> simp
  have hy1 : H.delta p {ids 1} y = (12*Λ)*(5/3 - p h/6) := by
    let z1 : Fin 1 → N := fun _ => z 0
    have hd := anchored_payoff_difference H hH hB 1 y h hyh z1
      (by simp [z1]) (fun j => by fin_cases j; exact ⟨hzy 0, hzh 0⟩)
      (by simp [hvy]) (by simp [hvh]) (fun j => by fin_cases j; exact hvz 0)
      (ids 1) (by simpa [copyGadget, z1] using he 1) p hp
    rw [hd, hw1', hvy]
    norm_num
    ring_nf <;> simp
  have hy2 : H.delta p {ids 2} y = -(24*Λ) := by
    have hd := singleton_payoff_difference H hH hB y (by simp [hvy])
      (ids 2) (by simpa [copyGadget] using he 2) p hp
    rw [hd, hw2']
  have hx3 : H.delta p {ids 3} x = (4*Λ)*(p h/2) := by
    have hd := anchored_payoff_difference H hH hB 0 x h hxh (fun j => Fin.elim0 j)
      (by simp) (fun j => Fin.elim0 j) (by simp [hvx]) (by simp [hvh])
      (fun j => Fin.elim0 j) (ids 3) (by simpa [copyGadget] using he 3) p hp
    rw [hd, hw3', hvx]
    norm_num
    ring_nf <;> simp
  have hx4 : H.delta p {ids 4} x = 8*Λ := by
    let z2 : Fin 2 → N := fun j => if j = 0 then z 1 else z 2
    have hz2nod : (List.ofFn z2).Nodup := by
      simp [z2, List.ofFn_succ, hzx, hzh, hz12]
    have hd := anchored_payoff_difference H hH hB 2 x h hxh z2 hz2nod
      (fun j => by fin_cases j <;> simp [z2, hzx, hzh])
      (by simp [hvx]) (by simp [hvh])
      (fun j => by fin_cases j <;> simp [z2, hvz])
      (ids 4) (by
        rw [he 4]
        ext a
        simp [copyGadget, z2, or_comm, or_left_comm, or_assoc, eq_comm]) p hp
    rw [hd, hw4', hvx]
    norm_num
    ring_nf <;> simp
  have hx6 : H.delta p {ids 6} x = -(9*Λ) := by
    have hd := singleton_payoff_difference H hH hB x (by simp [hvx])
      (ids 6) (by simpa [copyGadget] using he 6) p hp
    rw [hd, hw6']
  have hh0 : H.delta p {ids 0} h = (4*Λ)*(p y/2 + 1/2) := by
    have hd := anchored_payoff_difference H hH hB 0 h y hyh.symm (fun j => Fin.elim0 j)
      (by simp) (fun j => Fin.elim0 j) (by simp [hvh]) (by simp [hvy])
      (fun j => Fin.elim0 j) (ids 0) (by
        rw [he 0]
        ext a
        simp [copyGadget, or_comm, or_left_comm, or_assoc, eq_comm]) p hp
    rw [hd, hw0', hvh]
    norm_num
    ring_nf <;> simp
  have hh1 : H.delta p {ids 1} h = 12*Λ := by
    let z1 : Fin 1 → N := fun _ => z 0
    have hd := anchored_payoff_difference H hH hB 1 h y hyh.symm z1
      (by simp [z1]) (fun j => by fin_cases j; exact ⟨hzh 0, hzy 0⟩)
      (by simp [hvh]) (by simp [hvy]) (fun j => by fin_cases j; exact hvz 0)
      (ids 1) (by
        rw [he 1]
        ext a
        simp [copyGadget, z1, or_comm, or_left_comm, or_assoc, eq_comm]) p hp
    rw [hd, hw1', hvh]
    norm_num
  have hh3 : H.delta p {ids 3} h = (4*Λ)*(p x/2 + 1/2) := by
    have hd := anchored_payoff_difference H hH hB 0 h x hxh.symm (fun j => Fin.elim0 j)
      (by simp) (fun j => Fin.elim0 j) (by simp [hvh]) (by simp [hvx])
      (fun j => Fin.elim0 j) (ids 3) (by
        rw [he 3]
        ext a
        simp [copyGadget, or_comm, or_left_comm, or_assoc, eq_comm]) p hp
    rw [hd, hw3', hvh]
    norm_num
    ring_nf <;> simp
  have hh4 : H.delta p {ids 4} h = (16*Λ)*(5/4 - p x/4) := by
    let z2 : Fin 2 → N := fun j => if j = 0 then z 1 else z 2
    have hz2nod : (List.ofFn z2).Nodup := by
      simp [z2, List.ofFn_succ, hzx, hzh, hz12]
    have hd := anchored_payoff_difference H hH hB 2 h x hxh.symm z2 hz2nod
      (fun j => by fin_cases j <;> simp [z2, hzh, hzx])
      (by simp [hvh]) (by simp [hvx])
      (fun j => by fin_cases j <;> simp [z2, hvz])
      (ids 4) (by
        rw [he 4]
        ext a
        simp [copyGadget, z2, or_comm, or_left_comm, or_assoc, eq_comm]) p hp
    rw [hd, hw4', hvh]
    norm_num
    ring_nf <;> simp
  have hh5 : H.delta p {ids 5} h = -(36*Λ) := by
    have hd := singleton_payoff_difference H hH hB h (by simp [hvh])
      (ids 5) (by simpa [copyGadget] using he 5) p hp
    rw [hd, hw5']
  constructor
  · rw [hsum]
    rw [Fin.sum_univ_seven]
    rw [hy0, hy1, hy2]
    have hzero3 : H.delta p {ids 3} y = 0 := by
      apply delta_singleton_eq_zero
      rw [he 3]
      simp [copyGadget, hyx, hyh]
    have hzero4 : H.delta p {ids 4} y = 0 := by
      apply delta_singleton_eq_zero
      rw [he 4]
      simp [copyGadget, hyx, hyh, hyz]
    have hzero5 : H.delta p {ids 5} y = 0 := by
      apply delta_singleton_eq_zero
      rw [he 5]
      simp [copyGadget, hyh]
    have hzero6 : H.delta p {ids 6} y = 0 := by
      apply delta_singleton_eq_zero
      rw [he 6]
      simp [copyGadget, hyx]
    rw [hzero3, hzero4, hzero5, hzero6]
    ring
  constructor
  · rw [hsum]
    rw [Fin.sum_univ_seven]
    have hzero0 : H.delta p {ids 0} x = 0 := by
      apply delta_singleton_eq_zero
      rw [he 0]
      simp [copyGadget, hyx.symm, hxh]
    have hzero1 : H.delta p {ids 1} x = 0 := by
      apply delta_singleton_eq_zero
      rw [he 1]
      simp [copyGadget, hyx.symm, hxh, hxz]
    have hzero2 : H.delta p {ids 2} x = 0 := by
      apply delta_singleton_eq_zero
      rw [he 2]
      simp [copyGadget, hyx.symm]
    have hzero5 : H.delta p {ids 5} x = 0 := by
      apply delta_singleton_eq_zero
      rw [he 5]
      simp [copyGadget, hxh]
    rw [hzero0, hzero1, hzero2, hx3, hx4, hzero5, hx6]
    ring
  · rw [hsum]
    rw [Fin.sum_univ_seven]
    have hzero2 : H.delta p {ids 2} h = 0 := by
      apply delta_singleton_eq_zero
      rw [he 2]
      simp [copyGadget, hyh.symm]
    have hzero6 : H.delta p {ids 6} h = 0 := by
      apply delta_singleton_eq_zero
      rw [he 6]
      simp [copyGadget, hxh.symm]
    rw [hh0, hh1, hzero2, hh3, hh4, hh5, hzero6]
    ring

private lemma copy_ne_bound {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (y x h : N) (R : Finset (Fin H.edges.length)) (Λ : ℝ) (hΛ : 0 < Λ)
    (p : N → ℝ) (hp : H.LegalBinary p) (η : ℝ) (hη : 0 ≤ η)
    (hne : H.IsNE η (H.binaryProfile p))
    (hRx : H.delta p R x = 2*Λ*(p h - 1/2))
    (hRh : H.delta p R h = 2*Λ*(p y - p x))
    (hWh : H.incidentWeight h = 72*Λ) (hWx : H.incidentWeight x ≤ 30*Λ)
    (houtx : |H.delta p (Finset.univ \ R) x| ≤ Λ/2)
    (houth : H.delta p (Finset.univ \ R) h = 0) :
    |p x-p y| ≤ 300*η := by
  classical
  have hdev := binary_deviation_inequalities H hH hB η hη p hne
  have hxsplit := totalDelta_split H p R x
  have hhsplit := totalDelta_split H p R h
  have houtbounds := abs_le.mp houtx
  have hxweight : η*H.incidentWeight x ≤ η*(30*Λ) :=
    mul_le_mul_of_nonneg_left hWx hη
  apply abs_le.mpr
  constructor
  · by_contra! hbad
    have hδ : 300*η < p y-p x := by linarith
    have hδpos : 0 < p y-p x := by nlinarith
    have hhpos : 0 < H.totalDelta p h := by
      rw [hhsplit, hRh, houth, add_zero]
      nlinarith [mul_pos hΛ hδpos]
    have hjin := (hdev h).1 hhpos
    rw [hhsplit, hRh, houth, add_zero, hWh] at hjin
    have hprod : (1-p h)*(p y-p x) ≤ 36*η := by
      nlinarith only [hjin, hΛ]
    have hph : 7/8 < p h := by
      by_contra! hle
      have hcoef : (1/8 : ℝ) ≤ 1-p h := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoef hδpos.le
      nlinarith only [hprod, hmul, hδ, hη]
    have hΔlower : Λ/4 ≤ H.totalDelta p x := by
      rw [hxsplit, hRx]
      nlinarith [houtbounds.1, hph, hΛ]
    have hxpos : 0 < H.totalDelta p x := lt_of_lt_of_le (by positivity) hΔlower
    have hxin := (hdev x).1 hxpos
    have hone : 0 ≤ 1-p x := by linarith [(hp.1 x).2]
    have hmul := mul_le_mul_of_nonneg_left hΔlower hone
    have hchain : (1-p x)*(Λ/4) ≤ η*(30*Λ) :=
      hmul.trans (hxin.trans hxweight)
    have hxbound : 1-p x ≤ 120*η := by
      nlinarith only [hchain, hΛ]
    linarith [(hp.1 y).2]
  · by_contra! hbad
    have hδ : 300*η < p x-p y := by linarith
    have hδpos : 0 < p x-p y := by nlinarith
    have hhneg : H.totalDelta p h < 0 := by
      rw [hhsplit, hRh, houth, add_zero]
      nlinarith [mul_pos hΛ hδpos]
    have hjin := (hdev h).2 hhneg
    rw [hhsplit, hRh, houth, add_zero, hWh] at hjin
    have hprod : p h*(p x-p y) ≤ 36*η := by
      nlinarith only [hjin, hΛ]
    have hph : p h < 1/8 := by
      by_contra! hge
      have hmul := mul_le_mul_of_nonneg_right hge hδpos.le
      nlinarith only [hprod, hmul, hδ, hη]
    have hΔupper : H.totalDelta p x ≤ -(Λ/4) := by
      rw [hxsplit, hRx]
      nlinarith [houtbounds.2, hph, hΛ]
    have hxneg : H.totalDelta p x < 0 := lt_of_le_of_lt hΔupper (by nlinarith [hΛ])
    have hxin := (hdev x).2 hxneg
    have hmul := mul_le_mul_of_nonneg_left
      (show Λ/4 ≤ -H.totalDelta p x by linarith) (hp.1 x).1
    have hchain : p x*(Λ/4) ≤ η*(30*Λ) := by
      have hmul' : p x*(Λ/4) ≤ -(p x)*H.totalDelta p x := by
        nlinarith only [hmul]
      exact hmul'.trans (hxin.trans hxweight)
    have hxbound : p x ≤ 120*η := by
      nlinarith only [hchain, hΛ]
    linarith [(hp.1 y).1]

end CorrelatedAuctionComplexity.Main

open CorrelatedAuctionComplexity.Main

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (y x h : N) (z : Fin 3 → N) (hroles : CopyRoles H y x h z)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (ids : Fin (copyGadget y x h z).auctions.length → Fin H.edges.length)
    (hocc : Occurs H (copyGadget y x h z) ids Λ)
    (hout : (∑ e ∈ Finset.univ \ gadgetEdges H (copyGadget y x h z) ids,
      if x ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) ≤ Λ/2)
    (p : N → ℝ) (hp : H.LegalBinary p) (η : ℝ) (hη : 0 ≤ η) :
    (H.IsNE η (H.binaryProfile p) → |p x - p y| ≤ 300*η) ∧
      H.delta p (gadgetEdges H (copyGadget y x h z) ids) y = 0 := by
  obtain ⟨hy, hx, hh⟩ := copy_delta_identities H hH hB y x h z hroles Λ hΛ ids hocc p hp
  refine ⟨?_, hy⟩
  intro hne
  obtain ⟨hWh, hWx, houtx, houth⟩ :=
    copy_bookkeeping H hH hB y x h z hroles.1 hroles.2.2.1 Λ hΛ ids hocc hout p hp
  exact copy_ne_bound H hH hB y x h (gadgetEdges H (copyGadget y x h z) ids)
    Λ hΛ p hp η hη hne hx hh hWh hWx houtx houth
