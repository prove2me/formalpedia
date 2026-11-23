-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.singleton_payoff_difference
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:47:35.603169+00:00
-- url     : https://prove2.me/submissions/2a27a4b6-d4f1-45b7-a548-8b623b1a71c5

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

open scoped BigOperators
open CorrelatedAuctionComplexity.Main

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (x : N) (hx : H.value x ∈ ({2,3,4} : Finset ℚ))
    (e : Fin H.edges.length) (he : (H.edge e).participants = {x})
    (p : N → ℝ) (hp : H.LegalBinary p) :
    H.delta p {e} x = -((H.edge e).weight : ℝ) := by
  classical
  have hprofileProb (q : N → Bool → ℝ) (hq : ∀ j, IsLottery (q j)) :
      ∑ b : N → Bool, AGT.profileProb q b = 1 := by
    have hsum (j : N) : q j true + q j false = 1 := by
      simpa using (hq j).2
    have h := Finset.prod_univ_sum (fun _ : N => (Finset.univ : Finset Bool)) q
    rw [Fintype.piFinset_univ] at h
    simpa [AGT.profileProb, hsum] using h.symm
  have hbase (j : N) : IsLottery (fun a : Bool => if a then p j else 1 - p j) := by
    constructor
    · intro a
      cases a <;> simp <;> linarith [(hp.1 j).1, (hp.1 j).2]
    · simp
  have hdev (t : Bool) :
      ∀ j, IsLottery (deviation
        (fun (j : N) (a : Bool) => if a then p j else 1 - p j) x t j) := by
    intro j
    by_cases hjx : j = x
    · subst j
      cases t <;> constructor
      · intro a
        cases a <;> simp [deviation]
      · simp [deviation]
      · intro a
        cases a <;> simp [deviation] <;> linarith [(hp.1 x).1, (hp.1 x).2]
      · simp [deviation]
    · simpa [deviation, hjx] using hbase j
  have hsumDev (t : Bool) :
      ∑ b : N → Bool, AGT.profileProb (deviation
        (fun (j : N) (a : Bool) => if a then p j else 1 - p j) x t) b = 1 :=
    hprofileProb _ (hdev t)
  have hsingle (t : Bool) (b : N → Bool) (hb : b x = t) :
      (singlePayoff {x} H.value (fun j => if b j then 1 else 0) x : ℝ) =
        (H.value x : ℝ) - if t then 1 else 0 := by
    have h : singlePayoff {x} H.value (fun j => if b j then 1 else 0) x =
        H.value x - (if b x then (1 : ℚ) else 0) := by
      simp [singlePayoff, Finset.filter_singleton]
    rw [h]
    rw [hb]
    cases t <;> simp
  have hedge (t : Bool) :
      H.binaryEdgePure p e x t = ((H.edge e).weight : ℝ) *
        ((H.value x : ℝ) - if t then 1 else 0) := by
    unfold HDFPA.binaryEdgePure
    rw [he, expectation]
    calc
      ((H.edge e).weight : ℝ) * ∑ b : N → Bool,
          AGT.profileProb (deviation
            (fun (j : N) (a : Bool) => if a then p j else 1 - p j) x t) b *
          (singlePayoff {x} H.value (fun j => if b j then 1 else 0) x : ℝ) =
        ((H.edge e).weight : ℝ) * ∑ b : N → Bool,
          AGT.profileProb (deviation
            (fun (j : N) (a : Bool) => if a then p j else 1 - p j) x t) b *
          ((H.value x : ℝ) - if t then 1 else 0) := by
            congr 1
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hbt : b x = t
            · rw [hsingle t b hbt]
            · have hzero : AGT.profileProb (deviation
                  (fun (j : N) (a : Bool) => if a then p j else 1 - p j) x t) b = 0 := by
                rw [AGT.profileProb]
                apply Finset.prod_eq_zero (Finset.mem_univ x)
                simp [deviation, hbt]
              rw [hzero]
              simp
      _ = ((H.edge e).weight : ℝ) * ((∑ b : N → Bool,
          AGT.profileProb (deviation
            (fun (j : N) (a : Bool) => if a then p j else 1 - p j) x t) b) *
          ((H.value x : ℝ) - if t then 1 else 0)) := by
            rw [Finset.sum_mul]
      _ = ((H.edge e).weight : ℝ) *
          ((H.value x : ℝ) - if t then 1 else 0) := by
            rw [hsumDev t, one_mul]
  simp [HDFPA.delta, hedge]
  ring
