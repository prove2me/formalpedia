-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.binary_deviation_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:55:09.306674+00:00
-- url     : https://prove2.me/submissions/8e26daa1-2f6c-48ea-ac50-c5094c5b30e3

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false
set_option maxRecDepth 4000

open scoped BigOperators
open CorrelatedAuctionComplexity.Main

private lemma binary_payoff_zero_nonneg {N : Type} [DecidableEq N]
    (S : Finset N) (v : N → ℚ) (x : N) (hv : 0 ≤ v x)
    (b : N → Bool) (hb : b x = false) :
    0 ≤ (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ) := by
  unfold singlePayoff
  split
  · rw [Rat.cast_div]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Rat.cast_zero, sub_zero]
    apply div_nonneg
    · exact_mod_cast hv
    · positivity
  · norm_num

private lemma binary_payoff_one_nonpos {N : Type} [DecidableEq N]
    (S : Finset N) (v : N → ℚ) (x : N) (hv : v x < 1)
    (b : N → Bool) (hb : b x = true) :
    (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ) ≤ 0 := by
  unfold singlePayoff
  split
  · rw [Rat.cast_div]
    simp only [hb, ↓reduceIte, Rat.cast_one]
    apply div_nonpos_of_nonpos_of_nonneg
    · have hh : v x - 1 ≤ 0 := sub_nonpos.mpr hv.le
      exact_mod_cast hh
    · positivity
  · norm_num

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (η : ℝ) (hη : 0 ≤ η) (p : N → ℝ)
    (hne : H.IsNE η (H.binaryProfile p)) :
    ∀ x, (0 < H.totalDelta p x → (1-p x)*H.totalDelta p x ≤ η*H.incidentWeight x) ∧
      (H.totalDelta p x < 0 → -(p x)*H.totalDelta p x ≤ η*H.incidentWeight x) := by
  classical
  intro x
  let zeroBid : H.Bid := ⟨0, by simp [hB]⟩
  let oneBid : H.Bid := ⟨1, by simp [hB]⟩
  let eBid : Bool ≃ H.Bid :=
    { toFun := fun t => if t then oneBid else zeroBid
      invFun := fun b => decide (b.val = 1)
      left_inv := by
        intro t
        cases t <;> simp [zeroBid, oneBid]
      right_inv := by
        intro b
        have hb : b.val = 0 ∨ b.val = 1 := by
          simpa [hB] using b.property
        rcases hb with hb | hb
        · have hbb : b = zeroBid := Subtype.ext hb
          subst b
          simp [zeroBid]
        · have hbb : b = oneBid := Subtype.ext hb
          subst b
          simp [oneBid] }
  let eProf : (N → Bool) ≃ (N → H.Bid) :=
    Equiv.piCongrRight (fun _ : N => eBid)
  let q : N → Bool → ℝ := fun j a => if a then p j else 1 - p j
  have hp : H.LegalBinary p := by
    constructor
    · intro i
      have hnonneg_one : 0 ≤ p i := by
        have hh := (hne.1 i).1.1 oneBid
        simpa [HDFPA.binaryProfile, oneBid] using hh
      have hnonneg_zero : 0 ≤ 1 - p i := by
        have hh := (hne.1 i).1.1 zeroBid
        simpa [HDFPA.binaryProfile, zeroBid] using hh
      have hsum : (∑ t : Bool, H.binaryProfile p i (eBid t)) =
          ∑ b : H.Bid, H.binaryProfile p i b := by
        apply Fintype.sum_equiv eBid
        intro t
        rfl
      have hlottery := (hne.1 i).1.2
      rw [← hsum] at hlottery
      have hsumval : (1 - p i) + p i = 1 := by
        simpa [eBid, zeroBid, oneBid, HDFPA.binaryProfile, q] using hlottery
      exact ⟨hnonneg_one, by linarith⟩
    · intro i hi
      have hh := (hne.1 i).2 oneBid (by simpa [oneBid] using hi)
      simpa [HDFPA.binaryProfile, oneBid] using hh
  have hprob (b : N → Bool) :
      AGT.profileProb (H.binaryProfile p) (fun j => eBid (b j)) =
        AGT.profileProb q b := by
    unfold AGT.profileProb
    apply Finset.prod_congr rfl
    intro j hj
    cases h : b j <;> simp [HDFPA.binaryProfile, eBid, zeroBid, oneBid, q, h]
  have hdevprob (t : Bool) (b : N → Bool) :
      AGT.profileProb (deviation q x t) b =
        if b x = t then (∏ j ∈ Finset.univ.erase x, q j (b j)) else 0 := by
    unfold AGT.profileProb
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => deviation q x t j (b j)) (Finset.mem_univ x)]
    have herase : (∏ j ∈ Finset.univ.erase x, deviation q x t j (b j)) =
        ∏ j ∈ Finset.univ.erase x, q j (b j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjx : j ≠ x := (Finset.mem_erase.mp hj).1
      simp [deviation, Function.update_of_ne hjx]
    rw [herase]
    by_cases h : b x = t <;> simp [deviation, h]
  have hprob_erase (b : N → Bool) :
      AGT.profileProb q b = q x (b x) * ∏ j ∈ Finset.univ.erase x, q j (b j) := by
    unfold AGT.profileProb
    rw [← Finset.mul_prod_erase Finset.univ (fun j => q j (b j)) (Finset.mem_univ x)]
  have hdevbase (t : Bool) (b : N → Bool) :
      AGT.profileProb (deviation (H.binaryProfile p) x (eBid t))
          (fun j => eBid (b j)) =
        AGT.profileProb (deviation q x t) b := by
    unfold AGT.profileProb
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hjx : j = x
    · subst j
      cases t <;> cases h : b x <;>
        simp [deviation, HDFPA.binaryProfile, eBid, zeroBid, oneBid, q, h]
    · simp only [deviation, Function.update_of_ne hjx]
      cases h : b j <;> simp [HDFPA.binaryProfile, eBid, zeroBid, oneBid, q, h]
  have hprob_nonneg (t : Bool) (b : N → Bool) :
      0 ≤ AGT.profileProb (deviation q x t) b := by
    unfold AGT.profileProb
    apply Finset.prod_nonneg
    intro j hj
    by_cases hjx : j = x
    · subst j
      by_cases h : b x = t <;> simp [deviation, h]
    · simp only [deviation, Function.update_of_ne hjx]
      cases h : b j <;> simp [q, h, (hp.1 j).1, (hp.1 j).2]
  have reindex (σ : H.Profile) (q' : N → Bool → ℝ)
      (hσ : ∀ b : N → Bool,
        AGT.profileProb σ (fun j => eBid (b j)) = AGT.profileProb q' b)
      (e : Fin H.edges.length) :
      H.edgeUtility e σ x = ((H.edge e).weight : ℝ) * expectation q'
        (fun b => (singlePayoff (H.edge e).participants H.value
          (fun j => if b j then 1 else 0) x : ℝ)) := by
    unfold HDFPA.edgeUtility expectation
    congr 1
    symm
    apply Fintype.sum_equiv eProf
    intro b
    change AGT.profileProb q' b *
      (singlePayoff (H.edge e).participants H.value
        (fun j => if b j then 1 else 0) x : ℝ) =
      AGT.profileProb σ (fun j => eBid (b j)) *
      (singlePayoff (H.edge e).participants H.value
        (fun j => (eBid (b j)).val) x : ℝ)
    rw [hσ b]
    have hv : (fun j => (eBid (b j)).val) =
        (fun j => if b j then (1 : ℚ) else 0) := by
      funext j
      cases h : b j <;> simp [eBid, zeroBid, oneBid, h]
    rw [hv]
  have hpure (t : Bool) (e : Fin H.edges.length) :
      H.edgeUtility e (deviation (H.binaryProfile p) x (eBid t)) x =
        H.binaryEdgePure p e x t := by
    simpa [HDFPA.binaryEdgePure] using
      (reindex (deviation (H.binaryProfile p) x (eBid t))
        (deviation q x t) (hdevbase t) e)
  have hpureUtility (t : Bool) :
      H.pureUtility (H.binaryProfile p) x (eBid t) =
        ∑ e : Fin H.edges.length, H.binaryEdgePure p e x t := by
    unfold HDFPA.pureUtility HDFPA.utility
    apply Finset.sum_congr rfl
    intro e he
    exact hpure t e
  have hmixed_edge (e : Fin H.edges.length) :
      H.edgeUtility e (H.binaryProfile p) x =
        p x * H.binaryEdgePure p e x true +
          (1 - p x) * H.binaryEdgePure p e x false := by
    rw [reindex (H.binaryProfile p) q hprob e]
    unfold HDFPA.binaryEdgePure expectation
    calc
      ((H.edge e).weight : ℝ) * ∑ b : N → Bool,
          AGT.profileProb q b *
            (singlePayoff (H.edge e).participants H.value
              (fun j => if b j then 1 else 0) x : ℝ) =
          ((H.edge e).weight : ℝ) *
            (p x * (∑ b : N → Bool, AGT.profileProb (deviation q x true) b *
              (singlePayoff (H.edge e).participants H.value
                (fun j => if b j then 1 else 0) x : ℝ)) +
            (1 - p x) * (∑ b : N → Bool, AGT.profileProb (deviation q x false) b *
              (singlePayoff (H.edge e).participants H.value
                (fun j => if b j then 1 else 0) x : ℝ))) := by
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b hb
        rw [hdevprob true b, hdevprob false b, hprob_erase b]
        cases h : b x <;> simp [q, h] <;> ring
      _ = p x * (((H.edge e).weight : ℝ) *
            ∑ b : N → Bool, AGT.profileProb (deviation q x true) b *
              (singlePayoff (H.edge e).participants H.value
                (fun j => if b j then 1 else 0) x : ℝ)) +
          (1 - p x) * (((H.edge e).weight : ℝ) *
            ∑ b : N → Bool, AGT.profileProb (deviation q x false) b *
              (singlePayoff (H.edge e).participants H.value
                (fun j => if b j then 1 else 0) x : ℝ)) := by ring
  have hmixed :
      H.utility (H.binaryProfile p) x =
        p x * H.pureUtility (H.binaryProfile p) x oneBid +
          (1 - p x) * H.pureUtility (H.binaryProfile p) x zeroBid := by
    have hpureOne := hpureUtility true
    have hpureZero := hpureUtility false
    change H.pureUtility (H.binaryProfile p) x oneBid =
        ∑ e : Fin H.edges.length, H.binaryEdgePure p e x true at hpureOne
    change H.pureUtility (H.binaryProfile p) x zeroBid =
        ∑ e : Fin H.edges.length, H.binaryEdgePure p e x false at hpureZero
    unfold HDFPA.utility
    calc
      (∑ e : Fin H.edges.length, H.edgeUtility e (H.binaryProfile p) x) =
          ∑ e : Fin H.edges.length,
            (p x * H.binaryEdgePure p e x true +
              (1 - p x) * H.binaryEdgePure p e x false) := by
        apply Finset.sum_congr rfl
        intro e he
        exact hmixed_edge e
      _ = p x * (∑ e : Fin H.edges.length, H.binaryEdgePure p e x true) +
          (1 - p x) * (∑ e : Fin H.edges.length, H.binaryEdgePure p e x false) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [← hpureOne, ← hpureZero]
  have hdelta : H.totalDelta p x =
      H.pureUtility (H.binaryProfile p) x oneBid -
        H.pureUtility (H.binaryProfile p) x zeroBid := by
    have hpureOne := hpureUtility true
    have hpureZero := hpureUtility false
    change H.pureUtility (H.binaryProfile p) x oneBid =
        ∑ e : Fin H.edges.length, H.binaryEdgePure p e x true at hpureOne
    change H.pureUtility (H.binaryProfile p) x zeroBid =
        ∑ e : Fin H.edges.length, H.binaryEdgePure p e x false at hpureZero
    rw [hpureOne, hpureZero]
    simp only [HDFPA.totalDelta, HDFPA.delta, Finset.sum_sub_distrib]
  have hzeroLegal : (zeroBid : H.Bid).val ≤ H.value x := by
    have hv := (hH.2.2.2.1 x).1
    simpa [zeroBid] using hv
  constructor
  · intro hpos
    by_cases hv : H.value x < 1
    · exfalso
      have hsign (e : Fin H.edges.length) :
          H.binaryEdgePure p e x true - H.binaryEdgePure p e x false ≤ 0 := by
        let u : (N → Bool) → ℝ := fun b =>
          (singlePayoff (H.edge e).participants H.value
            (fun j => if b j then 1 else 0) x : ℝ)
        have hEone : expectation (deviation q x true) u ≤ 0 := by
          unfold expectation
          apply Finset.sum_nonpos
          intro b hb
          cases hbx : b x
          · rw [hdevprob true b]
            simp [hbx]
          · apply mul_nonpos_of_nonneg_of_nonpos (hprob_nonneg true b)
            exact binary_payoff_one_nonpos _ _ _ hv b hbx
        have hEzero : 0 ≤ expectation (deviation q x false) u := by
          unfold expectation
          apply Finset.sum_nonneg
          intro b hb
          cases hbx : b x
          · apply mul_nonneg (hprob_nonneg false b)
            exact binary_payoff_zero_nonneg _ _ _ (hH.2.2.2.1 x).1 b hbx
          · rw [hdevprob false b]
            simp [hbx]
        have hwQ : 0 < (H.edge e).weight :=
          (hH.2.2.2.2.1 (H.edge e) (List.getElem_mem e.isLt)).2
        have hw : (0 : ℝ) ≤ ((H.edge e).weight : ℝ) := by exact_mod_cast hwQ.le
        change ((H.edge e).weight : ℝ) * expectation (deviation q x true) u -
          ((H.edge e).weight : ℝ) * expectation (deviation q x false) u ≤ 0
        have h1 : ((H.edge e).weight : ℝ) * expectation (deviation q x true) u ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hw hEone
        have h0 : 0 ≤ ((H.edge e).weight : ℝ) * expectation (deviation q x false) u :=
          mul_nonneg hw hEzero
        linarith
      have htotal : H.totalDelta p x ≤ 0 := by
        unfold HDFPA.totalDelta HDFPA.delta
        apply Finset.sum_nonpos
        intro e he
        exact hsign e
      exact (not_lt_of_ge htotal) hpos
    · have hv1 : 1 ≤ H.value x := le_of_not_gt hv
      have honeLegal : (oneBid : H.Bid).val ≤ H.value x := by simpa [oneBid] using hv1
      have hdev := hne.2 x oneBid honeLegal
      rw [hdelta]
      rw [hmixed] at hdev
      nlinarith
  · intro hneg
    have hdev := hne.2 x zeroBid hzeroLegal
    rw [hdelta]
    rw [hmixed] at hdev
    nlinarith
