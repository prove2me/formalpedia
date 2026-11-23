-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.outside_perturbation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:29:09.238348+00:00
-- url     : https://prove2.me/submissions/6916f0f4-a8c5-4c6e-8df7-3b89714910e2

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false
set_option maxRecDepth 4000

open scoped BigOperators

namespace CorrelatedAuctionComplexity.Main

private lemma payoff_zero_le_two_payoff_one {N : Type} [Fintype N] [DecidableEq N]
    (S : Finset N) (v : N → ℚ) (x : N) (hxS : x ∈ S) (hx : v x = 2)
    (b : N → Bool) (hb : b x = false) :
    (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ) ≤
      2 * (singlePayoff S v
        (fun j => if (Function.update b x true) j then 1 else 0) x : ℝ) := by
  let b0 : N → ℚ := fun j => if b j then 1 else 0
  let b1 : N → ℚ := fun j => if (Function.update b x true) j then 1 else 0
  change (singlePayoff S v b0 x : ℝ) ≤ 2 * (singlePayoff S v b1 x : ℝ)
  have hwin1 : x ∈ S ∧ ∀ j ∈ S, b1 j ≤ b1 x := by
    refine ⟨hxS, ?_⟩
    intro j hj
    have hb1x : b1 x = 1 := by simp [b1]
    rw [hb1x]
    dsimp [b1]
    split <;> norm_num
  unfold singlePayoff
  rw [if_pos hwin1]
  have hb1x : b1 x = 1 := by simp [b1]
  rw [hb1x, hx]
  by_cases hwin0 : x ∈ S ∧ ∀ j ∈ S, b0 j ≤ b0 x
  · have hall : ∀ j ∈ S, b j = false := by
      intro j hj
      cases hbj : b j with
      | false => rfl
      | true =>
        have hh := hwin0.2 j hj
        norm_num [b0, hbj, hb] at hh
    rw [if_pos hwin0]
    have hb0x : b0 x = 0 := by simp [b0, hb]
    rw [hb0x]
    have hall0 : ∀ j ∈ S, ∀ k ∈ S, b0 k ≤ b0 j := by
      intro j hj k hk
      simp [b0, hall j hj, hall k hk]
    conv_lhs =>
      rw [Rat.cast_div]
      arg 2
      arg 1
      arg 1
      arg 1
      exact (@Finset.filter_eq_self N (fun j => ∀ k ∈ S, b0 k ≤ b0 j)
        (fun a => Finset.decidableDforallFinset) S).mpr (fun j hj => hall0 j hj)
    have hfilter1 : ∀ j ∈ S, (∀ k ∈ S, b1 k ≤ b1 j) ↔ j = x := by
      intro j hj
      constructor
      · intro h
        by_contra hjx
        have hh := h x hxS
        have hbj : b1 j = 0 := by
          simp [b1, Function.update, hjx, hall j hj]
        norm_num [hb1x, hbj] at hh
      · intro hjx
        subst j
        exact hwin1.2
    conv_rhs =>
      arg 2
      rw [Rat.cast_div]
      arg 2
      arg 1
      arg 1
      arg 1
      exact (@Finset.filter_congr N _ _ (fun a => Finset.decidableDforallFinset)
        inferInstance S) hfilter1
    rw [Finset.filter_eq', if_pos hxS]
    norm_num only [Rat.cast_sub, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one,
      Rat.cast_natCast, Finset.card_singleton, Nat.cast_one, sub_zero, sub_self,
      div_one, mul_one]
    have hcardpos : (0 : ℝ) < (S.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨x, hxS⟩)
    have hcard0 : (1 : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨x, hxS⟩)
    apply (div_le_iff₀ hcardpos).mpr
    nlinarith
  · rw [if_neg hwin0]
    norm_num only [Rat.cast_zero, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat,
      Rat.cast_one, Rat.cast_natCast, zero_le]
    positivity

private lemma payoff_one_le_one {N : Type} [Fintype N] [DecidableEq N]
    (S : Finset N) (v : N → ℚ) (x : N) (hxS : x ∈ S) (hx : v x = 2)
    (b : N → Bool) (hb : b x = true) :
    (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ) ≤ 1 := by
  let b1 : N → ℚ := fun j => if b j then 1 else 0
  change (singlePayoff S v b1 x : ℝ) ≤ 1
  unfold singlePayoff
  split
  · rename_i hwin
    have hxwin : x ∈ @Finset.filter N (fun j => ∀ k ∈ S, b1 k ≤ b1 j)
        (fun a => Finset.decidableDforallFinset) S :=
      (@Finset.mem_filter N (fun j => ∀ k ∈ S, b1 k ≤ b1 j)
        (fun a => Finset.decidableDforallFinset) S x).mpr ⟨hwin.1, hwin.2⟩
    have hcardpos : (0 : ℝ) <
        ((@Finset.filter N (fun j => ∀ k ∈ S, b1 k ≤ b1 j)
          (fun a => Finset.decidableDforallFinset) S).card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨x, hxwin⟩)
    have hcard1 : (1 : ℝ) ≤
        ((@Finset.filter N (fun j => ∀ k ∈ S, b1 k ≤ b1 j)
          (fun a => Finset.decidableDforallFinset) S).card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨x, hxwin⟩)
    have hbx : b1 x = 1 := by simp [b1, hb]
    rw [hbx, hx, Rat.cast_div]
    norm_num only [Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one, Rat.cast_natCast,
      sub_self, zero_div]
    apply (div_le_iff₀ hcardpos).mpr
    nlinarith
  · norm_num

private lemma payoff_binary_nonneg {N : Type} [Fintype N] [DecidableEq N]
    (S : Finset N) (v : N → ℚ) (x : N) (hx : v x = 2) (b : N → Bool) :
    0 ≤ (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ) := by
  unfold singlePayoff
  split
  · rw [Rat.cast_div]
    apply div_nonneg
    · have hq : (0 : ℚ) ≤ v x - (if b x then 1 else 0) := by
        rw [hx]
        split <;> norm_num
      exact_mod_cast hq
    · positivity
  · norm_num

private lemma deviation_prob {N : Type} [Fintype N] [DecidableEq N] (q : N → Bool → ℝ)
    (x : N) (t : Bool) (b : N → Bool) :
    AGT.profileProb (deviation q x t) b =
      if b x = t then (∏ j ∈ Finset.univ.erase x, q j (b j)) else 0 := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
  by_cases h : b x = t
  · simp only [deviation, Function.update_self, h, ↓reduceIte, one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    have hjx : j ≠ x := (Finset.mem_erase.mp hj).1
    simp [Function.update, hjx]
  · simp [deviation, h]

private lemma binary_lottery {N : Type} [Fintype N] [DecidableEq N] (p : N → ℝ)
    (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) :
    ∀ j, AGT.IsLottery ((fun (j : N) (a : Bool) => if a then p j else 1 - p j) j) := by
  intro j
  constructor
  · intro a
    cases a <;> simp [hp j]
  · simp

private lemma deviation_lottery {N : Type} [Fintype N] [DecidableEq N] (q : N → Bool → ℝ)
    (hq : ∀ j, AGT.IsLottery (q j)) (x : N) (t : Bool) :
    ∀ j, AGT.IsLottery (deviation q x t j) := by
  intro j
  by_cases h : j = x
  · subst j
    constructor
    · intro a
      by_cases ha : a = t <;> simp [deviation, ha]
    · cases t <;> simp [deviation]
  · simpa [deviation, Function.update, h] using hq j

private lemma deviation_prob_sum {N : Type} [Fintype N] [DecidableEq N] (q : N → Bool → ℝ)
    (hq : ∀ j, AGT.IsLottery (q j)) (x : N) (t : Bool) :
    ∑ b : N → Bool, AGT.profileProb (deviation q x t) b = 1 := by
  rw [show (∑ b : N → Bool, AGT.profileProb (deviation q x t) b) =
      ∏ j, ∑ a, deviation q x t j a by
    rw [Finset.prod_univ_sum]
    rfl]
  calc
    ∏ j, ∑ a, deviation q x t j a = ∏ _j : N, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact (deviation_lottery q hq x t j).2
    _ = 1 := by simp

private lemma deviation_prob_nonneg {N : Type} [Fintype N] [DecidableEq N]
    (q : N → Bool → ℝ) (hq : ∀ j, AGT.IsLottery (q j))
    (x : N) (t : Bool) (b : N → Bool) :
    0 ≤ AGT.profileProb (deviation q x t) b := by
  unfold AGT.profileProb
  apply Finset.prod_nonneg
  intro j hj
  exact (deviation_lottery q hq x t j).1 (b j)

private lemma expectation_deviation_nonneg {N : Type} [Fintype N] [DecidableEq N]
    (q : N → Bool → ℝ) (hq : ∀ j, AGT.IsLottery (q j))
    (x : N) (t : Bool) (u : (N → Bool) → ℝ) (hu : ∀ b, 0 ≤ u b) :
    0 ≤ expectation (deviation q x t) u := by
  unfold expectation
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg (deviation_prob_nonneg q hq x t b) (hu b)

private lemma pure_update_flip {N : Type} [Fintype N] [DecidableEq N] (x : N) :
    ∃ τ : (N → Bool) ≃ (N → Bool),
      (∀ b, τ b x = !b x) ∧
      (∀ b, b x = false → τ b = Function.update b x true) ∧
      (∀ (q : N → Bool → ℝ) b,
        (∏ j ∈ Finset.univ.erase x, q j (τ b j)) =
          ∏ j ∈ Finset.univ.erase x, q j (b j)) := by
  let τ : (N → Bool) ≃ (N → Bool) :=
    { toFun := fun b => Function.update b x (!b x)
      invFun := fun b => Function.update b x (!b x)
      left_inv := by
        intro b
        funext j
        by_cases h : j = x
        · subst j
          simp
        · simp [Function.update, h]
      right_inv := by
        intro b
        funext j
        by_cases h : j = x
        · subst j
          simp
        · simp [Function.update, h] }
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro b
    simp [τ]
  · intro b hb
    simp [τ, hb]
  · intro q b
    apply Finset.prod_congr rfl
    intro j hj
    have h : j ≠ x := (Finset.mem_erase.mp hj).1
    simp [τ, Function.update, h]

private lemma expectation_zero_le_two_one {N : Type} [Fintype N] [DecidableEq N]
    (q : N → Bool → ℝ) (hq : ∀ j a, 0 ≤ q j a)
    (S : Finset N) (v : N → ℚ) (x : N) (hxS : x ∈ S) (hx : v x = 2) :
    expectation (deviation q x false)
        (fun b => (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ)) ≤
      2 * expectation (deviation q x true)
        (fun b => (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ)) := by
  obtain ⟨τ, hflip, hupdate, hprod⟩ := pure_update_flip (N := N) x
  let u : (N → Bool) → ℝ :=
    fun b => (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ)
  have hpoint (b : N → Bool) :
      AGT.profileProb (deviation q x false) b * u b ≤
        2 * (AGT.profileProb (deviation q x true) (τ b) * u (τ b)) := by
    cases hb : b x with
    | false =>
      have hτ : τ b x = true := by rw [hflip, hb]; rfl
      have hP : 0 ≤ ∏ j ∈ Finset.univ.erase x, q j (b j) := by
        apply Finset.prod_nonneg
        intro j hj
        exact hq j (b j)
      rw [deviation_prob, deviation_prob]
      simp only [hb, hτ, ↓reduceIte]
      rw [hprod q b, hupdate b hb]
      change (∏ j ∈ Finset.univ.erase x, q j (b j)) * u b ≤
        2 * ((∏ j ∈ Finset.univ.erase x, q j (b j)) *
          (singlePayoff S v (fun j => if (Function.update b x true) j then 1 else 0) x : ℝ))
      calc
        (∏ j ∈ Finset.univ.erase x, q j (b j)) * u b ≤
            (∏ j ∈ Finset.univ.erase x, q j (b j)) *
              (2 * (singlePayoff S v
                (fun j => if (Function.update b x true) j then 1 else 0) x : ℝ)) :=
          mul_le_mul_of_nonneg_left (payoff_zero_le_two_payoff_one S v x hxS hx b hb) hP
        _ = _ := by ring
    | true =>
      have hτ : τ b x = false := by rw [hflip, hb]; rfl
      rw [deviation_prob, deviation_prob]
      simp [hb, hτ]
  unfold expectation
  change (∑ b : N → Bool, AGT.profileProb (deviation q x false) b * u b) ≤ _
  calc
    (∑ b : N → Bool, AGT.profileProb (deviation q x false) b * u b) ≤
        ∑ b : N → Bool, 2 * (AGT.profileProb (deviation q x true) (τ b) * u (τ b)) := by
      apply Finset.sum_le_sum
      intro b hb
      exact hpoint b
    _ = 2 * ∑ b : N → Bool, AGT.profileProb (deviation q x true) (τ b) * u (τ b) := by
      rw [Finset.mul_sum]
    _ = 2 * ∑ b : N → Bool, AGT.profileProb (deviation q x true) b * u b := by
      congr 1
      apply Fintype.sum_equiv τ
      intro b
      rfl

private lemma expectation_one_le_one {N : Type} [Fintype N] [DecidableEq N]
    (q : N → Bool → ℝ) (hq : ∀ j, AGT.IsLottery (q j))
    (S : Finset N) (v : N → ℚ) (x : N) (hxS : x ∈ S) (hx : v x = 2) :
    expectation (deviation q x true)
        (fun b => (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ)) ≤ 1 := by
  let u : (N → Bool) → ℝ :=
    fun b => (singlePayoff S v (fun j => if b j then 1 else 0) x : ℝ)
  have hpoint (b : N → Bool) :
      AGT.profileProb (deviation q x true) b * u b ≤
        AGT.profileProb (deviation q x true) b * 1 := by
    by_cases hb : b x = true
    · exact mul_le_mul_of_nonneg_left (payoff_one_le_one S v x hxS hx b hb)
        (deviation_prob_nonneg q hq x true b)
    · have hP : AGT.profileProb (deviation q x true) b = 0 := by
        rw [deviation_prob]
        simp [hb]
      simp [hP]
  unfold expectation
  change (∑ b : N → Bool, AGT.profileProb (deviation q x true) b * u b) ≤ 1
  calc
    (∑ b : N → Bool, AGT.profileProb (deviation q x true) b * u b) ≤
        ∑ b : N → Bool, AGT.profileProb (deviation q x true) b * 1 := by
      apply Finset.sum_le_sum
      intro b hb
      exact hpoint b
    _ = ∑ b : N → Bool, AGT.profileProb (deviation q x true) b := by simp
    _ = 1 := deviation_prob_sum q hq x true

private lemma edge_delta_abs_le {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (x : N) (hx : H.value x = 2)
    (e : Fin H.edges.length) (hxS : x ∈ (H.edge e).participants)
    (p : N → ℝ) (hp : H.LegalBinary p) :
    |H.binaryEdgePure p e x true - H.binaryEdgePure p e x false| ≤
      ((H.edge e).weight : ℝ) := by
  let q : N → Bool → ℝ := fun j a => if a then p j else 1 - p j
  let u : (N → Bool) → ℝ := fun b =>
    (singlePayoff (H.edge e).participants H.value (fun j => if b j then 1 else 0) x : ℝ)
  let E0 : ℝ := expectation (deviation q x false) u
  let E1 : ℝ := expectation (deviation q x true) u
  have hq : ∀ j, AGT.IsLottery (q j) := binary_lottery p hp.1
  have hq0 : ∀ j a, 0 ≤ q j a := fun j a => (hq j).1 a
  have hu : ∀ b, 0 ≤ u b := fun b => payoff_binary_nonneg _ _ _ hx b
  have hE0 : 0 ≤ E0 := expectation_deviation_nonneg q hq x false u hu
  have hE1 : 0 ≤ E1 := expectation_deviation_nonneg q hq x true u hu
  have hcmp : E0 ≤ 2 * E1 := expectation_zero_le_two_one q hq0 _ _ x hxS hx
  have hE1le : E1 ≤ 1 := expectation_one_le_one q hq _ _ x hxS hx
  have hdiff : |E1 - E0| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hwQ : 0 < (H.edge e).weight :=
    (hH.2.2.2.2.1 (H.edge e) (List.getElem_mem e.isLt)).2
  have hw : (0 : ℝ) ≤ ((H.edge e).weight : ℝ) := by exact_mod_cast hwQ.le
  change |((H.edge e).weight : ℝ) * E1 - ((H.edge e).weight : ℝ) * E0| ≤ _
  rw [show ((H.edge e).weight : ℝ) * E1 - ((H.edge e).weight : ℝ) * E0 =
    ((H.edge e).weight : ℝ) * (E1 - E0) by ring]
  rw [abs_mul, abs_of_nonneg hw]
  calc
    ((H.edge e).weight : ℝ) * |E1 - E0| ≤ ((H.edge e).weight : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hdiff hw
    _ = ((H.edge e).weight : ℝ) := mul_one _

end CorrelatedAuctionComplexity.Main

open CorrelatedAuctionComplexity.Main

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (x : N) (hx : H.value x = 2) (p : N → ℝ) (hp : H.LegalBinary p)
    (R : Finset (Fin H.edges.length)) (hR : ∀ e ∈ R, x ∈ (H.edge e).participants) :
    |H.delta p R x| ≤ ∑ e ∈ R, ((H.edge e).weight : ℝ) := by
  classical
  unfold HDFPA.delta
  calc
    |∑ e ∈ R, (H.binaryEdgePure p e x true - H.binaryEdgePure p e x false)| ≤
        ∑ e ∈ R, |H.binaryEdgePure p e x true - H.binaryEdgePure p e x false| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ R, ((H.edge e).weight : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      exact CorrelatedAuctionComplexity.Main.edge_delta_abs_le H hH x hx e (hR e he) p hp
