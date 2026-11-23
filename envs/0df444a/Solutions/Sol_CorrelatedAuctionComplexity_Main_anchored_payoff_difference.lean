-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.anchored_payoff_difference
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:27:26.505366+00:00
-- url     : https://prove2.me/submissions/b2156527-f092-4ade-9b50-2c41de0b7435

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

open CorrelatedAuctionComplexity.Main

private lemma boolProb_sum_one {N : Type} [Fintype N] [DecidableEq N]
    (q : N → Bool → ℝ) (hq : ∀ j, q j true + q j false = 1) :
    ∑ b : N → Bool, ∏ j, q j (b j) = 1 := by
  have h := (Finset.prod_univ_sum (fun _ : N => (Finset.univ : Finset Bool)) q).symm
  simp only [Fintype.sum_bool, hq, Finset.prod_const_one] at h
  rw [Fintype.piFinset_univ] at h
  exact h

private lemma boolProb_sum_fiber {N : Type} [Fintype N] [DecidableEq N]
    (q : N → Bool → ℝ) (hq : ∀ j, q j true + q j false = 1)
    (y : N) (a : Bool) :
    ∑ b ∈ Finset.univ.filter (fun b : N → Bool => b y = a), ∏ j, q j (b j) = q y a := by
  classical
  let E : {b : N → Bool // b y = a} ≃ ({j : N // j ≠ y} → Bool) :=
    { toFun := fun b j => b.1 j.1
      invFun := fun c => ⟨fun j => if h : j = y then a else c ⟨j,h⟩, by simp⟩
      left_inv := by
        intro b
        apply Subtype.ext
        funext j
        by_cases h : j = y
        · subst j
          simp [b.2]
        · simp [h]
      right_inv := by
        intro c
        funext j
        simp [j.2] }
  have hprod (b : {b : N → Bool // b y = a}) :
      (∏ j, q j (b.1 j)) = q y a * ∏ j : {j : N // j ≠ y}, q j.1 (b.1 j.1) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => q j (b.1 j)) (Finset.mem_univ y)]
    rw [b.2]
    congr 1
    exact Finset.prod_subtype (p := fun j => j ≠ y) (Finset.univ.erase y)
      (by simp) (fun j => q j (b.1 j))
  calc
    (∑ b ∈ Finset.univ.filter (fun b : N → Bool => b y = a), ∏ j, q j (b j)) =
        ∑ b : {b : N → Bool // b y = a}, ∏ j, q j (b.1 j) := by
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ c : ({j : N // j ≠ y} → Bool), q y a * ∏ j : {j : N // j ≠ y}, q j.1 (c j) := by
      apply Fintype.sum_equiv E
      intro b
      exact hprod b
    _ = q y a * ∑ c : ({j : N // j ≠ y} → Bool), ∏ j : {j : N // j ≠ y}, q j.1 (c j) := by
      rw [Finset.mul_sum]
    _ = q y a := by
      rw [boolProb_sum_one (N := {j : N // j ≠ y}) (fun j => q j.1) (fun j => hq j.1), mul_one]

private lemma boolProb_expect_coord {N : Type} [Fintype N] [DecidableEq N]
    (q : N → Bool → ℝ) (hq : ∀ j, q j true + q j false = 1)
    (y : N) (f : Bool → ℝ) :
    (∑ b : N → Bool, (∏ j, q j (b j)) * f (b y)) =
      ∑ a : Bool, q y a * f a := by
  rw [← Finset.sum_fiberwise Finset.univ (fun b : N → Bool => b y)
    (fun b => (∏ j, q j (b j)) * f (b y))]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b ∈ Finset.univ.filter (fun b : N → Bool => b y = a),
        (∏ j, q j (b j)) * f (b y)) =
        ∑ b ∈ Finset.univ.filter (fun b : N → Bool => b y = a),
          (∏ j, q j (b j)) * f a := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [(Finset.mem_filter.mp hb).2]
    _ = q y a * f a := by rw [← Finset.sum_mul, boolProb_sum_fiber q hq y a]

private lemma boolProb_dev_coord {N : Type} [Fintype N] [DecidableEq N]
    (q : N → Bool → ℝ) (hq : ∀ j, q j true + q j false = 1)
    (x y : N) (hxy : x ≠ y) (t : Bool) (f : Bool → ℝ) :
    (∑ b : N → Bool, (∏ j, deviation q x t j (b j)) * f (b y)) =
      ∑ a : Bool, q y a * f a := by
  let qd := deviation q x t
  have hsum (j : N) : qd j true + qd j false = 1 := by
    by_cases h : j = x
    · subst j
      cases t <;> simp [qd, deviation]
    · simp [qd, deviation, Function.update_of_ne h, hq j]
  change (∑ b : N → Bool, (∏ j, qd j (b j)) * f (b y)) = _
  rw [boolProb_expect_coord qd hsum y f]
  simp [qd, deviation, Function.update_of_ne (Ne.symm hxy)]

private lemma singlePayoff_congr {N : Type} [DecidableEq N]
    (S : Finset N) (v : N → ℚ) (i : N) (b c : N → ℚ)
    (h : ∀ j ∈ S, b j = c j) :
    singlePayoff S v b i = singlePayoff S v c i := by
  have hh (j : N) : (j ∈ S ∧ ∀ k ∈ S, b k ≤ b j) ↔
      (j ∈ S ∧ ∀ k ∈ S, c k ≤ c j) := by
    by_cases hj : j ∈ S
    · simp only [hj, true_and]
      apply forall_congr'
      intro k
      by_cases hk : k ∈ S
      · simp [hk, h k hk, h j hj]
      · simp [hk]
    · simp [hj]
  have hf : (S.filter fun j => ∀ k ∈ S, b k ≤ b j) =
      (S.filter fun j => ∀ k ∈ S, c k ≤ c j) := by
    ext j
    simp only [Finset.mem_filter]
    exact hh j
  by_cases hi : i ∈ S
  · simp only [singlePayoff, hh i, hf]
    rw [h i hi]
  · simp [singlePayoff, hi]

private def canonicalBid {N : Type} [DecidableEq N] (x y : N) (t a : Bool) : N → ℚ :=
  fun j => if j = x then (if t then 1 else 0) else if j = y then (if a then 1 else 0) else 0

private noncomputable def payoffCase (v : ℚ) (m : ℕ) (t a : Bool) : ℝ :=
  if t then (if a then ((v : ℝ) - 1) / 2 else (v : ℝ) - 1)
  else (if a then 0 else (v : ℝ) / (m + 2 : ℕ))

private lemma anchored_singlePayoff {N : Type} [Fintype N] [DecidableEq N]
    (S : Finset N) (v : N → ℚ) (m : ℕ) (x y : N) (hxy : x ≠ y) (z : Fin m → N)
    (hz : Function.Injective z) (hfresh : ∀ j, z j ≠ x ∧ z j ≠ y)
    (he : S = {x,y} ∪ Finset.univ.image z)
    (t a : Bool) (b : N → Bool) (hbt : b x = t) (hba : b y = a)
    (hbz : ∀ j, b (z j) = false) :
    ((singlePayoff S v (fun j => if b j then 1 else 0) x : ℚ) : ℝ) =
      payoffCase (v x) m t a := by
  classical
  have hcard : S.card = m + 2 := by
    have hd : Disjoint ({x,y} : Finset N) (Finset.univ.image z) := by
      rw [Finset.disjoint_left]
      intro c hc hcz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hcz
      rcases hc with hcx | hcy
      · exact (hfresh j).1 (hjeq.trans hcx)
      · exact (hfresh j).2 (hjeq.trans hcy)
    rw [he, Finset.card_union_of_disjoint hd, Finset.card_pair hxy,
      Finset.card_image_of_injective _ hz, Finset.card_univ, Fintype.card_fin]
    omega
  have hmem (j : N) : j ∈ S ↔ j = x ∨ j = y ∨ ∃ k, z k = j := by
    rw [he]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and]
    tauto
  have hbid (j : N) (hj : j ∈ S) : (if b j then (1 : ℚ) else 0) = canonicalBid x y t a j := by
    rcases (hmem j).mp hj with hjx | hjy | ⟨k, hkj⟩
    · subst j
      simp [canonicalBid, hbt]
    · subst j
      simp [canonicalBid, hba, Ne.symm hxy]
    · subst j
      simp [canonicalBid, hbz k, (hfresh k).1, (hfresh k).2]
  rw [singlePayoff_congr S v x _ (canonicalBid x y t a) hbid]
  have hxS : x ∈ S := by simp [he]
  have hyS : y ∈ S := by simp [he]
  cases t <;> cases a
  · have hfilter : (S.filter fun j => ∀ k ∈ S, canonicalBid x y false false k ≤
        canonicalBid x y false false j) = S := by
      apply Finset.filter_true_of_mem
      intro j hj
      simp [canonicalBid]
    have hxwin : x ∈ S ∧ ∀ j ∈ S, canonicalBid x y false false j ≤
        canonicalBid x y false false x := by
      refine ⟨hxS, ?_⟩
      simp [canonicalBid]
    rw [singlePayoff, if_pos hxwin, Finset.filter_congr_decidable, hfilter]
    simp [canonicalBid, payoffCase, hcard]
  · have hxnot : ¬ (x ∈ S ∧ ∀ j ∈ S, canonicalBid x y false true j ≤
        canonicalBid x y false true x) := by
      intro h
      have := h.2 y hyS
      norm_num [canonicalBid, Ne.symm hxy] at this
    simp [singlePayoff, hxnot, payoffCase]
  · have hfilter : (S.filter fun j => ∀ k ∈ S, canonicalBid x y true false k ≤
        canonicalBid x y true false j) = {x} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        rcases (hmem j).mp h.1 with hjx | hjy | ⟨k, hkj⟩
        · exact hjx
        · subst j
          have := h.2 x hxS
          norm_num [canonicalBid, Ne.symm hxy] at this
        · subst j
          have := h.2 x hxS
          norm_num [canonicalBid, (hfresh k).1, (hfresh k).2] at this
      · intro h
        subst j
        refine ⟨hxS, ?_⟩
        intro k hk
        rcases (hmem k).mp hk with hkx | hky | ⟨r, hkr⟩
        · subst k
          simp [canonicalBid]
        · subst k
          simp [canonicalBid, Ne.symm hxy]
        · subst k
          simp [canonicalBid, (hfresh r).1, (hfresh r).2]
    have hxwin : x ∈ S ∧ ∀ j ∈ S, canonicalBid x y true false j ≤
        canonicalBid x y true false x := by
      have h : x ∈ S.filter (fun j => ∀ k ∈ S, canonicalBid x y true false k ≤
          canonicalBid x y true false j) := by rw [hfilter]; simp
      exact Finset.mem_filter.mp h
    rw [singlePayoff, if_pos hxwin, Finset.filter_congr_decidable, hfilter]
    simp [canonicalBid, payoffCase]
  · have hfilter : (S.filter fun j => ∀ k ∈ S, canonicalBid x y true true k ≤
        canonicalBid x y true true j) = {x,y} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h
        rcases (hmem j).mp h.1 with hjx | hjy | ⟨k, hkj⟩
        · simp [hjx]
        · simp [hjy]
        · subst j
          have := h.2 x hxS
          norm_num [canonicalBid, (hfresh k).1, (hfresh k).2] at this
      · intro h
        rcases h with hjx | hjy
        · subst j
          refine ⟨hxS, ?_⟩
          intro k hk
          rcases (hmem k).mp hk with hkx | hky | ⟨r, hkr⟩
          · subst k
            simp [canonicalBid]
          · subst k
            simp [canonicalBid, Ne.symm hxy]
          · subst k
            simp [canonicalBid, (hfresh r).1, (hfresh r).2]
        · subst j
          refine ⟨hyS, ?_⟩
          intro k hk
          rcases (hmem k).mp hk with hkx | hky | ⟨r, hkr⟩
          · subst k
            simp [canonicalBid, Ne.symm hxy]
          · subst k
            simp [canonicalBid, Ne.symm hxy]
          · subst k
            simp [canonicalBid, (hfresh r).1, (hfresh r).2]
    have hxwin : x ∈ S ∧ ∀ j ∈ S, canonicalBid x y true true j ≤
        canonicalBid x y true true x := by
      have h : x ∈ S.filter (fun j => ∀ k ∈ S, canonicalBid x y true true k ≤
          canonicalBid x y true true j) := by rw [hfilter]; simp
      exact Finset.mem_filter.mp h
    rw [singlePayoff, if_pos hxwin, Finset.filter_congr_decidable, hfilter]
    simp [canonicalBid, payoffCase, Finset.card_pair hxy]

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (m : ℕ) (x y : N) (hxy : x ≠ y) (z : Fin m → N)
    (hz : (List.ofFn z).Nodup) (hfresh : ∀ j, z j ≠ x ∧ z j ≠ y)
    (hx : H.value x ∈ ({2,3,4} : Finset ℚ))
    (hy : H.value y ∈ ({2,3,4} : Finset ℚ)) (hvz : ∀ j, H.value (z j) = 1/2)
    (e : Fin H.edges.length)
    (he : (H.edge e).participants = {x,y} ∪ Finset.univ.image z)
    (p : N → ℝ) (hp : H.LegalBinary p) :
    H.delta p {e} x = ((H.edge e).weight : ℝ) *
      ((((H.value x : ℝ)/(m+2 : ℕ)) - ((H.value x : ℝ)-1)/2)*p y +
        (H.value x : ℝ)-1-(H.value x : ℝ)/(m+2 : ℕ)) := by
  classical
  let q : N → Bool → ℝ := fun j a => if a then p j else 1 - p j
  have hq (j : N) : q j true + q j false = 1 := by simp [q]
  have hzi : Function.Injective z := List.nodup_ofFn.mp hz
  have hpz (j : Fin m) : p (z j) = 0 := by
    apply hp.2
    rw [hvz j]
    norm_num
  have hu (t : Bool) :
      (∑ b : N → Bool, (∏ j, deviation q x t j (b j)) *
        ((singlePayoff (H.edge e).participants H.value
          (fun j => if b j then 1 else 0) x : ℚ) : ℝ)) =
        ∑ a : Bool, q y a * payoffCase (H.value x) m t a := by
    rw [← boolProb_dev_coord q hq x y hxy t (payoffCase (H.value x) m t)]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hbz : ∀ j, b (z j) = false
    · by_cases hbt : b x = t
      · rw [anchored_singlePayoff (H.edge e).participants H.value m x y hxy z hzi
          hfresh he t (b y) b hbt rfl hbz]
      · have hzeroFactor : deviation q x t x (b x) = 0 := by
          simp [deviation, hbt]
        have hzero : (∏ k, deviation q x t k (b k)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ x)
          exact hzeroFactor
        rw [hzero]
        simp
    · obtain ⟨j, hj⟩ := not_forall.mp hbz
      have hjt : b (z j) = true := by
        cases h : b (z j) <;> simp_all
      have hzeroFactor : deviation q x t (z j) (b (z j)) = 0 := by
        rw [hjt]
        simp [q, deviation, Function.update_of_ne (hfresh j).1, hpz j]
      have hzero : (∏ k, deviation q x t k (b k)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (z j))
        exact hzeroFactor
      rw [hzero]
      simp
  have hbinary (t : Bool) :
      H.binaryEdgePure p e x t = ((H.edge e).weight : ℝ) *
        (p y * payoffCase (H.value x) m t true +
          (1 - p y) * payoffCase (H.value x) m t false) := by
    simp only [HDFPA.binaryEdgePure, expectation, AGT.profileProb]
    have hh := congrArg (fun A : ℝ => ((H.edge e).weight : ℝ) * A) (hu t)
    simpa [q, Fintype.sum_bool] using hh
  simp only [HDFPA.delta, Finset.sum_singleton, hbinary]
  simp only [payoffCase, Bool.false_eq_true, ↓reduceIte]
  ring
