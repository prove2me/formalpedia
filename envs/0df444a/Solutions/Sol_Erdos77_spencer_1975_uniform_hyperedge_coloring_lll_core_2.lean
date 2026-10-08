-- Prove2me | solution 2 for Erdos77.spencer_1975_uniform_hyperedge_coloring_lll_core
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:46:35.052067+00:00
-- url     : https://prove2.me/submissions/80bbdd11-bc7f-4de8-a04d-25bda05e9ae7

import Mathlib

set_option autoImplicit false

universe u

namespace Erdos77Aux2d30

open Finset

/-- Step A (one colour class): modifying coordinates in `A` keeps `G`, so the constant-`b` part is small. -/
lemma stepA_const {ι : Type u} [Fintype ι] [DecidableEq ι] (A : Finset ι) (G : Finset (ι → Bool))
    (hG : ∀ c c' : ι → Bool, (∀ i, i ∉ A → c i = c' i) → c ∈ G → c' ∈ G) (b : Bool) :
    2 ^ A.card * (G.filter (fun c => ∀ i ∈ A, c i = b)).card ≤ G.card := by
  have key : ((G.filter (fun c => ∀ i ∈ A, c i = b)) ×ˢ (univ : Finset (A → Bool))).card
      ≤ G.card := by
    apply Finset.card_le_card_of_injOn
      (fun x : (ι → Bool) × (A → Bool) => fun i => if h : i ∈ A then x.2 ⟨i, h⟩ else x.1 i)
    · intro x hx
      rw [mem_coe, mem_product, mem_filter] at hx
      apply hG x.1 _ _ hx.1.1
      intro i hi
      simp [hi]
    · intro x hx y hy hxy
      rw [mem_coe, mem_product, mem_filter] at hx hy
      have hpt := congrFun hxy
      refine Prod.ext ?_ ?_
      · funext i
        by_cases hi : i ∈ A
        · rw [hx.1.2 i hi, hy.1.2 i hi]
        · have := hpt i
          simp only [hi, dite_false] at this
          exact this
      · funext j
        have := hpt j.1
        simp only [j.2, dite_true] at this
        exact this
  rw [card_product, card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] at key
  rw [mul_comm]
  exact key

lemma stepA {ι : Type u} [Fintype ι] [DecidableEq ι] (A : Finset ι) (G : Finset (ι → Bool))
    (hG : ∀ c c' : ι → Bool, (∀ i, i ∉ A → c i = c' i) → c ∈ G → c' ∈ G) :
    2 ^ A.card * (G.filter (fun c => ∃ b : Bool, ∀ i ∈ A, c i = b)).card ≤ 2 * G.card := by
  have hsub : G.filter (fun c => ∃ b : Bool, ∀ i ∈ A, c i = b) ⊆
      G.filter (fun c => ∀ i ∈ A, c i = true) ∪ G.filter (fun c => ∀ i ∈ A, c i = false) := by
    intro c hc
    rw [mem_filter] at hc
    obtain ⟨hcG, b, hb⟩ := hc
    rw [mem_union, mem_filter, mem_filter]
    cases b
    · exact Or.inr ⟨hcG, hb⟩
    · exact Or.inl ⟨hcG, hb⟩
  have h1 := stepA_const A G hG true
  have h2 := stepA_const A G hG false
  calc 2 ^ A.card * (G.filter (fun c => ∃ b : Bool, ∀ i ∈ A, c i = b)).card
      ≤ 2 ^ A.card * ((G.filter (fun c => ∀ i ∈ A, c i = true)).card
          + (G.filter (fun c => ∀ i ∈ A, c i = false)).card) := by
        apply Nat.mul_le_mul_left
        exact (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ 2 * G.card := by rw [mul_add]; omega

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- the r-subsets of `s` -/
abbrev Ed (r : ℕ) (s : Finset V) : Finset (Finset V) := s.powersetCard r

abbrev IsBad (r : ℕ) (s : Finset V) (c : Finset V → Bool) : Prop :=
  ∃ b : Bool, ∀ e ∈ Ed r s, c e = b

def Good (r : ℕ) (T : Finset (Finset V)) : Finset (Finset V → Bool) :=
  univ.filter (fun c => ∀ t ∈ T, ¬ IsBad r t c)

lemma mem_Good (r : ℕ) (T : Finset (Finset V)) (c : Finset V → Bool) :
    c ∈ Good r T ↔ ∀ t ∈ T, ¬ IsBad r t c := by
  simp [Good]

lemma Good_anti (r : ℕ) {T T' : Finset (Finset V)} (h : T' ⊆ T) : Good r T ⊆ Good r T' := by
  intro c hc
  rw [mem_Good] at hc ⊢
  exact fun t ht => hc t (h ht)

lemma Good_inv (r : ℕ) (s : Finset V) (T : Finset (Finset V))
    (hT : ∀ t ∈ T, Disjoint (Ed r s) (Ed r t)) :
    ∀ c c' : Finset V → Bool, (∀ i, i ∉ Ed r s → c i = c' i) → c ∈ Good r T → c' ∈ Good r T := by
  intro c c' hcc' hc
  rw [mem_Good] at hc ⊢
  intro t ht hbad
  apply hc t ht
  obtain ⟨b, hb⟩ := hbad
  refine ⟨b, fun e he => ?_⟩
  have hne : e ∉ Ed r s := Finset.disjoint_right.mp (hT t ht) he
  rw [hcc' e hne]
  exact hb e he

/-- Step B: degree bound. -/
lemma stepB (r k : ℕ) (s : Finset V) (hs : s.card = k) :
    (((univ : Finset V).powersetCard k).filter
        (fun t => ¬ Disjoint (Ed r s) (Ed r t))).card
      ≤ k.choose r * (Fintype.card V - r).choose (k - r) := by
  set K := (univ : Finset V).powersetCard k with hK
  have hsub : K.filter (fun t => ¬ Disjoint (Ed r s) (Ed r t)) ⊆
      (Ed r s).biUnion (fun e => K.filter (fun t => e ⊆ t)) := by
    intro t ht
    rw [mem_filter] at ht
    obtain ⟨htK, hnd⟩ := ht
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨e, he1, he2⟩ := hnd
    rw [mem_biUnion]
    refine ⟨e, he1, ?_⟩
    rw [mem_filter]
    exact ⟨htK, (mem_powersetCard.mp he2).1⟩
  have hone : ∀ e ∈ Ed r s,
      (K.filter (fun t => e ⊆ t)).card ≤ (Fintype.card V - r).choose (k - r) := by
    intro e he
    have hec : e.card = r := (mem_powersetCard.mp he).2
    have hcompl : (eᶜ).card = Fintype.card V - r := by rw [card_compl, hec]
    calc (K.filter (fun t => e ⊆ t)).card ≤ ((eᶜ).powersetCard (k - r)).card := by
          apply Finset.card_le_card_of_injOn (fun t => t \ e)
          · intro t ht
            rw [mem_coe, mem_filter, hK, mem_powersetCard] at ht
            rw [mem_coe, mem_powersetCard]
            refine ⟨?_, ?_⟩
            · intro x hx
              rw [mem_compl]
              exact (mem_sdiff.mp hx).2
            · rw [card_sdiff_of_subset ht.2, ht.1.2, hec]
          · intro t ht t' ht' htt
            rw [mem_coe, mem_filter] at ht ht'
            have h1 := sdiff_union_of_subset ht.2
            have h2 := sdiff_union_of_subset ht'.2
            simp only at htt
            rw [← h1, ← h2, htt]
      _ = (Fintype.card V - r).choose (k - r) := by rw [card_powersetCard, hcompl]
  calc (K.filter (fun t => ¬ Disjoint (Ed r s) (Ed r t))).card
      ≤ ((Ed r s).biUnion (fun e => K.filter (fun t => e ⊆ t))).card := card_le_card hsub
    _ ≤ ∑ e ∈ Ed r s, (K.filter (fun t => e ⊆ t)).card := card_biUnion_le
    _ ≤ ∑ _e ∈ Ed r s, (Fintype.card V - r).choose (k - r) := sum_le_sum hone
    _ = k.choose r * (Fintype.card V - r).choose (k - r) := by
        rw [sum_const, smul_eq_mul, card_powersetCard, hs]

/-- Counting Lovasz local lemma for monochromatic k-sets of r-subsets. -/
theorem lll_core (r k : ℕ) (hrk : r ≤ k) (hkn : k ≤ Fintype.card V)
    (hcond : (4 : ℝ) * (k.choose r : ℝ) * ((Fintype.card V - r).choose (k - r) : ℝ) *
      (2 : ℝ) ^ (1 - (k.choose r : ℝ)) < 1) :
    ∃ c : Finset V → Bool, ∀ s : Finset V, s.card = k → ¬ IsBad r s c := by
  set K := (univ : Finset V).powersetCard k with hK
  set m := k.choose r with hm
  set C := (Fintype.card V - r).choose (k - r) with hC
  set p : ℝ := 2 / 2 ^ m with hp
  have hp0 : 0 < p := by positivity
  have hrp : (2 : ℝ) ^ (1 - (m : ℝ)) = p := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  rw [hrp] at hcond
  have hC1 : 1 ≤ C := Nat.choose_pos (by omega)
  have hm1 : 1 ≤ m := Nat.choose_pos hrk
  have hC1r : (1 : ℝ) ≤ C := by exact_mod_cast hC1
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hDp : 2 * ((m * C : ℕ) : ℝ) * p ≤ 1 / 2 := by push_cast; nlinarith
  have hp4 : 2 * p ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ ((m * C : ℕ) : ℝ) := by push_cast; nlinarith
    nlinarith
  have hEd : ∀ s ∈ K, (Ed r s).card = m := by
    intro s hs
    rw [card_powersetCard, (mem_powersetCard.mp hs).2]
  -- Step A in real form
  have hA : ∀ s ∈ K, ∀ T : Finset (Finset V), (∀ t ∈ T, Disjoint (Ed r s) (Ed r t)) →
      (((Good r T).filter (IsBad r s)).card : ℝ) ≤ p * (Good r T).card := by
    intro s hs T hT
    have h := stepA (Ed r s) (Good r T) (Good_inv r s T hT)
    rw [hEd s hs] at h
    have h' : (2 : ℝ) ^ m * (((Good r T).filter (IsBad r s)).card : ℝ) ≤ 2 * (Good r T).card := by
      exact_mod_cast h
    rw [hp, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  -- Step C
  have claim : ∀ T : Finset (Finset V), T ⊆ K → ∀ s ∈ K, s ∉ T →
      (((Good r T).filter (IsBad r s)).card : ℝ) ≤ 2 * p * (Good r T).card := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
    intro hTK s hs hsT
    set T2 := T.filter (fun t => Disjoint (Ed r s) (Ed r t)) with hT2
    set T1 := T.filter (fun t => ¬ Disjoint (Ed r s) (Ed r t)) with hT1
    have hT2T : T2 ⊆ T := filter_subset _ _
    have hT2K : T2 ⊆ K := hT2T.trans hTK
    have h1 : ((Good r T).filter (IsBad r s)).card ≤ ((Good r T2).filter (IsBad r s)).card :=
      card_le_card (filter_subset_filter _ (Good_anti r hT2T))
    have h2 := hA s hs T2 (fun t ht => (mem_filter.mp ht).2)
    have h3 : (Good r T2).card ≤ (Good r T).card +
        ∑ t ∈ T1, ((Good r T2).filter (IsBad r t)).card := by
      have hsub : Good r T2 ⊆ Good r T ∪ T1.biUnion (fun t => (Good r T2).filter (IsBad r t)) := by
        intro c hc
        by_cases hcT : c ∈ Good r T
        · exact mem_union_left _ hcT
        · apply mem_union_right
          rw [mem_Good] at hcT
          push_neg at hcT
          obtain ⟨t, htT, hbad⟩ := hcT
          rw [mem_biUnion]
          refine ⟨t, ?_, mem_filter.mpr ⟨hc, hbad⟩⟩
          rw [hT1, mem_filter]
          refine ⟨htT, fun hdis => ?_⟩
          exact (mem_Good r T2 c).mp hc t (mem_filter.mpr ⟨htT, hdis⟩) hbad
      calc (Good r T2).card
          ≤ (Good r T ∪ T1.biUnion (fun t => (Good r T2).filter (IsBad r t))).card :=
            card_le_card hsub
        _ ≤ (Good r T).card + (T1.biUnion (fun t => (Good r T2).filter (IsBad r t))).card :=
            card_union_le _ _
        _ ≤ (Good r T).card + ∑ t ∈ T1, ((Good r T2).filter (IsBad r t)).card := by
            have := card_biUnion_le (s := T1) (t := fun t => (Good r T2).filter (IsBad r t))
            omega
    have h4 : ∀ t ∈ T1,
        (((Good r T2).filter (IsBad r t)).card : ℝ) ≤ 2 * p * (Good r T2).card := by
      intro t ht
      rw [hT1, mem_filter] at ht
      have hss : T2 ⊂ T := filter_ssubset.mpr ⟨t, ht.1, by simpa using ht.2⟩
      apply ih T2 hss hT2K t (hTK ht.1)
      intro htT2
      exact ht.2 (mem_filter.mp htT2).2
    have h5 : T1.card ≤ m * C := by
      have := stepB r k s (mem_powersetCard.mp hs).2
      refine le_trans (card_le_card ?_) this
      intro t ht
      rw [hT1, mem_filter] at ht
      rw [mem_filter]
      exact ⟨hTK ht.1, ht.2⟩
    have h3r : ((Good r T2).card : ℝ) ≤ (Good r T).card +
        ∑ t ∈ T1, (((Good r T2).filter (IsBad r t)).card : ℝ) := by exact_mod_cast h3
    have hsum : ∑ t ∈ T1, (((Good r T2).filter (IsBad r t)).card : ℝ) ≤
        (T1.card : ℝ) * (2 * p * (Good r T2).card) := by
      have := Finset.sum_le_card_nsmul T1 (fun t => (((Good r T2).filter (IsBad r t)).card : ℝ))
        (2 * p * (Good r T2).card) h4
      simpa [nsmul_eq_mul] using this
    have h5r : (T1.card : ℝ) ≤ ((m * C : ℕ) : ℝ) := by exact_mod_cast h5
    have hY2 : (0 : ℝ) ≤ (Good r T2).card := by positivity
    have hbig : (T1.card : ℝ) * (2 * p * (Good r T2).card) ≤ (1 / 2) * (Good r T2).card := by
      have e1 : (T1.card : ℝ) * (2 * p * (Good r T2).card) ≤
          ((m * C : ℕ) : ℝ) * (2 * p * (Good r T2).card) :=
        mul_le_mul_of_nonneg_right h5r (by positivity)
      have e2 : ((m * C : ℕ) : ℝ) * (2 * p * (Good r T2).card) =
          (2 * ((m * C : ℕ) : ℝ) * p) * (Good r T2).card := by
        ring
      rw [e2] at e1
      nlinarith
    have hY : ((Good r T2).card : ℝ) ≤ 2 * (Good r T).card := by linarith
    have h1r : (((Good r T).filter (IsBad r s)).card : ℝ) ≤
        ((Good r T2).filter (IsBad r s)).card := by
      exact_mod_cast h1
    calc (((Good r T).filter (IsBad r s)).card : ℝ) ≤ ((Good r T2).filter (IsBad r s)).card := h1r
      _ ≤ p * (Good r T2).card := h2
      _ ≤ p * (2 * (Good r T).card) := mul_le_mul_of_nonneg_left hY hp0.le
      _ = 2 * p * (Good r T).card := by ring
  -- Step D
  have hpos : ∀ T : Finset (Finset V), T ⊆ K → 0 < (Good r T).card := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      apply card_pos.mpr
      refine ⟨fun _ => true, ?_⟩
      rw [mem_Good]
      intro t ht
      simp at ht
    | insert s T hsT ih =>
      intro hTK
      have hTK' : T ⊆ K := (subset_insert _ _).trans hTK
      have hsK : s ∈ K := hTK (mem_insert_self _ _)
      have hY := ih hTK'
      have hc := claim T hTK' s hsK hsT
      have hsplit := card_filter_add_card_filter_not (s := Good r T) (IsBad r s)
      have hsub : (Good r T).filter (fun c => ¬ IsBad r s c) ⊆ Good r (insert s T) := by
        intro c hc'
        rw [mem_filter] at hc'
        rw [mem_Good] at hc' ⊢
        intro t ht
        rcases mem_insert.mp ht with h | h
        · rw [h]; exact hc'.2
        · exact hc'.1 t h
      have hle := card_le_card hsub
      have hYr : (0 : ℝ) < (Good r T).card := by exact_mod_cast hY
      have hsplitr : (((Good r T).filter (IsBad r s)).card : ℝ) +
          ((Good r T).filter (fun c => ¬ IsBad r s c)).card = (Good r T).card := by
        exact_mod_cast hsplit
      have hfr : (0 : ℝ) < ((Good r T).filter (fun c => ¬ IsBad r s c)).card := by nlinarith
      have hf : 0 < ((Good r T).filter (fun c => ¬ IsBad r s c)).card := by exact_mod_cast hfr
      omega
  obtain ⟨c, hc⟩ := card_pos.mp (hpos K (subset_refl _))
  refine ⟨c, fun s hs => ?_⟩
  rw [mem_Good] at hc
  apply hc s
  rw [hK, mem_powersetCard]
  exact ⟨subset_univ _, hs⟩

end Erdos77Aux2d30

theorem solution (V : Type*) [Fintype V]
    [DecidableEq V] (r k : Nat) (hr : 1 <= r) (hrk : r <= k)
    (hkn : k <= Fintype.card V)
    (hcond :
      (4 : Real) * (Nat.choose k r : Real) *
          (Nat.choose (Fintype.card V - r) (k - r) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k r : Real)) < 1) :
    Exists fun c : {e : Finset V // e.card = r} -> Bool =>
      forall s : Finset V, s.card = k ->
        And
          (Exists fun e : {e : Finset V // e.card = r} =>
            And (forall v : V, Membership.mem (e : Finset V) v -> Membership.mem s v) (c e = true))
          (Exists fun e : {e : Finset V // e.card = r} =>
            And (forall v : V, Membership.mem (e : Finset V) v -> Membership.mem s v) (c e = false)) := by
  obtain ⟨c, hc⟩ := Erdos77Aux2d30.lll_core (V := V) r k hrk hkn hcond
  refine ⟨fun e => c e.1, fun s hs => ⟨?_, ?_⟩⟩
  · by_contra hno
    apply hc s hs
    refine ⟨false, fun e he => ?_⟩
    obtain ⟨hes, he2⟩ := Finset.mem_powersetCard.mp he
    cases hce : c e
    · rfl
    · exact absurd ⟨⟨e, he2⟩, fun v hv => hes hv, hce⟩ hno
  · by_contra hno
    apply hc s hs
    refine ⟨true, fun e he => ?_⟩
    obtain ⟨hes, he2⟩ := Finset.mem_powersetCard.mp he
    cases hce : c e
    · exact absurd ⟨⟨e, he2⟩, fun v hv => hes hv, hce⟩ hno
    · rfl
