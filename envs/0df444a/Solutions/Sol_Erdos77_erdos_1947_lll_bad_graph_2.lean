-- Prove2me | solution 2 for Erdos77.erdos_1947_lll_bad_graph
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T08:41:41.816012+00:00
-- url     : https://prove2.me/submissions/a6f3dd30-e73d-40e8-a963-199aa97ed7e1

import Mathlib

set_option autoImplicit false

namespace Erdos77Aux5de4

open Finset

/-- Step A (one colour class): modifying coordinates in `A` keeps `G`, so the constant-`b` part is small. -/
lemma stepA_const {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (G : Finset (ι → Bool))
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

lemma stepA {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (G : Finset (ι → Bool))
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

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the edges (2-subsets) of `s` -/
abbrev Ed (s : Finset V) : Finset (Finset V) := s.powersetCard 2

abbrev IsBad (s : Finset V) (c : Finset V → Bool) : Prop := ∃ b : Bool, ∀ e ∈ Ed s, c e = b

def Good (T : Finset (Finset V)) : Finset (Finset V → Bool) :=
  univ.filter (fun c => ∀ t ∈ T, ¬ IsBad t c)

lemma mem_Good (T : Finset (Finset V)) (c : Finset V → Bool) :
    c ∈ Good T ↔ ∀ t ∈ T, ¬ IsBad t c := by
  simp [Good]

lemma Good_anti {T T' : Finset (Finset V)} (h : T' ⊆ T) : Good T ⊆ Good T' := by
  intro c hc
  rw [mem_Good] at hc ⊢
  exact fun t ht => hc t (h ht)

lemma Good_inv (s : Finset V) (T : Finset (Finset V)) (hT : ∀ t ∈ T, Disjoint (Ed s) (Ed t)) :
    ∀ c c' : Finset V → Bool, (∀ i, i ∉ Ed s → c i = c' i) → c ∈ Good T → c' ∈ Good T := by
  intro c c' hcc' hc
  rw [mem_Good] at hc ⊢
  intro t ht hbad
  apply hc t ht
  obtain ⟨b, hb⟩ := hbad
  refine ⟨b, fun e he => ?_⟩
  have hne : e ∉ Ed s := Finset.disjoint_right.mp (hT t ht) he
  rw [hcc' e hne]
  exact hb e he

/-- Step B: degree bound. -/
lemma stepB (k : ℕ) (s : Finset V) (hs : s.card = k) :
    (((univ : Finset V).powersetCard k).filter
        (fun t => ¬ Disjoint (Ed s) (Ed t))).card
      ≤ k.choose 2 * (Fintype.card V - 2).choose (k - 2) := by
  set K := (univ : Finset V).powersetCard k with hK
  have hsub : K.filter (fun t => ¬ Disjoint (Ed s) (Ed t)) ⊆
      (Ed s).biUnion (fun e => K.filter (fun t => e ⊆ t)) := by
    intro t ht
    rw [mem_filter] at ht
    obtain ⟨htK, hnd⟩ := ht
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨e, he1, he2⟩ := hnd
    rw [mem_biUnion]
    refine ⟨e, he1, ?_⟩
    rw [mem_filter]
    exact ⟨htK, (mem_powersetCard.mp he2).1⟩
  have hone : ∀ e ∈ Ed s, (K.filter (fun t => e ⊆ t)).card ≤ (Fintype.card V - 2).choose (k - 2) := by
    intro e he
    have hec : e.card = 2 := (mem_powersetCard.mp he).2
    have hcompl : (eᶜ).card = Fintype.card V - 2 := by rw [card_compl, hec]
    calc (K.filter (fun t => e ⊆ t)).card ≤ ((eᶜ).powersetCard (k - 2)).card := by
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
      _ = (Fintype.card V - 2).choose (k - 2) := by rw [card_powersetCard, hcompl]
  calc (K.filter (fun t => ¬ Disjoint (Ed s) (Ed t))).card
      ≤ ((Ed s).biUnion (fun e => K.filter (fun t => e ⊆ t))).card := card_le_card hsub
    _ ≤ ∑ e ∈ Ed s, (K.filter (fun t => e ⊆ t)).card := card_biUnion_le
    _ ≤ ∑ _e ∈ Ed s, (Fintype.card V - 2).choose (k - 2) := sum_le_sum hone
    _ = k.choose 2 * (Fintype.card V - 2).choose (k - 2) := by
        rw [sum_const, smul_eq_mul, card_powersetCard, hs]

/-- Counting Lovasz local lemma for monochromatic k-sets of 2-subsets. -/
theorem lll_core (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ Fintype.card V)
    (hcond : (4 : ℝ) * (k.choose 2 : ℝ) * ((Fintype.card V - 2).choose (k - 2) : ℝ) *
      (2 : ℝ) ^ (1 - (k.choose 2 : ℝ)) < 1) :
    ∃ c : Finset V → Bool, ∀ s : Finset V, s.card = k → ¬ IsBad s c := by
  set K := (univ : Finset V).powersetCard k with hK
  set m := k.choose 2 with hm
  set C := (Fintype.card V - 2).choose (k - 2) with hC
  set p : ℝ := 2 / 2 ^ m with hp
  have hp0 : 0 < p := by positivity
  have hrp : (2 : ℝ) ^ (1 - (m : ℝ)) = p := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  rw [hrp] at hcond
  have hC1 : 1 ≤ C := Nat.choose_pos (by omega)
  have hm1 : 1 ≤ m := Nat.choose_pos hk
  have hC1r : (1 : ℝ) ≤ C := by exact_mod_cast hC1
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hDp : 2 * ((m * C : ℕ) : ℝ) * p ≤ 1 / 2 := by push_cast; nlinarith
  have hp4 : 2 * p ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ ((m * C : ℕ) : ℝ) := by push_cast; nlinarith
    nlinarith
  have hEd : ∀ s ∈ K, (Ed s).card = m := by
    intro s hs
    rw [card_powersetCard, (mem_powersetCard.mp hs).2]
  -- Step A in real form
  have hA : ∀ s ∈ K, ∀ T : Finset (Finset V), (∀ t ∈ T, Disjoint (Ed s) (Ed t)) →
      (((Good T).filter (IsBad s)).card : ℝ) ≤ p * (Good T).card := by
    intro s hs T hT
    have h := stepA (Ed s) (Good T) (Good_inv s T hT)
    rw [hEd s hs] at h
    have h' : (2 : ℝ) ^ m * (((Good T).filter (IsBad s)).card : ℝ) ≤ 2 * (Good T).card := by
      exact_mod_cast h
    rw [hp, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  -- Step C
  have claim : ∀ T : Finset (Finset V), T ⊆ K → ∀ s ∈ K, s ∉ T →
      (((Good T).filter (IsBad s)).card : ℝ) ≤ 2 * p * (Good T).card := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
    intro hTK s hs hsT
    set T2 := T.filter (fun t => Disjoint (Ed s) (Ed t)) with hT2
    set T1 := T.filter (fun t => ¬ Disjoint (Ed s) (Ed t)) with hT1
    have hT2T : T2 ⊆ T := filter_subset _ _
    have hT2K : T2 ⊆ K := hT2T.trans hTK
    have h1 : ((Good T).filter (IsBad s)).card ≤ ((Good T2).filter (IsBad s)).card :=
      card_le_card (filter_subset_filter _ (Good_anti hT2T))
    have h2 := hA s hs T2 (fun t ht => (mem_filter.mp ht).2)
    have h3 : (Good T2).card ≤ (Good T).card + ∑ t ∈ T1, ((Good T2).filter (IsBad t)).card := by
      have hsub : Good T2 ⊆ Good T ∪ T1.biUnion (fun t => (Good T2).filter (IsBad t)) := by
        intro c hc
        by_cases hcT : c ∈ Good T
        · exact mem_union_left _ hcT
        · apply mem_union_right
          rw [mem_Good] at hcT
          push_neg at hcT
          obtain ⟨t, htT, hbad⟩ := hcT
          rw [mem_biUnion]
          refine ⟨t, ?_, mem_filter.mpr ⟨hc, hbad⟩⟩
          rw [hT1, mem_filter]
          refine ⟨htT, fun hdis => ?_⟩
          exact (mem_Good T2 c).mp hc t (mem_filter.mpr ⟨htT, hdis⟩) hbad
      calc (Good T2).card ≤ (Good T ∪ T1.biUnion (fun t => (Good T2).filter (IsBad t))).card :=
            card_le_card hsub
        _ ≤ (Good T).card + (T1.biUnion (fun t => (Good T2).filter (IsBad t))).card :=
            card_union_le _ _
        _ ≤ (Good T).card + ∑ t ∈ T1, ((Good T2).filter (IsBad t)).card := by
            have := card_biUnion_le (s := T1) (t := fun t => (Good T2).filter (IsBad t))
            omega
    have h4 : ∀ t ∈ T1, (((Good T2).filter (IsBad t)).card : ℝ) ≤ 2 * p * (Good T2).card := by
      intro t ht
      rw [hT1, mem_filter] at ht
      have hss : T2 ⊂ T := filter_ssubset.mpr ⟨t, ht.1, by simpa using ht.2⟩
      apply ih T2 hss hT2K t (hTK ht.1)
      intro htT2
      exact ht.2 (mem_filter.mp htT2).2
    have h5 : T1.card ≤ m * C := by
      have := stepB k s (mem_powersetCard.mp hs).2
      refine le_trans (card_le_card ?_) this
      intro t ht
      rw [hT1, mem_filter] at ht
      rw [mem_filter]
      exact ⟨hTK ht.1, ht.2⟩
    have h3r : ((Good T2).card : ℝ) ≤ (Good T).card +
        ∑ t ∈ T1, (((Good T2).filter (IsBad t)).card : ℝ) := by exact_mod_cast h3
    have hsum : ∑ t ∈ T1, (((Good T2).filter (IsBad t)).card : ℝ) ≤
        (T1.card : ℝ) * (2 * p * (Good T2).card) := by
      have := Finset.sum_le_card_nsmul T1 (fun t => (((Good T2).filter (IsBad t)).card : ℝ))
        (2 * p * (Good T2).card) h4
      simpa [nsmul_eq_mul] using this
    have h5r : (T1.card : ℝ) ≤ ((m * C : ℕ) : ℝ) := by exact_mod_cast h5
    have hY2 : (0 : ℝ) ≤ (Good T2).card := by positivity
    have hbig : (T1.card : ℝ) * (2 * p * (Good T2).card) ≤ (1 / 2) * (Good T2).card := by
      have e1 : (T1.card : ℝ) * (2 * p * (Good T2).card) ≤ ((m * C : ℕ) : ℝ) * (2 * p * (Good T2).card) :=
        mul_le_mul_of_nonneg_right h5r (by positivity)
      have e2 : ((m * C : ℕ) : ℝ) * (2 * p * (Good T2).card) = (2 * ((m * C : ℕ) : ℝ) * p) * (Good T2).card := by
        ring
      rw [e2] at e1
      nlinarith
    have hY : ((Good T2).card : ℝ) ≤ 2 * (Good T).card := by linarith
    have h1r : (((Good T).filter (IsBad s)).card : ℝ) ≤ ((Good T2).filter (IsBad s)).card := by
      exact_mod_cast h1
    calc (((Good T).filter (IsBad s)).card : ℝ) ≤ ((Good T2).filter (IsBad s)).card := h1r
      _ ≤ p * (Good T2).card := h2
      _ ≤ p * (2 * (Good T).card) := mul_le_mul_of_nonneg_left hY hp0.le
      _ = 2 * p * (Good T).card := by ring
  -- Step D
  have hpos : ∀ T : Finset (Finset V), T ⊆ K → 0 < (Good T).card := by
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
      have hsplit := card_filter_add_card_filter_not (s := Good T) (IsBad s)
      have hsub : (Good T).filter (fun c => ¬ IsBad s c) ⊆ Good (insert s T) := by
        intro c hc'
        rw [mem_filter] at hc'
        rw [mem_Good] at hc' ⊢
        intro t ht
        rcases mem_insert.mp ht with h | h
        · rw [h]; exact hc'.2
        · exact hc'.1 t h
      have hle := card_le_card hsub
      have hYr : (0 : ℝ) < (Good T).card := by exact_mod_cast hY
      have hsplitr : (((Good T).filter (IsBad s)).card : ℝ) +
          ((Good T).filter (fun c => ¬ IsBad s c)).card = (Good T).card := by
        exact_mod_cast hsplit
      have hfr : (0 : ℝ) < ((Good T).filter (fun c => ¬ IsBad s c)).card := by nlinarith
      have hf : 0 < ((Good T).filter (fun c => ¬ IsBad s c)).card := by exact_mod_cast hfr
      omega
  obtain ⟨c, hc⟩ := card_pos.mp (hpos K (subset_refl _))
  refine ⟨c, fun s hs => ?_⟩
  rw [mem_Good] at hc
  apply hc s
  rw [hK, mem_powersetCard]
  exact ⟨subset_univ _, hs⟩

end Erdos77Aux5de4

theorem solution (k n : Nat) (hk : 2 <= k) (hkn : k <= n)
    (hcond : (4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
      (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun G : SimpleGraph (Fin n) =>
      And
        (Not (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin n) =>
          And (s.card = k) ((Compl.compl G).IsClique s))) := by
  obtain ⟨c, hc⟩ := Erdos77Aux5de4.lll_core (V := Fin n) k hk (by rw [Fintype.card_fin]; exact hkn)
    (by rw [Fintype.card_fin]; exact hcond)
  let G : SimpleGraph (Fin n) :=
    { Adj := fun a b => a ≠ b ∧ c {a, b} = true
      symm := ⟨fun a b h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
      loopless := ⟨fun a h => h.1 rfl⟩ }
  refine ⟨G, ?_, ?_⟩
  · rintro ⟨s, hs, hcl⟩
    apply hc s hs
    refine ⟨true, fun e he => ?_⟩
    obtain ⟨hes, he2⟩ := Finset.mem_powersetCard.mp he
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he2
    have hx : x ∈ s := hes (by simp)
    have hy : y ∈ s := hes (by simp)
    exact (hcl (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy).2
  · rintro ⟨s, hs, hcl⟩
    apply hc s hs
    refine ⟨false, fun e he => ?_⟩
    obtain ⟨hes, he2⟩ := Finset.mem_powersetCard.mp he
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he2
    have hx : x ∈ s := hes (by simp)
    have hy : y ∈ s := hes (by simp)
    have hadj := hcl (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
    rw [SimpleGraph.compl_adj] at hadj
    have hn : ¬ (x ≠ y ∧ c {x, y} = true) := hadj.2
    cases hcv : c {x, y}
    · rfl
    · exact absurd ⟨hxy, hcv⟩ hn
