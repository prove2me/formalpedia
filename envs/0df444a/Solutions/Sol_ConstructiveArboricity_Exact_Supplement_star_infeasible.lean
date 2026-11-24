-- Prove2me | solution 1 for ConstructiveArboricity.Exact.Supplement.star_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T22:00:13.635166+00:00
-- url     : https://prove2.me/submissions/8efa5463-2783-4f79-a29d-17fdc2860c32

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_StarNetwork

open Classical Finset

namespace StarFlow

variable {N : Type*} [Fintype N] [DecidableEq N]

noncomputable def exc (ψ : N × N → ℤ) (x : N) : ℤ :=
  (∑ a, if a.2 = x then ψ a else 0) - ∑ a, if a.1 = x then ψ a else 0

lemma exc_update (ψ : N × N → ℤ) (a0 : N × N) (δ : ℤ) (x : N) :
    exc (fun a => ψ a + if a = a0 then δ else 0) x =
      exc ψ x + (if a0.2 = x then δ else 0) - (if a0.1 = x then δ else 0) := by
  have key : ∀ (p : N × N → Prop) [DecidablePred p],
      (∑ a, if p a then ψ a + (if a = a0 then δ else 0) else 0) =
        (∑ a, if p a then ψ a else 0) + (if p a0 then δ else 0) := by
    intro p _
    have : ∀ a, (if p a then ψ a + (if a = a0 then δ else 0) else 0) =
        (if p a then ψ a else 0) + (if a = a0 then (if p a then δ else 0) else 0) := by
      intro a
      by_cases h2 : a = a0
      · subst h2; by_cases h1 : p a <;> simp [h1]
      · by_cases h1 : p a <;> simp [h1, h2]
    simp only [this, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq' Finset.univ a0]
    simp
  unfold exc
  rw [key (fun a => a.2 = x), key (fun a => a.1 = x)]
  ring

lemma exc_nat (c : N × N → ℕ) (s t : N) (ψ : N × N → ℕ) (z : N) :
    exc (fun a => (ψ a : ℤ)) z =
      (∑ a ∈ univ.filter (fun a : N × N => a.2 = z), (ψ a : ℤ)) -
        ∑ a ∈ univ.filter (fun a : N × N => a.1 = z), (ψ a : ℤ) := by
  simp [exc, Finset.sum_filter]

def Reach (R : N → N → Prop) (s : N) : ℕ → N → Prop
  | 0, x => x = s
  | n+1, x => ∃ y, Reach R s n y ∧ R y x

def Lay (R : N → N → Prop) (s : N) (n : ℕ) (x : N) : Prop := ∃ m ≤ n, Reach R s m x

lemma lay_mono {R : N → N → Prop} {s : N} {n m : ℕ} {x : N} (h : n ≤ m) (hx : Lay R s n x) :
    Lay R s m x := by
  obtain ⟨k, hk, hr⟩ := hx
  exact ⟨k, le_trans hk h, hr⟩

lemma lay_succ {R : N → N → Prop} {s : N} {n : ℕ} {x : N} (hx : Lay R s (n+1) x) :
    Lay R s n x ∨ Reach R s (n+1) x := by
  obtain ⟨k, hk, hr⟩ := hx
  rcases Nat.lt_or_ge k (n+1) with h | h
  · left; exact ⟨k, by omega, hr⟩
  · right; have : k = n+1 := by omega
    subst this; exact hr

theorem augment (c : N × N → ℕ) (s t : N) (φ : N × N → ℕ)
    (R : N → N → Prop)
    (hR : ∀ u w, R u w → (φ (u, w) < c (u, w) ∨ 0 < φ (w, u)))
    (hφ : ∀ a, φ a ≤ c a)
    (n : ℕ) : ∀ x, Lay R s n x → ∃ ψ : N × N → ℤ, (∀ a, 0 ≤ ψ a ∧ ψ a ≤ c a) ∧
      (∀ z, exc ψ z = exc (fun a => (φ a : ℤ)) z + (if z = x then 1 else 0) - (if z = s then 1 else 0)) ∧
      (∀ a, ψ a ≠ φ a → Lay R s n a.1 ∧ Lay R s n a.2) := by
  induction n with
  | zero =>
    intro x hx
    obtain ⟨m, hm, hr⟩ := hx
    have : m = 0 := by omega
    subst this
    have hxs : x = s := hr
    subst hxs
    refine ⟨fun a => (φ a : ℤ), fun a => ⟨by positivity, Nat.cast_le.mpr (hφ a)⟩, ?_, ?_⟩
    · intro z; simp
    · intro a ha; exact absurd rfl ha
  | succ n ih =>
    intro x hx
    rcases lay_succ hx with hx | hx
    · obtain ⟨ψ, h1, h2, h3⟩ := ih x hx
      exact ⟨ψ, h1, h2, fun a ha => ⟨lay_mono (Nat.le_succ n) (h3 a ha).1,
        lay_mono (Nat.le_succ n) (h3 a ha).2⟩⟩
    · by_cases hxn : Lay R s n x
      · obtain ⟨ψ, h1, h2, h3⟩ := ih x hxn
        exact ⟨ψ, h1, h2, fun a ha => ⟨lay_mono (Nat.le_succ n) (h3 a ha).1,
          lay_mono (Nat.le_succ n) (h3 a ha).2⟩⟩
      obtain ⟨y, hy, hyx⟩ := hx
      have hyl : Lay R s n y := ⟨n, le_refl _, hy⟩
      obtain ⟨ψ, h1, h2, h3⟩ := ih y hyl
      have hxy : x ≠ y := fun h => hxn (h ▸ hyl)
      have hyx' : y ≠ x := fun h => hxy h.symm
      have u1 : ψ (y, x) = φ (y, x) := by
        by_contra hne; exact hxn (h3 _ hne).2
      have u2 : ψ (x, y) = φ (x, y) := by
        by_contra hne; exact hxn (h3 _ hne).1
      have hxl : Lay R s (n+1) x := ⟨n+1, le_refl _, ⟨y, hy, hyx⟩⟩
      have hyl' : Lay R s (n+1) y := lay_mono (Nat.le_succ n) hyl
      rcases hR y x hyx with hlt | hpos
      · refine ⟨fun a => ψ a + if a = (y, x) then 1 else 0, ?_, ?_, ?_⟩
        · intro a
          by_cases ha : a = (y, x)
          · subst ha
            have := h1 (y, x)
            simp only [if_true]
            rw [u1] at this
            exact ⟨by omega, by have : (φ (y, x) : ℤ) < c (y, x) := by exact_mod_cast hlt
                                omega⟩
          · simp only [ha, if_false, add_zero]; exact h1 a
        · intro z
          rw [exc_update, h2 z]
          split_ifs <;> subst_vars <;> first | ring1 | contradiction | simp_all
        · intro a ha
          by_cases hae : a = (y, x)
          · subst hae; exact ⟨hyl', hxl⟩
          · simp only [hae, if_false, add_zero] at ha
            exact ⟨lay_mono (Nat.le_succ n) (h3 a ha).1, lay_mono (Nat.le_succ n) (h3 a ha).2⟩
      · refine ⟨fun a => ψ a + if a = (x, y) then -1 else 0, ?_, ?_, ?_⟩
        · intro a
          by_cases ha : a = (x, y)
          · subst ha
            have := h1 (x, y)
            simp only [if_true]
            rw [u2] at this
            have h0 : (0 : ℤ) < φ (x, y) := by exact_mod_cast hpos
            exact ⟨by omega, by omega⟩
          · simp only [ha, if_false, add_zero]; exact h1 a
        · intro z
          rw [exc_update, h2 z]
          split_ifs <;> subst_vars <;> first | ring1 | contradiction | simp_all
        · intro a ha
          by_cases hae : a = (x, y)
          · subst hae; exact ⟨hxl, hyl'⟩
          · simp only [hae, if_false, add_zero] at ha
            exact ⟨lay_mono (Nat.le_succ n) (h3 a ha).1, lay_mono (Nat.le_succ n) (h3 a ha).2⟩

open OneTwoThree.Weighting in
lemma flowValue_eq (s : N) (f : N × N → ℕ) :
    flowValue Prod.fst Prod.snd s f = - exc (fun a => (f a : ℤ)) s := by
  rw [exc_nat (fun _ => 0) s s]
  unfold flowValue
  ring

open OneTwoThree.Weighting in
theorem exists_cut (c : N × N → ℕ) (s t : N) (hst : s ≠ t) (φ : N × N → ℕ)
    (hφ : IsSTFlow Prod.fst Prod.snd c s t φ)
    (hmax : ∀ ψ : N × N → ℕ, IsSTFlow Prod.fst Prod.snd c s t ψ →
      flowValue Prod.fst Prod.snd s ψ ≤ flowValue Prod.fst Prod.snd s φ) :
    ∃ S : Set N, s ∈ S ∧ t ∉ S ∧
      (∑ a ∈ univ.filter (fun a : N × N => a.1 ∈ S ∧ a.2 ∉ S), (c a : ℤ)) =
        flowValue Prod.fst Prod.snd s φ := by
  classical
  set R : N → N → Prop := fun u w => φ (u, w) < c (u, w) ∨ 0 < φ (w, u) with hRdef
  set S : Set N := {x | ∃ n, Reach R s n x} with hS
  have hsS : s ∈ S := ⟨0, rfl⟩
  have hcl : ∀ u w, u ∈ S → R u w → w ∈ S := by
    rintro u w ⟨n, hn⟩ h; exact ⟨n+1, u, hn, h⟩
  have hφc : ∀ a, φ a ≤ c a := hφ.1
  have hcons : ∀ x, x ≠ s → x ≠ t → exc (fun a => (φ a : ℤ)) x = 0 := by
    intro x h1 h2
    rw [exc_nat (fun _ => 0) s t]
    have := hφ.2 x h1 h2
    have h' : (∑ a ∈ univ.filter (fun a : N × N => a.2 = x), (φ a : ℤ)) =
        ∑ a ∈ univ.filter (fun a : N × N => a.1 = x), (φ a : ℤ) := by exact_mod_cast this
    simpa [sub_eq_zero] using h'
  have htS : t ∉ S := by
    rintro ⟨n, hn⟩
    obtain ⟨ψ, h1, h2, -⟩ := augment c s t φ R (fun u w h => h) hφc n t ⟨n, le_refl _, hn⟩
    have hcast : ∀ a, (((ψ a).toNat : ℕ) : ℤ) = ψ a := fun a => Int.toNat_of_nonneg (h1 a).1
    have hexc : ∀ z, exc (fun a => (((ψ a).toNat : ℕ) : ℤ)) z = exc ψ z := by
      intro z; simp only [hcast]
    have hfl : IsSTFlow Prod.fst Prod.snd c s t (fun a => (ψ a).toNat) := by
      refine ⟨fun a => ?_, fun x hx1 hx2 => ?_⟩
      · have := (h1 a).2; show (ψ a).toNat ≤ c a; omega
      · have h0 : exc (fun a => (((ψ a).toNat : ℕ) : ℤ)) x = 0 := by
          rw [hexc, h2 x, hcons x hx1 hx2]; simp [hx1, hx2]
        rw [exc_nat (fun _ => 0) s t] at h0
        have h0' : (∑ a ∈ univ.filter (fun a : N × N => a.2 = x), (((ψ a).toNat : ℕ) : ℤ)) =
            ∑ a ∈ univ.filter (fun a : N × N => a.1 = x), (((ψ a).toNat : ℕ) : ℤ) := by
          rw [← sub_eq_zero]; exact h0
        exact_mod_cast h0'
    have := hmax _ hfl
    rw [flowValue_eq, flowValue_eq, hexc, h2 s, ← neg_le_neg_iff] at this
    simp [hst] at this
  have hcut1 : ∀ a : N × N, a.1 ∈ S → a.2 ∉ S → φ a = c a := by
    intro a h1 h2
    by_contra hne
    apply h2
    apply hcl a.1 a.2 h1
    left; exact lt_of_le_of_ne (hφc a) hne
  have hcut2 : ∀ a : N × N, a.1 ∉ S → a.2 ∈ S → φ a = 0 := by
    intro a h1 h2
    by_contra hne
    apply h1
    apply hcl a.2 a.1 h2
    right; exact Nat.pos_of_ne_zero hne
  refine ⟨S, hsS, htS, ?_⟩
  -- sum of excesses over S
  have hsum1 : (∑ x, if x ∈ S then exc (fun a => (φ a : ℤ)) x else 0) =
      exc (fun a => (φ a : ℤ)) s := by
    rw [Finset.sum_eq_single s]
    · simp [hsS]
    · intro x _ hx
      by_cases hxS : x ∈ S
      · have : x ≠ t := fun h => htS (h ▸ hxS)
        simp [hcons x hx this]
      · simp [hxS]
    · simp
  have hsum2 : (∑ x, if x ∈ S then exc (fun a => (φ a : ℤ)) x else 0) =
      (∑ a : N × N, ((if a.2 ∈ S then (φ a : ℤ) else 0) - if a.1 ∈ S then (φ a : ℤ) else 0)) := by
    have e1 : ∀ (g : N × N → N) (f : N × N → ℤ),
        (∑ x, if x ∈ S then ∑ a, (if g a = x then f a else 0) else 0) =
          ∑ a, if g a ∈ S then f a else 0 := by
      intro g f
      have : ∀ x, (if x ∈ S then ∑ a, (if g a = x then f a else 0) else 0) =
          ∑ a, (if g a = x ∧ x ∈ S then f a else 0) := by
        intro x
        by_cases hx : x ∈ S <;> simp [hx]
      simp only [this]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ∀ x, (if g a = x ∧ x ∈ S then f a else 0) = if x = g a then (if g a ∈ S then f a else 0) else 0 := by
        intro x
        by_cases h : x = g a
        · subst h; by_cases h2 : g a ∈ S <;> simp [h2]
        · simp [h, Ne.symm h]
      simp only [this]
      simp
    have hA := e1 Prod.snd (fun a => (φ a : ℤ))
    have hB := e1 Prod.fst (fun a => (φ a : ℤ))
    calc (∑ x, if x ∈ S then exc (fun a => (φ a : ℤ)) x else 0)
        = ∑ x, ((if x ∈ S then ∑ a : N × N, (if a.2 = x then (φ a : ℤ) else 0) else 0) -
            (if x ∈ S then ∑ a : N × N, (if a.1 = x then (φ a : ℤ) else 0) else 0)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x ∈ S <;> simp [hx, exc]
      _ = _ := by rw [Finset.sum_sub_distrib, hA, hB, Finset.sum_sub_distrib]
  have hsum3 : (∑ a : N × N, ((if a.2 ∈ S then (φ a : ℤ) else 0) - if a.1 ∈ S then (φ a : ℤ) else 0)) =
      - ∑ a ∈ univ.filter (fun a : N × N => a.1 ∈ S ∧ a.2 ∉ S), (c a : ℤ) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h1 : a.1 ∈ S <;> by_cases h2 : a.2 ∈ S
    · simp [h1, h2]
    · simp [h1, h2, hcut1 a h1 h2]
    · simp [h1, h2, hcut2 a h1 h2]
    · simp [h1, h2]
  rw [flowValue_eq, ← hsum1, hsum2, hsum3]
  ring

end StarFlow
namespace ConstructiveArboricity.Exact

lemma acyclic_edges_le {V : Type*} [Fintype V] [Nonempty V] (H : SimpleGraph V) (hH : H.IsAcyclic) :
    H.edgeFinset.card + 1 ≤ Fintype.card V := by
  obtain ⟨F, hHF, hF⟩ := SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic (le_top : H ≤ ⊤) hH
  have hmax : Maximal SimpleGraph.IsAcyclic F := by
    refine ⟨hF.1.2, fun H' hH' hle => ?_⟩
    exact hF.2 ⟨le_top, hH'⟩ hle
  have ht : F.IsTree := SimpleGraph.maximal_isAcyclic_iff_isTree.1 hmax
  have := ht.card_edgeFinset
  have h2 : H.edgeFinset.card ≤ F.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hHF)
  omega

lemma one_forest_edges (G : Graph) (T : Set (Fin G.m)) (hT : G.IsForest T)
    (X : Finset (Fin G.n)) (hX : X.Nonempty) :
    (univ.filter fun e => e ∈ T ∧ (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X).card + 1 ≤ X.card := by
  let x0 : X := ⟨hX.choose, hX.choose_spec⟩
  haveI : Nonempty X := ⟨x0⟩
  let Hx := (G.onEdges T).comap (fun v : X => v.1)
  have hac : Hx.IsAcyclic := SimpleGraph.IsAcyclic.of_comap (Function.Embedding.subtype _) hT
  have key := acyclic_edges_le Hx hac
  rw [Fintype.card_coe] at key
  refine le_trans (Nat.succ_le_succ ?_) key
  let f : Fin G.m → Sym2 X := fun e =>
    if h : (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X then s(⟨_, h.1⟩, ⟨_, h.2⟩) else s(x0, x0)
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro e he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he
    obtain ⟨heT, h1, h2⟩ := he
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_coe]
    simp only [f, dif_pos (And.intro h1 h2)]
    rw [SimpleGraph.mem_edgeSet]
    show (G.onEdges T).Adj (G.ends e).1 (G.ends e).2
    unfold Graph.onEdges
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨e, heT, rfl⟩, G.noLoops e⟩
  · intro e he e' he' hee
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he he'
    simp only [f, dif_pos (And.intro he.2.1 he.2.2), dif_pos (And.intro he'.2.1 he'.2.2)] at hee
    have := congrArg (Sym2.map Subtype.val) hee
    simp only [Sym2.map_pair_eq] at this
    exact G.simple this

lemma forest_partition_edges (G : Graph) (k : ℕ) (c : Fin G.m → Fin k) (hc : G.ForestPartition k c)
    (X : Finset (Fin G.n)) (hX : X.Nonempty) :
    (univ.filter fun e => (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X).card ≤ k * (X.card - 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := c) (t := (univ : Finset (Fin k))) (fun _ _ => Finset.mem_univ _)]
  have : ∀ i : Fin k, (Finset.filter (fun e => c e = i) (univ.filter fun e => (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X)).card ≤ X.card - 1 := by
    intro i
    have := one_forest_edges G {e | c e = i} (hc i) X hX
    have h2 : Finset.filter (fun e => c e = i) (univ.filter fun e => (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X) =
        univ.filter fun e => e ∈ {e | c e = i} ∧ (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X := by
      ext e; simp [and_comm, and_left_comm, and_assoc]
    rw [h2]; convert Nat.le_sub_of_add_le this using 2
    ext e; simp
  calc _ ≤ ∑ _i : Fin k, (X.card - 1) := Finset.sum_le_sum fun i _ => this i
    _ = k * (X.card - 1) := by simp

end ConstructiveArboricity.Exact

namespace StarFlow
open OneTwoThree.Weighting

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem cut_of_sSup (c : N × N → ℕ) (s t : N) (hst : s ≠ t) :
    ∃ S : Set N, s ∈ S ∧ t ∉ S ∧
      (∑ a ∈ univ.filter (fun a : N × N => a.1 ∈ S ∧ a.2 ∉ S), (c a : ℤ)) =
        ((sSup {v : ℕ | ∃ f, IsSTFlow Prod.fst Prod.snd c s t f ∧
          flowValue Prod.fst Prod.snd s f = (v : ℤ)} : ℕ) : ℤ) := by
  set V : Set ℕ := {v : ℕ | ∃ f, IsSTFlow Prod.fst Prod.snd c s t f ∧
          flowValue Prod.fst Prod.snd s f = (v : ℤ)} with hV
  have hne : V.Nonempty := by
    refine ⟨0, fun _ => 0, ⟨fun a => Nat.zero_le _, fun x _ _ => by simp⟩, ?_⟩
    simp [flowValue]
  have hbdd : BddAbove V := by
    refine ⟨∑ a, c a, ?_⟩
    rintro v ⟨f, hf, hfv⟩
    have h1 : (v : ℤ) ≤ ∑ a ∈ univ.filter (fun a : N × N => a.1 = s), (f a : ℤ) := by
      rw [← hfv]; unfold flowValue
      have : 0 ≤ ∑ a ∈ univ.filter (fun a : N × N => a.2 = s), (f a : ℤ) :=
        Finset.sum_nonneg fun _ _ => by positivity
      linarith
    have h2 : (∑ a ∈ univ.filter (fun a : N × N => a.1 = s), (f a : ℤ)) ≤ ∑ a, (c a : ℤ) := by
      calc _ ≤ ∑ a ∈ univ.filter (fun a : N × N => a.1 = s), (c a : ℤ) :=
            Finset.sum_le_sum fun a _ => by exact_mod_cast hf.1 a
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
    have : (v : ℤ) ≤ ((∑ a, c a : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨φ, hφ, hv⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ ψ : N × N → ℕ, IsSTFlow Prod.fst Prod.snd c s t ψ →
      flowValue Prod.fst Prod.snd s ψ ≤ flowValue Prod.fst Prod.snd s φ := by
    intro ψ hψ
    rw [hv]
    by_cases hneg : flowValue Prod.fst Prod.snd s ψ < 0
    · have : (0 : ℤ) ≤ (sSup V : ℕ) := by positivity
      omega
    · have hmem : (flowValue Prod.fst Prod.snd s ψ).toNat ∈ V :=
        ⟨ψ, hψ, (Int.toNat_of_nonneg (not_lt.1 hneg)).symm⟩
      have := le_csSup hbdd hmem
      have h3 := Int.toNat_of_nonneg (not_lt.1 hneg)
      omega
  obtain ⟨S, h1, h2, h3⟩ := exists_cut c s t hst φ hφ hmax
  exact ⟨S, h1, h2, by rw [h3, hv]⟩

end StarFlow

namespace ConstructiveArboricity.Exact.Supplement
open Classical Finset

def ovx (G : Graph) (r : Fin G.n) (e : Fin G.m) : Fin G.n :=
  if (G.ends e).1 = r then (G.ends e).2 else (G.ends e).1

lemma ovx_ne (G : Graph) (r : Fin G.n) (e : Fin G.m) : ovx G r e ≠ r := by
  unfold ovx
  split_ifs with h
  · intro h2; exact G.noLoops e (h.trans h2.symm)
  · exact h

lemma mem_starEdges (G : Graph) (r : Fin G.n) (e : Fin G.m) :
    e ∈ starEdges G r ↔ (G.ends e).1 = r ∨ (G.ends e).2 = r := by
  simp [starEdges]

lemma edge_ovx (G : Graph) (r : Fin G.n) (e : Fin G.m) (he : e ∈ starEdges G r) :
    G.edge e = s(r, ovx G r e) := by
  rw [mem_starEdges] at he
  unfold ovx Graph.edge
  by_cases h : (G.ends e).1 = r
  · simp [h]
  · have h2 : (G.ends e).2 = r := he.resolve_left h
    simp [h, h2, Sym2.eq_swap]

lemma ovx_inj (G : Graph) (r : Fin G.n) (e e' : Fin G.m) (he : e ∈ starEdges G r)
    (he' : e' ∈ starEdges G r) (h : ovx G r e = ovx G r e') : e = e' := by
  have : G.edge e = G.edge e' := by rw [edge_ovx G r e he, edge_ovx G r e' he', h]
  exact G.simple this

lemma ends_of_orient (G : Graph) (tail : Fin G.m → Fin G.n) (ho : G.IsOrientation tail)
    (e : Fin G.m) :
    ((G.ends e).1 = tail e ∧ (G.ends e).2 = G.head tail e) ∨
      ((G.ends e).1 = G.head tail e ∧ (G.ends e).2 = tail e) := by
  unfold Graph.head
  rcases ho e with h | h
  · left; simp [h]
  · right
    have : tail e ≠ (G.ends e).1 := by rw [h]; exact (G.noLoops e).symm
    refine ⟨?_, h.symm⟩
    simp [this]

lemma colored_ne {G : Graph} {k : ℕ} {r : Fin G.n} (a : StarInput G k r) (e : Fin G.m) (i : Fin k)
    (h : a.color e = some i) : (G.ends e).1 ≠ r ∧ (G.ends e).2 ≠ r := by
  have : e ∉ starEdges G r := fun hm => by
    have := (a.uncolored e).2 hm; rw [h] at this; simp at this
  rw [mem_starEdges] at this
  tauto

theorem core (G : Graph) {k : ℕ} {r : Fin G.n} (a : StarInput G k r) (o : Rooting G a)
    (col : Fin G.m → Fin k) (hcol : G.ForestPartition k col)
    (S : Set (StarNode G k r)) (hs : sourceNode G k r ∈ S) (ht : sinkNode G k r ∉ S)
    (hC : (∑ p ∈ univ.filter (fun p : StarNode G k r × StarNode G k r => p.1 ∈ S ∧ p.2 ∉ S),
      starCapacity G a o p) < (starEdges G r).card) : False := by
  set Cs := univ.filter (fun p : StarNode G k r × StarNode G k r => p.1 ∈ S ∧ p.2 ∉ S) with hCs
  have hmemCs : ∀ p, p ∈ Cs ↔ p.1 ∈ S ∧ p.2 ∉ S := by intro p; simp [hCs]
  have hm : (starEdges G r).card ≤ G.m := by
    simpa using Finset.card_le_univ (starEdges G r)
  have hA : ∀ (x : NonRoot G r) (i : Fin k), qNode x ∈ S ↔ qcNode x i ∈ S := by
    intro x i
    constructor
    · intro hx; by_contra hn
      have hmem : (qNode x, qcNode x i) ∈ Cs := (hmemCs _).2 ⟨hx, hn⟩
      have h1 := Finset.single_le_sum (f := starCapacity G a o) (fun _ _ => Nat.zero_le _) hmem
      have hc : starCapacity G a o (qNode x, qcNode x i) = G.m + 1 := by
        simp [starCapacity, qNode, qcNode]
      omega
    · intro hx; by_contra hn
      have hmem : (qcNode x i, qNode x) ∈ Cs := (hmemCs _).2 ⟨hx, hn⟩
      have h1 := Finset.single_le_sum (f := starCapacity G a o) (fun _ _ => Nat.zero_le _) hmem
      have hc : starCapacity G a o (qcNode x i, qNode x) = G.m + 1 := by
        simp [starCapacity, qNode, qcNode]
      omega
  let inX : Fin G.n → Prop := fun v => v = r ∨ ∃ h : v ≠ r, qNode (k := k) ⟨v, h⟩ ∈ S
  let X : Finset (Fin G.n) := univ.filter inX
  let Xs : Finset (NonRoot G r) := univ.filter (fun x => qNode (k := k) x ∈ S)
  have hrX : r ∈ X := by simp [X, inX]
  have hXcard : X.card = Xs.card + 1 := by
    have : X = insert r (Xs.image Subtype.val) := by
      ext v
      by_cases hv : v = r
      · subst hv; simp [X, inX]
      · simp only [X, inX, Xs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_image, hv, false_or]
        constructor
        · rintro ⟨h, hh⟩; exact ⟨⟨v, h⟩, hh, rfl⟩
        · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    rw [this, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ Subtype.val_injective]
    simp only [Finset.mem_image, not_exists, not_and]
    intro y _ h; exact y.2 h
  have hfor := ConstructiveArboricity.Exact.forest_partition_edges G k col hcol X ⟨r, hrX⟩
  rw [hXcard, Nat.add_sub_cancel] at hfor
  -- the star edges
  let nr : Fin G.m → NonRoot G r := fun e => ⟨ovx G r e, ovx_ne G r e⟩
  let Lv := (starEdges G r).filter (fun e => qNode (k := k) (nr e) ∉ S)
  let E1 := (starEdges G r).filter (fun e => qNode (k := k) (nr e) ∈ S)
  have hU : E1.card + Lv.card = (starEdges G r).card :=
    Finset.card_filter_add_card_filter_not _
  let stay : NonRoot G r × Fin k → Prop := fun p => ∃ e, ∃ y : NonRoot G r,
    a.color e = some p.2 ∧ o.tail e = p.1.1 ∧ G.head o.tail e = y.1 ∧ qcNode y p.2 ∈ S
  let LP := (Xs ×ˢ (univ : Finset (Fin k))).filter (fun p => ¬ stay p)
  let StayS := (Xs ×ˢ (univ : Finset (Fin k))).filter stay
  have hLP : StayS.card + LP.card = k * Xs.card := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_product]; simp [mul_comm]
  let E2 := (univ : Finset (Fin G.m)).filter
    (fun e => (a.color e).isSome ∧ (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X)
  let P1 := Cs.filter (fun p => p.1 = sourceNode G k r ∧ 1 ≤ starCapacity G a o p)
  let P2 := Cs.filter (fun p => (∃ (x : NonRoot G r) (i : Fin k), p.1 = qcNode x i) ∧
    1 ≤ starCapacity G a o p)
  have c1 : Lv.card ≤ P1.card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun e p => p = (sourceNode G k r, qNode (k := k) (nr e))) ?_ ?_
    · intro e he
      rw [Finset.mem_filter] at he
      refine ⟨(sourceNode G k r, qNode (nr e)), ?_, rfl⟩
      have hcap : starCapacity G a o (sourceNode G k r, qNode (nr e)) = 1 := by
        simp only [starCapacity, sourceNode, qNode, nr]
        rw [if_pos ⟨e, he.1, edge_ovx G r e he.1⟩]
      refine Finset.mem_filter.2 ⟨(hmemCs _).2 ⟨hs, he.2⟩, rfl, by rw [hcap]⟩
    · intro p _ e1 he1 e2 he2
      have h1 : (sourceNode G k r, qNode (k := k) (nr e1)) = (sourceNode G k r, qNode (nr e2)) := by
        rw [← he1.2, ← he2.2]
      have h2 : nr e1 = nr e2 := by
        have := congrArg Prod.snd h1
        simpa [qNode] using this
      have h3 : ovx G r e1 = ovx G r e2 := congrArg Subtype.val h2
      exact ovx_inj G r e1 e2 (Finset.mem_filter.1 he1.1).1 (Finset.mem_filter.1 he2.1).1 h3
  have c2 : LP.card ≤ P2.card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun (p : NonRoot G r × Fin k) b => b.1 = qcNode p.1 p.2) ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hx, -⟩, hns⟩ := hp
      obtain ⟨x, i⟩ := p
      have hxS : qNode (k := k) x ∈ S := (Finset.mem_filter.1 hx).2
      have hqc : qcNode x i ∈ S := (hA x i).1 hxS
      by_cases hfree : ∃ e, a.color e = some i ∧ o.tail e = x.1
      · obtain ⟨e, he1, he2⟩ := hfree
        have hh : G.head o.tail e ≠ r := by
          have := colored_ne a e i he1
          rcases ends_of_orient G o.tail o.oriented e with h | h
          · rw [← h.2]; exact this.2
          · rw [← h.1]; exact this.1
        have hn : qcNode (k := k) ⟨G.head o.tail e, hh⟩ i ∉ S := fun hin =>
          hns ⟨e, ⟨_, hh⟩, he1, he2, rfl, hin⟩
        have hcap : starCapacity G a o (qcNode x i, qcNode (k := k) ⟨G.head o.tail e, hh⟩ i) = 1 := by
          simp only [starCapacity, qcNode]
          rw [if_pos ⟨trivial, e, he1, he2, rfl⟩]
        exact ⟨(qcNode x i, qcNode ⟨G.head o.tail e, hh⟩ i),
          Finset.mem_filter.2 ⟨(hmemCs _).2 ⟨hqc, hn⟩, ⟨x, i, rfl⟩, by rw [hcap]⟩, rfl⟩
      · have hcap : starCapacity G a o (qcNode x i, sinkNode G k r) = 1 := by
          simp only [starCapacity, qcNode, sinkNode]
          rw [if_pos hfree]
        exact ⟨(qcNode x i, sinkNode G k r),
          Finset.mem_filter.2 ⟨(hmemCs _).2 ⟨hqc, ht⟩, ⟨x, i, rfl⟩, by rw [hcap]⟩, rfl⟩
    · intro b _ p hp p' hp'
      have : qcNode (k := k) p.1 p.2 = qcNode p'.1 p'.2 := by rw [← hp.2, ← hp'.2]
      simp only [qcNode, Sum.inr.injEq, Prod.mk.injEq] at this
      exact Prod.ext this.1 this.2
  have hinX : ∀ x : NonRoot G r, qNode (k := k) x ∈ S → x.1 ∈ X := fun x hx =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨x.2, hx⟩⟩
  have c3 : StayS.card ≤ E2.card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun (p : NonRoot G r × Fin k) e => a.color e = some p.2 ∧ o.tail e = p.1.1) ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hx, -⟩, e, y, h1, h2, h3, h4⟩ := hp
      have hxS : qNode (k := k) p.1 ∈ S := (Finset.mem_filter.1 hx).2
      have hyS : qNode (k := k) y ∈ S := (hA y p.2).2 h4
      have htx : o.tail e ∈ X := by rw [h2]; exact hinX _ hxS
      have hhy : G.head o.tail e ∈ X := by rw [h3]; exact hinX _ hyS
      refine ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [h1], ?_⟩, h1, h2⟩
      rcases ends_of_orient G o.tail o.oriented e with h | h
      · rw [h.1, h.2]; exact ⟨htx, hhy⟩
      · rw [h.1, h.2]; exact ⟨hhy, htx⟩
    · intro e _ p hp p' hp'
      have h1 : p.2 = p'.2 := Option.some.inj (hp.2.1.symm.trans hp'.2.1)
      have h2 : p.1.1 = p'.1.1 := hp.2.2.symm.trans hp'.2.2
      exact Prod.ext (Subtype.ext h2) h1
  have c4 : P1.card + P2.card ≤ ∑ p ∈ Cs, starCapacity G a o p := by
    have hd : Disjoint P1 P2 := Finset.disjoint_left.2 fun p h1 h2 => by
      have e1 := (Finset.mem_filter.1 h1).2.1
      obtain ⟨x, i, e2⟩ := (Finset.mem_filter.1 h2).2.1
      rw [e1] at e2
      simp [sourceNode, qcNode] at e2
    have h1 : (P1 ∪ P2).card • 1 ≤ ∑ p ∈ P1 ∪ P2, starCapacity G a o p :=
      Finset.card_nsmul_le_sum _ _ _ (fun p hp => by
        rcases Finset.mem_union.1 hp with h | h
        · exact (Finset.mem_filter.1 h).2.2
        · exact (Finset.mem_filter.1 h).2.2)
    have h2 : ∑ p ∈ P1 ∪ P2, starCapacity G a o p ≤ ∑ p ∈ Cs, starCapacity G a o p :=
      Finset.sum_le_sum_of_subset (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    rw [Finset.card_union_of_disjoint hd] at h1
    simp at h1
    omega
  have c5 : E1.card + E2.card ≤
      (univ.filter fun e => (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X).card := by
    have hd : Disjoint E1 E2 := Finset.disjoint_left.2 fun e h1 h2 => by
      have e1 := ((a.uncolored e).2 (Finset.mem_filter.1 h1).1)
      have e2 := (Finset.mem_filter.1 h2).2.1
      rw [e1] at e2; simp at e2
    rw [← Finset.card_union_of_disjoint hd]
    refine Finset.card_le_card fun e he => ?_
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.1 he with h | h
    · obtain ⟨hmem, hq⟩ := Finset.mem_filter.1 h
      have := edge_ovx G r e hmem
      unfold Graph.edge at this
      rw [Sym2.eq_iff] at this
      have hov : ovx G r e ∈ X := hinX (nr e) hq
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact ⟨hrX, hov⟩
      · rw [h1, h2]; exact ⟨hov, hrX⟩
    · exact (Finset.mem_filter.1 h).2.2
  have c5' := le_trans c5 hfor
  omega

end ConstructiveArboricity.Exact.Supplement

namespace ConstructiveArboricity.Exact.Supplement
open Classical

theorem star_infeasible (G : Graph) (k : ℕ) (r : Fin G.n)
    (a : StarInput G k r) (o : Rooting G a) (hk : 1 ≤ k)
    (h : starFlowValue G a o < (starEdges G r).card) : ¬ G.Feasible k := by
  rintro ⟨col, hcol⟩
  obtain ⟨S, hs, ht, hsum⟩ := StarFlow.cut_of_sSup (starCapacity G a o) (sourceNode G k r)
    (sinkNode G k r) (by simp [sourceNode, sinkNode])
  apply core G a o col hcol S hs ht
  have h2 : (∑ p ∈ univ.filter (fun p : StarNode G k r × StarNode G k r => p.1 ∈ S ∧ p.2 ∉ S),
      starCapacity G a o p) = starFlowValue G a o := by
    have := hsum
    exact_mod_cast this
  rw [h2]; exact h

end ConstructiveArboricity.Exact.Supplement

theorem solution (G : ConstructiveArboricity.Exact.Graph) (k : ℕ) (r : Fin G.n)
    (a : ConstructiveArboricity.Exact.Supplement.StarInput G k r)
    (o : ConstructiveArboricity.Exact.Supplement.Rooting G a) (hk : 1 ≤ k)
    (h : ConstructiveArboricity.Exact.Supplement.starFlowValue G a o <
      (ConstructiveArboricity.Exact.Supplement.starEdges G r).card) : ¬ G.Feasible k :=
  ConstructiveArboricity.Exact.Supplement.star_infeasible G k r a o hk h
