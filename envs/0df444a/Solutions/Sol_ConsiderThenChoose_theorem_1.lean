-- Prove2me | solution 1 for ConsiderThenChoose.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T07:08:34.834673+00:00
-- url     : https://prove2.me/submissions/e5f6a744-3e6e-49ce-b0b2-b5db13f0dd17

import Mathlib
import Definitions.Def_ConsiderThenChoose_stateSpace
import Definitions.Def_ConsiderThenChoose_dpTime

set_option autoImplicit false

namespace CTCProof330

open ConsiderThenChoose

theorem walk_closed {V : Type} (G : SimpleGraph V) (A B : Set V)
    (hAB : ∀ x ∈ A, x ∈ B → ∀ y ∈ A, G.Adj x y → y ∈ B)
    {u v : A} (p : (G.induce A).Walk u v) (hu : (u : V) ∈ B) : (v : V) ∈ B := by
  induction p with
  | nil => exact hu
  | cons h p ih =>
    apply ih
    exact hAB _ (Subtype.prop _) hu _ (Subtype.prop _) (by simpa using h)

theorem mem_vtx_inl {N K : ℕ} (S : Finset (Fin N)) (T : Finset (Fin K)) (p : Fin N) :
    (Sum.inl p : Fin N ⊕ Fin K) ∈ vtx S T ↔ p ∈ S := by
  simp [vtx]

theorem mem_vtx_inr {N K : ℕ} (S : Finset (Fin N)) (T : Finset (Fin K)) (j : Fin K) :
    (Sum.inr j : Fin N ⊕ Fin K) ∈ vtx S T ↔ j ∈ T := by
  simp [vtx]

theorem vtx_mono {N K : ℕ} {S S1 : Finset (Fin N)} {T T1 : Finset (Fin K)}
    (hS : S1 ⊆ S) (hT : T1 ⊆ T) : vtx S1 T1 ⊆ vtx S T := by
  intro v hv
  rcases v with p | j
  · rw [mem_vtx_inl] at hv ⊢; exact hS hv
  · rw [mem_vtx_inr] at hv ⊢; exact hT hv

theorem adj_inr_inl {N K : ℕ} (C : Fin K → Finset (Fin N)) (j : Fin K) (q : Fin N) :
    (bipGraph C).Adj (Sum.inr j) (Sum.inl q) ↔ q ∈ C j := by
  simp [bipGraph]

theorem adj_inl_inr {N K : ℕ} (C : Fin K → Finset (Fin N)) (j : Fin K) (q : Fin N) :
    (bipGraph C).Adj (Sum.inl q) (Sum.inr j) ↔ q ∈ C j := by
  simp [bipGraph]

theorem not_adj_inl_inl {N K : ℕ} (C : Fin K → Finset (Fin N)) (p q : Fin N) :
    ¬ (bipGraph C).Adj (Sum.inl p) (Sum.inl q) := by
  simp [bipGraph]

theorem not_adj_inr_inr {N K : ℕ} (C : Fin K → Finset (Fin N)) (p q : Fin K) :
    ¬ (bipGraph C).Adj (Sum.inr p) (Sum.inr q) := by
  simp [bipGraph]

/-- Two components of the same `G[S,T]` that share a vertex are equal. -/
theorem comp_sub {N K : ℕ} (C : Fin K → Finset (Fin N)) {S S1 S2 : Finset (Fin N)}
    {T T1 T2 : Finset (Fin K)} (h1 : IsComponent C S T S1 T1) (h2 : IsComponent C S T S2 T2)
    (v : Fin N ⊕ Fin K) (hv1 : v ∈ vtx S1 T1) (hv2 : v ∈ vtx S2 T2) :
    vtx S1 T1 ⊆ vtx S2 T2 := by
  intro w hw
  obtain ⟨p⟩ := h1.2.2.1.preconnected ⟨v, hv1⟩ ⟨w, hw⟩
  exact walk_closed _ _ _ (fun x _ hxB y hyA hadj =>
    h2.2.2.2 x hxB y (vtx_mono h1.1 h1.2.1 hyA) hadj) p hv2

theorem comp_unique {N K : ℕ} (C : Fin K → Finset (Fin N)) {S S1 S2 : Finset (Fin N)}
    {T T1 T2 : Finset (Fin K)} (h1 : IsComponent C S T S1 T1) (h2 : IsComponent C S T S2 T2)
    (p : Fin N) (hp1 : p ∈ S1) (hp2 : p ∈ S2) : S1 = S2 ∧ T1 = T2 := by
  have a := comp_sub C h1 h2 (Sum.inl p) ((mem_vtx_inl _ _ _).2 hp1) ((mem_vtx_inl _ _ _).2 hp2)
  have b := comp_sub C h2 h1 (Sum.inl p) ((mem_vtx_inl _ _ _).2 hp2) ((mem_vtx_inl _ _ _).2 hp1)
  constructor
  · ext q
    constructor
    · intro hq; exact (mem_vtx_inl _ _ _).1 (a ((mem_vtx_inl _ _ _).2 hq))
    · intro hq; exact (mem_vtx_inl _ _ _).1 (b ((mem_vtx_inl _ _ _).2 hq))
  · ext q
    constructor
    · intro hq; exact (mem_vtx_inr _ _ _).1 (a ((mem_vtx_inr _ _ _).2 hq))
    · intro hq; exact (mem_vtx_inr _ _ _).1 (b ((mem_vtx_inr _ _ _).2 hq))

/-- Invariant: every product `q ≥ min S` considered by a type of `T` lies in `S`. -/
theorem inv {N K : ℕ} (C : Fin K → Finset (Fin N)) {x : Finset (Fin N) × Finset (Fin K)}
    (hx : InStateSpace C x) :
    ∃ h : x.1.Nonempty, ∀ j ∈ x.2, ∀ q : Fin N, x.1.min' h ≤ q → q ∈ C j → q ∈ x.1 := by
  induction hx with
  | @root S' T' hc hS hT =>
    refine ⟨hS, fun j hj q _ hq => ?_⟩
    have := hc.2.2.2 (Sum.inr j) ((mem_vtx_inr _ _ _).2 hj) (Sum.inl q)
      ((mem_vtx_inl _ _ _).2 (Finset.mem_univ q)) ((adj_inr_inl C j q).2 hq)
    exact (mem_vtx_inl _ _ _).1 this
  | @stock S S' T T' _ h hc hS hT ih =>
    obtain ⟨h0, ih⟩ := ih
    refine ⟨hS, fun j hj q hq hqc => ?_⟩
    have hjT : j ∈ T := (Finset.mem_sdiff.1 (hc.2.1 hj)).1
    have hmS' : S'.min' hS ∈ S.erase (S.min' h) := hc.1 (Finset.min'_mem _ _)
    have hlt : S.min' h < q := by
      have h1 := Finset.ne_of_mem_erase hmS'
      have h2 := Finset.min'_le S _ (Finset.mem_of_mem_erase hmS')
      exact lt_of_lt_of_le (lt_of_le_of_ne h2 (Ne.symm h1)) hq
    have hqS : q ∈ S := ih j hjT q hlt.le hqc
    have hqE : q ∈ S.erase (S.min' h) := Finset.mem_erase.2 ⟨ne_of_gt hlt, hqS⟩
    have := hc.2.2.2 (Sum.inr j) ((mem_vtx_inr _ _ _).2 hj) (Sum.inl q)
      ((mem_vtx_inl _ _ _).2 hqE) ((adj_inr_inl C j q).2 hqc)
    exact (mem_vtx_inl _ _ _).1 this
  | @skip S S' T T' _ h hc hS hT ih =>
    obtain ⟨h0, ih⟩ := ih
    refine ⟨hS, fun j hj q hq hqc => ?_⟩
    have hjT : j ∈ T := hc.2.1 hj
    have hmS' : S'.min' hS ∈ S.erase (S.min' h) := hc.1 (Finset.min'_mem _ _)
    have hlt : S.min' h < q := by
      have h1 := Finset.ne_of_mem_erase hmS'
      have h2 := Finset.min'_le S _ (Finset.mem_of_mem_erase hmS')
      exact lt_of_lt_of_le (lt_of_le_of_ne h2 (Ne.symm h1)) hq
    have hqS : q ∈ S := ih j hjT q hlt.le hqc
    have hqE : q ∈ S.erase (S.min' h) := Finset.mem_erase.2 ⟨ne_of_gt hlt, hqS⟩
    have := hc.2.2.2 (Sum.inr j) ((mem_vtx_inr _ _ _).2 hj) (Sum.inl q)
      ((mem_vtx_inl _ _ _).2 hqE) ((adj_inr_inl C j q).2 hqc)
    exact (mem_vtx_inl _ _ _).1 this

theorem conn {N K : ℕ} (C : Fin K → Finset (Fin N)) {x : Finset (Fin N) × Finset (Fin K)}
    (hx : InStateSpace C x) : ((bipGraph C).induce (vtx x.1 x.2)).Connected := by
  cases hx with
  | root hc _ _ => exact hc.2.2.1
  | stock _ _ hc _ _ => exact hc.2.2.1
  | skip _ _ hc _ _ => exact hc.2.2.1

/-- A state is determined by its most preferred product and its type set. -/
theorem state_sub {N K : ℕ} (C : Fin K → Finset (Fin N)) {x y : Finset (Fin N) × Finset (Fin K)}
    (hx : InStateSpace C x) (hy : InStateSpace C y) (hT : x.2 = y.2)
    (hxn : x.1.Nonempty) (hyn : y.1.Nonempty) (hm : x.1.min' hxn = y.1.min' hyn) :
    x.1 ⊆ y.1 := by
  obtain ⟨_, hinv⟩ := inv C hy
  intro q hq
  have hst : (Sum.inl (x.1.min' hxn) : Fin N ⊕ Fin K) ∈ vtx x.1 x.2 :=
    (mem_vtx_inl _ _ _).2 (Finset.min'_mem _ _)
  have hq' : (Sum.inl q : Fin N ⊕ Fin K) ∈ vtx x.1 x.2 := (mem_vtx_inl _ _ _).2 hq
  obtain ⟨p⟩ := (conn C hx).preconnected ⟨_, hst⟩ ⟨_, hq'⟩
  have key := walk_closed (bipGraph C) (vtx x.1 x.2) (vtx y.1 y.2) ?_ p
    ((mem_vtx_inl _ _ _).2 (by rw [hm]; exact Finset.min'_mem _ _))
  · exact (mem_vtx_inl _ _ _).1 key
  · intro a ha hb b hb' hab
    rcases a with a | a <;> rcases b with b | b
    · exact absurd hab (not_adj_inl_inl C a b)
    · rw [mem_vtx_inr] at hb' ⊢; rw [← hT]; exact hb'
    · rw [mem_vtx_inl] at hb' ⊢
      rw [mem_vtx_inr] at hb
      have hle : y.1.min' hyn ≤ b := by rw [← hm]; exact Finset.min'_le _ _ hb'
      exact hinv a hb b hle ((adj_inr_inl C a b).1 hab)
    · exact absurd hab (not_adj_inr_inr C a b)

open Classical in
theorem bound_mul {N K : ℕ} (C : Fin K → Finset (Fin N)) :
    (stateSpace C).ncard ≤ N * 2 ^ K := by
  have hS : stateSpace C = ↑(Finset.univ.filter (fun x => InStateSpace C x)) := by
    ext x; simp [stateSpace]
  rw [hS, Set.ncard_coe_finset]
  have hsub : Finset.univ.filter (fun x => InStateSpace C x) ⊆
      (Finset.univ : Finset (Fin N)).biUnion (fun i =>
        Finset.univ.filter (fun x => InStateSpace C x ∧ x.1.min = (i : WithTop (Fin N)))) := by
    intro x hx
    have hx' : InStateSpace C x := (Finset.mem_filter.1 hx).2
    obtain ⟨hn, _⟩ := inv C hx'
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨x.1.min' hn, hx', (Finset.coe_min' hn).symm⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hfib : ∀ i : Fin N, (Finset.univ.filter (fun x : Finset (Fin N) × Finset (Fin K) =>
      InStateSpace C x ∧ x.1.min = (i : WithTop (Fin N)))).card ≤ 2 ^ K := by
    intro i
    have : (Finset.univ : Finset (Finset (Fin K))).card = 2 ^ K := by simp
    rw [← this]
    refine Finset.card_le_card_of_injOn (fun x => x.2) (fun _ _ => Finset.mem_univ _) ?_
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
    obtain ⟨hnx, _⟩ := inv C hx.1
    obtain ⟨hny, _⟩ := inv C hy.1
    have hm : x.1.min' hnx = y.1.min' hny := by
      have e1 := Finset.coe_min' hnx
      have e2 := Finset.coe_min' hny
      rw [hx.2] at e1; rw [hy.2] at e2
      exact WithTop.coe_injective (e1.trans e2.symm)
    have a := state_sub C hx.1 hy.1 hxy hnx hny hm
    have b := state_sub C hy.1 hx.1 hxy.symm hny hnx hm.symm
    exact Prod.ext (Finset.Subset.antisymm a b) hxy
  calc ∑ i : Fin N, _ ≤ ∑ _i : Fin N, 2 ^ K := Finset.sum_le_sum (fun i _ => hfib i)
    _ = N * 2 ^ K := by simp

/-- One step of the recursion. -/
def Step {N K : ℕ} (C : Fin K → Finset (Fin N)) (x y : Finset (Fin N) × Finset (Fin K)) : Prop :=
  ∃ h : x.1.Nonempty,
    (IsComponent C (x.1.erase (x.1.min' h)) (x.2 \ typesOf C (x.1.min' h)) y.1 y.2 ∨
      IsComponent C (x.1.erase (x.1.min' h)) x.2 y.1 y.2) ∧ y.1.Nonempty ∧ y.2.Nonempty

theorem reach {N K : ℕ} (C : Fin K → Finset (Fin N)) {x : Finset (Fin N) × Finset (Fin K)}
    (hx : InStateSpace C x) :
    ∃ r : Finset (Fin N) × Finset (Fin K),
      (IsComponent C Finset.univ Finset.univ r.1 r.2 ∧ r.1.Nonempty ∧ r.2.Nonempty) ∧
      Relation.ReflTransGen (Step C) r x := by
  induction hx with
  | @root S' T' hc hS hT => exact ⟨(S', T'), ⟨hc, hS, hT⟩, Relation.ReflTransGen.refl⟩
  | @stock S S' T T' _ h hc hS hT ih =>
    obtain ⟨r, hr, hrr⟩ := ih
    exact ⟨r, hr, hrr.tail ⟨h, Or.inl hc, hS, hT⟩⟩
  | @skip S S' T T' _ h hc hS hT ih =>
    obtain ⟨r, hr, hrr⟩ := ih
    exact ⟨r, hr, hrr.tail ⟨h, Or.inr hc, hS, hT⟩⟩

theorem disj_sum {N : ℕ} {α : Type} [DecidableEq α] (Y : Finset α) (f : α → Finset (Fin N))
    (U : Finset (Fin N)) (hsub : ∀ y ∈ Y, f y ⊆ U)
    (hdisj : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ p, p ∈ f y → p ∈ f y' → y = y') :
    ∑ y ∈ Y, (2 ^ (f y).card - 1) ≤ 2 ^ U.card - 1 := by
  have e : ∀ s : Finset (Fin N), 2 ^ s.card - 1 = (s.powerset.erase ∅).card := by
    intro s
    rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset _), Finset.card_powerset]
  rw [Finset.sum_congr rfl (fun y _ => e (f y)), e U, ← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_powerset] at hs ⊢
    obtain ⟨y, hy, hne, hsy⟩ := hs
    exact ⟨hne, hsy.trans (hsub y hy)⟩
  · intro y hy y' hy' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs hs'
    simp only [Finset.mem_erase, Finset.mem_powerset] at hs hs'
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hs.1
    exact hne (hdisj y hy y' hy' p (hs.2 hp) (hs'.2 hp))

open Classical in
theorem count (N K : ℕ) (C : Fin K → Finset (Fin N)) (n : ℕ) :
    ∀ x : Finset (Fin N) × Finset (Fin K), x.1.card ≤ n → x.1.Nonempty →
      (Finset.univ.filter (fun y => Relation.ReflTransGen (Step C) x y)).card ≤ 2 ^ x.1.card - 1 := by
  induction n with
  | zero =>
    intro x hc hn
    have := Finset.card_pos.2 hn
    omega
  | succ n ih =>
    intro x hc hn
    set m := x.1.min' hn with hm
    set R : Finset (Fin N) × Finset (Fin K) → Finset (Finset (Fin N) × Finset (Fin K)) :=
      fun z => Finset.univ.filter (fun y => Relation.ReflTransGen (Step C) z y) with hR
    set kids := Finset.univ.filter (fun y => Step C x y) with hkids
    have hsub : R x ⊆ insert x (kids.biUnion R) := by
      intro y hy
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      rcases hy.cases_head with h | ⟨z, hz, hzy⟩
      · rw [h]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        simp only [Finset.mem_biUnion, hkids, hR, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨z, hz, hzy⟩
    have hkid : ∀ z ∈ kids, z.1 ⊆ x.1.erase m ∧ z.1.Nonempty := by
      intro z hz
      simp only [hkids, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨h, hc', hz1, _⟩ := hz
      rcases hc' with hc' | hc'
      · exact ⟨hc'.1, hz1⟩
      · exact ⟨hc'.1, hz1⟩
    have hEc : (x.1.erase m).card = x.1.card - 1 :=
      Finset.card_erase_of_mem (Finset.min'_mem _ _)
    have hpos := Finset.card_pos.2 hn
    have hstep : ∀ z ∈ kids, (R z).card ≤ 2 ^ z.1.card - 1 := by
      intro z hz
      obtain ⟨h1, h2⟩ := hkid z hz
      have := Finset.card_le_card h1
      exact ih z (by omega) h2
    set P : Finset (Fin N) × Finset (Fin K) → Prop :=
      fun z => IsComponent C (x.1.erase m) (x.2 \ typesOf C m) z.1 z.2 with hP
    have hA : ∑ z ∈ kids.filter P, (2 ^ z.1.card - 1) ≤ 2 ^ (x.1.erase m).card - 1 := by
      refine disj_sum _ (fun z : Finset (Fin N) × Finset (Fin K) => z.1) _ ?_ ?_
      · intro z hz; exact (hkid z (Finset.mem_of_mem_filter z hz)).1
      · intro z hz z' hz' p hp hp'
        have a := (Finset.mem_filter.1 hz).2
        have b := (Finset.mem_filter.1 hz').2
        obtain ⟨e1, e2⟩ := comp_unique C a b p hp hp'
        exact Prod.ext e1 e2
    have hB : ∑ z ∈ kids.filter (fun z => ¬ P z), (2 ^ z.1.card - 1) ≤
        2 ^ (x.1.erase m).card - 1 := by
      have hQ : ∀ z ∈ kids.filter (fun z => ¬ P z), IsComponent C (x.1.erase m) x.2 z.1 z.2 := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
        simp only [hkids, Finset.mem_filter, Finset.mem_univ, true_and] at hz1
        obtain ⟨h, hc', _, _⟩ := hz1
        rcases hc' with hc' | hc'
        · exact absurd hc' hz2
        · exact hc'
      refine disj_sum _ (fun z : Finset (Fin N) × Finset (Fin K) => z.1) _ ?_ ?_
      · intro z hz; exact (hkid z (Finset.mem_of_mem_filter z hz)).1
      · intro z hz z' hz' p hp hp'
        obtain ⟨e1, e2⟩ := comp_unique C (hQ z hz) (hQ z' hz') p hp hp'
        exact Prod.ext e1 e2
    have hsum : ∑ z ∈ kids, (R z).card ≤ ∑ z ∈ kids, (2 ^ z.1.card - 1) :=
      Finset.sum_le_sum hstep
    have hsplit : ∑ z ∈ kids.filter P, (2 ^ z.1.card - 1) +
        ∑ z ∈ kids.filter (fun z => ¬ P z), (2 ^ z.1.card - 1) =
        ∑ z ∈ kids, (2 ^ z.1.card - 1) := by
      exact Finset.sum_filter_add_sum_filter_not kids P _
    have hcard : (R x).card ≤ 1 + ∑ z ∈ kids, (R z).card :=
      (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans
        (by have := Finset.card_biUnion_le (s := kids) (t := R); omega))
    have hpow : 2 ^ x.1.card = 2 * 2 ^ (x.1.card - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hone : 1 ≤ 2 ^ (x.1.card - 1) := Nat.one_le_two_pow
    rw [hEc] at hA hB
    show (R x).card ≤ 2 ^ x.1.card - 1
    rw [hpow]
    generalize 2 ^ (x.1.card - 1) = t at hA hB hone ⊢
    omega

open Classical in
theorem bound_pow {N K : ℕ} (C : Fin K → Finset (Fin N)) :
    (stateSpace C).ncard ≤ 2 ^ N := by
  have hS : stateSpace C = ↑(Finset.univ.filter (fun x => InStateSpace C x)) := by
    ext x; simp [stateSpace]
  rw [hS, Set.ncard_coe_finset]
  set R : Finset (Fin N) × Finset (Fin K) → Finset (Finset (Fin N) × Finset (Fin K)) :=
    fun z => Finset.univ.filter (fun y => Relation.ReflTransGen (Step C) z y) with hR
  set roots := Finset.univ.filter (fun r : Finset (Fin N) × Finset (Fin K) =>
    IsComponent C Finset.univ Finset.univ r.1 r.2 ∧ r.1.Nonempty ∧ r.2.Nonempty) with hroots
  have hsub : Finset.univ.filter (fun x => InStateSpace C x) ⊆ roots.biUnion R := by
    intro x hx
    obtain ⟨r, hr, hrr⟩ := reach C (Finset.mem_filter.1 hx).2
    simp only [Finset.mem_biUnion, hroots, hR, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨r, hr, hrr⟩
  have h1 : ∑ r ∈ roots, (R r).card ≤ ∑ r ∈ roots, (2 ^ r.1.card - 1) := by
    apply Finset.sum_le_sum
    intro r hr
    have hr' := (Finset.mem_filter.1 hr).2
    exact count N K C r.1.card r le_rfl hr'.2.1
  have h2 : ∑ r ∈ roots, (2 ^ r.1.card - 1) ≤ 2 ^ (Finset.univ : Finset (Fin N)).card - 1 := by
    refine disj_sum _ (fun z : Finset (Fin N) × Finset (Fin K) => z.1) _ ?_ ?_
    · intro z _; exact Finset.subset_univ _
    · intro z hz z' hz' p hp hp'
      obtain ⟨e1, e2⟩ := comp_unique C (Finset.mem_filter.1 hz).2.1
        (Finset.mem_filter.1 hz').2.1 p hp hp'
      exact Prod.ext e1 e2
  have h3 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have hone : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  generalize 2 ^ N = t at h2 hone ⊢
  omega

theorem main_1 : ∀ (N K : ℕ) (C : Fin K → Finset (Fin N)),
    (stateSpace C).ncard ≤ min (2 ^ N) (N * 2 ^ K) :=
  fun _ _ C => le_min (bound_pow C) (bound_mul C)

theorem main_2 : ∀ K : ℕ, ∃ c : ℕ, ∀ (N : ℕ) (C : Fin K → Finset (Fin N)),
    dpTime C ≤ c * N ^ 2 := by
  intro K
  refine ⟨2 * K * 2 ^ K, fun N C => ?_⟩
  have h := bound_mul C
  unfold dpTime
  calc (N * K + K) * (stateSpace C).ncard ≤ (N * K + K) * (N * 2 ^ K) :=
        Nat.mul_le_mul_left _ h
    _ = (K * 2 ^ K * N) * (N + 1) := by ring
    _ ≤ (K * 2 ^ K * N) * (2 * N) := by
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · subst h0; simp
        · exact Nat.mul_le_mul_left _ (by omega)
    _ = 2 * K * 2 ^ K * N ^ 2 := by ring

theorem main_3 : ∀ a b : ℕ, ∃ c d : ℕ, ∀ (N K : ℕ) (C : Fin K → Finset (Fin N)),
    K ≤ a * Nat.log 2 N + b → dpTime C ≤ c * N ^ d := by
  intro a b
  refine ⟨2 * (a + b) * 2 ^ b, a + 3, fun N K C hK => ?_⟩
  have h := bound_mul C
  unfold dpTime
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    have : (stateSpace C).ncard = 0 := by simpa using h
    rw [this]; simp
  have hL : Nat.log 2 N ≤ N := Nat.log_le_self 2 N
  have hKN : K ≤ (a + b) * N := by nlinarith
  have hP : 2 ^ K ≤ N ^ a * 2 ^ b := by
    calc 2 ^ K ≤ 2 ^ (a * Nat.log 2 N + b) := Nat.pow_le_pow_right (by norm_num) hK
      _ = (2 ^ Nat.log 2 N) ^ a * 2 ^ b := by rw [pow_add, mul_comm a, pow_mul]
      _ ≤ N ^ a * 2 ^ b :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) a)
  calc (N * K + K) * (stateSpace C).ncard ≤ (N * K + K) * (N * 2 ^ K) :=
        Nat.mul_le_mul_left _ h
    _ = (N * (N + 1)) * (K * 2 ^ K) := by ring
    _ ≤ (N * (2 * N)) * (((a + b) * N) * (N ^ a * 2 ^ b)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul hKN hP)
    _ = 2 * (a + b) * 2 ^ b * N ^ (a + 3) := by ring

end CTCProof330

open ConsiderThenChoose in
theorem solution :
    (∀ (N K : ℕ) (C : Fin K → Finset (Fin N)),
        (stateSpace C).ncard ≤ min (2 ^ N) (N * 2 ^ K)) ∧
    (∀ K : ℕ, ∃ c : ℕ, ∀ (N : ℕ) (C : Fin K → Finset (Fin N)),
        dpTime C ≤ c * N ^ 2) ∧
    (∀ a b : ℕ, ∃ c d : ℕ, ∀ (N K : ℕ) (C : Fin K → Finset (Fin N)),
        K ≤ a * Nat.log 2 N + b → dpTime C ≤ c * N ^ d) := by
  exact ⟨CTCProof330.main_1, CTCProof330.main_2, CTCProof330.main_3⟩
