-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.discrete_separation_mconvex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T16:57:36.476474+00:00
-- url     : https://prove2.me/submissions/cada6f8d-af9b-41c3-b0fe-19a521704012

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB

set_option autoImplicit false

namespace P2MB0e1201f

open DiscreteConvex.MConvexSetsB

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `x + χ_a - χ_b`. -/
def mv (x : V → ℤ) (a b : V) : V → ℤ := fun w => x w + CharVec a w - CharVec b w

/-- l1 distance. -/
def dd (x y : V → ℤ) : ℕ := ∑ v, (x v - y v).natAbs

lemma cv_self (a : V) : CharVec a a = 1 := by simp [CharVec]

lemma cv_ne {a w : V} (h : w ≠ a) : CharVec a w = 0 := by simp [CharVec, h]

lemma exc' {B : Set (V → ℤ)} (h : ExchangeAxiomB B) {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    {u : V} (hu : y u < x u) : ∃ v, x v < y v ∧ mv x v u ∈ B ∧ mv y u v ∈ B := by
  obtain ⟨v, hv, h1, h2⟩ := h x hx y hy u hu
  refine ⟨v, hv, ?_, h2⟩
  convert h1 using 1
  funext w; simp only [mv]; ring

lemma dstep (x y x' y' : V → ℤ) (s b : V) (hsb : s ≠ b)
    (h : ∀ v, x' v - y' v = x v - y v + CharVec s v - CharVec b v) (hs : x s < y s) :
    (y b < x b → dd x' y' < dd x y) ∧ (x b ≤ y b → dd x' y' ≤ dd x y) := by
  have hsum : ∑ v, (((x' v - y' v).natAbs : ℤ) - ((x v - y v).natAbs : ℤ)) =
      (((x' s - y' s).natAbs : ℤ) - ((x s - y s).natAbs : ℤ)) +
      (((x' b - y' b).natAbs : ℤ) - ((x b - y b).natAbs : ℤ)) := by
    apply Fintype.sum_eq_add s b hsb
    rintro v ⟨h1, h2⟩
    rw [h v, cv_ne h1, cv_ne h2]; simp
  rw [Finset.sum_sub_distrib] at hsum
  have e1 : (dd x' y' : ℤ) = ∑ v, ((x' v - y' v).natAbs : ℤ) := by simp [dd]
  have e2 : (dd x y : ℤ) = ∑ v, ((x v - y v).natAbs : ℤ) := by simp [dd]
  have hs' := h s
  have hb' := h b
  rw [cv_self, cv_ne hsb] at hs'
  rw [cv_self, cv_ne (Ne.symm hsb)] at hb'
  constructor
  · intro hlt
    have : (dd x' y' : ℤ) < dd x y := by
      rw [e1, e2]; omega
    exact_mod_cast this
  · intro hle
    have : (dd x' y' : ℤ) ≤ dd x y := by
      rw [e1, e2]; omega
    exact_mod_cast this

lemma comp {B : Set (V → ℤ)} (h : ExchangeAxiomB B) {w : V → ℤ} {a b c : V}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : mv w a b ∈ B) (h2 : mv w b c ∈ B) : mv w a c ∈ B := by
  obtain ⟨v, hv, -, h'⟩ := exc' h h1 h2 (u := a)
    (by simp only [mv]; rw [cv_self, cv_ne hab, cv_ne hac]; omega)
  have hvb : v = b := by
    by_contra hvb
    simp only [mv] at hv
    rw [cv_ne hvb] at hv
    by_cases hva : v = a
    · subst hva; rw [cv_self, cv_ne hac] at hv; omega
    · rw [cv_ne hva] at hv
      by_cases hvc : v = c
      · subst hvc; rw [cv_self] at hv; omega
      · rw [cv_ne hvc] at hv; omega
  subst hvb
  convert h' using 1
  funext t; simp only [mv]; ring

/-- Two exchanges, first form (u = a). -/
lemma two_a {B : Set (V → ℤ)} (h : ExchangeAxiomB B) {w : V → ℤ} {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : mv w a b ∈ B) (h2 : mv w c d ∈ B) : mv w a d ∈ B ∨ mv (mv w a b) c d ∈ B := by
  obtain ⟨v, hv, -, h'⟩ := exc' h h1 h2 (u := a)
    (by simp only [mv]; rw [cv_self, cv_ne hab, cv_ne hac, cv_ne had]; omega)
  by_cases hvb : v = b
  · subst hvb; right; convert h' using 1; funext t; simp only [mv]; ring
  by_cases hvc : v = c
  · subst hvc; left; convert h' using 1; funext t; simp only [mv]; ring
  exfalso
  simp only [mv] at hv
  rw [cv_ne hvb, cv_ne hvc] at hv
  by_cases hva : v = a
  · subst hva; rw [cv_self, cv_ne had] at hv; omega
  · rw [cv_ne hva] at hv
    by_cases hvd : v = d
    · subst hvd; rw [cv_self] at hv; omega
    · rw [cv_ne hvd] at hv; omega

/-- Two exchanges, second form (u = d). -/
lemma two_d {B : Set (V → ℤ)} (h : ExchangeAxiomB B) {w : V → ℤ} {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : mv w a b ∈ B) (h2 : mv w c d ∈ B) : mv w c b ∈ B ∨ mv (mv w a b) c d ∈ B := by
  obtain ⟨v, hv, h', h''⟩ := exc' h h1 h2 (u := d)
    (by simp only [mv]; rw [cv_self, cv_ne had.symm, cv_ne hbd.symm, cv_ne hcd.symm]; omega)
  by_cases hvc : v = c
  · subst hvc; right; exact h'
  by_cases hvb : v = b
  · subst hvb; left; convert h'' using 1; funext t; simp only [mv]; ring
  exfalso
  simp only [mv] at hv
  rw [cv_ne hvb, cv_ne hvc] at hv
  by_cases hva : v = a
  · subst hva; rw [cv_self, cv_ne had] at hv; omega
  · rw [cv_ne hva] at hv
    by_cases hvd : v = d
    · subst hvd; rw [cv_self] at hv; omega
    · rw [cv_ne hvd] at hv; omega

lemma sum_mv (x : V → ℤ) (a b : V) : ∑ w, mv x a b w = ∑ w, x w := by
  simp [mv, CharVec, Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma sum_mv_in (X : Finset V) (x : V → ℤ) {a b : V} (ha : a ∈ X) (hb : b ∈ X) :
    ∑ w ∈ X, mv x a b w = ∑ w ∈ X, x w := by
  simp [mv, CharVec, Finset.sum_add_distrib, Finset.sum_sub_distrib, ha, hb]

/-- Constant sum on an M-convex set. -/
lemma const_sum {B : Set (V → ℤ)} (h : ExchangeAxiomB B) :
    ∀ n, ∀ x y, x ∈ B → y ∈ B → dd x y = n → ∑ w, x w = ∑ w, y w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro x y hx hy hn
  by_cases hex : ∃ u, y u < x u
  · obtain ⟨u, hu⟩ := hex
    obtain ⟨v, hv, h1, -⟩ := exc' h hx hy hu
    have hvu : v ≠ u := by rintro rfl; omega
    have hlt := (dstep x y (mv x v u) y v u hvu (fun t => by simp only [mv]; ring) hv).1 hu
    rw [← sum_mv x v u]
    exact IH _ (hn ▸ hlt) _ _ h1 hy rfl
  · push_neg at hex
    by_cases hex2 : ∃ u, x u < y u
    · obtain ⟨u, hu⟩ := hex2
      obtain ⟨v, hv, -, -⟩ := exc' h hy hx hu
      exact absurd (hex v) (not_le.mpr hv)
    · push_neg at hex2
      have : x = y := funext fun t => le_antisymm (hex t) (hex2 t)
      rw [this]

/-- Local optimality implies global optimality for `z ↦ z(X)`. -/
lemma max_local {B : Set (V → ℤ)} (h : ExchangeAxiomB B) (X : Finset V) (x : V → ℤ)
    (hx : x ∈ B) (H : ∀ a ∈ X, ∀ b ∉ X, mv x a b ∉ B) :
    ∀ n, ∀ z, z ∈ B → dd z x = n → ∑ w ∈ X, z w ≤ ∑ w ∈ X, x w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro z hz hn
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, huX, hu⟩ := Finset.exists_lt_of_sum_lt hcon
  obtain ⟨v, hv, h1, h2⟩ := exc' h hz hx hu
  by_cases hvX : v ∈ X
  · have hvu : v ≠ u := by rintro rfl; omega
    have hlt := (dstep z x (mv z v u) x v u hvu (fun t => by simp only [mv]; ring) hv).1 hu
    have := IH _ (hn ▸ hlt) _ h1 rfl
    rw [sum_mv_in X z hvX huX] at this
    omega
  · exact H u huX v hvX h2

/-- Exchange-graph arcs. -/
def Arc (B1 B2 : Set (V → ℤ)) (x y : V → ℤ) (a b : V) : Prop :=
  a ≠ b ∧ (mv x a b ∈ B1 ∨ mv y b a ∈ B2)

/-- Nodes that reach `supp⁻(y - x)` within `k` arcs. -/
def Rch (B1 B2 : Set (V → ℤ)) (x y : V → ℤ) : ℕ → Set V
  | 0 => {a | y a < x a}
  | k + 1 => Rch B1 B2 x y k ∪ {a | ∃ b, Arc B1 B2 x y a b ∧ b ∈ Rch B1 B2 x y k}

lemma key {B1 B2 : Set (V → ℤ)} (hE1 : ExchangeAxiomB B1) (hE2 : ExchangeAxiomB B2) :
    ∀ k, ∀ x y s, x ∈ B1 → y ∈ B2 → x s < y s → s ∈ Rch B1 B2 x y k →
      ∃ x' ∈ B1, ∃ y' ∈ B2, dd x' y' < dd x y := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro x y s hx hy hs hsk
  by_cases hmin : ∃ j < k, ∃ s', x s' < y s' ∧ s' ∈ Rch B1 B2 x y j
  · obtain ⟨j, hj, s', h1, h2⟩ := hmin
    exact IH j hj x y s' hx hy h1 h2
  push_neg at hmin
  cases k with
  | zero =>
    simp only [Rch, Set.mem_setOf_eq] at hsk; omega
  | succ m =>
  rcases hsk with hsk | ⟨b, ⟨hsb, harc⟩, hb⟩
  · exact absurd hsk (hmin m (by omega) s hs)
  have hsR0 : ∀ j ≤ m, s ∉ Rch B1 B2 x y j := fun j hj => hmin j (by omega) s hs
  have hsR : ∀ j < m, ∀ d ∈ Rch B1 B2 x y j, ¬ Arc B1 B2 x y s d :=
    fun j hj d hd ha => hmin (j + 1) (by omega) s hs (Or.inr ⟨d, ha, hd⟩)
  rcases lt_trichotomy (x b) (y b) with hb' | hb' | hb'
  · exact absurd hb (hmin m (by omega) b hb')
  · rcases harc with hA | hB
    · -- move x along the arc s → b
      have T : ∀ j ≤ m, ∀ c ∈ Rch B1 B2 x y j, c ∈ Rch B1 B2 (mv x s b) y j := by
        intro j
        induction j with
        | zero =>
          intro _ c hc
          simp only [Rch, Set.mem_setOf_eq] at hc ⊢
          have hcs : c ≠ s := by rintro rfl; omega
          have hcb : c ≠ b := by rintro rfl; omega
          simp only [mv]; rw [cv_ne hcs, cv_ne hcb]; omega
        | succ j ihj =>
          intro hj c hc
          rcases hc with hc | ⟨d, ⟨hcd, hA' | hB'⟩, hd⟩
          · exact Or.inl (ihj (by omega) c hc)
          · have hd' := ihj (by omega) d hd
            refine Or.inr ⟨d, ⟨hcd, Or.inl ?_⟩, hd'⟩
            by_cases hcs : c = s
            · subst hcs
              exact absurd (Or.inr ⟨d, ⟨hcd, Or.inl hA'⟩, hd⟩) (hsR0 (j + 1) hj)
            by_cases hds : d = s
            · rw [hds] at hd; exact absurd hd (hsR0 j (by omega))
            by_cases hdb : d = b
            · rw [hdb] at hd; exact absurd ⟨hsb, Or.inl hA⟩ (hsR j (by omega) b hd)
            by_cases hcb : c = b
            · rw [hcb] at hA'
              exact absurd ⟨Ne.symm hds, Or.inl (comp hE1 hsb (Ne.symm hdb) (Ne.symm hds) hA hA')⟩
                (hsR j (by omega) d hd)
            rcases two_a hE1 hsb (Ne.symm hcs) (Ne.symm hds) (Ne.symm hcb) (Ne.symm hdb) hcd hA hA'
              with h | h
            · exact absurd ⟨Ne.symm hds, Or.inl h⟩ (hsR j (by omega) d hd)
            · exact h
          · exact Or.inr ⟨d, ⟨hcd, Or.inr hB'⟩, ihj (by omega) d hd⟩
      have hb2 : mv x s b b < y b := by
        simp only [mv]; rw [cv_self, cv_ne (Ne.symm hsb)]; omega
      obtain ⟨x'', hx'', y'', hy'', hlt⟩ := IH m (by omega) (mv x s b) y b hA hy hb2 (T m le_rfl b hb)
      exact ⟨x'', hx'', y'', hy'', lt_of_lt_of_le hlt
        ((dstep x y (mv x s b) y s b hsb (fun t => by simp only [mv]; ring) hs).2 hb'.le)⟩
    · -- move y along the arc s → b
      have T : ∀ j ≤ m, ∀ c ∈ Rch B1 B2 x y j, c ∈ Rch B1 B2 x (mv y b s) j := by
        intro j
        induction j with
        | zero =>
          intro _ c hc
          simp only [Rch, Set.mem_setOf_eq] at hc ⊢
          have hcs : c ≠ s := by rintro rfl; omega
          have hcb : c ≠ b := by rintro rfl; omega
          simp only [mv]; rw [cv_ne hcs, cv_ne hcb]; omega
        | succ j ihj =>
          intro hj c hc
          rcases hc with hc | ⟨d, ⟨hcd, hA' | hB'⟩, hd⟩
          · exact Or.inl (ihj (by omega) c hc)
          · exact Or.inr ⟨d, ⟨hcd, Or.inl hA'⟩, ihj (by omega) d hd⟩
          · have hd' := ihj (by omega) d hd
            refine Or.inr ⟨d, ⟨hcd, Or.inr ?_⟩, hd'⟩
            by_cases hcs : c = s
            · subst hcs
              exact absurd (Or.inr ⟨d, ⟨hcd, Or.inr hB'⟩, hd⟩) (hsR0 (j + 1) hj)
            by_cases hds : d = s
            · rw [hds] at hd; exact absurd hd (hsR0 j (by omega))
            by_cases hdb : d = b
            · rw [hdb] at hd; exact absurd ⟨hsb, Or.inr hB⟩ (hsR j (by omega) b hd)
            by_cases hcb : c = b
            · rw [hcb] at hB'
              exact absurd ⟨Ne.symm hds, Or.inr (comp hE2 hdb hsb.symm hds hB' hB)⟩
                (hsR j (by omega) d hd)
            rcases two_d hE2 (Ne.symm hsb) (Ne.symm hdb) (Ne.symm hcb) (Ne.symm hds) (Ne.symm hcs)
              (Ne.symm hcd) hB hB' with h | h
            · exact absurd ⟨Ne.symm hds, Or.inr h⟩ (hsR j (by omega) d hd)
            · exact h
      have hb2 : x b < mv y b s b := by
        simp only [mv]; rw [cv_self, cv_ne (Ne.symm hsb)]; omega
      obtain ⟨x'', hx'', y'', hy'', hlt⟩ := IH m (by omega) x (mv y b s) b hx hB hb2 (T m le_rfl b hb)
      exact ⟨x'', hx'', y'', hy'', lt_of_lt_of_le hlt
        ((dstep x y x (mv y b s) s b hsb (fun t => by simp only [mv]; ring) hs).2 hb'.le)⟩
  · rcases harc with hA | hB
    · exact ⟨mv x s b, hA, y, hy,
        (dstep x y (mv x s b) y s b hsb (fun t => by simp only [mv]; ring) hs).1 hb'⟩
    · exact ⟨x, hx, mv y b s, hB,
        (dstep x y x (mv y b s) s b hsb (fun t => by simp only [mv]; ring) hs).1 hb'⟩

theorem main {V : Type*} [Fintype V] [DecidableEq V]
    (B1 B2 : Set (V → ℤ)) (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2)
    (hB1ne : B1.Nonempty) (hB2ne : B2.Nonempty) (hdisj : B1 ∩ B2 = ∅) :
    ∃ p : V → ℤ, ((∀ v, p v = 0 ∨ p v = 1) ∨ (∀ v, p v = 0 ∨ p v = -1)) ∧
      sInf ((fun x : V → ℤ => (∑ v, (p v : ℝ) * (x v : ℝ))) '' B1) -
        sSup ((fun x : V → ℤ => (∑ v, (p v : ℝ) * (x v : ℝ))) '' B2) ≥ 1 := by
  classical
  have hex : ∃ n, ∃ x ∈ B1, ∃ y ∈ B2, dd x y = n := by
    obtain ⟨x, hx⟩ := hB1ne; obtain ⟨y, hy⟩ := hB2ne; exact ⟨_, x, hx, y, hy, rfl⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Nat.find_spec hex
  have hmp : ∀ x' ∈ B1, ∀ y' ∈ B2, ¬ dd x' y' < dd x y := by
    intro x' hx' y' hy' hlt
    rw [hxy] at hlt
    exact Nat.find_min hex hlt ⟨x', hx', y', hy', rfl⟩
  have hne : x ≠ y := by
    rintro rfl
    have : x ∈ B1 ∩ B2 := ⟨hx, hy⟩
    rw [hdisj] at this; exact this
  have cs1 : ∀ z ∈ B1, ∑ w, z w = ∑ w, x w := fun z hz => const_sum hExc1 _ z x hz hx rfl
  have cs2 : ∀ z ∈ B2, ∑ w, z w = ∑ w, y w := fun z hz => const_sum hExc2 _ z y hz hy rfl
  by_cases hpos : ∃ s, x s < y s
  · obtain ⟨s, hs⟩ := hpos
    have hnot : ∀ k, ∀ s', x s' < y s' → s' ∉ Rch B1 B2 x y k := by
      intro k s' h1 h2
      obtain ⟨x', hx', y', hy', hlt⟩ := key hExc1 hExc2 k x y s' hx hy h1 h2
      exact hmp x' hx' y' hy' hlt
    set X : Finset V := Finset.univ.filter (fun a => ∀ k, a ∉ Rch B1 B2 x y k) with hXdef
    have memX : ∀ a, a ∈ X ↔ ∀ k, a ∉ Rch B1 B2 x y k := by
      intro a; simp [hXdef]
    have closed : ∀ a ∈ X, ∀ b ∉ X, ¬ Arc B1 B2 x y a b := by
      intro a ha b hb harc
      rw [memX] at ha hb
      push_neg at hb
      obtain ⟨k, hk⟩ := hb
      exact ha (k + 1) (Or.inr ⟨b, harc, hk⟩)
    -- x maximizes z(X) on B1
    have hmax1 : ∀ z ∈ B1, ∑ w ∈ X, z w ≤ ∑ w ∈ X, x w := by
      intro z hz
      refine max_local hExc1 X x hx ?_ _ z hz rfl
      intro a ha b hb hmem
      have hab : a ≠ b := by rintro rfl; exact hb ha
      exact closed a ha b hb ⟨hab, Or.inl hmem⟩
    -- y maximizes z(Xᶜ) on B2
    have hmax2 : ∀ z ∈ B2, ∑ w ∈ Xᶜ, z w ≤ ∑ w ∈ Xᶜ, y w := by
      intro z hz
      refine max_local hExc2 Xᶜ y hy ?_ _ z hz rfl
      intro b hb a ha hmem
      rw [Finset.mem_compl] at hb
      simp only [Finset.mem_compl, not_not] at ha
      have hab : a ≠ b := by rintro rfl; exact hb ha
      exact closed a ha b hb ⟨hab, Or.inr hmem⟩
    have hmin2 : ∀ z ∈ B2, ∑ w ∈ X, y w ≤ ∑ w ∈ X, z w := by
      intro z hz
      have h1 := Finset.sum_add_sum_compl X z
      have h2 := Finset.sum_add_sum_compl X y
      have h3 := cs2 z hz
      have h4 := hmax2 z hz
      omega
    -- gap
    have hgap : ∑ w ∈ X, x w + 1 ≤ ∑ w ∈ X, y w := by
      have hsX : s ∈ X := (memX s).2 (fun k => hnot k s hs)
      have hle : ∀ w ∈ X, x w ≤ y w := by
        intro w hw
        by_contra hc; push_neg at hc
        exact (memX w).1 hw 0 hc
      have h1 : ∑ w ∈ X, (y w - x w) = (y s - x s) + ∑ w ∈ X.erase s, (y w - x w) :=
        (Finset.add_sum_erase X _ hsX).symm
      have h2 : 0 ≤ ∑ w ∈ X.erase s, (y w - x w) :=
        Finset.sum_nonneg (fun w hw => by have := hle w (Finset.mem_of_mem_erase hw); omega)
      rw [Finset.sum_sub_distrib] at h1
      omega
    refine ⟨fun v => if v ∈ X then -1 else 0, Or.inr (fun v => by by_cases h : v ∈ X <;> simp [h]), ?_⟩
    have hf : ∀ z : V → ℤ,
        (∑ v, (((if v ∈ X then -1 else 0 : ℤ)) : ℝ) * (z v : ℝ)) = -((∑ w ∈ X, z w : ℤ) : ℝ) := by
      intro z
      push_cast
      rw [← Finset.sum_neg_distrib]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => v ∈ X)]
      have hfx : Finset.univ.filter (fun v => v ∈ X) = X := by ext v; simp
      rw [hfx]
      have h0 : ∑ v ∈ Finset.univ.filter (fun v => v ∉ X),
          ((if v ∈ X then (-1 : ℝ) else 0) * (z v : ℝ)) = 0 :=
        Finset.sum_eq_zero (fun v hv => by simp at hv; simp [hv])
      rw [h0, add_zero]
      exact Finset.sum_congr rfl (fun v hv => by simp [hv])
    simp only [hf]
    have hL : -(((∑ w ∈ X, x w : ℤ)) : ℝ) ≤
        sInf ((fun z : V → ℤ => -(((∑ w ∈ X, z w : ℤ)) : ℝ)) '' B1) := by
      apply le_csInf (hB1ne.image _)
      rintro _ ⟨z, hz, rfl⟩
      have := hmax1 z hz
      simp only [neg_le_neg_iff]; exact_mod_cast this
    have hU : sSup ((fun z : V → ℤ => -(((∑ w ∈ X, z w : ℤ)) : ℝ)) '' B2) ≤
        -(((∑ w ∈ X, y w : ℤ)) : ℝ) := by
      apply csSup_le (hB2ne.image _)
      rintro _ ⟨z, hz, rfl⟩
      have := hmin2 z hz
      simp only [neg_le_neg_iff]; exact_mod_cast this
    have hg : ((∑ w ∈ X, x w : ℤ) : ℝ) + 1 ≤ ((∑ w ∈ X, y w : ℤ) : ℝ) := by exact_mod_cast hgap
    linarith
  · push_neg at hpos
    -- y ≤ x pointwise, y ≠ x: sums differ; use p = 1
    have hgap : ∑ w, y w + 1 ≤ ∑ w, x w := by
      obtain ⟨u, hu⟩ : ∃ u, x u ≠ y u := by
        by_contra h; push_neg at h; exact hne (funext h)
      have hlt : y u < x u := lt_of_le_of_ne (hpos u) (Ne.symm hu)
      have : ∑ w, y w < ∑ w, x w := Finset.sum_lt_sum (fun w _ => hpos w) ⟨u, Finset.mem_univ _, hlt⟩
      omega
    refine ⟨fun _ => 1, Or.inl (fun v => Or.inr rfl), ?_⟩
    have hf : ∀ z : V → ℤ, (∑ v, (((fun _ => (1 : ℤ)) v : ℤ) : ℝ) * (z v : ℝ)) = ((∑ w, z w : ℤ) : ℝ) := by
      intro z; push_cast; simp
    simp only [hf]
    have hL : ((∑ w, x w : ℤ) : ℝ) ≤ sInf ((fun z : V → ℤ => ((∑ w, z w : ℤ) : ℝ)) '' B1) := by
      apply le_csInf (hB1ne.image _)
      rintro _ ⟨z, hz, rfl⟩
      dsimp only; rw [cs1 z hz]
    have hU : sSup ((fun z : V → ℤ => ((∑ w, z w : ℤ) : ℝ)) '' B2) ≤ ((∑ w, y w : ℤ) : ℝ) := by
      apply csSup_le (hB2ne.image _)
      rintro _ ⟨z, hz, rfl⟩
      dsimp only; rw [cs2 z hz]
    have hg : ((∑ w, y w : ℤ) : ℝ) + 1 ≤ ((∑ w, x w : ℤ) : ℝ) := by exact_mod_cast hgap
    linarith

end P2MB0e1201f

open DiscreteConvex.MConvexSetsB in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (B1 B2 : Set (V → ℤ)) (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2)
    (hB1ne : B1.Nonempty) (hB2ne : B2.Nonempty) (hdisj : B1 ∩ B2 = ∅) :
    ∃ p : V → ℤ, ((∀ v, p v = 0 ∨ p v = 1) ∨ (∀ v, p v = 0 ∨ p v = -1)) ∧
      sInf ((fun x : V → ℤ => (∑ v, (p v : ℝ) * (x v : ℝ))) '' B1) -
        sSup ((fun x : V → ℤ => (∑ v, (p v : ℝ) * (x v : ℝ))) '' B2) ≥ 1 := by
  exact P2MB0e1201f.main B1 B2 hExc1 hExc2 hB1ne hB2ne hdisj
