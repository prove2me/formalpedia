-- Prove2me | solution 1 for FriedmannCunningham.parity_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T07:42:16.832141+00:00
-- url     : https://prove2.me/submissions/a7689342-d11f-4b60-808a-db6c84d0271e

import Definitions.Def_friedmann_cunningham
import Mathlib.Data.Fintype.Pigeonhole

set_option autoImplicit false

namespace FriedmannCunningham

open FriedmannMultiplicity
open FriedmannSimplex

@[ext]
lemma Name.ext {u v : Name} (h1 : u.kind = v.kind) (h2 : u.level = v.level) (h3 : u.one = v.one) :
    u = v := by
  cases u; cases v; simp_all

/-! ### Part 1: General Multiplicity Order and `playValue` Unfolding Infrastructure -/

lemma reward_injective : Function.Injective FriedmannParity.reward := by
  intro p q hpq
  unfold FriedmannParity.reward at hpq
  split_ifs at hpq <;> omega

section GeneralOrder

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma setEquivalent_refl (G : FriedmannParity.Game V) (A : Finset V) : SetEquivalent G A A :=
  fun _ => rfl

omit [Fintype V] [DecidableEq V] in
lemma setEquivalent_symm {G : FriedmannParity.Game V} {A B : Finset V} (h : SetEquivalent G A B) :
    SetEquivalent G B A :=
  fun p => (h p).symm

omit [Fintype V] [DecidableEq V] in
lemma setEquivalent_trans {G : FriedmannParity.Game V} {A B C : Finset V}
    (h1 : SetEquivalent G A B) (h2 : SetEquivalent G B C) :
    SetEquivalent G A C :=
  fun p => (h1 p).trans (h2 p)

omit [Fintype V] [DecidableEq V] in
lemma not_setLT_of_setEquivalent {G : FriedmannParity.Game V} {A B : Finset V}
    (h : SetEquivalent G A B) : ¬ SetLT G A B := by
  rintro ⟨p, hpne, _, _⟩
  exact hpne (h p)

omit [Fintype V] [DecidableEq V] in
lemma setLT_congr_left {G : FriedmannParity.Game V} {A A' B : Finset V}
    (hA : SetEquivalent G A A') (h : SetLT G A B) : SetLT G A' B := by
  rcases h with ⟨p, hpne, hgt, hpar⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← hA p]; exact hpne
  · intro q hq; rw [← hA q]; exact hgt q hq
  · rcases hpar with ⟨he, hlt⟩ | ⟨ho, hlt⟩
    · left; rw [← hA p]; exact ⟨he, hlt⟩
    · right; rw [← hA p]; exact ⟨ho, hlt⟩

omit [Fintype V] [DecidableEq V] in
lemma setLT_congr_right {G : FriedmannParity.Game V} {A B B' : Finset V}
    (hB : SetEquivalent G B B') (h : SetLT G A B) : SetLT G A B' := by
  rcases h with ⟨p, hpne, hgt, hpar⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← hB p]; exact hpne
  · intro q hq; rw [← hB q]; exact hgt q hq
  · rcases hpar with ⟨he, hlt⟩ | ⟨ho, hlt⟩
    · left; rw [← hB p]; exact ⟨he, hlt⟩
    · right; rw [← hB p]; exact ⟨ho, hlt⟩

omit [Fintype V] [DecidableEq V] in
lemma setLT_asymm {G : FriedmannParity.Game V} {A B : Finset V}
    (h1 : SetLT G A B) (h2 : SetLT G B A) : False := by
  rcases h1 with ⟨p₁, hpne₁, hgt₁, hpar₁⟩
  rcases h2 with ⟨p₂, hpne₂, hgt₂, hpar₂⟩
  rcases lt_trichotomy p₁ p₂ with hlt | rfl | hgt
  · exact hpne₂ (hgt₁ p₂ hlt).symm
  · rcases hpar₁ with ⟨he₁, hlt₁⟩ | ⟨ho₁, hlt₁⟩ <;>
    rcases hpar₂ with ⟨he₂, hlt₂⟩ | ⟨ho₂, hlt₂⟩ <;> omega
  · exact hpne₁ (hgt₂ p₁ hgt).symm

omit [Fintype V] [DecidableEq V] in
lemma setLT_trans {G : FriedmannParity.Game V} {A B C : Finset V}
    (h1 : SetLT G A B) (h2 : SetLT G B C) : SetLT G A C := by
  rcases h1 with ⟨p₁, hpne₁, hgt₁, hpar₁⟩
  rcases h2 with ⟨p₂, hpne₂, hgt₂, hpar₂⟩
  rcases lt_trichotomy p₁ p₂ with hlt | rfl | hgt
  · refine ⟨p₂, ?_, ?_, ?_⟩
    · rw [hgt₁ p₂ hlt]; exact hpne₂
    · intro q hq
      exact (hgt₁ q (lt_trans hlt hq)).trans (hgt₂ q hq)
    · rw [hgt₁ p₂ hlt]; exact hpar₂
  · refine ⟨p₁, ?_, ?_, ?_⟩
    · rcases hpar₁ with ⟨_, hlt₁⟩ | ⟨_, hlt₁⟩ <;>
      rcases hpar₂ with ⟨_, hlt₂⟩ | ⟨_, hlt₂⟩ <;> omega
    · intro q hq
      exact (hgt₁ q hq).trans (hgt₂ q hq)
    · rcases hpar₁ with ⟨he₁, hlt₁⟩ | ⟨ho₁, hlt₁⟩ <;>
      rcases hpar₂ with ⟨he₂, hlt₂⟩ | ⟨ho₂, hlt₂⟩
      · left; exact ⟨he₁, by omega⟩
      · omega
      · omega
      · right; exact ⟨ho₁, by omega⟩
  · refine ⟨p₁, ?_, ?_, ?_⟩
    · rw [← hgt₂ p₁ hgt]; exact hpne₁
    · intro q hq
      exact (hgt₁ q hq).trans (hgt₂ q (lt_trans hgt hq))
    · rw [← hgt₂ p₁ hgt]; exact hpar₁

omit [Fintype V] [DecidableEq V] in
lemma count_eq_zero_of_sup_lt {G : FriedmannParity.Game V} {A : Finset V} {q : ℕ}
    (hq : A.sup G.priority < q) : count G A q = 0 := by
  classical
  unfold count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v hv
  have hle : G.priority v ≤ A.sup G.priority := Finset.le_sup hv
  omega

omit [Fintype V] [DecidableEq V] in
lemma setLT_trichotomy_aux (G : FriedmannParity.Game V) (A B : Finset V) :
    ∀ M : ℕ, (∀ q, M < q → count G A q = count G B q) →
      SetEquivalent G A B ∨ SetLT G A B ∨ SetLT G B A
  | 0, hgt => by
    rcases lt_trichotomy (count G A 0) (count G B 0) with hlt | heq | hgt0
    · right; left
      exact ⟨0, by omega, hgt, Or.inl ⟨rfl, hlt⟩⟩
    · left
      intro q
      rcases Nat.eq_zero_or_pos q with rfl | hpos
      · exact heq
      · exact hgt q hpos
    · right; right
      exact ⟨0, by omega, fun q hq => (hgt q hq).symm, Or.inl ⟨rfl, hgt0⟩⟩
  | M + 1, hgt => by
    rcases lt_trichotomy (count G A (M + 1)) (count G B (M + 1)) with hlt | heq | hgt1
    · right; rcases Nat.mod_two_eq_zero_or_one (M + 1) with hpar | hpar
      · left; exact ⟨M + 1, by omega, hgt, Or.inl ⟨hpar, hlt⟩⟩
      · right; exact ⟨M + 1, by omega, fun q hq => (hgt q hq).symm, Or.inr ⟨hpar, hlt⟩⟩
    · apply setLT_trichotomy_aux G A B M
      intro q hq
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hq) with rfl | hq'
      · exact heq
      · exact hgt q hq'
    · right; rcases Nat.mod_two_eq_zero_or_one (M + 1) with hpar | hpar
      · right; exact ⟨M + 1, by omega, fun q hq => (hgt q hq).symm, Or.inl ⟨hpar, hgt1⟩⟩
      · left; exact ⟨M + 1, by omega, hgt, Or.inr ⟨hpar, hgt1⟩⟩

omit [Fintype V] in
lemma setLT_trichotomy (G : FriedmannParity.Game V) (A B : Finset V) :
    SetEquivalent G A B ∨ SetLT G A B ∨ SetLT G B A := by
  apply setLT_trichotomy_aux G A B ((A ∪ B).sup G.priority)
  intro q hq
  have hA : A.sup G.priority < q :=
    lt_of_le_of_lt (Finset.sup_mono Finset.subset_union_left) hq
  have hB : B.sup G.priority < q :=
    lt_of_le_of_lt (Finset.sup_mono Finset.subset_union_right) hq
  rw [count_eq_zero_of_sup_lt hA, count_eq_zero_of_sup_lt hB]

omit [Fintype V] [DecidableEq V] in
lemma valueLT_asymm {G : FriedmannParity.Game V} {a b : FriedmannParity.Valuation V}
    (h1 : ValueLT G a b) (h2 : ValueLT G b a) : False := by
  rcases h1 with hr1 | ⟨hp1, hs1⟩ | ⟨hp1, heq1, hl1⟩ <;>
  rcases h2 with hr2 | ⟨hp2, hs2⟩ | ⟨hp2, heq2, hl2⟩
  · omega
  · rw [hp2] at hr1; omega
  · rw [hp2] at hr1; omega
  · rw [hp1] at hr2; omega
  · exact setLT_asymm hs1 hs2
  · exact not_setLT_of_setEquivalent (setEquivalent_symm heq2) hs1
  · rw [hp1] at hr2; omega
  · exact not_setLT_of_setEquivalent (setEquivalent_symm heq1) hs2
  · rcases hl1 with ⟨ho1, hlt1⟩ | ⟨he1, hlt1⟩ <;>
    rcases hl2 with ⟨ho2, hlt2⟩ | ⟨he2, hlt2⟩ <;> omega

omit [Fintype V] [DecidableEq V] in
lemma valueLT_irrefl (G : FriedmannParity.Game V) (a : FriedmannParity.Valuation V) :
    ¬ ValueLT G a a :=
  fun h => valueLT_asymm h h

omit [Fintype V] [DecidableEq V] in
lemma valueLE_refl (G : FriedmannParity.Game V) (a : FriedmannParity.Valuation V) :
    ValueLE G a a :=
  valueLT_irrefl G a

omit [Fintype V] [DecidableEq V] in
lemma valueLE_total (G : FriedmannParity.Game V) (a b : FriedmannParity.Valuation V) :
    ValueLE G a b ∨ ValueLE G b a := by
  by_cases h : ValueLT G b a
  · right; exact fun h' => valueLT_asymm h h'
  · left; exact h

omit [Fintype V] [DecidableEq V] in
lemma valueLT_trans {G : FriedmannParity.Game V} {a b c : FriedmannParity.Valuation V}
    (h1 : ValueLT G a b) (h2 : ValueLT G b c) : ValueLT G a c := by
  rcases h1 with hr1 | ⟨hp1, hs1⟩ | ⟨hp1, heq1, hl1⟩ <;>
  rcases h2 with hr2 | ⟨hp2, hs2⟩ | ⟨hp2, heq2, hl2⟩
  · left; omega
  · left; rw [← hp2]; exact hr1
  · left; rw [← hp2]; exact hr1
  · left; rw [hp1]; exact hr2
  · right; left; exact ⟨hp1.trans hp2, setLT_trans hs1 hs2⟩
  · right; left; exact ⟨hp1.trans hp2, setLT_congr_right heq2 hs1⟩
  · left; rw [hp1]; exact hr2
  · right; left; exact ⟨hp1.trans hp2, setLT_congr_left (setEquivalent_symm heq1) hs2⟩
  · right; right
    refine ⟨hp1.trans hp2, setEquivalent_trans heq1 heq2, ?_⟩
    rw [← hp1] at hl2
    rcases hl1 with ⟨ho1, hlt1⟩ | ⟨he1, hlt1⟩ <;>
    rcases hl2 with ⟨ho2, hlt2⟩ | ⟨he2, hlt2⟩
    · left; exact ⟨ho1, by omega⟩
    · omega
    · omega
    · right; exact ⟨he1, by omega⟩

def ValEq (G : FriedmannParity.Game V) (a b : FriedmannParity.Valuation V) : Prop :=
  a.cyclePriority = b.cyclePriority ∧
  SetEquivalent G a.path b.path ∧
  a.length = b.length

omit [Fintype V] in
lemma valueLT_trichotomy (G : FriedmannParity.Game V) (a b : FriedmannParity.Valuation V) :
    ValEq G a b ∨ ValueLT G a b ∨ ValueLT G b a := by
  rcases lt_trichotomy (FriedmannParity.reward a.cyclePriority) (FriedmannParity.reward b.cyclePriority) with hlt | heq | hgt
  · right; left; exact Or.inl hlt
  · have hp : a.cyclePriority = b.cyclePriority := reward_injective heq
    rcases setLT_trichotomy G a.path b.path with hseq | hslt | hsgt
    · rcases lt_trichotomy a.length b.length with hllt | hleq | hlgt
      · right; rcases Nat.mod_two_eq_zero_or_one a.cyclePriority with hpar | hpar
        · right; exact Or.inr (Or.inr ⟨hp.symm, setEquivalent_symm hseq, Or.inr ⟨hp ▸ hpar, hllt⟩⟩)
        · left; exact Or.inr (Or.inr ⟨hp, hseq, Or.inl ⟨hpar, hllt⟩⟩)
      · left; exact ⟨hp, hseq, hleq⟩
      · right; rcases Nat.mod_two_eq_zero_or_one a.cyclePriority with hpar | hpar
        · left; exact Or.inr (Or.inr ⟨hp, hseq, Or.inr ⟨hpar, hlgt⟩⟩)
        · right; exact Or.inr (Or.inr ⟨hp.symm, setEquivalent_symm hseq, Or.inl ⟨hp ▸ hpar, hlgt⟩⟩)
    · right; left; exact Or.inr (Or.inl ⟨hp, hslt⟩)
    · right; right; exact Or.inr (Or.inl ⟨hp.symm, hsgt⟩)
  · right; right; exact Or.inl hgt

omit [Fintype V] in
lemma valueLE_iff (G : FriedmannParity.Game V) (a b : FriedmannParity.Valuation V) :
    ValueLE G a b ↔ ValEq G a b ∨ ValueLT G a b := by
  constructor
  · intro h
    rcases valueLT_trichotomy G a b with heq | hlt | hgt
    · exact Or.inl heq
    · exact Or.inr hlt
    · exact False.elim (h hgt)
  · rintro (⟨hp, hseq, hlen⟩ | hlt) hgt
    · rcases hgt with hr | ⟨_, hslt⟩ | ⟨_, _, hl⟩
      · rw [hp] at hr; omega
      · exact not_setLT_of_setEquivalent (setEquivalent_symm hseq) hslt
      · rcases hl with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega
    · exact valueLT_asymm hlt hgt

omit [Fintype V] [DecidableEq V] in
lemma valueLT_of_valEq_of_valueLT {G : FriedmannParity.Game V} {a b c : FriedmannParity.Valuation V}
    (h1 : ValEq G a b) (h2 : ValueLT G b c) : ValueLT G a c := by
  rcases h1 with ⟨hp1, hseq1, hlen1⟩
  rcases h2 with hr2 | ⟨hp2, hs2⟩ | ⟨hp2, heq2, hl2⟩
  · left; rw [hp1]; exact hr2
  · right; left; exact ⟨hp1.trans hp2, setLT_congr_left (setEquivalent_symm hseq1) hs2⟩
  · right; right
    refine ⟨hp1.trans hp2, setEquivalent_trans hseq1 heq2, ?_⟩
    rw [hp1, hlen1]; exact hl2

omit [Fintype V] [DecidableEq V] in
lemma valueLT_of_valueLT_of_valEq {G : FriedmannParity.Game V} {a b c : FriedmannParity.Valuation V}
    (h1 : ValueLT G a b) (h2 : ValEq G b c) : ValueLT G a c := by
  rcases h2 with ⟨hp2, hseq2, hlen2⟩
  rcases h1 with hr1 | ⟨hp1, hs1⟩ | ⟨hp1, heq1, hl1⟩
  · left; rw [← hp2]; exact hr1
  · right; left; exact ⟨hp1.trans hp2, setLT_congr_right hseq2 hs1⟩
  · right; right
    refine ⟨hp1.trans hp2, setEquivalent_trans heq1 hseq2, ?_⟩
    rw [← hlen2]; exact hl1

omit [Fintype V] [DecidableEq V] in
lemma valEq_symm {G : FriedmannParity.Game V} {a b : FriedmannParity.Valuation V}
    (h : ValEq G a b) : ValEq G b a :=
  ⟨h.1.symm, setEquivalent_symm h.2.1, h.2.2.symm⟩

omit [Fintype V] [DecidableEq V] in
lemma valEq_trans {G : FriedmannParity.Game V} {a b c : FriedmannParity.Valuation V}
    (h1 : ValEq G a b) (h2 : ValEq G b c) : ValEq G a c :=
  ⟨h1.1.trans h2.1, setEquivalent_trans h1.2.1 h2.2.1, h1.2.2.trans h2.2.2⟩

omit [Fintype V] in
lemma valueLE_trans {G : FriedmannParity.Game V} {a b c : FriedmannParity.Valuation V}
    (h1 : ValueLE G a b) (h2 : ValueLE G b c) : ValueLE G a c := by
  rw [valueLE_iff] at h1 h2 ⊢
  rcases h1 with heq1 | hlt1 <;> rcases h2 with heq2 | hlt2
  · exact Or.inl (valEq_trans heq1 heq2)
  · exact Or.inr (valueLT_of_valEq_of_valueLT heq1 hlt2)
  · exact Or.inr (valueLT_of_valueLT_of_valEq hlt1 heq2)
  · exact Or.inr (valueLT_trans hlt1 hlt2)

omit [Fintype V] in
lemma valEq_of_valueLE_antisymm {G : FriedmannParity.Game V} {a b : FriedmannParity.Valuation V}
    (h1 : ValueLE G a b) (h2 : ValueLE G b a) : ValEq G a b := by
  rcases valueLT_trichotomy G a b with heq | hlt | hgt
  · exact heq
  · exact False.elim (h2 hlt)
  · exact False.elim (h1 hgt)

end GeneralOrder

section GeneralOrbit

variable {V : Type} [Fintype V] [DecidableEq V]

def step (G : FriedmannParity.Game V) (σ τ : V → V) (w : V) : V :=
  if G.owner w = false then σ w else τ w

omit [Fintype V] [DecidableEq V] in
lemma play_eq_iterate (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    FriedmannParity.play G σ τ v t = (step G σ τ)^[t] v :=
  rfl

omit [Fintype V] [DecidableEq V] in
lemma play_zero (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    FriedmannParity.play G σ τ v 0 = v :=
  rfl

omit [Fintype V] [DecidableEq V] in
lemma play_succ (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    FriedmannParity.play G σ τ v (t + 1) = FriedmannParity.play G σ τ (step G σ τ v) t :=
  Function.iterate_succ_apply (step G σ τ) t v

omit [Fintype V] [DecidableEq V] in
lemma play_succ' (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    FriedmannParity.play G σ τ v (t + 1) = step G σ τ (FriedmannParity.play G σ τ v t) :=
  Function.iterate_succ_apply' (step G σ τ) t v

omit [Fintype V] [DecidableEq V] in
lemma play_add (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) (a b : ℕ) :
    FriedmannParity.play G σ τ v (a + b) =
      FriedmannParity.play G σ τ (FriedmannParity.play G σ τ v a) b := by
  simp only [play_eq_iterate]
  rw [Nat.add_comm, Function.iterate_add_apply]

omit [DecidableEq V] in
lemma mem_recurring_iff {π : ℕ → V} {w : V} :
    w ∈ FriedmannParity.recurring π ↔ ∀ t, ∃ k, t ≤ k ∧ π k = w := by
  classical
  unfold FriedmannParity.recurring
  simp

omit [DecidableEq V] in
lemma recurring_step (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    FriedmannParity.recurring (FriedmannParity.play G σ τ (step G σ τ v)) =
      FriedmannParity.recurring (FriedmannParity.play G σ τ v) := by
  ext w
  simp only [mem_recurring_iff]
  constructor
  · intro h t
    rcases h t with ⟨k, htk, hk⟩
    refine ⟨k + 1, by omega, ?_⟩
    rw [play_succ]
    exact hk
  · intro h t
    rcases h (t + 1) with ⟨k, htk, hk⟩
    refine ⟨k - 1, by omega, ?_⟩
    rw [← play_succ]
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1]
    exact hk

omit [DecidableEq V] in
lemma recurring_play (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    FriedmannParity.recurring (FriedmannParity.play G σ τ (FriedmannParity.play G σ τ v t)) =
      FriedmannParity.recurring (FriedmannParity.play G σ τ v) := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [play_succ, ih, recurring_step]

omit [DecidableEq V] in
lemma recurring_nonempty (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    (FriedmannParity.recurring (FriedmannParity.play G σ τ v)).Nonempty := by
  classical
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hnot : ∀ w : V, ∃ t, ∀ k, t ≤ k → FriedmannParity.play G σ τ v k ≠ w := by
    intro w
    have hw : w ∉ FriedmannParity.recurring (FriedmannParity.play G σ τ v) := by simp [h]
    rw [mem_recurring_iff] at hw
    simpa using hw
  choose B hB using hnot
  let T := Finset.univ.sup B
  let w := FriedmannParity.play G σ τ v T
  have hle : B w ≤ T := Finset.le_sup (Finset.mem_univ w)
  exact hB w T hle rfl

omit [DecidableEq V] in
lemma exists_play_eq_of_mem_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v)) :
    ∃ k, FriedmannParity.play G σ τ v k = w := by
  rw [mem_recurring_iff] at hw
  rcases hw 0 with ⟨k, _, hk⟩
  exact ⟨k, hk⟩

omit [DecidableEq V] in
lemma step_mem_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v)) :
    step G σ τ w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v) := by
  rw [mem_recurring_iff] at hw ⊢
  intro t
  rcases hw t with ⟨k, htk, hk⟩
  refine ⟨k + 1, by omega, ?_⟩
  rw [play_succ', hk]

omit [DecidableEq V] in
lemma play_mem_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v)) (s : ℕ) :
    FriedmannParity.play G σ τ w s ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v) := by
  induction s with
  | zero => exact hw
  | succ s ih =>
    rw [play_succ']
    exact step_mem_recurring ih

omit [DecidableEq V] in
lemma recurring_eq_of_mem_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v)) :
    FriedmannParity.recurring (FriedmannParity.play G σ τ w) =
      FriedmannParity.recurring (FriedmannParity.play G σ τ v) := by
  rcases exists_play_eq_of_mem_recurring hw with ⟨t₀, rfl⟩
  exact recurring_play G σ τ v t₀

omit [DecidableEq V] in
lemma exists_recurring_eq_sup (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    ∃ w, w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v) ∧
      G.priority w = (FriedmannParity.recurring (FriedmannParity.play G σ τ v)).sup G.priority := by
  rcases Finset.exists_mem_eq_sup (FriedmannParity.recurring (FriedmannParity.play G σ τ v))
    (recurring_nonempty G σ τ v) G.priority with ⟨w, hw, hp⟩
  exact ⟨w, hw, hp.symm⟩

noncomputable def cycleLeader (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) : V := by
  classical
  let π := FriedmannParity.play G σ τ v
  let p := (FriedmannParity.recurring π).sup G.priority
  exact if h : ∃ w, w ∈ FriedmannParity.recurring π ∧ G.priority w = p
    then Classical.choose h else v

omit [DecidableEq V] in
lemma cycleLeader_eq_choose (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    cycleLeader G σ τ v = Classical.choose (exists_recurring_eq_sup G σ τ v) := by
  unfold cycleLeader
  dsimp only
  rw [dif_pos (exists_recurring_eq_sup G σ τ v)]

omit [DecidableEq V] in
lemma cycleLeader_mem_recurring (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    cycleLeader G σ τ v ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v) := by
  rw [cycleLeader_eq_choose]
  exact (Classical.choose_spec (exists_recurring_eq_sup G σ τ v)).1

omit [DecidableEq V] in
lemma priority_cycleLeader (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    G.priority (cycleLeader G σ τ v) =
      (FriedmannParity.recurring (FriedmannParity.play G σ τ v)).sup G.priority := by
  rw [cycleLeader_eq_choose]
  exact (Classical.choose_spec (exists_recurring_eq_sup G σ τ v)).2

omit [DecidableEq V] in
lemma cycleLeader_step (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    cycleLeader G σ τ (step G σ τ v) = cycleLeader G σ τ v := by
  rw [cycleLeader_eq_choose, cycleLeader_eq_choose]
  have hrec := recurring_step G σ τ v
  congr! 2
  all_goals rw [hrec]

omit [Fintype V] [DecidableEq V] in
lemma exists_lt_of_play_eq_of_add {G : FriedmannParity.Game V} {σ τ : V → V} {v w : V} {i j : ℕ}
    (hij : i < j) (heq : FriedmannParity.play G σ τ v i = FriedmannParity.play G σ τ v j) :
    ∀ d : ℕ, FriedmannParity.play G σ τ v (i + d) = w →
      ∃ r < j, FriedmannParity.play G σ τ v r = w := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hlt : i + d < j
    · exact ⟨i + d, hlt, hd⟩
    · have hlt' : i + d - j < d := by omega
      apply ih (i + d - j) hlt'
      have h1 : j + (i + d - j) = i + d := by omega
      rw [play_add, heq, ← play_add, h1, hd]

omit [DecidableEq V] in
lemma exists_lt_of_play_eq_of_mem_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v))
    {i j : ℕ} (hij : i < j)
    (heq : FriedmannParity.play G σ τ v i = FriedmannParity.play G σ τ v j) :
    ∃ r < j, FriedmannParity.play G σ τ v r = w := by
  rw [mem_recurring_iff] at hw
  rcases hw i with ⟨k, hik, hk⟩
  have hk' : i + (k - i) = k := by omega
  rw [← hk'] at hk
  exact exists_lt_of_play_eq_of_add hij heq (k - i) hk

omit [DecidableEq V] in
lemma exists_play_eq_cycleLeader (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    ∃ k : ℕ, FriedmannParity.play G σ τ v k = cycleLeader G σ τ v :=
  exists_play_eq_of_mem_recurring (cycleLeader_mem_recurring G σ τ v)

lemma playValue_cyclePriority (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    (FriedmannParity.playValue G σ τ v).cyclePriority =
      (FriedmannParity.recurring (FriedmannParity.play G σ τ v)).sup G.priority :=
  rfl

lemma playValue_cyclePriority_eq_priority_cycleLeader
    (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    (FriedmannParity.playValue G σ τ v).cyclePriority = G.priority (cycleLeader G σ τ v) :=
  (priority_cycleLeader G σ τ v).symm

lemma playValue_cyclePriority_step (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    (FriedmannParity.playValue G σ τ (step G σ τ v)).cyclePriority =
      (FriedmannParity.playValue G σ τ v).cyclePriority := by
  simp only [playValue_cyclePriority, recurring_step]

lemma playValue_length_eq_find (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    (FriedmannParity.playValue G σ τ v).length =
      Nat.find (exists_play_eq_cycleLeader G σ τ v) := by
  classical
  change (if h : ∃ k : ℕ, FriedmannParity.play G σ τ v k = cycleLeader G σ τ v
    then Nat.find h else 0) = _
  rw [dif_pos (exists_play_eq_cycleLeader G σ τ v)]

lemma play_playValue_length (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) :
    FriedmannParity.play G σ τ v (FriedmannParity.playValue G σ τ v).length =
      cycleLeader G σ τ v := by
  rw [playValue_length_eq_find]
  exact Nat.find_spec (exists_play_eq_cycleLeader G σ τ v)

lemma play_ne_cycleLeader_of_lt_length {G : FriedmannParity.Game V} {σ τ : V → V} {v : V} {t : ℕ}
    (ht : t < (FriedmannParity.playValue G σ τ v).length) :
    FriedmannParity.play G σ τ v t ≠ cycleLeader G σ τ v := by
  rw [playValue_length_eq_find] at ht
  exact Nat.find_min (exists_play_eq_cycleLeader G σ τ v) ht

lemma length_le_of_play_eq_cycleLeader (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) {t : ℕ}
    (ht : FriedmannParity.play G σ τ v t = cycleLeader G σ τ v) :
    (FriedmannParity.playValue G σ τ v).length ≤ t := by
  rw [playValue_length_eq_find]
  exact Nat.find_min' (exists_play_eq_cycleLeader G σ τ v) ht

lemma play_injective_of_le_length (G : FriedmannParity.Game V) (σ τ : V → V) (v : V) {i j : ℕ}
    (hi : i ≤ (FriedmannParity.playValue G σ τ v).length)
    (hj : j ≤ (FriedmannParity.playValue G σ τ v).length)
    (heq : FriedmannParity.play G σ τ v i = FriedmannParity.play G σ τ v j) :
    i = j := by
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · rcases exists_lt_of_play_eq_of_mem_recurring (cycleLeader_mem_recurring G σ τ v) hlt heq with
      ⟨r, hrj, hr⟩
    exact False.elim (play_ne_cycleLeader_of_lt_length (lt_of_lt_of_le hrj hj) hr)
  · rfl
  · rcases exists_lt_of_play_eq_of_mem_recurring (cycleLeader_mem_recurring G σ τ v) hgt heq.symm with
      ⟨r, hri, hr⟩
    exact False.elim (play_ne_cycleLeader_of_lt_length (lt_of_lt_of_le hri hi) hr)

lemma mem_playValue_path_iff {G : FriedmannParity.Game V} {σ τ : V → V} {v u : V} :
    u ∈ (FriedmannParity.playValue G σ τ v).path ↔
      (∃ t < (FriedmannParity.playValue G σ τ v).length, FriedmannParity.play G σ τ v t = u) ∧
      (FriedmannParity.playValue G σ τ v).cyclePriority < G.priority u := by
  classical
  change u ∈ ((Finset.range (FriedmannParity.playValue G σ τ v).length).image
    (FriedmannParity.play G σ τ v)).filter
    (fun w => (FriedmannParity.playValue G σ τ v).cyclePriority < G.priority w) ↔ _
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]

lemma playValue_path_eq_empty_of_mem_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v x : V}
    (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v)) :
    (FriedmannParity.playValue G σ τ x).path = ∅ := by
  ext u
  rw [mem_playValue_path_iff]
  simp only [Finset.notMem_empty, iff_false, not_and]
  rintro ⟨t, _, rfl⟩
  have hmem : FriedmannParity.play G σ τ x t ∈
      FriedmannParity.recurring (FriedmannParity.play G σ τ x) :=
    play_mem_recurring (by rw [recurring_eq_of_mem_recurring hx]; exact hx) t
  have hle : G.priority (FriedmannParity.play G σ τ x t) ≤
      (FriedmannParity.playValue G σ τ x).cyclePriority :=
    Finset.le_sup hmem
  omega

noncomputable def prepend (G : FriedmannParity.Game V) (u : V)
    (a : FriedmannParity.Valuation V) : FriedmannParity.Valuation V := by
  classical
  exact ⟨a.cyclePriority,
    if a.cyclePriority < G.priority u then insert u a.path else a.path,
    a.length + 1⟩

lemma playValue_length_eq_succ_of_ne_cycleLeader {G : FriedmannParity.Game V} {σ τ : V → V} {u : V}
    (hu : u ≠ cycleLeader G σ τ u) :
    (FriedmannParity.playValue G σ τ u).length =
      (FriedmannParity.playValue G σ τ (step G σ τ u)).length + 1 := by
  have hpos : 0 < (FriedmannParity.playValue G σ τ u).length := by
    by_contra h0
    have hzero : (FriedmannParity.playValue G σ τ u).length = 0 := by omega
    have hplay := play_playValue_length G σ τ u
    rw [hzero, play_zero] at hplay
    exact hu hplay
  have hle1 : (FriedmannParity.playValue G σ τ (step G σ τ u)).length ≤
      (FriedmannParity.playValue G σ τ u).length - 1 := by
    apply length_le_of_play_eq_cycleLeader G σ τ (step G σ τ u)
    rw [cycleLeader_step, ← play_succ]
    have h1 : (FriedmannParity.playValue G σ τ u).length - 1 + 1 =
        (FriedmannParity.playValue G σ τ u).length := by omega
    rw [h1]
    exact play_playValue_length G σ τ u
  have hle2 : (FriedmannParity.playValue G σ τ u).length ≤
      (FriedmannParity.playValue G σ τ (step G σ τ u)).length + 1 := by
    apply length_le_of_play_eq_cycleLeader G σ τ u
    rw [play_succ, ← cycleLeader_step]
    exact play_playValue_length G σ τ (step G σ τ u)
  omega

lemma notMem_playValue_step_path_of_ne_cycleLeader {G : FriedmannParity.Game V} {σ τ : V → V} {u : V}
    (hu : u ≠ cycleLeader G σ τ u) :
    u ∉ (FriedmannParity.playValue G σ τ (step G σ τ u)).path := by
  rw [mem_playValue_path_iff]
  rintro ⟨⟨t, ht, hplay⟩, _⟩
  have hlen : (FriedmannParity.playValue G σ τ u).length =
      (FriedmannParity.playValue G σ τ (step G σ τ u)).length + 1 :=
    playValue_length_eq_succ_of_ne_cycleLeader hu
  rw [← play_succ] at hplay
  have h0 : FriedmannParity.play G σ τ u (t + 1) = FriedmannParity.play G σ τ u 0 := hplay
  have hinj := play_injective_of_le_length G σ τ u (by omega) (by omega) h0
  omega

lemma playValue_eq_prepend_of_ne_cycleLeader {G : FriedmannParity.Game V} {σ τ : V → V} {u : V}
    (hu : u ≠ cycleLeader G σ τ u) :
    FriedmannParity.playValue G σ τ u =
      prepend G u (FriedmannParity.playValue G σ τ (step G σ τ u)) := by
  classical
  have hcp := (playValue_cyclePriority_step G σ τ u).symm
  have hlen : (FriedmannParity.playValue G σ τ u).length =
      (FriedmannParity.playValue G σ τ (step G σ τ u)).length + 1 :=
    playValue_length_eq_succ_of_ne_cycleLeader hu
  have hpath : (FriedmannParity.playValue G σ τ u).path =
      if (FriedmannParity.playValue G σ τ (step G σ τ u)).cyclePriority < G.priority u
      then insert u (FriedmannParity.playValue G σ τ (step G σ τ u)).path
      else (FriedmannParity.playValue G σ τ (step G σ τ u)).path := by
    ext x
    rw [mem_playValue_path_iff, hlen, playValue_cyclePriority_step]
    split_ifs with hpu
    · simp only [Finset.mem_insert, mem_playValue_path_iff, playValue_cyclePriority_step]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hpx⟩
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · left; rfl
        · right
          refine ⟨⟨t - 1, by omega, ?_⟩, hpx⟩
          rw [← play_succ]
          have ht1 : t - 1 + 1 = t := by omega
          rw [ht1]
      · rintro (rfl | ⟨⟨t, ht, rfl⟩, hpx⟩)
        · exact ⟨⟨0, by omega, rfl⟩, hpu⟩
        · refine ⟨⟨t + 1, by omega, ?_⟩, hpx⟩
          rw [play_succ]
    · simp only [mem_playValue_path_iff, playValue_cyclePriority_step]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hpx⟩
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exact False.elim (hpu hpx)
        · refine ⟨⟨t - 1, by omega, ?_⟩, hpx⟩
          rw [← play_succ]
          have ht1 : t - 1 + 1 = t := by omega
          rw [ht1]
      · rintro ⟨⟨t, ht, rfl⟩, hpx⟩
        refine ⟨⟨t + 1, by omega, ?_⟩, hpx⟩
        rw [play_succ]
  unfold prepend
  cases hpv : FriedmannParity.playValue G σ τ u
  cases hpv' : FriedmannParity.playValue G σ τ (step G σ τ u)
  simp only [hpv, hpv'] at hcp hlen hpath ⊢
  congr!

omit [Fintype V] in
lemma count_insert_of_notMem {G : FriedmannParity.Game V} {A : Finset V} {u : V}
    (hu : u ∉ A) (q : ℕ) :
    count G (insert u A) q = count G A q + (if G.priority u = q then 1 else 0) := by
  classical
  unfold count
  rw [Finset.filter_insert]
  split_ifs with hq
  · rw [Finset.card_insert_of_notMem]
    simp [hu]
  · omega

omit [Fintype V] in
lemma count_prepend_of_notMem {G : FriedmannParity.Game V} {a : FriedmannParity.Valuation V}
    {u : V} (hu : u ∉ a.path) (q : ℕ) :
    count G (prepend G u a).path q =
      count G a.path q + (if a.cyclePriority < G.priority u ∧ G.priority u = q then 1 else 0) := by
  classical
  change count G (if a.cyclePriority < G.priority u then insert u a.path else a.path) q = _
  by_cases h1 : a.cyclePriority < G.priority u
  · rw [if_pos h1, count_insert_of_notMem hu]
    by_cases h2 : G.priority u = q
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), Nat.add_zero]

omit [Fintype V] in
lemma valueLE_prepend {G : FriedmannParity.Game V} {a b : FriedmannParity.Valuation V} {u : V}
    (hp : a.cyclePriority = b.cyclePriority) (hua : u ∉ a.path) (hub : u ∉ b.path)
    (hab : ValueLE G a b) :
    ValueLE G (prepend G u a) (prepend G u b) := by
  intro hlt
  apply hab
  have hcnt : ∀ q, count G (prepend G u a).path q =
      count G a.path q + (if a.cyclePriority < G.priority u ∧ G.priority u = q then 1 else 0) :=
    count_prepend_of_notMem hua
  have hcnt' : ∀ q, count G (prepend G u b).path q =
      count G b.path q + (if a.cyclePriority < G.priority u ∧ G.priority u = q then 1 else 0) := by
    intro q
    rw [count_prepend_of_notMem hub q, hp]
  rcases hlt with hr | ⟨_, ⟨p, hpne, hgt, hpar⟩⟩ | ⟨_, hseq, hl⟩
  · left
    exact hr
  · right; left
    refine ⟨hp.symm, p, ?_, ?_, ?_⟩
    · intro heq
      apply hpne
      rw [hcnt p, hcnt' p, heq]
    · intro q hq
      have hq' := hgt q hq
      rw [hcnt q, hcnt' q] at hq'
      omega
    · rcases hpar with ⟨he, hltp⟩ | ⟨ho, hltp⟩
      · left
        rw [hcnt p, hcnt' p] at hltp
        exact ⟨he, by omega⟩
      · right
        rw [hcnt p, hcnt' p] at hltp
        exact ⟨ho, by omega⟩
  · right; right
    refine ⟨hp.symm, ?_, ?_⟩
    · intro q
      have hq := hseq q
      rw [hcnt q, hcnt' q] at hq
      omega
    · change (b.cyclePriority % 2 = 1 ∧ b.length + 1 < a.length + 1) ∨
        (b.cyclePriority % 2 = 0 ∧ a.length + 1 < b.length + 1) at hl
      rcases hl with ⟨ho, hltl⟩ | ⟨he, hltl⟩
      · left; exact ⟨ho, by omega⟩
      · right; exact ⟨he, by omega⟩

lemma count_playValue_step {G : FriedmannParity.Game V} {σ τ : V → V} {u : V} {q : ℕ}
    (hq : (FriedmannParity.playValue G σ τ u).cyclePriority < q) :
    count G (FriedmannParity.playValue G σ τ u).path q =
      count G (FriedmannParity.playValue G σ τ (step G σ τ u)).path q +
        (if G.priority u = q then 1 else 0) := by
  by_cases hu : u = cycleLeader G σ τ u
  · have hpu : G.priority u = (FriedmannParity.playValue G σ τ u).cyclePriority := by
      rw [playValue_cyclePriority_eq_priority_cycleLeader, ← hu]
    have hne : G.priority u ≠ q := by omega
    have humem : u ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ u) := by
      have hmem := cycleLeader_mem_recurring G σ τ u
      rwa [← hu] at hmem
    have hp1 : (FriedmannParity.playValue G σ τ u).path = ∅ :=
      playValue_path_eq_empty_of_mem_recurring humem
    have hp2 : (FriedmannParity.playValue G σ τ (step G σ τ u)).path = ∅ :=
      playValue_path_eq_empty_of_mem_recurring (step_mem_recurring humem)
    rw [hp1, hp2, if_neg hne, Nat.add_zero]
  · rw [playValue_eq_prepend_of_ne_cycleLeader hu,
      count_prepend_of_notMem (notMem_playValue_step_path_of_ne_cycleLeader hu),
      playValue_cyclePriority_step]
    split_ifs with h1 h2 h2
    · rfl
    · exact False.elim (h2 h1.2)
    · exact False.elim (h1 ⟨by omega, h2⟩)
    · rfl

end GeneralOrbit

/-! ### Part 2: Vertex, Priority, Row, and Column Infrastructure for `parityGame n` -/

section ParityGameInfrastructure

def ValidRow (n : ℕ) (p : Kind × ℕ) : Prop :=
  match p.1 with
  | .a => 2 ≤ p.2 ∧ p.2 ≤ n
  | .b => 2 ≤ p.2 ∧ p.2 ≤ n - 1
  | .c => 2 ≤ p.2 ∧ p.2 ≤ n
  | .d => 2 ≤ p.2 ∧ p.2 ≤ n
  | .e => 1 ≤ p.2 ∧ p.2 ≤ n

lemma rowName_valid {n : ℕ} (hn : 3 ≤ n) (r : Fin (rows n)) :
    ValidRow n (rowName n r) := by
  have hr := r.isLt
  unfold rows at hr
  unfold rowName
  split_ifs <;> dsimp [ValidRow] <;> omega

lemma rowRank_lt_rows {n : ℕ} (hn : 3 ≤ n) {p : Kind × ℕ} (hp : ValidRow n p) :
    rowRank n p < rows n := by
  rcases p with ⟨k, i⟩
  cases k <;> dsimp [ValidRow, rowRank, rows] at hp ⊢ <;> omega

lemma rowRank_rowName {n : ℕ} (_hn : 3 ≤ n) (r : Fin (rows n)) :
    rowRank n (rowName n r) = r.val := by
  have hr := r.isLt
  unfold rows at hr
  unfold rowName
  split_ifs <;> dsimp [rowRank] <;> omega

lemma rowName_rowRank {n : ℕ} (hn : 3 ≤ n) {p : Kind × ℕ} (hp : ValidRow n p) :
    rowName n ⟨rowRank n p, rowRank_lt_rows hn hp⟩ = p := by
  rcases p with ⟨k, i⟩
  cases k <;> dsimp [ValidRow, rowRank, rowName] at hp ⊢ <;>
    split_ifs <;> first | omega | exact Prod.ext rfl (by omega)

def mkRow (n : ℕ) (hn : 3 ≤ n) (p : Kind × ℕ) (hp : ValidRow n p) : Fin (rows n) :=
  ⟨rowRank n p, rowRank_lt_rows hn hp⟩

@[simp]
lemma rowName_mkRow {n : ℕ} (hn : 3 ≤ n) (p : Kind × ℕ) (hp : ValidRow n p) :
    rowName n (mkRow n hn p hp) = p :=
  rowName_rowRank hn hp

lemma rowName_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (rowName n) := by
  intro q r hqr
  apply Fin.ext
  rw [← rowRank_rowName hn q, ← rowRank_rowName hn r, hqr]

lemma mkRow_rowName {n : ℕ} (hn : 3 ≤ n) (r : Fin (rows n)) :
    mkRow n hn (rowName n r) (rowName_valid hn r) = r := by
  apply rowName_injective hn
  exact rowName_mkRow hn _ _

lemma columnName_of_val {n : ℕ} (j : Fin (cols n)) (m : ℕ) (hm : j.val = m) :
    columnName n j =
      if m = 0 then ⟨.e, 1, true⟩
      else if m < 4 * n - 5 then
        let i := (m - 1) / 4 + 2
        match (m - 1) % 4 with
        | 0 => ⟨.d, i, false⟩
        | 1 => ⟨.e, i, true⟩
        | 2 => ⟨.b, i, true⟩
        | _ => ⟨.b, i, false⟩
      else if m < 6 * n - 7 then
        ⟨.c, (m - (4 * n - 5)) / 2 + 2, decide ((m - (4 * n - 5)) % 2 = 1)⟩
      else if m < 7 * n - 7 then ⟨.e, m - (6 * n - 7) + 1, false⟩
      else if m < 8 * n - 8 then ⟨.d, m - (7 * n - 7) + 2, true⟩
      else ⟨.a, n - (m - (8 * n - 8)) / 2, decide ((m - (8 * n - 8)) % 2 = 0)⟩ := by
  unfold columnName
  dsimp only
  subst hm
  rfl

lemma columnRank_lt_cols {n : ℕ} (hn : 3 ≤ n) (p : Kind × ℕ) (hp : ValidRow n p) (b : Bool) :
    columnRank n ⟨p.1, p.2, b⟩ < cols n := by
  rcases p with ⟨k, i⟩
  cases k <;> cases b <;> dsimp [ValidRow, columnRank, cols] at hp ⊢ <;>
    (try split_ifs) <;> omega

lemma columnName_columnRank {n : ℕ} (hn : 3 ≤ n) (p : Kind × ℕ) (hp : ValidRow n p) (b : Bool)
    (h : columnRank n ⟨p.1, p.2, b⟩ % cols n < cols n) :
    columnName n ⟨columnRank n ⟨p.1, p.2, b⟩ % cols n, h⟩ = ⟨p.1, p.2, b⟩ := by
  rcases p with ⟨k, i⟩
  have hlt := columnRank_lt_cols hn (k, i) hp b
  set j0 : Fin (cols n) := ⟨columnRank n ⟨k, i, b⟩ % cols n, h⟩
  have hmod : j0.val = columnRank n ⟨k, i, b⟩ := Nat.mod_eq_of_lt hlt
  cases k <;> cases b <;> dsimp [ValidRow, columnRank] at hp hmod ⊢
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact Name.ext rfl (by dsimp; omega) (by dsimp; rw [decide_eq_false_iff_not]; omega)
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact Name.ext rfl (by dsimp; omega) (by dsimp; rw [decide_eq_true_eq]; omega)
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_pos (by omega)]
    dsimp only
    have hrem : (4 * (i - 2) + 4 - 1) % 4 = 3 := by omega
    have hdiv : (4 * (i - 2) + 4 - 1) / 4 + 2 = i := by omega
    rw [hrem, hdiv]; rfl
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_pos (by omega)]
    dsimp only
    have hrem : (4 * (i - 2) + 3 - 1) % 4 = 2 := by omega
    have hdiv : (4 * (i - 2) + 3 - 1) / 4 + 2 = i := by omega
    rw [hrem, hdiv]; rfl
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact Name.ext rfl (by dsimp; omega) (by dsimp; rw [decide_eq_false_iff_not]; omega)
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact Name.ext rfl (by dsimp; omega) (by dsimp; rw [decide_eq_true_eq]; omega)
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_pos (by omega)]
    dsimp only
    have hrem : (4 * (i - 2) + 1 - 1) % 4 = 0 := by omega
    have hdiv : (4 * (i - 2) + 1 - 1) / 4 + 2 = i := by omega
    rw [hrem, hdiv]; rfl
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact Name.ext rfl (by dsimp; omega) rfl
  · rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega)]
    exact Name.ext rfl (by dsimp; omega) rfl
  · by_cases hi1 : i = 1
    · subst hi1
      rw [if_pos rfl] at hmod
      rw [columnName_of_val j0 _ hmod]
      simp
    · rw [if_neg hi1] at hmod
      rw [columnName_of_val j0 _ hmod, if_neg (by omega), if_pos (by omega)]
      dsimp only
      have hrem : (4 * (i - 2) + 2 - 1) % 4 = 1 := by omega
      have hdiv : (4 * (i - 2) + 2 - 1) / 4 + 2 = i := by omega
      rw [hrem, hdiv]; rfl

lemma columnName_actionColumn (n : ℕ) (hn : 3 ≤ n) (r : Fin (rows n)) (b : Bool) :
    columnName n (actionColumn n hn r b) = ⟨(rowName n r).1, (rowName n r).2, b⟩ :=
  columnName_columnRank hn (rowName n r) (rowName_valid hn r) b _

lemma columnName_valid_and_rank {n : ℕ} (hn : 3 ≤ n) (j : Fin (cols n)) :
    ValidRow n ((columnName n j).kind, (columnName n j).level) ∧
      columnRank n (columnName n j) = j.val := by
  set m := j.val
  have hj : m < 10 * (n - 1) := j.isLt
  have hdiv4 := Nat.div_add_mod (m - 1) 4
  have hdiv2c := Nat.div_add_mod (m - (4 * n - 5)) 2
  have hdiv2a := Nat.div_add_mod (m - (8 * n - 8)) 2
  have hval := columnName_of_val j m rfl
  split_ifs at hval with h0 h1 h2 h3 h4
  · rw [hval]; simp only [ValidRow, columnRank, ite_true]; omega
  · dsimp only at hval
    have hmod : (m - 1) % 4 = 0 ∨ (m - 1) % 4 = 1 ∨
        (m - 1) % 4 = 2 ∨ (m - 1) % 4 = 3 := by omega
    rcases hmod with hm | hm | hm | hm
    · rw [hm] at hval; rw [hval]; simp only [ValidRow, columnRank]; omega
    · rw [hm] at hval; rw [hval]; simp only [ValidRow, columnRank]; split_ifs <;> omega
    · rw [hm] at hval; rw [hval]; simp only [ValidRow, columnRank]; omega
    · rw [hm] at hval; rw [hval]; simp only [ValidRow, columnRank]; omega
  · rw [hval]
    cases hd : decide ((m - (4 * n - 5)) % 2 = 1) <;>
      [rw [decide_eq_false_iff_not] at hd; rw [decide_eq_true_eq] at hd] <;>
      simp only [ValidRow, columnRank] <;> omega
  · rw [hval]; simp only [ValidRow, columnRank]; omega
  · rw [hval]; simp only [ValidRow, columnRank]; omega
  · rw [hval]
    cases hd : decide ((m - (8 * n - 8)) % 2 = 0) <;>
      [rw [decide_eq_false_iff_not] at hd; rw [decide_eq_true_eq] at hd] <;>
      simp only [ValidRow, columnRank] <;> omega

lemma columnName_valid {n : ℕ} (hn : 3 ≤ n) (j : Fin (cols n)) :
    ValidRow n ((columnName n j).kind, (columnName n j).level) :=
  (columnName_valid_and_rank hn j).1

lemma columnRank_columnName {n : ℕ} (hn : 3 ≤ n) (j : Fin (cols n)) :
    columnRank n (columnName n j) = j.val :=
  (columnName_valid_and_rank hn j).2

lemma val_vertexCode (n k : ℕ) (hk : k < vertices n) :
    (vertexCode n k).val = k :=
  Nat.mod_eq_of_lt hk

lemma val_sinkVertex (n : ℕ) : (sinkVertex n).val = rows n + 3 * n + 1 :=
  val_vertexCode n _ (by unfold vertices; omega)

lemma val_sVertex (n : ℕ) : (sVertex n).val = rows n + 3 * n :=
  val_vertexCode n _ (by unfold vertices; omega)

lemma val_fVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (fVertex n i).val = rows n + (i - 1) :=
  val_vertexCode n _ (by unfold vertices; omega)

lemma val_gVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (gVertex n i).val = rows n + n + (i - 1) :=
  val_vertexCode n _ (by unfold vertices; omega)

lemma val_hVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (hVertex n i).val = rows n + 2 * n + (i - 1) :=
  val_vertexCode n _ (by unfold vertices; omega)

def rowVertex (n : ℕ) (p : Kind × ℕ) : Fin (vertices n) :=
  vertexCode n (rowRank n p)

lemma val_rowVertex {n : ℕ} (hn : 3 ≤ n) {p : Kind × ℕ} (hp : ValidRow n p) :
    (rowVertex n p).val = rowRank n p := by
  have hlt := rowRank_lt_rows hn hp
  exact val_vertexCode n _ (by unfold vertices; omega)

lemma val_rowVertex_lt_rows {n : ℕ} (hn : 3 ≤ n) {p : Kind × ℕ} (hp : ValidRow n p) :
    (rowVertex n p).val < rows n := by
  rw [val_rowVertex hn hp]
  exact rowRank_lt_rows hn hp

lemma rowName_rowVertex {n : ℕ} (hn : 3 ≤ n) {p : Kind × ℕ} (hp : ValidRow n p) :
    rowName n ⟨(rowVertex n p).val, val_rowVertex_lt_rows hn hp⟩ = p := by
  have h : (⟨(rowVertex n p).val, val_rowVertex_lt_rows hn hp⟩ : Fin (rows n)) =
      mkRow n hn p hp := by
    ext
    exact val_rowVertex hn hp
  rw [h, rowName_mkRow]

lemma decisionVertex_eq_rowVertex {n : ℕ} {p : Kind × ℕ} (hp : ValidRow n p) :
    decisionVertex n p.1 p.2 = rowVertex n p := by
  rcases p with ⟨k, i⟩
  unfold decisionVertex rowVertex
  cases k <;> dsimp [ValidRow] at hp ⊢ <;> split_ifs <;> omega

lemma actionSource_eq_rowVertex {n : ℕ} (hn : 3 ≤ n) (j : Fin (cols n)) :
    actionSource n j = rowVertex n ((columnName n j).kind, (columnName n j).level) :=
  decisionVertex_eq_rowVertex (columnName_valid hn j)

lemma eq_sVertex_iff (n : ℕ) (v : Fin (vertices n)) :
    v = sVertex n ↔ v.val = rows n + 3 * n := by
  rw [Fin.ext_iff, val_sVertex]

lemma eq_sinkVertex_iff (n : ℕ) (v : Fin (vertices n)) :
    v = sinkVertex n ↔ v.val = rows n + 3 * n + 1 := by
  rw [Fin.ext_iff, val_sinkVertex]

lemma gamePriority_eq (n : ℕ) (v : Fin (vertices n)) :
    gamePriority n v =
      if v.val < 2 * (n - 1) + (n - 2) then 3
      else if v.val < rows n then 5
      else if v.val < rows n + n then 6
      else if v.val < rows n + 2 * n then 2 * (v.val - (rows n + n) + 1) + 7
      else if v.val < rows n + 3 * n then 2 * (v.val - (rows n + 2 * n) + 1) + 8
      else if v.val = rows n + 3 * n then 8
      else 1 := by
  unfold gamePriority rowName rows
  simp only [eq_sVertex_iff, rows]
  by_cases hv : v.val < 5 * (n - 1)
  · rw [dif_pos hv]
    split_ifs <;> dsimp <;> omega
  · rw [dif_neg hv]
    split_ifs <;> omega

lemma gamePriority_sinkVertex (n : ℕ) : gamePriority n (sinkVertex n) = 1 := by
  rw [gamePriority_eq, val_sinkVertex]
  unfold rows
  split_ifs <;> omega

lemma gamePriority_sVertex (n : ℕ) : gamePriority n (sVertex n) = 8 := by
  rw [gamePriority_eq, val_sVertex]
  unfold rows
  split_ifs <;> omega

lemma gamePriority_fVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    gamePriority n (fVertex n i) = 6 := by
  rw [gamePriority_eq, val_fVertex n i hi1 hin]
  unfold rows
  split_ifs <;> omega

lemma gamePriority_gVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    gamePriority n (gVertex n i) = 2 * i + 7 := by
  rw [gamePriority_eq, val_gVertex n i hi1 hin]
  unfold rows
  split_ifs <;> omega

lemma gamePriority_hVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    gamePriority n (hVertex n i) = 2 * i + 8 := by
  rw [gamePriority_eq, val_hVertex n i hi1 hin]
  unfold rows
  split_ifs <;> omega

lemma gamePriority_rowVertex {n : ℕ} (hn : 3 ≤ n) {p : Kind × ℕ} (hp : ValidRow n p) :
    gamePriority n (rowVertex n p) =
      match p.1 with
      | .a | .b | .c => 3
      | .d | .e => 5 := by
  unfold gamePriority
  rw [dif_pos (val_rowVertex_lt_rows hn hp), rowName_rowVertex hn hp]
  rfl

lemma step_mem_gameSuccessors {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    (v : Fin (vertices n)) :
    step (parityGame n) σ τ v ∈ gameSuccessors n v := by
  unfold step
  by_cases h : (parityGame n).owner v = false
  · rw [if_pos h]
    exact hσ v h
  · rw [if_neg h]
    have ht : (parityGame n).owner v = true := by
      cases h' : (parityGame n).owner v
      · exact False.elim (h h')
      · rfl
    exact hτ v ht

lemma gameSuccessors_sinkVertex (n : ℕ) :
    gameSuccessors n (sinkVertex n) = {sinkVertex n} := by
  unfold gameSuccessors
  simp only [eq_sVertex_iff, val_sinkVertex]
  split_ifs <;> try omega
  rfl

lemma step_sinkVertex {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ) :
    step (parityGame n) σ τ (sinkVertex n) = sinkVertex n := by
  have h := step_mem_gameSuccessors hσ hτ (sinkVertex n)
  rwa [gameSuccessors_sinkVertex, Finset.mem_singleton] at h

lemma play_sinkVertex {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ) (t : ℕ) :
    FriedmannParity.play (parityGame n) σ τ (sinkVertex n) t = sinkVertex n := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [play_succ', ih, step_sinkVertex hσ hτ]

lemma eq_sinkVertex_of_sinkVertex_mem_recurring {n : ℕ}
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v w : Fin (vertices n)}
    (hsink : sinkVertex n ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v))
    (hw : w ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)) :
    w = sinkVertex n := by
  rcases exists_play_eq_of_mem_recurring hsink with ⟨t₀, ht₀⟩
  rw [mem_recurring_iff] at hw
  rcases hw t₀ with ⟨k, htk, hk⟩
  have hk' : t₀ + (k - t₀) = k := by omega
  rw [← hk, ← hk', play_add, ht₀, play_sinkVertex hσ hτ]

lemma cycleLeader_sinkVertex {n : ℕ}
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ) :
    cycleLeader (parityGame n) σ τ (sinkVertex n) = sinkVertex n := by
  have hsink : sinkVertex n ∈
      FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ (sinkVertex n)) := by
    rw [mem_recurring_iff]
    intro t
    exact ⟨t, le_rfl, play_sinkVertex hσ hτ t⟩
  exact eq_sinkVertex_of_sinkVertex_mem_recurring hσ hτ hsink
    (cycleLeader_mem_recurring (parityGame n) σ τ (sinkVertex n))

lemma playValue_cyclePriority_sinkVertex {n : ℕ}
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ) :
    (FriedmannParity.playValue (parityGame n) σ τ (sinkVertex n)).cyclePriority = 1 := by
  rw [playValue_cyclePriority_eq_priority_cycleLeader, cycleLeader_sinkVertex hσ hτ]
  exact gamePriority_sinkVertex n

lemma cycleLeader_eq_of_two_cycle {n : ℕ}
    {σ τ' : Fin (vertices n) → Fin (vertices n)}
    {w u : Fin (vertices n)}
    (hu_own : (parityGame n).owner u = false)
    (hu_p : gamePriority n u = 5)
    (hw_p : gamePriority n w = 6)
    (hσu : σ u = w)
    (hstep_w : step (parityGame n) σ τ' w = u) :
    cycleLeader (parityGame n) σ τ' w = w := by
  have hstep_u : step (parityGame n) σ τ' u = w := by
    unfold step
    rw [if_pos hu_own, hσu]
  have hplay_or : ∀ t : ℕ,
      FriedmannParity.play (parityGame n) σ τ' w t = w ∨
      FriedmannParity.play (parityGame n) σ τ' w t = u := by
    intro t
    induction t with
    | zero => left; rfl
    | succ t ih =>
      rw [play_succ']
      rcases ih with h | h
      · right; rw [h, hstep_w]
      · left; rw [h, hstep_u]
  have hplay_even : ∀ m : ℕ, FriedmannParity.play (parityGame n) σ τ' w (2 * m) = w := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      have h1 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
      rw [h1, play_succ', play_succ', ih, hstep_w, hstep_u]
  have hw_rec : w ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ' w) := by
    rw [mem_recurring_iff]
    intro t
    exact ⟨2 * t, by omega, hplay_even t⟩
  have hle_sup : 6 ≤ (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ' w)).sup
      (gamePriority n) := by
    rw [← hw_p]
    exact Finset.le_sup hw_rec
  have hcl_rec := cycleLeader_mem_recurring (parityGame n) σ τ' w
  have hcl_p : gamePriority n (cycleLeader (parityGame n) σ τ' w) =
      (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ' w)).sup
        (gamePriority n) :=
    priority_cycleLeader (parityGame n) σ τ' w
  rcases exists_play_eq_of_mem_recurring hcl_rec with ⟨t, ht⟩
  rcases hplay_or t with h | h
  · rw [← ht, h]
  · have hcl_u : cycleLeader (parityGame n) σ τ' w = u := ht.symm.trans h
    rw [hcl_u, hu_p] at hcl_p
    omega

/-! ### Part 3: `ReachMax` Prefix-Merge Calculus and Bellman Verification Lemma -/

inductive ReachMax (n : ℕ) (σ τ : Fin (vertices n) → Fin (vertices n)) :
    Fin (vertices n) → Fin (vertices n) → ℕ → Prop
  | refl (x : Fin (vertices n)) : ReachMax n σ τ x x 0
  | next {x y : Fin (vertices n)} {m : ℕ}
      (h : ReachMax n σ τ (step (parityGame n) σ τ x) y m) :
      ReachMax n σ τ x y (max (gamePriority n x) m)

lemma ReachMax.step_eq {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x z y : Fin (vertices n)} {m m' : ℕ}
    (hstep : step (parityGame n) σ τ x = z)
    (h : ReachMax n σ τ z y m)
    (hm : max (gamePriority n x) m = m') :
    ReachMax n σ τ x y m' := by
  subst hstep hm
  exact ReachMax.next h

lemma ReachMax.one_step {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x y : Fin (vertices n)} {m : ℕ}
    (hstep : step (parityGame n) σ τ x = y)
    (hm : gamePriority n x = m) :
    ReachMax n σ τ x y m :=
  ReachMax.step_eq hstep (ReachMax.refl y) (by omega)

lemma ReachMax.trans {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x y z : Fin (vertices n)} {m₁ m₂ : ℕ}
    (h1 : ReachMax n σ τ x y m₁) (h2 : ReachMax n σ τ y z m₂) :
    ReachMax n σ τ x z (max m₁ m₂) := by
  induction h1 with
  | refl =>
    simpa [Nat.zero_max] using h2
  | next _ ih =>
    rw [Nat.max_assoc]
    exact ReachMax.next (ih h2)

lemma ReachMax.trans_eq {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x y z : Fin (vertices n)} {m₁ m₂ m : ℕ}
    (h1 : ReachMax n σ τ x y m₁) (h2 : ReachMax n σ τ y z m₂) (hm : max m₁ m₂ = m) :
    ReachMax n σ τ x z m := by
  subst hm
  exact h1.trans h2

lemma cyclePriority_eq_of_reachMax {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x y : Fin (vertices n)} {m : ℕ} (h : ReachMax n σ τ x y m) :
    (FriedmannParity.playValue (parityGame n) σ τ x).cyclePriority =
      (FriedmannParity.playValue (parityGame n) σ τ y).cyclePriority := by
  induction h with
  | refl => rfl
  | next _ ih => rw [← playValue_cyclePriority_step, ih]

lemma cycleLeader_eq_of_reachMax {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x y : Fin (vertices n)} {m : ℕ} (h : ReachMax n σ τ x y m) :
    cycleLeader (parityGame n) σ τ x = cycleLeader (parityGame n) σ τ y := by
  induction h with
  | refl => rfl
  | next _ ih => rw [← cycleLeader_step, ih]

lemma count_eq_of_reachMax {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x y : Fin (vertices n)} {m q : ℕ}
    (h : ReachMax n σ τ x y m)
    (hcp : (FriedmannParity.playValue (parityGame n) σ τ y).cyclePriority = 1)
    (hq : m < q) (hq1 : 1 < q) :
    count (parityGame n) (FriedmannParity.playValue (parityGame n) σ τ x).path q =
      count (parityGame n) (FriedmannParity.playValue (parityGame n) σ τ y).path q := by
  induction h with
  | refl => rfl
  | @next x y m h ih =>
    have hcpx : (FriedmannParity.playValue (parityGame n) σ τ x).cyclePriority = 1 := by
      rw [← playValue_cyclePriority_step, cyclePriority_eq_of_reachMax h, hcp]
    rw [count_playValue_step (u := x) (by omega)]
    change count (parityGame n)
        (FriedmannParity.playValue (parityGame n) σ τ (step (parityGame n) σ τ x)).path q +
      (if gamePriority n x = q then 1 else 0) = _
    have hne : gamePriority n x ≠ q := by omega
    rw [if_neg hne, Nat.add_zero]
    exact ih hcp (by omega)

lemma count_lt_of_reachMax {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x y : Fin (vertices n)} {m : ℕ}
    (h : ReachMax n σ τ x y m)
    (hcp : (FriedmannParity.playValue (parityGame n) σ τ y).cyclePriority = 1)
    (hm : 1 < m) :
    count (parityGame n) (FriedmannParity.playValue (parityGame n) σ τ y).path m <
      count (parityGame n) (FriedmannParity.playValue (parityGame n) σ τ x).path m := by
  induction h with
  | refl => omega
  | @next x y m₀ h ih =>
    have hcpx : (FriedmannParity.playValue (parityGame n) σ τ x).cyclePriority = 1 := by
      rw [← playValue_cyclePriority_step, cyclePriority_eq_of_reachMax h, hcp]
    set p := max (gamePriority n x) m₀
    rw [count_playValue_step (u := x) (by omega)]
    change _ < count (parityGame n)
        (FriedmannParity.playValue (parityGame n) σ τ (step (parityGame n) σ τ x)).path p +
      (if gamePriority n x = p then 1 else 0)
    by_cases hxm : m₀ < gamePriority n x
    · have hp : p = gamePriority n x := Nat.max_eq_left (le_of_lt hxm)
      have heq := count_eq_of_reachMax h hcp (by omega) hm
      rw [heq, if_pos hp.symm]
      omega
    · have hp : p = m₀ := Nat.max_eq_right (not_lt.mp hxm)
      have hlt := ih hcp (by omega)
      rw [← hp] at hlt
      omega

lemma valueLT_of_reachMax_even {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x₁ x₂ y : Fin (vertices n)} {m₁ m₂ : ℕ}
    (h₁ : ReachMax n σ τ x₁ y m₁)
    (h₂ : ReachMax n σ τ x₂ y m₂)
    (hcp : (FriedmannParity.playValue (parityGame n) σ τ y).cyclePriority = 1)
    (hlt : m₁ < m₂) (hm₂ : 1 < m₂) (heven : m₂ % 2 = 0) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) σ τ x₁)
      (FriedmannParity.playValue (parityGame n) σ τ x₂) := by
  have hcp₁ := (cyclePriority_eq_of_reachMax h₁).trans hcp
  have hcp₂ := (cyclePriority_eq_of_reachMax h₂).trans hcp
  have hc₁ := count_eq_of_reachMax h₁ hcp hlt hm₂
  have hc₂ := count_lt_of_reachMax h₂ hcp hm₂
  right; left
  refine ⟨hcp₁.trans hcp₂.symm, m₂, by omega, ?_, Or.inl ⟨heven, by omega⟩⟩
  intro q hq
  rw [count_eq_of_reachMax h₁ hcp (lt_trans hlt hq) (lt_trans hm₂ hq),
      count_eq_of_reachMax h₂ hcp hq (lt_trans hm₂ hq)]

lemma valueLT_of_reachMax_odd {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    {x₁ x₂ y : Fin (vertices n)} {m₁ m₂ : ℕ}
    (h₁ : ReachMax n σ τ x₁ y m₁)
    (h₂ : ReachMax n σ τ x₂ y m₂)
    (hcp : (FriedmannParity.playValue (parityGame n) σ τ y).cyclePriority = 1)
    (hlt : m₂ < m₁) (hm₁ : 1 < m₁) (hodd : m₁ % 2 = 1) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) σ τ x₁)
      (FriedmannParity.playValue (parityGame n) σ τ x₂) := by
  have hcp₁ := (cyclePriority_eq_of_reachMax h₁).trans hcp
  have hcp₂ := (cyclePriority_eq_of_reachMax h₂).trans hcp
  have hc₁ := count_lt_of_reachMax h₁ hcp hm₁
  have hc₂ := count_eq_of_reachMax h₂ hcp hlt hm₁
  right; left
  refine ⟨hcp₁.trans hcp₂.symm, m₁, by omega, ?_, Or.inr ⟨hodd, by omega⟩⟩
  intro q hq
  rw [count_eq_of_reachMax h₁ hcp hq (lt_trans hm₁ hq),
      count_eq_of_reachMax h₂ hcp (lt_trans hlt hq) (lt_trans hm₁ hq)]

lemma valueLE_of_bellman_aux {n : ℕ}
    {σ τ τ' : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    (hτ' : FriedmannParity.Legal (parityGame n) true τ')
    (hreach : ∀ x, ∃ m, ReachMax n σ τ x (sinkVertex n) m)
    (hbell : ∀ x, (parityGame n).owner x = true → ∀ w ∈ gameSuccessors n x,
      ((parityGame n).owner w = false ∧ gamePriority n w = 5 ∧
        gamePriority n x = 6 ∧ σ w = x) ∨
      ValueLE (parityGame n)
        (FriedmannParity.playValue (parityGame n) σ τ (τ x))
        (FriedmannParity.playValue (parityGame n) σ τ w)) :
    ∀ L x, (FriedmannParity.playValue (parityGame n) σ τ' x).length = L →
      (FriedmannParity.playValue (parityGame n) σ τ' x).cyclePriority = 1 →
      ValueLE (parityGame n)
        (FriedmannParity.playValue (parityGame n) σ τ x)
        (FriedmannParity.playValue (parityGame n) σ τ' x)
  | 0, x, hL, hcp' => by
    have hcl' : x = cycleLeader (parityGame n) σ τ' x := by
      have hplay := play_playValue_length (parityGame n) σ τ' x
      rwa [hL, play_zero] at hplay
    have hpx : gamePriority n x = 1 := by
      have hp := playValue_cyclePriority_eq_priority_cycleLeader (parityGame n) σ τ' x
      rw [← hcl', hcp'] at hp
      exact hp.symm
    have hxsink : x = sinkVertex n := by
      have hv := x.isLt
      unfold vertices rows at hv
      rw [gamePriority_eq] at hpx
      rw [eq_sinkVertex_iff]
      unfold rows at hpx ⊢
      split_ifs at hpx <;> omega
    subst hxsink
    have hcl := (cycleLeader_sinkVertex hσ hτ).symm
    have hlen : (FriedmannParity.playValue (parityGame n) σ τ (sinkVertex n)).length = 0 := by
      have h0 := length_le_of_play_eq_cycleLeader (parityGame n) σ τ (sinkVertex n) (t := 0) hcl
      omega
    have hp1 : (FriedmannParity.playValue (parityGame n) σ τ (sinkVertex n)).path = ∅ := by
      ext u; rw [mem_playValue_path_iff, hlen]; simp
    have hp2 : (FriedmannParity.playValue (parityGame n) σ τ' (sinkVertex n)).path = ∅ := by
      ext u; rw [mem_playValue_path_iff, hL]; simp
    rw [valueLE_iff]
    left
    refine ⟨?_, ?_, by omega⟩
    · rw [playValue_cyclePriority_sinkVertex hσ hτ, hcp']
    · intro q; rw [hp1, hp2]
  | L + 1, x, hL, hcp' => by
    have hne' : x ≠ cycleLeader (parityGame n) σ τ' x := by
      intro heq
      have h0 := length_le_of_play_eq_cycleLeader (parityGame n) σ τ' x (t := 0) heq
      omega
    have hlen_step : (FriedmannParity.playValue (parityGame n) σ τ' (step (parityGame n) σ τ' x)).length = L := by
      have hsucc := playValue_length_eq_succ_of_ne_cycleLeader hne'
      omega
    have hcp'_step : (FriedmannParity.playValue (parityGame n) σ τ' (step (parityGame n) σ τ' x)).cyclePriority = 1 := by
      rw [playValue_cyclePriority_step, hcp']
    have ih := valueLE_of_bellman_aux hσ hτ hτ' hreach hbell L
      (step (parityGame n) σ τ' x) hlen_step hcp'_step
    rcases hreach x with ⟨mx, hmx⟩
    have hcl : cycleLeader (parityGame n) σ τ x = sinkVertex n :=
      (cycleLeader_eq_of_reachMax hmx).trans (cycleLeader_sinkVertex hσ hτ)
    have hne : x ≠ cycleLeader (parityGame n) σ τ x := by
      rw [hcl]
      intro hxsink
      subst hxsink
      exact hne' (cycleLeader_sinkVertex hσ hτ').symm
    have hcp : (FriedmannParity.playValue (parityGame n) σ τ x).cyclePriority = 1 :=
      (cyclePriority_eq_of_reachMax hmx).trans (playValue_cyclePriority_sinkVertex hσ hτ)
    have hstep_le : ValueLE (parityGame n)
        (FriedmannParity.playValue (parityGame n) σ τ (step (parityGame n) σ τ x))
        (FriedmannParity.playValue (parityGame n) σ τ (step (parityGame n) σ τ' x)) := by
      unfold step
      by_cases hown : (parityGame n).owner x = false
      · rw [if_pos hown, if_pos hown]
        exact valueLE_refl (parityGame n) _
      · rw [if_neg hown, if_neg hown]
        have hown_t : (parityGame n).owner x = true := by
          cases h : (parityGame n).owner x
          · exact False.elim (hown h)
          · rfl
        have hw_mem : τ' x ∈ gameSuccessors n x := hτ' x hown_t
        rcases hbell x hown_t (τ' x) hw_mem with ⟨hw_own, hw_p, hx_p, hσw⟩ | hle
        · have hstep_x : step (parityGame n) σ τ' x = τ' x := by
            unfold step; rw [if_neg hown]
          have hcl_x := cycleLeader_eq_of_two_cycle hw_own hw_p hx_p hσw hstep_x
          exact False.elim (hne' hcl_x.symm)
        · exact hle
    have htrans := valueLE_trans hstep_le ih
    rw [playValue_eq_prepend_of_ne_cycleLeader hne,
        playValue_eq_prepend_of_ne_cycleLeader hne']
    apply valueLE_prepend _
      (notMem_playValue_step_path_of_ne_cycleLeader hne)
      (notMem_playValue_step_path_of_ne_cycleLeader hne')
      htrans
    rw [playValue_cyclePriority_step, playValue_cyclePriority_step, hcp, hcp']

lemma valEq_value_playValue_of_bellman {n : ℕ}
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    (hreach : ∀ x, ∃ m, ReachMax n σ τ x (sinkVertex n) m)
    (hbell : ∀ x, (parityGame n).owner x = true → ∀ w ∈ gameSuccessors n x,
      ((parityGame n).owner w = false ∧ gamePriority n w = 5 ∧
        gamePriority n x = 6 ∧ σ w = x) ∨
      ValueLE (parityGame n)
        (FriedmannParity.playValue (parityGame n) σ τ (τ x))
        (FriedmannParity.playValue (parityGame n) σ τ w))
    (hcyc : ∀ τ', FriedmannParity.Legal (parityGame n) true τ' → ∀ x,
      (FriedmannParity.playValue (parityGame n) σ τ' x).cyclePriority = 1 ∨
      (FriedmannParity.playValue (parityGame n) σ τ' x).cyclePriority = 6)
    (v : Fin (vertices n)) :
    ValEq (parityGame n)
      (value (parityGame n) σ v)
      (FriedmannParity.playValue (parityGame n) σ τ v) := by
  classical
  have hmin_tau : ∀ τ', FriedmannParity.Legal (parityGame n) true τ' →
      ValueLE (parityGame n)
        (FriedmannParity.playValue (parityGame n) σ τ v)
        (FriedmannParity.playValue (parityGame n) σ τ' v) := by
    intro τ' hτ'
    rcases hcyc τ' hτ' v with hcp1 | hcp6
    · exact valueLE_of_bellman_aux hσ hτ hτ' hreach hbell _ v rfl hcp1
    · rw [valueLE_iff]
      right; left
      rcases hreach v with ⟨mv, hmv⟩
      have hcp : (FriedmannParity.playValue (parityGame n) σ τ v).cyclePriority = 1 :=
        (cyclePriority_eq_of_reachMax hmv).trans (playValue_cyclePriority_sinkVertex hσ hτ)
      rw [hcp, hcp6]
      unfold FriedmannParity.reward
      omega
  have hex : ∃ a, IsMinimum (parityGame n) σ v a :=
    ⟨FriedmannParity.playValue (parityGame n) σ τ v, ⟨τ, hτ, rfl⟩, hmin_tau⟩
  have hspec : IsMinimum (parityGame n) σ v (Classical.choose hex) :=
    Classical.choose_spec hex
  have hval : value (parityGame n) σ v = Classical.choose hex := by
    unfold value
    rw [dif_pos hex]
  rw [hval]
  rcases hspec.1 with ⟨τ₀, hτ₀, hval₀⟩
  exact valEq_of_valueLE_antisymm (hspec.2 τ hτ) (hval₀ ▸ hmin_tau τ₀ hτ₀)

end ParityGameInfrastructure

/-! ### Part 4: Phase Policies, `phaseTau`, Canonical `ReachMax` Ladders, and Bellman Optimality -/

noncomputable section PhaseOptimality

open Classical

def policyStrategy (n : ℕ) (π : Kind → ℕ → Bool) : Fin (vertices n) → Fin (vertices n) :=
  fun v =>
    if hv : v.val < rows n then
      let r := rowName n ⟨v.val, hv⟩
      actionTarget n ⟨r.1, r.2, π r.1 r.2⟩
    else v

lemma policyStrategy_legal (n : ℕ) (π : Kind → ℕ → Bool) :
    FriedmannParity.Legal (parityGame n) false (policyStrategy n π) := by
  intro v hv
  change decide (rows n ≤ v.val) = false at hv
  rw [decide_eq_false_iff_not, not_le] at hv
  unfold policyStrategy parityGame gameSuccessors
  dsimp only
  rw [dif_pos hv, dif_pos hv]
  cases π (rowName n ⟨v.val, hv⟩).1 (rowName n ⟨v.val, hv⟩).2 <;> simp

lemma policyStrategy_rowVertex {n : ℕ} (hn : 3 ≤ n) (π : Kind → ℕ → Bool)
    {k : Kind} {i : ℕ} (hp : ValidRow n (k, i)) :
    policyStrategy n π (rowVertex n (k, i)) = actionTarget n ⟨k, i, π k i⟩ := by
  unfold policyStrategy
  rw [dif_pos (val_rowVertex_lt_rows hn hp), rowName_rowVertex hn hp]

lemma owner_rowVertex {n : ℕ} (hn : 3 ≤ n) {p : Kind × ℕ} (hp : ValidRow n p) :
    (parityGame n).owner (rowVertex n p) = false := by
  change decide (rows n ≤ (rowVertex n p).val) = false
  rw [decide_eq_false_iff_not, not_le]
  exact val_rowVertex_lt_rows hn hp

lemma step_rowVertex {n : ℕ} (hn : 3 ≤ n) (π : Kind → ℕ → Bool)
    (τ : Fin (vertices n) → Fin (vertices n)) {k : Kind} {i : ℕ} (hp : ValidRow n (k, i)) :
    step (parityGame n) (policyStrategy n π) τ (rowVertex n (k, i)) =
      actionTarget n ⟨k, i, π k i⟩ := by
  unfold step
  rw [if_pos (owner_rowVertex hn hp), policyStrategy_rowVertex hn π hp]

lemma owner_fVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (parityGame n).owner (fVertex n i) = true := by
  change decide (rows n ≤ (fVertex n i).val) = true
  rw [decide_eq_true_eq, val_fVertex n i hi1 hin]
  omega

lemma owner_gVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (parityGame n).owner (gVertex n i) = true := by
  change decide (rows n ≤ (gVertex n i).val) = true
  rw [decide_eq_true_eq, val_gVertex n i hi1 hin]
  omega

lemma owner_hVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (parityGame n).owner (hVertex n i) = true := by
  change decide (rows n ≤ (hVertex n i).val) = true
  rw [decide_eq_true_eq, val_hVertex n i hi1 hin]
  omega

lemma owner_sVertex (n : ℕ) :
    (parityGame n).owner (sVertex n) = true := by
  change decide (rows n ≤ (sVertex n).val) = true
  rw [decide_eq_true_eq, val_sVertex]
  omega

lemma gameSuccessors_fVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    gameSuccessors n (fVertex n i) =
      if i = 1 then {hVertex n 1, decisionVertex n .e 1}
      else {hVertex n i, decisionVertex n .d i, decisionVertex n .e i} := by
  unfold gameSuccessors
  have hval := val_fVertex n i hi1 hin
  have h1 : ¬ (fVertex n i).val < rows n := by omega
  have h2 : (fVertex n i).val < rows n + n := by omega
  have h3 : (fVertex n i).val - rows n + 1 = i := by omega
  rw [dif_neg h1, if_pos h2]
  dsimp only
  rw [h3]
  split_ifs with hi <;> subst_vars <;> rfl

lemma gameSuccessors_gVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    gameSuccessors n (gVertex n i) = {fVertex n i} := by
  unfold gameSuccessors
  have hval := val_gVertex n i hi1 hin
  have h1 : ¬ (gVertex n i).val < rows n := by omega
  have h2 : ¬ (gVertex n i).val < rows n + n := by omega
  have h3 : (gVertex n i).val < rows n + 2 * n := by omega
  have h4 : (gVertex n i).val - (rows n + n) + 1 = i := by omega
  rw [dif_neg h1, if_neg h2, if_pos h3, h4]

lemma gameSuccessors_hVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    gameSuccessors n (hVertex n i) = {decisionVertex n .a (i + 1)} := by
  unfold gameSuccessors
  have hval := val_hVertex n i hi1 hin
  have h1 : ¬ (hVertex n i).val < rows n := by omega
  have h2 : ¬ (hVertex n i).val < rows n + n := by omega
  have h3 : ¬ (hVertex n i).val < rows n + 2 * n := by omega
  have h4 : (hVertex n i).val < rows n + 3 * n := by omega
  have h5 : (hVertex n i).val - (rows n + 2 * n) + 2 = i + 1 := by omega
  rw [dif_neg h1, if_neg h2, if_neg h3, if_pos h4, h5]

lemma gameSuccessors_sVertex (n : ℕ) :
    gameSuccessors n (sVertex n) = {decisionVertex n .c n} := by
  unfold gameSuccessors
  have hval := val_sVertex n
  have h1 : ¬ (sVertex n).val < rows n := by omega
  have h2 : ¬ (sVertex n).val < rows n + n := by omega
  have h3 : ¬ (sVertex n).val < rows n + 2 * n := by omega
  have h4 : ¬ (sVertex n).val < rows n + 3 * n := by omega
  rw [dif_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos rfl]

lemma step_gVertex {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    step (parityGame n) σ τ (gVertex n i) = fVertex n i := by
  have h := hτ (gVertex n i) (owner_gVertex n i hi1 hin)
  change τ (gVertex n i) ∈ gameSuccessors n (gVertex n i) at h
  rw [gameSuccessors_gVertex n i hi1 hin, Finset.mem_singleton] at h
  unfold step
  rw [if_neg (by rw [owner_gVertex n i hi1 hin]; decide), h]

lemma step_hVertex {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    step (parityGame n) σ τ (hVertex n i) = decisionVertex n .a (i + 1) := by
  have h := hτ (hVertex n i) (owner_hVertex n i hi1 hin)
  change τ (hVertex n i) ∈ gameSuccessors n (hVertex n i) at h
  rw [gameSuccessors_hVertex n i hi1 hin, Finset.mem_singleton] at h
  unfold step
  rw [if_neg (by rw [owner_hVertex n i hi1 hin]; decide), h]

lemma step_sVertex {n : ℕ} {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hτ : FriedmannParity.Legal (parityGame n) true τ) :
    step (parityGame n) σ τ (sVertex n) = decisionVertex n .c n := by
  have h := hτ (sVertex n) (owner_sVertex n)
  change τ (sVertex n) ∈ gameSuccessors n (sVertex n) at h
  rw [gameSuccessors_sVertex n, Finset.mem_singleton] at h
  unfold step
  rw [if_neg (by rw [owner_sVertex n]; decide), h]

lemma step_fVertex {n : ℕ} (σ τ : Fin (vertices n) → Fin (vertices n))
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    step (parityGame n) σ τ (fVertex n i) = τ (fVertex n i) := by
  unfold step
  rw [if_neg (by rw [owner_fVertex n i hi1 hin]; decide)]

def fTarget (n : ℕ) (π : Kind → ℕ → Bool) (c_max b_max i : ℕ) : Fin (vertices n) :=
  if (i = 1 ∨ π .d i = true) ∧ π .e i = true then
    hVertex n i
  else if 1 < i ∧ π .d i = false ∧ π .e i = true then
    decisionVertex n .d i
  else if 1 < i ∧ π .d i = false ∧ π .e i = false then
    if c_max < i ∧ b_max = c_max then decisionVertex n .d i else decisionVertex n .e i
  else
    if c_max < i then decisionVertex n .e i
    else if i < c_max ∧ π .a c_max = true ∧
        ∀ k ∈ Finset.Ico (i + 1) c_max, π .a k = false then
      decisionVertex n .e i
    else
      hVertex n i

def phaseTau (n : ℕ) (π : Kind → ℕ → Bool) (c_max b_max : ℕ) (v : Fin (vertices n)) :
    Fin (vertices n) :=
  if v.val < rows n then v
  else if v.val < rows n + n then
    fTarget n π c_max b_max (v.val - rows n + 1)
  else if v.val < rows n + 2 * n then
    fVertex n (v.val - (rows n + n) + 1)
  else if v.val < rows n + 3 * n then
    decisionVertex n .a (v.val - (rows n + 2 * n) + 2)
  else if v = sVertex n then
    decisionVertex n .c n
  else
    sinkVertex n

lemma fTarget_mem_gameSuccessors (n : ℕ) (π : Kind → ℕ → Bool) (c_max b_max i : ℕ)
    (hi1 : 1 ≤ i) (hin : i ≤ n) :
    fTarget n π c_max b_max i ∈ gameSuccessors n (fVertex n i) := by
  rw [gameSuccessors_fVertex n i hi1 hin]
  unfold fTarget
  by_cases hi : i = 1
  · subst hi
    split_ifs <;> simp_all
  · rw [if_neg hi]
    split_ifs <;> simp

lemma phaseTau_legal (n : ℕ) (π : Kind → ℕ → Bool) (c_max b_max : ℕ) :
    FriedmannParity.Legal (parityGame n) true (phaseTau n π c_max b_max) := by
  intro v hv
  change decide (rows n ≤ v.val) = true at hv
  rw [decide_eq_true_eq] at hv
  have hnot : ¬ v.val < rows n := by omega
  unfold phaseTau parityGame
  dsimp only
  rw [if_neg hnot]
  by_cases h1 : v.val < rows n + n
  · rw [if_pos h1]
    set i := v.val - rows n + 1
    have hi1 : 1 ≤ i := by omega
    have hin : i ≤ n := by omega
    have hfv : v = fVertex n i := by
      ext
      rw [val_fVertex n i hi1 hin]
      omega
    rw [hfv]
    exact fTarget_mem_gameSuccessors n π c_max b_max i hi1 hin
  · rw [if_neg h1]
    unfold gameSuccessors
    rw [dif_neg hnot, if_neg h1]
    split_ifs <;> simp

lemma phaseTau_fVertex (n : ℕ) (π : Kind → ℕ → Bool) (c_max b_max i : ℕ)
    (hi1 : 1 ≤ i) (hin : i ≤ n) :
    phaseTau n π c_max b_max (fVertex n i) = fTarget n π c_max b_max i := by
  unfold phaseTau
  have hval := val_fVertex n i hi1 hin
  rw [if_neg (by omega), if_pos (by omega)]
  have hi : (fVertex n i).val - rows n + 1 = i := by omega
  rw [hi]

lemma step_fVertex_phaseTau {n : ℕ} (σ : Fin (vertices n) → Fin (vertices n))
    (π : Kind → ℕ → Bool) (c_max b_max i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    step (parityGame n) σ (phaseTau n π c_max b_max) (fVertex n i) =
      fTarget n π c_max b_max i := by
  rw [step_fVertex σ _ hi1 hin, phaseTau_fVertex n π c_max b_max i hi1 hin]

structure ValidPhasePolicy (n : ℕ) (π : Kind → ℕ → Bool) (c_max b_max : ℕ) : Prop where
  hc_range : 1 ≤ c_max ∧ c_max ≤ n
  hc_iff : ∀ i, 2 ≤ i → i ≤ n → (π .c i = true ↔ i = c_max)
  hc_e : π .e c_max = true
  hc_d : 2 ≤ c_max → π .d c_max = true
  hb_range : 1 ≤ b_max ∧ b_max ≤ n - 1
  hb_iff : ∀ i, 2 ≤ i → i ≤ n - 1 → (π .b i = true ↔ i = b_max)
  hb_ed : 2 ≤ b_max → π .e b_max = true ∧ π .d b_max = true
  ha_d : ∀ i, 2 ≤ i → i ≤ n → π .a i = true → π .d i = true
  ha_e : ∀ i, 2 ≤ i → i ≤ n → π .a i = true → c_max ≤ i → π .e i = true
  hd_false : ∀ i, 2 ≤ i → i ≤ n → π .d i = false →
    c_max < i ∨
    (i < c_max ∧ (b_max = 1 ∨ i < b_max) ∧ π .e 1 = true ∧
      ∀ k, 2 ≤ k → k < c_max → π .a k = false)
  hd_he_false : ∀ i, 2 ≤ i → i ≤ n → π .d i = false → π .e i = false →
    ¬ (c_max < i ∧ b_max = c_max) →
    (c_max < b_max ∧ b_max < i ∧ π .a b_max = false) ∨
    ((b_max = 1 ∨ i ≤ b_max) ∧ 2 ≤ c_max ∧ π .e 1 = true ∧ π .a c_max = true ∧
      ∀ k, 2 ≤ k → k < c_max → π .a k = false)
  he_false_lt_cmax : ∀ i, 1 ≤ i → i < c_max → (i = 1 ∨ π .d i = true) →
    π .e i = false → π .a c_max = true →
    ∀ k, i < k → k < c_max → π .a k = true → π .e k = false ∧ π .d k = true

lemma decisionVertex_a_succ_n (n : ℕ) :
    decisionVertex n .a (n + 1) = sinkVertex n := by
  unfold decisionVertex
  rw [if_pos ⟨rfl, rfl⟩]

lemma decisionVertex_b_one (n : ℕ) :
    decisionVertex n .b 1 = gVertex n 1 := by
  unfold decisionVertex
  rw [if_neg (by rintro ⟨h, _⟩; cases h), if_pos ⟨Or.inl rfl, rfl⟩]

lemma decisionVertex_c_one (n : ℕ) :
    decisionVertex n .c 1 = gVertex n 1 := by
  unfold decisionVertex
  rw [if_neg (by rintro ⟨h, _⟩; cases h), if_pos ⟨Or.inr rfl, rfl⟩]

def bEff (b_max i : ℕ) : ℕ := if b_max < i then b_max else 1

lemma bEff_range {m i : ℕ} (hm : 1 ≤ m) (hi2 : 2 ≤ i) :
    1 ≤ bEff m i ∧ bEff m i < i ∧ bEff m i ≤ m := by
  unfold bEff
  split_ifs <;> omega

lemma bEff_eq_self_of_ge_two {m i : ℕ} (h : 2 ≤ bEff m i) :
    bEff m i = m ∧ m < i := by
  unfold bEff at h ⊢
  split_ifs at h ⊢ <;> omega

lemma bEff_ne_self_of_lt {m i k : ℕ} (h : bEff m i < k) (hki : k < i) :
    k ≠ m := by
  unfold bEff at h
  split_ifs at h <;> omega

lemma reachMax_c_ladder {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (τ : Fin (vertices n) → Fin (vertices n))
    (hi2 : 2 ≤ i) (hin : i ≤ n + 1) :
    ∀ d k, k - max 2 (bEff c_max i) = d → max 2 (bEff c_max i) ≤ k → k ≤ i - 1 →
      ReachMax n (policyStrategy n π) τ (decisionVertex n .c k) (gVertex n (bEff c_max i)) 3
  | 0, k, hd, hle, hki => by
    have hc := hV.hc_range
    have hce_rng := bEff_range hc.1 hi2
    have hk : k = max 2 (bEff c_max i) := by omega
    have hk2 : 2 ≤ k := by omega
    have hkn : k ≤ n := by omega
    have hvp : ValidRow n (.c, k) := ⟨hk2, hkn⟩
    rw [decisionVertex_eq_rowVertex hvp]
    by_cases hkc : k = bEff c_max i
    · have hce := (bEff_eq_self_of_ge_two (hkc ▸ hk2)).1
      have hkc' : k = c_max := hkc.trans hce
      have hck : π .c k = true := (hV.hc_iff k hk2 hkn).mpr hkc'
      refine ReachMax.one_step ?_ (gamePriority_rowVertex hn hvp)
      rw [step_rowVertex hn π τ hvp, hck, hkc]
      rfl
    · have hce1 : bEff c_max i = 1 := by omega
      have hk_eq_2 : k = 2 := by omega
      have hne_c : 2 ≠ c_max := bEff_ne_self_of_lt (by omega : bEff c_max i < 2) (by omega)
      subst hk_eq_2
      have hck : π .c 2 = false := by
        cases h : π .c 2
        · rfl
        · exact False.elim (hne_c ((hV.hc_iff 2 (by omega) hkn).mp h))
      refine ReachMax.one_step ?_ (gamePriority_rowVertex hn hvp)
      rw [step_rowVertex hn π τ hvp, hck, hce1]
      exact decisionVertex_c_one n
  | d + 1, k, hd, hle, hki => by
    have hk2 : 2 < k := by omega
    have hkc : bEff c_max i < k := by omega
    have hkn : k ≤ n := by omega
    have hvp : ValidRow n (.c, k) := ⟨by omega, hkn⟩
    have hne_c : k ≠ c_max := bEff_ne_self_of_lt hkc (by omega)
    have hck : π .c k = false := by
      cases h : π .c k
      · rfl
      · exact False.elim (hne_c ((hV.hc_iff k (by omega) hkn).mp h))
    have hstep : step (parityGame n) (policyStrategy n π) τ (decisionVertex n .c k) =
        decisionVertex n .c (k - 1) := by
      rw [decisionVertex_eq_rowVertex hvp, step_rowVertex hn π τ hvp, hck]
      rfl
    have hp : gamePriority n (decisionVertex n .c k) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp, gamePriority_rowVertex hn hvp]
    have ih := reachMax_c_ladder hn hV τ hi2 hin d (k - 1) (by omega) (by omega) (by omega)
    exact ReachMax.step_eq hstep ih (by rw [hp]; omega)

lemma reachMax_s_to_g_cmax {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) {τ : Fin (vertices n) → Fin (vertices n)}
    (hτ : FriedmannParity.Legal (parityGame n) true τ) :
    ReachMax n (policyStrategy n π) τ (sVertex n) (gVertex n c_max) 8 := by
  have hc := hV.hc_range
  have hce : bEff c_max (n + 1) = c_max := by unfold bEff; rw [if_pos (by omega)]
  have h1 := reachMax_c_ladder hn hV τ (by omega : 2 ≤ n + 1) le_rfl
    (n - max 2 (bEff c_max (n + 1))) n rfl (by rw [hce]; omega) le_rfl
  rw [hce] at h1
  exact ReachMax.step_eq (step_sVertex hτ) h1 (by rw [gamePriority_sVertex]; omega)

lemma reachMax_g_f_h_of_ed {n : ℕ} {π : Kind → ℕ → Bool} (c_max b_max m : ℕ)
    (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (he : π .e m = true) (hd : 2 ≤ m → π .d m = true) :
    ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max)
      (gVertex n m) (decisionVertex n .a (m + 1)) (2 * m + 8) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hf_targ : fTarget n π c_max b_max m = hVertex n m := by
    unfold fTarget
    rw [if_pos ⟨by by_cases h : m = 1 <;> [exact Or.inl h; exact Or.inr (hd (by omega))], he⟩]
  have hstep_g : step (parityGame n) σ τ (gVertex n m) = fVertex n m :=
    step_gVertex hτ hm1 hmn
  have hstep_f : step (parityGame n) σ τ (fVertex n m) = hVertex n m := by
    rw [step_fVertex_phaseTau σ π c_max b_max m hm1 hmn, hf_targ]
  have hstep_h : step (parityGame n) σ τ (hVertex n m) = decisionVertex n .a (m + 1) :=
    step_hVertex hτ hm1 hmn
  have h1 : ReachMax n σ τ (hVertex n m) (decisionVertex n .a (m + 1)) (2 * m + 8) :=
    ReachMax.one_step hstep_h (gamePriority_hVertex n m hm1 hmn)
  have h2 : ReachMax n σ τ (fVertex n m) (decisionVertex n .a (m + 1)) (2 * m + 8) :=
    ReachMax.step_eq hstep_f h1 (by rw [gamePriority_fVertex n m hm1 hmn]; omega)
  exact ReachMax.step_eq hstep_g h2 (by rw [gamePriority_gVertex n m hm1 hmn]; omega)

lemma reachMax_s_to_a_cmax {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) :
    ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max)
      (sVertex n) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) := by
  have hc := hV.hc_range
  have h1 := reachMax_s_to_g_cmax hn hV (phaseTau_legal n π c_max b_max)
  have h2 := reachMax_g_f_h_of_ed c_max b_max c_max hc.1 hc.2 hV.hc_e hV.hc_d
  exact h1.trans_eq h2 (by omega)

lemma reachMax_b_ladder {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (τ : Fin (vertices n) → Fin (vertices n))
    (hi2 : 2 ≤ i) (hin : i ≤ n) :
    ∀ d k, k - max 2 (bEff b_max i) = d → max 2 (bEff b_max i) ≤ k → k ≤ i - 1 →
      ReachMax n (policyStrategy n π) τ (decisionVertex n .b k) (gVertex n (bEff b_max i)) 3
  | 0, k, hd, hle, hki => by
    have hb := hV.hb_range
    have hbe_rng := bEff_range hb.1 hi2
    have hk : k = max 2 (bEff b_max i) := by omega
    have hk2 : 2 ≤ k := by omega
    have hkn : k ≤ n - 1 := by omega
    have hvp : ValidRow n (.b, k) := ⟨hk2, hkn⟩
    rw [decisionVertex_eq_rowVertex hvp]
    by_cases hkb : k = bEff b_max i
    · have hbe := (bEff_eq_self_of_ge_two (hkb ▸ hk2)).1
      have hkb' : k = b_max := hkb.trans hbe
      have hbk : π .b k = true := (hV.hb_iff k hk2 hkn).mpr hkb'
      refine ReachMax.one_step ?_ (gamePriority_rowVertex hn hvp)
      rw [step_rowVertex hn π τ hvp, hbk, hkb]
      rfl
    · have hbe1 : bEff b_max i = 1 := by omega
      have hk_eq_2 : k = 2 := by omega
      have hne_b : 2 ≠ b_max := bEff_ne_self_of_lt (by omega : bEff b_max i < 2) (by omega)
      subst hk_eq_2
      have hbk : π .b 2 = false := by
        cases h : π .b 2
        · rfl
        · exact False.elim (hne_b ((hV.hb_iff 2 (by omega) hkn).mp h))
      refine ReachMax.one_step ?_ (gamePriority_rowVertex hn hvp)
      rw [step_rowVertex hn π τ hvp, hbk, hbe1]
      exact decisionVertex_b_one n
  | d + 1, k, hd, hle, hki => by
    have hk2 : 2 < k := by omega
    have hkb : bEff b_max i < k := by omega
    have hkn : k ≤ n - 1 := by omega
    have hvp : ValidRow n (.b, k) := ⟨by omega, hkn⟩
    have hne_b : k ≠ b_max := bEff_ne_self_of_lt hkb (by omega)
    have hbk : π .b k = false := by
      cases h : π .b k
      · rfl
      · exact False.elim (hne_b ((hV.hb_iff k (by omega) hkn).mp h))
    have hstep : step (parityGame n) (policyStrategy n π) τ (decisionVertex n .b k) =
        decisionVertex n .b (k - 1) := by
      rw [decisionVertex_eq_rowVertex hvp, step_rowVertex hn π τ hvp, hbk]
      rfl
    have hp : gamePriority n (decisionVertex n .b k) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp, gamePriority_rowVertex hn hvp]
    have ih := reachMax_b_ladder hn hV τ hi2 hin d (k - 1) (by omega) (by omega) (by omega)
    exact ReachMax.step_eq hstep ih (by rw [hp]; omega)

lemma reachMax_d_to_g_bEff {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (τ : Fin (vertices n) → Fin (vertices n))
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hdi : π .d i = false) :
    ReachMax n (policyStrategy n π) τ (rowVertex n (.d, i)) (gVertex n (bEff b_max i)) 5 := by
  have hvp : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hstep : step (parityGame n) (policyStrategy n π) τ (rowVertex n (.d, i)) =
      decisionVertex n .b (i - 1) := by
    rw [step_rowVertex hn π τ hvp, hdi]
    rfl
  have hp : gamePriority n (rowVertex n (.d, i)) = 5 := gamePriority_rowVertex hn hvp
  have hbe := bEff_range hV.hb_range.1 hi2
  by_cases hi_eq_2 : i = 2
  · subst hi_eq_2
    have hbe1 : bEff b_max 2 = 1 := by omega
    rw [hbe1]
    rw [show 2 - 1 = 1 from rfl, decisionVertex_b_one n] at hstep
    exact ReachMax.one_step hstep hp
  · have h1 := reachMax_b_ladder hn hV τ hi2 hin (i - 1 - max 2 (bEff b_max i)) (i - 1)
      rfl (by omega) le_rfl
    exact ReachMax.step_eq hstep h1 (by rw [hp]; omega)

lemma reachMax_a_ladder_all_false {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    (τ : Fin (vertices n) → Fin (vertices n)) :
    ∀ d k m, m - k = d → 2 ≤ k → k ≤ m → m ≤ n + 1 →
      (∀ r, k ≤ r → r < m → π .a r = false) →
      ReachMax n (policyStrategy n π) τ
        (decisionVertex n .a k) (decisionVertex n .a m) (if k = m then 0 else 3)
  | 0, k, m, hd, hk2, hkm, hmn, _ => by
    have h : k = m := by omega
    subst h
    rw [if_pos rfl]
    exact ReachMax.refl _
  | d + 1, k, m, hd, hk2, hkm, hmn, hfalse => by
    have hkm' : k < m := by omega
    have hkn : k ≤ n := by omega
    have hvp : ValidRow n (.a, k) := ⟨hk2, hkn⟩
    have hak : π .a k = false := hfalse k le_rfl hkm'
    have hstep : step (parityGame n) (policyStrategy n π) τ (decisionVertex n .a k) =
        decisionVertex n .a (k + 1) := by
      rw [decisionVertex_eq_rowVertex hvp, step_rowVertex hn π τ hvp, hak]
      rfl
    have hp : gamePriority n (decisionVertex n .a k) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp, gamePriority_rowVertex hn hvp]
    have ih := reachMax_a_ladder_all_false hn τ d (k + 1) m (by omega) (by omega) (by omega) hmn
      (fun r hr1 hr2 => hfalse r (by omega) hr2)
    rw [if_neg (by omega)]
    exact ReachMax.step_eq hstep ih (by rw [hp]; split_ifs <;> omega)

lemma reachMax_a_ladder_general {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) :
    ∀ d k m, m - k = d → 2 ≤ k → k ≤ m → m ≤ n + 1 →
      (c_max < m ∨ π .a c_max = false ∨ ∀ r, k ≤ r → r < m → π .a r = true → π .e r = true) →
      ∃ ma, (ma ≤ 3 ∨ (10 ≤ ma ∧ ma % 2 = 0 ∧ ma ≤ 2 * m + 6)) ∧
        ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max)
          (decisionVertex n .a k) (decisionVertex n .a m) ma
  | 0, k, m, hd, hk2, hkm, hmn, _ => by
    have h : k = m := by omega
    subst h
    exact ⟨0, Or.inl (by omega), ReachMax.refl _⟩
  | d + 1, k, m, hd, hk2, hkm, hmn, hcm => by
    set σ := policyStrategy n π
    set τ := phaseTau n π c_max b_max
    have hτ := phaseTau_legal n π c_max b_max
    have hkm' : k < m := by omega
    have hkn : k ≤ n := by omega
    have hvp : ValidRow n (.a, k) := ⟨hk2, hkn⟩
    have hp_ak : gamePriority n (decisionVertex n .a k) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp, gamePriority_rowVertex hn hvp]
    have hcm_next : c_max < m ∨ π .a c_max = false ∨
        ∀ r, k + 1 ≤ r → r < m → π .a r = true → π .e r = true := by
      rcases hcm with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr fun r hr1 hr2 => h r (by omega) hr2)
    by_cases hak : π .a k = false
    · have hstep : step (parityGame n) σ τ (decisionVertex n .a k) =
          decisionVertex n .a (k + 1) := by
        rw [decisionVertex_eq_rowVertex hvp, step_rowVertex hn π τ hvp, hak]
        rfl
      rcases reachMax_a_ladder_general hn hV d (k + 1) m (by omega) (by omega) (by omega) hmn hcm_next
        with ⟨ma, hma, hreach⟩
      refine ⟨max 3 ma, ?_, ReachMax.step_eq hstep hreach (by rw [hp_ak])⟩
      rcases hma with hle3 | ⟨h10, hev, hle⟩
      · left; omega
      · right; exact ⟨by omega, by rw [Nat.max_eq_right (by omega)]; exact hev, by omega⟩
    · have hak_t : π .a k = true := by cases h : π .a k <;> [exact False.elim (hak h); rfl]
      have hdk : π .d k = true := hV.ha_d k hk2 hkn hak_t
      have hstep_ak : step (parityGame n) σ τ (decisionVertex n .a k) = gVertex n k := by
        rw [decisionVertex_eq_rowVertex hvp, step_rowVertex hn π τ hvp, hak_t]
        rfl
      have hstep_gk : step (parityGame n) σ τ (gVertex n k) = fVertex n k :=
        step_gVertex hτ (by omega) hkn
      by_cases hft : fTarget n π c_max b_max k = hVertex n k
      · have hstep_fk : step (parityGame n) σ τ (fVertex n k) = hVertex n k := by
          rw [step_fVertex_phaseTau σ π c_max b_max k (by omega) hkn, hft]
        have hstep_hk : step (parityGame n) σ τ (hVertex n k) = decisionVertex n .a (k + 1) :=
          step_hVertex hτ (by omega) hkn
        have h1 : ReachMax n σ τ (hVertex n k) (decisionVertex n .a (k + 1)) (2 * k + 8) :=
          ReachMax.one_step hstep_hk (gamePriority_hVertex n k (by omega) hkn)
        have h2 : ReachMax n σ τ (fVertex n k) (decisionVertex n .a (k + 1)) (2 * k + 8) :=
          ReachMax.step_eq hstep_fk h1 (by rw [gamePriority_fVertex n k (by omega) hkn]; omega)
        have h3 : ReachMax n σ τ (gVertex n k) (decisionVertex n .a (k + 1)) (2 * k + 8) :=
          ReachMax.step_eq hstep_gk h2 (by rw [gamePriority_gVertex n k (by omega) hkn]; omega)
        have h4 : ReachMax n σ τ (decisionVertex n .a k) (decisionVertex n .a (k + 1)) (2 * k + 8) :=
          ReachMax.step_eq hstep_ak h3 (by rw [hp_ak]; omega)
        rcases reachMax_a_ladder_general hn hV d (k + 1) m (by omega) (by omega) (by omega) hmn hcm_next
          with ⟨ma, hma, hreach⟩
        refine ⟨max (2 * k + 8) ma, ?_, h4.trans hreach⟩
        right
        rcases hma with hle3 | ⟨h10, hev, hle⟩
        · exact ⟨by omega, by rw [Nat.max_eq_left (by omega)]; omega, by omega⟩
        · refine ⟨by omega, ?_, by omega⟩
          by_cases hcmp : ma ≤ 2 * k + 8
          · rw [Nat.max_eq_left hcmp]; omega
          · rw [Nat.max_eq_right (by omega)]; exact hev
      · have hek_f : π .e k = false := by
          cases h : π .e k
          · rfl
          · exfalso; apply hft; unfold fTarget; rw [if_pos ⟨Or.inr hdk, h⟩]
        have hkc : k < c_max := by
          by_contra hle
          have := hV.ha_e k hk2 hkn hak_t (by omega)
          rw [hek_f] at this; cases this
        have hac_t : π .a c_max = true := by
          cases h : π .a c_max
          · exfalso; apply hft; unfold fTarget
            rw [if_neg (by simp [hek_f]), if_neg (by simp [hdk]), if_neg (by simp [hdk]),
                if_neg (by omega), if_neg (by simp [h])]
          · rfl
        have hcm' : c_max < m := by
          rcases hcm with h | h | h
          · exact h
          · rw [hac_t] at h; cases h
          · have := h k le_rfl hkm' hak_t
            rw [hek_f] at this; cases this
        have hft_e : fTarget n π c_max b_max k = decisionVertex n .e k := by
          unfold fTarget at hft ⊢
          split_ifs at hft ⊢ with h1 h2 h3 h4 h5 h6
          · exfalso; exact hft rfl
          · simp [hdk] at h2
          · simp [hdk] at h3
          · rfl
          · rfl
          · rfl
          · exfalso; exact hft rfl
        have hvp_ek : ValidRow n (.e, k) := ⟨by omega, hkn⟩
        have hstep_fk : step (parityGame n) σ τ (fVertex n k) = rowVertex n (.e, k) := by
          rw [step_fVertex_phaseTau σ π c_max b_max k (by omega) hkn,
              hft_e, decisionVertex_eq_rowVertex hvp_ek]
        have hstep_ek : step (parityGame n) σ τ (rowVertex n (.e, k)) = sVertex n := by
          rw [step_rowVertex hn π τ hvp_ek, hek_f]; rfl
        have hs_reach := reachMax_s_to_a_cmax hn hV
        have h1 : ReachMax n σ τ (rowVertex n (.e, k)) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
          ReachMax.step_eq hstep_ek hs_reach
            (by rw [gamePriority_rowVertex hn hvp_ek]; dsimp only; have := hV.hc_range; omega)
        have h2 : ReachMax n σ τ (fVertex n k) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
          ReachMax.step_eq hstep_fk h1
            (by rw [gamePriority_fVertex n k (by omega) hkn]; have := hV.hc_range; omega)
        have h3 : ReachMax n σ τ (gVertex n k) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
          ReachMax.step_eq hstep_gk h2
            (by rw [gamePriority_gVertex n k (by omega) hkn]; omega)
        have h4 : ReachMax n σ τ (decisionVertex n .a k) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
          ReachMax.step_eq hstep_ak h3 (by rw [hp_ak]; omega)
        have hlt_d : m - (c_max + 1) < d + 1 := by omega
        rcases reachMax_a_ladder_general hn hV (m - (c_max + 1)) (c_max + 1) m rfl
          (by omega) (by omega) hmn (Or.inl hcm') with ⟨ma, hma, hreach⟩
        refine ⟨max (2 * c_max + 8) ma, ?_, h4.trans hreach⟩
        right
        rcases hma with hle3 | ⟨h10, hev, hle⟩
        · exact ⟨by omega, by rw [Nat.max_eq_left (by omega)]; omega, by omega⟩
        · refine ⟨by omega, ?_, by omega⟩
          by_cases hcmp : ma ≤ 2 * c_max + 8
          · rw [Nat.max_eq_left hcmp]; omega
          · rw [Nat.max_eq_right (by omega)]; exact hev
termination_by d => d

lemma reachMax_sink_of_a {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max k : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) :
    ∃ m, ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max)
      (decisionVertex n .a k) (sinkVertex n) m := by
  have hc := hV.hc_range
  rcases reachMax_a_ladder_general hn hV (n + 1 - k) k (n + 1) rfl hk2 hkn le_rfl
    (Or.inl (by omega)) with ⟨ma, _, hreach⟩
  rw [decisionVertex_a_succ_n] at hreach
  exact ⟨ma, hreach⟩

lemma reachMax_g1 {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) :
    (ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max)
      (gVertex n 1) (decisionVertex n .a 2) 10) ∨
    (π .e 1 = false ∧ 2 ≤ c_max ∧
      ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max)
        (gVertex n 1) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hstep_g1 : step (parityGame n) σ τ (gVertex n 1) = fVertex n 1 :=
    step_gVertex hτ le_rfl (by omega)
  by_cases hft : fTarget n π c_max b_max 1 = hVertex n 1
  · left
    have hstep_f1 : step (parityGame n) σ τ (fVertex n 1) = hVertex n 1 := by
      rw [step_fVertex_phaseTau σ π c_max b_max 1 le_rfl (by omega), hft]
    have hstep_h1 : step (parityGame n) σ τ (hVertex n 1) = decisionVertex n .a 2 :=
      step_hVertex hτ le_rfl (by omega)
    have h1 : ReachMax n σ τ (hVertex n 1) (decisionVertex n .a 2) 10 :=
      ReachMax.one_step hstep_h1 (gamePriority_hVertex n 1 le_rfl (by omega))
    have h2 : ReachMax n σ τ (fVertex n 1) (decisionVertex n .a 2) 10 :=
      ReachMax.step_eq hstep_f1 h1 (by rw [gamePriority_fVertex n 1 le_rfl (by omega)]; omega)
    exact ReachMax.step_eq hstep_g1 h2 (by rw [gamePriority_gVertex n 1 le_rfl (by omega)]; omega)
  · right
    have he1_f : π .e 1 = false := by
      cases h : π .e 1
      · rfl
      · exfalso; apply hft; unfold fTarget; rw [if_pos ⟨Or.inl rfl, h⟩]
    have hc2 : 2 ≤ c_max := by
      have hc := hV.hc_range
      by_contra hlt
      have hc1 : c_max = 1 := by omega
      have := hV.hc_e
      rw [hc1, he1_f] at this
      cases this
    have hft_e : fTarget n π c_max b_max 1 = decisionVertex n .e 1 := by
      unfold fTarget at hft ⊢
      split_ifs at hft ⊢ with h1 h2 h3 h4 h5 h6
      · exfalso; exact hft rfl
      · omega
      · omega
      · rfl
      · rfl
      · rfl
      · exfalso; exact hft rfl
    have hvp_e1 : ValidRow n (.e, 1) := ⟨le_rfl, by omega⟩
    have hstep_f1 : step (parityGame n) σ τ (fVertex n 1) = rowVertex n (.e, 1) := by
      rw [step_fVertex_phaseTau σ π c_max b_max 1 le_rfl (by omega),
          hft_e, decisionVertex_eq_rowVertex hvp_e1]
    have hstep_e1 : step (parityGame n) σ τ (rowVertex n (.e, 1)) = sVertex n := by
      rw [step_rowVertex hn π τ hvp_e1, he1_f]; rfl
    have hs := reachMax_s_to_a_cmax hn hV
    have h1 : ReachMax n σ τ (rowVertex n (.e, 1)) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
      ReachMax.step_eq hstep_e1 hs (by rw [gamePriority_rowVertex hn hvp_e1]; dsimp only; omega)
    have h2 : ReachMax n σ τ (fVertex n 1) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
      ReachMax.step_eq hstep_f1 h1 (by rw [gamePriority_fVertex n 1 le_rfl (by omega)]; omega)
    have h3 : ReachMax n σ τ (gVertex n 1) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
      ReachMax.step_eq hstep_g1 h2 (by rw [gamePriority_gVertex n 1 le_rfl (by omega)]; omega)
    exact ⟨he1_f, hc2, h3⟩

lemma reachMax_d_false_to_a {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (hi2 : 2 ≤ i) (hin : i ≤ n) (hdi : π .d i = false) :
    ∃ md, (10 ≤ md ∧ md % 2 = 0 ∧ md ≤ 2 * i + 6) ∧
      ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max)
        (rowVertex n (.d, i)) (decisionVertex n .a (i + 1)) md := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hai : π .a i = false := by
    cases h : π .a i
    · rfl
    · have := hV.ha_d i hi2 hin h; rw [hdi] at this; cases this
  have hvp_ai : ValidRow n (.a, i) := ⟨hi2, hin⟩
  have hstep_ai : step (parityGame n) σ τ (decisionVertex n .a i) = decisionVertex n .a (i + 1) := by
    rw [decisionVertex_eq_rowVertex hvp_ai, step_rowVertex hn π τ hvp_ai, hai]; rfl
  have hp_ai : gamePriority n (decisionVertex n .a i) = 3 := by
    rw [decisionVertex_eq_rowVertex hvp_ai, gamePriority_rowVertex hn hvp_ai]
  have hai_step : ReachMax n σ τ (decisionVertex n .a i) (decisionVertex n .a (i + 1)) 3 :=
    ReachMax.one_step hstep_ai hp_ai
  suffices hto_ai : ∃ md, (10 ≤ md ∧ md % 2 = 0 ∧ md ≤ 2 * i + 6) ∧
      ReachMax n σ τ (rowVertex n (.d, i)) (decisionVertex n .a i) md by
    rcases hto_ai with ⟨md, ⟨h10, hev, hle⟩, hreach⟩
    exact ⟨md, ⟨h10, hev, hle⟩, hreach.trans_eq hai_step (by omega)⟩
  have hd_g := reachMax_d_to_g_bEff hn hV τ hi2 hin hdi
  have hb := hV.hb_range
  have hbe := bEff_range hb.1 hi2
  by_cases hbe2 : 2 ≤ bEff b_max i
  · have hbe_eq := (bEff_eq_self_of_ge_two hbe2).1
    have hblt := (bEff_eq_self_of_ge_two hbe2).2
    have hci : c_max < i := by
      rcases hV.hd_false i hi2 hin hdi with h | ⟨_, hb1, _, _⟩
      · exact h
      · omega
    have hbed := hV.hb_ed (by omega)
    rw [hbe_eq] at hd_g
    have hg_a := reachMax_g_f_h_of_ed (n := n) c_max b_max b_max hb.1 (by omega) hbed.1 (fun _ => hbed.2)
    have hd_abe : ReachMax n σ τ (rowVertex n (.d, i)) (decisionVertex n .a (b_max + 1)) (2 * b_max + 8) :=
      hd_g.trans_eq hg_a (by omega)
    rcases reachMax_a_ladder_general hn hV (i - (b_max + 1)) (b_max + 1) i rfl
      (by omega) (by omega) (by omega) (Or.inl hci) with ⟨ma, hma, hreach_a⟩
    refine ⟨max (2 * b_max + 8) ma, ?_, hd_abe.trans hreach_a⟩
    rcases hma with hle3 | ⟨h10, hev, hle⟩
    · exact ⟨by omega, by rw [Nat.max_eq_left (by omega)]; omega, by omega⟩
    · refine ⟨by omega, ?_, by omega⟩
      by_cases hcmp : ma ≤ 2 * b_max + 8
      · rw [Nat.max_eq_left hcmp]; omega
      · rw [Nat.max_eq_right (by omega)]; exact hev
  · have hbe1 : bEff b_max i = 1 := by omega
    have hd_g1 : ReachMax n σ τ (rowVertex n (.d, i)) (gVertex n 1) 5 := hbe1 ▸ hd_g
    rcases reachMax_g1 hn hV with hg1 | ⟨he1_f, hc2, hg1⟩
    · have hd_a2 : ReachMax n σ τ (rowVertex n (.d, i)) (decisionVertex n .a 2) 10 :=
        hd_g1.trans_eq hg1 (by omega)
      rcases hV.hd_false i hi2 hin hdi with hci | ⟨hic, _, _, haf⟩
      · rcases reachMax_a_ladder_general hn hV (i - 2) 2 i rfl
          le_rfl hi2 (by omega) (Or.inl hci) with ⟨ma, hma, hreach_a⟩
        refine ⟨max 10 ma, ?_, hd_a2.trans hreach_a⟩
        rcases hma with hle3 | ⟨h10, hev, hle⟩
        · exact ⟨by omega, by rw [Nat.max_eq_left (by omega)], by omega⟩
        · refine ⟨by omega, ?_, by omega⟩
          by_cases hcmp : ma ≤ 10
          · rw [Nat.max_eq_left hcmp]
          · rw [Nat.max_eq_right (by omega)]; exact hev
      · have hreach_a := reachMax_a_ladder_all_false hn τ (i - 2) 2 i rfl
          le_rfl hi2 (by omega) (fun r hr2 hri => haf r hr2 (lt_trans hri hic))
        refine ⟨10, ⟨by omega, by omega, by omega⟩, hd_a2.trans_eq hreach_a ?_⟩
        split_ifs <;> omega
    · have hci : c_max < i := by
        rcases hV.hd_false i hi2 hin hdi with h | ⟨_, _, he1_t, _⟩
        · exact h
        · rw [he1_f] at he1_t; cases he1_t
      have hd_ac : ReachMax n σ τ (rowVertex n (.d, i)) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
        hd_g1.trans_eq hg1 (by omega)
      rcases reachMax_a_ladder_general hn hV (i - (c_max + 1)) (c_max + 1) i rfl
        (by omega) (by omega) (by omega) (Or.inl hci) with ⟨ma, hma, hreach_a⟩
      refine ⟨max (2 * c_max + 8) ma, ?_, hd_ac.trans hreach_a⟩
      rcases hma with hle3 | ⟨h10, hev, hle⟩
      · exact ⟨by omega, by rw [Nat.max_eq_left (by omega)]; omega, by omega⟩
      · refine ⟨by omega, ?_, by omega⟩
        by_cases hcmp : ma ≤ 2 * c_max + 8
        · rw [Nat.max_eq_left hcmp]; omega
        · rw [Nat.max_eq_right (by omega)]; exact hev

lemma reachMax_sink_of_valid {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (x : Fin (vertices n)) :
    ∃ m, ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max) x (sinkVertex n) m := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hc := hV.hc_range
  have hb := hV.hb_range
  rcases reachMax_sink_of_a hn hV (by omega) (by omega : c_max + 1 ≤ n + 1) with ⟨ms_a, hms_a⟩
  have hms : ReachMax n σ τ (sVertex n) (sinkVertex n) (max (2 * c_max + 8) ms_a) :=
    (reachMax_s_to_a_cmax hn hV).trans hms_a
  have hd_sink : ∀ i, 2 ≤ i → i ≤ n → π .d i = false →
      ∃ m, ReachMax n σ τ (rowVertex n (.d, i)) (sinkVertex n) m := by
    intro i hi2 hin hdi
    rcases reachMax_d_false_to_a hn hV hi2 hin hdi with ⟨md, _, hd_a⟩
    rcases reachMax_sink_of_a hn hV (by omega) (by omega : i + 1 ≤ n + 1) with ⟨ma, hma⟩
    exact ⟨_, hd_a.trans hma⟩
  have hf_sink : ∀ i, 1 ≤ i → i ≤ n → ∃ m, ReachMax n σ τ (fVertex n i) (sinkVertex n) m := by
    intro i hi1 hin
    have hstep_f : step (parityGame n) σ τ (fVertex n i) = fTarget n π c_max b_max i :=
      step_fVertex_phaseTau σ π c_max b_max i hi1 hin
    have hft_cases :
        fTarget n π c_max b_max i = hVertex n i ∨
        (2 ≤ i ∧ π .d i = false ∧ fTarget n π c_max b_max i = decisionVertex n .d i) ∨
        (π .e i = false ∧ fTarget n π c_max b_max i = decisionVertex n .e i) := by
      unfold fTarget
      split_ifs with h1 h2 h3 h4 h5 h6
      · left; rfl
      · right; left; exact ⟨by omega, h2.2.1, rfl⟩
      · right; left; exact ⟨by omega, h3.2.1, rfl⟩
      · right; right; exact ⟨h3.2.2, rfl⟩
      · right; right
        refine ⟨?_, rfl⟩
        cases he : π .e i
        · rfl
        · exfalso
          by_cases hd : i = 1 ∨ π .d i = true
          · exact h1 ⟨hd, he⟩
          · have hd_f : π .d i = false := by
              cases h : π .d i <;> [rfl; exact False.elim (hd (Or.inr h))]
            exact h2 ⟨by omega, hd_f, he⟩
      · right; right
        refine ⟨?_, rfl⟩
        cases he : π .e i
        · rfl
        · exfalso
          by_cases hd : i = 1 ∨ π .d i = true
          · exact h1 ⟨hd, he⟩
          · have hd_f : π .d i = false := by
              cases h : π .d i <;> [rfl; exact False.elim (hd (Or.inr h))]
            exact h2 ⟨by omega, hd_f, he⟩
      · left; rfl
    rcases hft_cases with hft | ⟨hi2, hdi_f, hft⟩ | ⟨hei_f, hft⟩
    · rw [hft] at hstep_f
      have hstep_h : step (parityGame n) σ τ (hVertex n i) = decisionVertex n .a (i + 1) :=
        step_hVertex hτ hi1 hin
      rcases reachMax_sink_of_a hn hV (by omega) (by omega : i + 1 ≤ n + 1) with ⟨ma, hma⟩
      exact ⟨_, ReachMax.next (hstep_f ▸ ReachMax.next (hstep_h ▸ hma))⟩
    · have hvp_d : ValidRow n (.d, i) := ⟨hi2, hin⟩
      rcases hd_sink i hi2 hin hdi_f with ⟨md, hmd⟩
      rw [hft, decisionVertex_eq_rowVertex hvp_d] at hstep_f
      exact ⟨_, ReachMax.next (hstep_f ▸ hmd)⟩
    · have hvp_e : ValidRow n (.e, i) := ⟨hi1, hin⟩
      have hstep_e : step (parityGame n) σ τ (rowVertex n (.e, i)) = sVertex n := by
        rw [step_rowVertex hn π τ hvp_e, hei_f]; rfl
      rw [hft, decisionVertex_eq_rowVertex hvp_e] at hstep_f
      exact ⟨_, ReachMax.next (hstep_f ▸ ReachMax.next (hstep_e ▸ hms))⟩
  have hg_sink : ∀ i, 1 ≤ i → i ≤ n → ∃ m, ReachMax n σ τ (gVertex n i) (sinkVertex n) m := by
    intro i hi1 hin
    rcases hf_sink i hi1 hin with ⟨mf, hmf⟩
    have hstep_g := step_gVertex (σ := σ) hτ hi1 hin
    exact ⟨_, ReachMax.next (hstep_g ▸ hmf)⟩
  have hh_sink : ∀ i, 1 ≤ i → i ≤ n → ∃ m, ReachMax n σ τ (hVertex n i) (sinkVertex n) m := by
    intro i hi1 hin
    rcases reachMax_sink_of_a hn hV (by omega) (by omega : i + 1 ≤ n + 1) with ⟨ma, hma⟩
    have hstep_h := step_hVertex (σ := σ) hτ hi1 hin
    exact ⟨_, ReachMax.next (hstep_h ▸ hma)⟩
  by_cases hx_rows : x.val < rows n
  · set r : Fin (rows n) := ⟨x.val, hx_rows⟩
    have hvp := rowName_valid hn r
    have hx_eq : x = rowVertex n (rowName n r) := by
      ext
      rw [val_rowVertex hn hvp, rowRank_rowName hn r]
    rw [hx_eq]
    rcases hr : rowName n r with ⟨k, i⟩
    rw [hr] at hvp
    cases k
    · have hvp' : 2 ≤ i ∧ i ≤ n := hvp
      rcases reachMax_sink_of_a hn hV hvp'.1 (by omega) with ⟨ma, hma⟩
      rw [decisionVertex_eq_rowVertex hvp] at hma
      exact ⟨ma, hma⟩
    · have hvp' : 2 ≤ i ∧ i ≤ n - 1 := hvp
      have hbe := bEff_range hb.1 (by omega : 2 ≤ i + 1)
      have hb_g := reachMax_b_ladder hn hV τ (by omega : 2 ≤ i + 1) (by omega : i + 1 ≤ n)
        (i - max 2 (bEff b_max (i + 1))) i rfl
        (by omega)
        (by omega)
      rw [decisionVertex_eq_rowVertex hvp] at hb_g
      rcases hg_sink (bEff b_max (i + 1)) hbe.1 (by omega) with ⟨mg, hmg⟩
      exact ⟨_, hb_g.trans hmg⟩
    · have hvp' : 2 ≤ i ∧ i ≤ n := hvp
      have hce := bEff_range hc.1 (by omega : 2 ≤ i + 1)
      have hc_g := reachMax_c_ladder hn hV τ (by omega : 2 ≤ i + 1) (by omega : i + 1 ≤ n + 1)
        (i - max 2 (bEff c_max (i + 1))) i rfl
        (by omega)
        (by omega)
      rw [decisionVertex_eq_rowVertex hvp] at hc_g
      rcases hg_sink (bEff c_max (i + 1)) hce.1 (by omega) with ⟨mg, hmg⟩
      exact ⟨_, hc_g.trans hmg⟩
    · have hvp' : 2 ≤ i ∧ i ≤ n := hvp
      by_cases hdi : π .d i = false
      · exact hd_sink i hvp'.1 hvp'.2 hdi
      · have hdi_t : π .d i = true := by cases h : π .d i <;> [exact False.elim (hdi h); rfl]
        have hstep_d : step (parityGame n) σ τ (rowVertex n (.d, i)) = fVertex n i := by
          rw [step_rowVertex hn π τ hvp, hdi_t]; rfl
        rcases hf_sink i (by omega) hvp'.2 with ⟨mf, hmf⟩
        exact ⟨_, ReachMax.next (hstep_d ▸ hmf)⟩
    · have hvp' : 1 ≤ i ∧ i ≤ n := hvp
      by_cases hei : π .e i = false
      · have hstep_e : step (parityGame n) σ τ (rowVertex n (.e, i)) = sVertex n := by
          rw [step_rowVertex hn π τ hvp, hei]; rfl
        exact ⟨_, ReachMax.next (hstep_e ▸ hms)⟩
      · have hei_t : π .e i = true := by cases h : π .e i <;> [exact False.elim (hei h); rfl]
        have hstep_e : step (parityGame n) σ τ (rowVertex n (.e, i)) = fVertex n i := by
          rw [step_rowVertex hn π τ hvp, hei_t]; rfl
        rcases hf_sink i hvp'.1 hvp'.2 with ⟨mf, hmf⟩
        exact ⟨_, ReachMax.next (hstep_e ▸ hmf)⟩
  · have hx_lt := x.isLt
    unfold vertices at hx_lt
    by_cases hx_f : x.val < rows n + n
    · set i := x.val - rows n + 1
      have hx_eq : x = fVertex n i := by
        ext; rw [val_fVertex n i (by omega) (by omega)]; omega
      rw [hx_eq]
      exact hf_sink i (by omega) (by omega)
    · by_cases hx_g : x.val < rows n + 2 * n
      · set i := x.val - (rows n + n) + 1
        have hx_eq : x = gVertex n i := by
          ext; rw [val_gVertex n i (by omega) (by omega)]; omega
        rw [hx_eq]
        exact hg_sink i (by omega) (by omega)
      · by_cases hx_h : x.val < rows n + 3 * n
        · set i := x.val - (rows n + 2 * n) + 1
          have hx_eq : x = hVertex n i := by
            ext; rw [val_hVertex n i (by omega) (by omega)]; omega
          rw [hx_eq]
          exact hh_sink i (by omega) (by omega)
        · by_cases hx_s : x.val = rows n + 3 * n
          · have hx_eq : x = sVertex n := (eq_sVertex_iff n x).mpr hx_s
            rw [hx_eq]
            exact ⟨_, hms⟩
          · have hx_eq : x = sinkVertex n := (eq_sinkVertex_iff n x).mpr (by omega)
            rw [hx_eq]
            exact ⟨0, ReachMax.refl _⟩

def CycOK (n : ℕ) (σ τ' : Fin (vertices n) → Fin (vertices n)) (x : Fin (vertices n)) : Prop :=
  (FriedmannParity.playValue (parityGame n) σ τ' x).cyclePriority = 1 ∨
  (FriedmannParity.playValue (parityGame n) σ τ' x).cyclePriority = 6

lemma cycOK_of_step {n : ℕ} {σ τ' : Fin (vertices n) → Fin (vertices n)} {x y : Fin (vertices n)}
    (hstep : step (parityGame n) σ τ' x = y) (hy : CycOK n σ τ' y) :
    CycOK n σ τ' x := by
  unfold CycOK at hy ⊢
  rwa [← hstep, playValue_cyclePriority_step] at hy

lemma cycOK_of_reachMax {n : ℕ} {σ τ' : Fin (vertices n) → Fin (vertices n)} {x y : Fin (vertices n)}
    {m : ℕ} (h : ReachMax n σ τ' x y m) (hy : CycOK n σ τ' y) :
    CycOK n σ τ' x := by
  unfold CycOK at hy ⊢
  rwa [cyclePriority_eq_of_reachMax h]

lemma cycOK_of_two_cycle_fVertex {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {τ' : Fin (vertices n) → Fin (vertices n)} {k : Kind} {i : ℕ}
    (hi1 : 1 ≤ i) (hin : i ≤ n) (hvp : ValidRow n (k, i))
    (hk : k = .d ∨ k = .e) (hbit : π k i = true)
    (hstep : step (parityGame n) (policyStrategy n π) τ' (fVertex n i) = rowVertex n (k, i)) :
    CycOK n (policyStrategy n π) τ' (fVertex n i) := by
  right
  have hu_own := owner_rowVertex hn hvp
  have hu_p : gamePriority n (rowVertex n (k, i)) = 5 := by
    rw [gamePriority_rowVertex hn hvp]
    rcases hk with rfl | rfl <;> rfl
  have hw_p := gamePriority_fVertex n i hi1 hin
  have hσu : policyStrategy n π (rowVertex n (k, i)) = fVertex n i := by
    rw [policyStrategy_rowVertex hn π hvp, hbit]
    rcases hk with rfl | rfl <;> rfl
  have hcl := cycleLeader_eq_of_two_cycle hu_own hu_p hw_p hσu hstep
  rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl]
  exact hw_p

lemma cycOK_fVertex_of_ed {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {τ' : Fin (vertices n) → Fin (vertices n)}
    (hτ' : FriedmannParity.Legal (parityGame n) true τ') {m : ℕ}
    (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (he : π .e m = true) (hd : 2 ≤ m → π .d m = true)
    (ha : CycOK n (policyStrategy n π) τ' (decisionVertex n .a (m + 1))) :
    CycOK n (policyStrategy n π) τ' (fVertex n m) := by
  set σ := policyStrategy n π
  have hmem := hτ' (fVertex n m) (owner_fVertex n m hm1 hmn)
  change τ' (fVertex n m) ∈ gameSuccessors n (fVertex n m) at hmem
  rw [gameSuccessors_fVertex n m hm1 hmn] at hmem
  have hstep_f := step_fVertex σ τ' hm1 hmn
  by_cases hm_eq_1 : m = 1
  · subst hm_eq_1
    rw [if_pos rfl] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · apply cycOK_of_step (hstep_f.trans h)
      exact cycOK_of_step (step_hVertex hτ' hm1 hmn) ha
    · have hvp : ValidRow n (.e, 1) := ⟨le_rfl, hmn⟩
      rw [decisionVertex_eq_rowVertex hvp] at h
      exact cycOK_of_two_cycle_fVertex hn le_rfl hmn hvp (Or.inr rfl) he (hstep_f.trans h)
  · rw [if_neg hm_eq_1] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · apply cycOK_of_step (hstep_f.trans h)
      exact cycOK_of_step (step_hVertex hτ' hm1 hmn) ha
    · have hvp : ValidRow n (.d, m) := ⟨by omega, hmn⟩
      rw [decisionVertex_eq_rowVertex hvp] at h
      exact cycOK_of_two_cycle_fVertex hn hm1 hmn hvp (Or.inl rfl) (hd (by omega)) (hstep_f.trans h)
    · have hvp : ValidRow n (.e, m) := ⟨hm1, hmn⟩
      rw [decisionVertex_eq_rowVertex hvp] at h
      exact cycOK_of_two_cycle_fVertex hn hm1 hmn hvp (Or.inr rfl) he (hstep_f.trans h)

lemma cycOK_a_of_valid {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max)
    {τ' : Fin (vertices n) → Fin (vertices n)}
    (hτ' : FriedmannParity.Legal (parityGame n) true τ') :
    ∀ d k, n + 1 - k = d → 2 ≤ k → k ≤ n + 1 →
      CycOK n (policyStrategy n π) τ' (decisionVertex n .a k)
  | 0, k, hd, hk2, hkn => by
    have hk : k = n + 1 := by omega
    subst hk
    rw [decisionVertex_a_succ_n]
    left
    exact playValue_cyclePriority_sinkVertex (policyStrategy_legal n π) hτ'
  | d + 1, k, hd, hk2, hkn => by
    set σ := policyStrategy n π
    have hkn' : k ≤ n := by omega
    have hvp : ValidRow n (.a, k) := ⟨hk2, hkn'⟩
    have ih_succ := cycOK_a_of_valid hn hV hτ' d (k + 1) (by omega) (by omega) (by omega)
    by_cases hak : π .a k = false
    · have hstep : step (parityGame n) σ τ' (decisionVertex n .a k) = decisionVertex n .a (k + 1) := by
        rw [decisionVertex_eq_rowVertex hvp, step_rowVertex hn π τ' hvp, hak]; rfl
      exact cycOK_of_step hstep ih_succ
    · have hak_t : π .a k = true := by cases h : π .a k <;> [exact False.elim (hak h); rfl]
      have hdk : π .d k = true := hV.ha_d k hk2 hkn' hak_t
      have hstep_ak : step (parityGame n) σ τ' (decisionVertex n .a k) = gVertex n k := by
        rw [decisionVertex_eq_rowVertex hvp, step_rowVertex hn π τ' hvp, hak_t]; rfl
      have hstep_gk := step_gVertex (σ := σ) hτ' (by omega) hkn'
      apply cycOK_of_step hstep_ak
      apply cycOK_of_step hstep_gk
      have hmem := hτ' (fVertex n k) (owner_fVertex n k (by omega) hkn')
      change τ' (fVertex n k) ∈ gameSuccessors n (fVertex n k) at hmem
      rw [gameSuccessors_fVertex n k (by omega) hkn', if_neg (by omega)] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hstep_fk := step_fVertex σ τ' (by omega) hkn'
      rcases hmem with h | h | h
      · apply cycOK_of_step (hstep_fk.trans h)
        exact cycOK_of_step (step_hVertex hτ' (by omega) hkn') ih_succ
      · have hvp_d : ValidRow n (.d, k) := ⟨hk2, hkn'⟩
        rw [decisionVertex_eq_rowVertex hvp_d] at h
        exact cycOK_of_two_cycle_fVertex hn (by omega) hkn' hvp_d (Or.inl rfl) hdk (hstep_fk.trans h)
      · have hvp_e : ValidRow n (.e, k) := ⟨by omega, hkn'⟩
        rw [decisionVertex_eq_rowVertex hvp_e] at h
        by_cases hek : π .e k = true
        · exact cycOK_of_two_cycle_fVertex hn (by omega) hkn' hvp_e (Or.inr rfl) hek (hstep_fk.trans h)
        · have hek_f : π .e k = false := by cases h' : π .e k <;> [rfl; exact False.elim (hek h')]
          have hkc : k < c_max := by
            by_contra hle
            exact hek (hV.ha_e k hk2 hkn' hak_t (by omega))
          have hstep_ek : step (parityGame n) σ τ' (rowVertex n (.e, k)) = sVertex n := by
            rw [step_rowVertex hn π τ' hvp_e, hek_f]; rfl
          apply cycOK_of_step (hstep_fk.trans h)
          apply cycOK_of_step hstep_ek
          have hs_g := reachMax_s_to_g_cmax hn hV hτ'
          apply cycOK_of_reachMax hs_g
          have hc := hV.hc_range
          apply cycOK_of_step (step_gVertex hτ' hc.1 hc.2)
          have ih_cmax := cycOK_a_of_valid hn hV hτ' (n + 1 - (c_max + 1)) (c_max + 1) rfl
            (by omega) (by omega)
          exact cycOK_fVertex_of_ed hn hτ' hc.1 hc.2 hV.hc_e hV.hc_d ih_cmax
termination_by d => d

lemma cyclePriority_one_or_six_of_valid {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max)
    {τ' : Fin (vertices n) → Fin (vertices n)}
    (hτ' : FriedmannParity.Legal (parityGame n) true τ')
    (x : Fin (vertices n)) :
    CycOK n (policyStrategy n π) τ' x := by
  set σ := policyStrategy n π
  have hc := hV.hc_range
  have hb := hV.hb_range
  have ha_ok : ∀ k, 2 ≤ k → k ≤ n + 1 → CycOK n σ τ' (decisionVertex n .a k) :=
    fun k hk2 hkn => cycOK_a_of_valid hn hV hτ' (n + 1 - k) k rfl hk2 hkn
  have hs_ok : CycOK n σ τ' (sVertex n) := by
    apply cycOK_of_reachMax (reachMax_s_to_g_cmax hn hV hτ')
    apply cycOK_of_step (step_gVertex hτ' hc.1 hc.2)
    exact cycOK_fVertex_of_ed hn hτ' hc.1 hc.2 hV.hc_e hV.hc_d (ha_ok (c_max + 1) (by omega) (by omega))
  have hf1_ok : CycOK n σ τ' (fVertex n 1) := by
    have hmem := hτ' (fVertex n 1) (owner_fVertex n 1 le_rfl (by omega))
    change τ' (fVertex n 1) ∈ gameSuccessors n (fVertex n 1) at hmem
    rw [gameSuccessors_fVertex n 1 le_rfl (by omega), if_pos rfl] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hstep_f1 := step_fVertex σ τ' le_rfl (by omega)
    rcases hmem with h | h
    · apply cycOK_of_step (hstep_f1.trans h)
      exact cycOK_of_step (step_hVertex hτ' le_rfl (by omega)) (ha_ok 2 le_rfl (by omega))
    · have hvp : ValidRow n (.e, 1) := ⟨le_rfl, by omega⟩
      rw [decisionVertex_eq_rowVertex hvp] at h
      by_cases he1 : π .e 1 = true
      · exact cycOK_of_two_cycle_fVertex hn le_rfl (by omega) hvp (Or.inr rfl) he1 (hstep_f1.trans h)
      · have he1_f : π .e 1 = false := by cases h' : π .e 1 <;> [rfl; exact False.elim (he1 h')]
        have hstep_e1 : step (parityGame n) σ τ' (rowVertex n (.e, 1)) = sVertex n := by
          rw [step_rowVertex hn π τ' hvp, he1_f]; rfl
        exact cycOK_of_step (hstep_f1.trans h) (cycOK_of_step hstep_e1 hs_ok)
  have hd_false_ok : ∀ i, 2 ≤ i → i ≤ n → π .d i = false → CycOK n σ τ' (rowVertex n (.d, i)) := by
    intro i hi2 hin hdi
    apply cycOK_of_reachMax (reachMax_d_to_g_bEff hn hV τ' hi2 hin hdi)
    have hbe := bEff_range hb.1 hi2
    apply cycOK_of_step (step_gVertex hτ' hbe.1 (by omega))
    by_cases hbe2 : 2 ≤ bEff b_max i
    · have hbe_eq := (bEff_eq_self_of_ge_two hbe2).1
      have hbed := hV.hb_ed (by omega)
      rw [hbe_eq]
      exact cycOK_fVertex_of_ed hn hτ' hb.1 (by omega) hbed.1
        (fun _ => hbed.2) (ha_ok (b_max + 1) (by omega) (by omega))
    · have hbe1 : bEff b_max i = 1 := by omega
      rw [hbe1]
      exact hf1_ok
  have hf_ok : ∀ i, 1 ≤ i → i ≤ n → CycOK n σ τ' (fVertex n i) := by
    intro i hi1 hin
    by_cases hi_eq_1 : i = 1
    · exact hi_eq_1 ▸ hf1_ok
    · have hmem := hτ' (fVertex n i) (owner_fVertex n i hi1 hin)
      change τ' (fVertex n i) ∈ gameSuccessors n (fVertex n i) at hmem
      rw [gameSuccessors_fVertex n i hi1 hin, if_neg hi_eq_1] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hstep_f := step_fVertex σ τ' hi1 hin
      rcases hmem with h | h | h
      · apply cycOK_of_step (hstep_f.trans h)
        exact cycOK_of_step (step_hVertex hτ' hi1 hin) (ha_ok (i + 1) (by omega) (by omega))
      · have hvp_d : ValidRow n (.d, i) := ⟨by omega, hin⟩
        rw [decisionVertex_eq_rowVertex hvp_d] at h
        by_cases hdi : π .d i = true
        · exact cycOK_of_two_cycle_fVertex hn hi1 hin hvp_d (Or.inl rfl) hdi (hstep_f.trans h)
        · have hdi_f : π .d i = false := by cases h' : π .d i <;> [rfl; exact False.elim (hdi h')]
          exact cycOK_of_step (hstep_f.trans h) (hd_false_ok i (by omega) hin hdi_f)
      · have hvp_e : ValidRow n (.e, i) := ⟨hi1, hin⟩
        rw [decisionVertex_eq_rowVertex hvp_e] at h
        by_cases hei : π .e i = true
        · exact cycOK_of_two_cycle_fVertex hn hi1 hin hvp_e (Or.inr rfl) hei (hstep_f.trans h)
        · have hei_f : π .e i = false := by cases h' : π .e i <;> [rfl; exact False.elim (hei h')]
          have hstep_e : step (parityGame n) σ τ' (rowVertex n (.e, i)) = sVertex n := by
            rw [step_rowVertex hn π τ' hvp_e, hei_f]; rfl
          exact cycOK_of_step (hstep_f.trans h) (cycOK_of_step hstep_e hs_ok)
  have hg_ok : ∀ i, 1 ≤ i → i ≤ n → CycOK n σ τ' (gVertex n i) :=
    fun i hi1 hin => cycOK_of_step (step_gVertex hτ' hi1 hin) (hf_ok i hi1 hin)
  have hh_ok : ∀ i, 1 ≤ i → i ≤ n → CycOK n σ τ' (hVertex n i) :=
    fun i hi1 hin => cycOK_of_step (step_hVertex hτ' hi1 hin) (ha_ok (i + 1) (by omega) (by omega))
  by_cases hx_rows : x.val < rows n
  · set r : Fin (rows n) := ⟨x.val, hx_rows⟩
    have hvp := rowName_valid hn r
    have hx_eq : x = rowVertex n (rowName n r) := by
      ext; rw [val_rowVertex hn hvp, rowRank_rowName hn r]
    rw [hx_eq]
    rcases hr : rowName n r with ⟨k, i⟩
    rw [hr] at hvp
    cases k
    · have hvp' : 2 ≤ i ∧ i ≤ n := hvp
      have h := ha_ok i hvp'.1 (by omega)
      rwa [decisionVertex_eq_rowVertex hvp] at h
    · have hvp' : 2 ≤ i ∧ i ≤ n - 1 := hvp
      have hbe := bEff_range hb.1 (by omega : 2 ≤ i + 1)
      have hb_g := reachMax_b_ladder hn hV τ' (by omega : 2 ≤ i + 1) (by omega : i + 1 ≤ n)
        (i - max 2 (bEff b_max (i + 1))) i rfl
        (by omega)
        (by omega)
      rw [decisionVertex_eq_rowVertex hvp] at hb_g
      exact cycOK_of_reachMax hb_g (hg_ok (bEff b_max (i + 1)) hbe.1 (by omega))
    · have hvp' : 2 ≤ i ∧ i ≤ n := hvp
      have hce := bEff_range hc.1 (by omega : 2 ≤ i + 1)
      have hc_g := reachMax_c_ladder hn hV τ' (by omega : 2 ≤ i + 1) (by omega : i + 1 ≤ n + 1)
        (i - max 2 (bEff c_max (i + 1))) i rfl
        (by omega)
        (by omega)
      rw [decisionVertex_eq_rowVertex hvp] at hc_g
      exact cycOK_of_reachMax hc_g (hg_ok (bEff c_max (i + 1)) hce.1 (by omega))
    · have hvp' : 2 ≤ i ∧ i ≤ n := hvp
      by_cases hdi : π .d i = false
      · exact hd_false_ok i hvp'.1 hvp'.2 hdi
      · have hdi_t : π .d i = true := by cases h : π .d i <;> [exact False.elim (hdi h); rfl]
        have hstep_d : step (parityGame n) σ τ' (rowVertex n (.d, i)) = fVertex n i := by
          rw [step_rowVertex hn π τ' hvp, hdi_t]; rfl
        exact cycOK_of_step hstep_d (hf_ok i (by omega) hvp'.2)
    · have hvp' : 1 ≤ i ∧ i ≤ n := hvp
      by_cases hei : π .e i = false
      · have hstep_e : step (parityGame n) σ τ' (rowVertex n (.e, i)) = sVertex n := by
          rw [step_rowVertex hn π τ' hvp, hei]; rfl
        exact cycOK_of_step hstep_e hs_ok
      · have hei_t : π .e i = true := by cases h : π .e i <;> [exact False.elim (hei h); rfl]
        have hstep_e : step (parityGame n) σ τ' (rowVertex n (.e, i)) = fVertex n i := by
          rw [step_rowVertex hn π τ' hvp, hei_t]; rfl
        exact cycOK_of_step hstep_e (hf_ok i hvp'.1 hvp'.2)
  · have hx_lt := x.isLt
    unfold vertices at hx_lt
    by_cases hx_f : x.val < rows n + n
    · set i := x.val - rows n + 1
      have hx_eq : x = fVertex n i := by
        ext; rw [val_fVertex n i (by omega) (by omega)]; omega
      rw [hx_eq]; exact hf_ok i (by omega) (by omega)
    · by_cases hx_g : x.val < rows n + 2 * n
      · set i := x.val - (rows n + n) + 1
        have hx_eq : x = gVertex n i := by
          ext; rw [val_gVertex n i (by omega) (by omega)]; omega
        rw [hx_eq]; exact hg_ok i (by omega) (by omega)
      · by_cases hx_h : x.val < rows n + 3 * n
        · set i := x.val - (rows n + 2 * n) + 1
          have hx_eq : x = hVertex n i := by
            ext; rw [val_hVertex n i (by omega) (by omega)]; omega
          rw [hx_eq]; exact hh_ok i (by omega) (by omega)
        · by_cases hx_s : x.val = rows n + 3 * n
          · have hx_eq : x = sVertex n := (eq_sVertex_iff n x).mpr hx_s
            rw [hx_eq]; exact hs_ok
          · have hx_eq : x = sinkVertex n := (eq_sinkVertex_iff n x).mpr (by omega)
            rw [hx_eq]; left; exact playValue_cyclePriority_sinkVertex (policyStrategy_legal n π) hτ'

lemma cyclePriority_eq_one_of_valid {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (y : Fin (vertices n)) :
    (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max) y).cyclePriority = 1 := by
  rcases reachMax_sink_of_valid hn hV y with ⟨ms, hms⟩
  exact (cyclePriority_eq_of_reachMax hms).trans
    (playValue_cyclePriority_sinkVertex (policyStrategy_legal n π) (phaseTau_legal n π c_max b_max))

lemma valueLT_d_false_hVertex {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (hi2 : 2 ≤ i) (hin : i ≤ n) (hdi : π .d i = false) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .d i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (hVertex n i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hvp_d : ValidRow n (.d, i) := ⟨hi2, hin⟩
  rcases reachMax_d_false_to_a hn hV hi2 hin hdi with ⟨md, ⟨_, _, hle⟩, hd_a⟩
  rw [← decisionVertex_eq_rowVertex hvp_d] at hd_a
  have hh_a : ReachMax n σ τ (hVertex n i) (decisionVertex n .a (i + 1)) (2 * i + 8) :=
    ReachMax.one_step (step_hVertex hτ (by omega) hin) (gamePriority_hVertex n i (by omega) hin)
  exact valueLT_of_reachMax_even hd_a hh_a
    (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (i + 1)))
    (by omega) (by omega) (by omega)

lemma valueLT_d_false_e_false_of_cmax_eq_bmax {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i : ℕ} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hdi : π .d i = false) (hei : π .e i = false)
    (hci : c_max < i) (hbc : b_max = c_max) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .d i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .e i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hvp_d : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hvp_e : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hd_g := reachMax_d_to_g_bEff hn hV τ hi2 hin hdi
  have hbe : bEff b_max i = c_max := by unfold bEff; rw [if_pos (by omega), hbc]
  rw [hbe, ← decisionVertex_eq_rowVertex hvp_d] at hd_g
  have hstep_e : step (parityGame n) σ τ (decisionVertex n .e i) = sVertex n := by
    rw [decisionVertex_eq_rowVertex hvp_e, step_rowVertex hn π τ hvp_e, hei]; rfl
  have hp_e : gamePriority n (decisionVertex n .e i) = 5 := by
    rw [decisionVertex_eq_rowVertex hvp_e, gamePriority_rowVertex hn hvp_e]
  have he_g : ReachMax n σ τ (decisionVertex n .e i) (gVertex n c_max) 8 :=
    ReachMax.step_eq hstep_e (reachMax_s_to_g_cmax hn hV hτ) (by rw [hp_e]; omega)
  exact valueLT_of_reachMax_even hd_g he_g
    (cyclePriority_eq_one_of_valid hn hV (gVertex n c_max))
    (by omega) (by omega) (by omega)

lemma valueLT_e_false_d_false_of_not_cmax_eq_bmax {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i : ℕ} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hdi : π .d i = false) (hei : π .e i = false)
    (hnot : ¬ (c_max < i ∧ b_max = c_max)) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .e i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .d i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hc := hV.hc_range
  have hb := hV.hb_range
  have hvp_d : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hvp_e : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hstep_e : step (parityGame n) σ τ (decisionVertex n .e i) = sVertex n := by
    rw [decisionVertex_eq_rowVertex hvp_e, step_rowVertex hn π τ hvp_e, hei]; rfl
  have hp_e : gamePriority n (decisionVertex n .e i) = 5 := by
    rw [decisionVertex_eq_rowVertex hvp_e, gamePriority_rowVertex hn hvp_e]
  have hd_g := reachMax_d_to_g_bEff hn hV τ hi2 hin hdi
  rw [← decisionVertex_eq_rowVertex hvp_d] at hd_g
  rcases hV.hd_he_false i hi2 hin hdi hei hnot with
    ⟨hcb, hbi, hab_f⟩ | ⟨hb_le, hc2, he1_t, hac_t, haf⟩
  · have hbe : bEff b_max i = b_max := by unfold bEff; rw [if_pos hbi]
    rw [hbe] at hd_g
    have hbed := hV.hb_ed (by omega)
    have hg_ab := reachMax_g_f_h_of_ed (n := n) c_max b_max b_max hb.1 (by omega) hbed.1 (fun _ => hbed.2)
    have hd_ab : ReachMax n σ τ (decisionVertex n .d i) (decisionVertex n .a (b_max + 1)) (2 * b_max + 8) :=
      hd_g.trans_eq hg_ab (by omega)
    have he_ac : ReachMax n σ τ (decisionVertex n .e i) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
      ReachMax.step_eq hstep_e (reachMax_s_to_a_cmax hn hV) (by rw [hp_e]; omega)
    rcases reachMax_a_ladder_general hn hV (b_max - (c_max + 1)) (c_max + 1) b_max rfl
      (by omega) (by omega) (by omega) (Or.inl hcb) with ⟨ma, hma, hac_ab⟩
    have hvp_ab : ValidRow n (.a, b_max) := ⟨by omega, by omega⟩
    have hstep_ab : step (parityGame n) σ τ (decisionVertex n .a b_max) = decisionVertex n .a (b_max + 1) := by
      rw [decisionVertex_eq_rowVertex hvp_ab, step_rowVertex hn π τ hvp_ab, hab_f]; rfl
    have hp_ab : gamePriority n (decisionVertex n .a b_max) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp_ab, gamePriority_rowVertex hn hvp_ab]
    have hab_step : ReachMax n σ τ (decisionVertex n .a b_max) (decisionVertex n .a (b_max + 1)) 3 :=
      ReachMax.one_step hstep_ab hp_ab
    have he_ab : ReachMax n σ τ (decisionVertex n .e i) (decisionVertex n .a (b_max + 1))
        (max (2 * c_max + 8) ma) :=
      (he_ac.trans hac_ab).trans_eq hab_step (by omega)
    have hlt : max (2 * c_max + 8) ma < 2 * b_max + 8 := by
      rcases hma with hle3 | ⟨_, _, hle⟩ <;> omega
    exact valueLT_of_reachMax_even he_ab hd_ab
      (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (b_max + 1)))
      hlt (by omega) (by omega)
  · have hbe1 : bEff b_max i = 1 := by unfold bEff; split_ifs <;> omega
    rw [hbe1] at hd_g
    have hg1_a2 := reachMax_g_f_h_of_ed (n := n) c_max b_max 1 le_rfl (by omega) he1_t (fun h => by omega)
    have hd_a2 : ReachMax n σ τ (decisionVertex n .d i) (decisionVertex n .a 2) 10 :=
      hd_g.trans_eq hg1_a2 (by omega)
    have ha2_ac := reachMax_a_ladder_all_false hn τ (c_max - 2) 2 c_max rfl
      le_rfl hc2 (by omega) haf
    have hvp_ac : ValidRow n (.a, c_max) := ⟨hc2, hc.2⟩
    have hstep_ac : step (parityGame n) σ τ (decisionVertex n .a c_max) = gVertex n c_max := by
      rw [decisionVertex_eq_rowVertex hvp_ac, step_rowVertex hn π τ hvp_ac, hac_t]; rfl
    have hp_ac : gamePriority n (decisionVertex n .a c_max) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp_ac, gamePriority_rowVertex hn hvp_ac]
    have hac_g : ReachMax n σ τ (decisionVertex n .a c_max) (gVertex n c_max) 3 :=
      ReachMax.one_step hstep_ac hp_ac
    have hd_ac : ReachMax n σ τ (decisionVertex n .d i) (decisionVertex n .a c_max) 10 :=
      hd_a2.trans_eq ha2_ac (by split_ifs <;> omega)
    have hd_gc : ReachMax n σ τ (decisionVertex n .d i) (gVertex n c_max) 10 :=
      hd_ac.trans_eq hac_g (by omega)
    have he_gc : ReachMax n σ τ (decisionVertex n .e i) (gVertex n c_max) 8 :=
      ReachMax.step_eq hstep_e (reachMax_s_to_g_cmax hn hV hτ) (by rw [hp_e]; omega)
    exact valueLT_of_reachMax_even he_gc hd_gc
      (cyclePriority_eq_one_of_valid hn hV (gVertex n c_max))
      (by omega) (by omega) (by omega)

lemma reachMax_a_to_s_of_exists_true {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hc : c_max ≤ n) (hac_t : π .a c_max = true) :
    ∀ d k, c_max - k = d → 2 ≤ k → k < c_max →
      (∀ r, k ≤ r → r < c_max → π .a r = true → π .e r = false ∧ π .d r = true) →
      (¬ ∀ r ∈ Finset.Ico k c_max, π .a r = false) →
      ∃ ms, 2 * k + 7 ≤ ms ∧ ms % 2 = 1 ∧
        ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max)
          (decisionVertex n .a k) (sVertex n) ms
  | 0, k, hd, _, hkc, _, _ => by omega
  | d + 1, k, hd, hk2, hkc, hinv, hnot_all => by
    set σ := policyStrategy n π
    set τ := phaseTau n π c_max b_max
    have hτ := phaseTau_legal n π c_max b_max
    have hkn : k ≤ n := by omega
    have hvp_ak : ValidRow n (.a, k) := ⟨hk2, hkn⟩
    have hp_ak : gamePriority n (decisionVertex n .a k) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp_ak, gamePriority_rowVertex hn hvp_ak]
    by_cases hak : π .a k = false
    · have hnot_all' : ¬ ∀ r ∈ Finset.Ico (k + 1) c_max, π .a r = false := by
        intro hall
        apply hnot_all
        intro r hr
        rw [Finset.mem_Ico] at hr
        by_cases hrk : r = k
        · subst hrk; exact hak
        · exact hall r (Finset.mem_Ico.mpr ⟨by omega, hr.2⟩)
      have hkc' : k + 1 < c_max := by
        by_contra hge
        apply hnot_all'
        intro r hr
        rw [Finset.mem_Ico] at hr
        omega
      rcases reachMax_a_to_s_of_exists_true hn hc hac_t d (k + 1) (by omega) (by omega) hkc'
        (fun r hr1 hr2 => hinv r (by omega) hr2) hnot_all' with ⟨ms, hge, hodd, hreach⟩
      have hstep : step (parityGame n) σ τ (decisionVertex n .a k) = decisionVertex n .a (k + 1) := by
        rw [decisionVertex_eq_rowVertex hvp_ak, step_rowVertex hn π τ hvp_ak, hak]; rfl
      refine ⟨ms, by omega, hodd, ReachMax.step_eq hstep hreach (by rw [hp_ak]; omega)⟩
    · have hak_t : π .a k = true := by cases h : π .a k <;> [exact False.elim (hak h); rfl]
      have ⟨hek_f, hdk_t⟩ := hinv k le_rfl hkc hak_t
      have hstep_ak : step (parityGame n) σ τ (decisionVertex n .a k) = gVertex n k := by
        rw [decisionVertex_eq_rowVertex hvp_ak, step_rowVertex hn π τ hvp_ak, hak_t]; rfl
      have hstep_gk : step (parityGame n) σ τ (gVertex n k) = fVertex n k :=
        step_gVertex hτ (by omega) hkn
      by_cases hall : ∀ r ∈ Finset.Ico (k + 1) c_max, π .a r = false
      · have hft : fTarget n π c_max b_max k = decisionVertex n .e k := by
          unfold fTarget
          rw [if_neg (by simp [hek_f]), if_neg (by simp [hdk_t]), if_neg (by simp [hdk_t]),
              if_neg (by omega), if_pos ⟨hkc, hac_t, hall⟩]
        have hvp_ek : ValidRow n (.e, k) := ⟨by omega, hkn⟩
        have hstep_fk : step (parityGame n) σ τ (fVertex n k) = rowVertex n (.e, k) := by
          rw [step_fVertex_phaseTau σ π c_max b_max k (by omega) hkn,
              hft, decisionVertex_eq_rowVertex hvp_ek]
        have hstep_ek : step (parityGame n) σ τ (rowVertex n (.e, k)) = sVertex n := by
          rw [step_rowVertex hn π τ hvp_ek, hek_f]; rfl
        have h1 : ReachMax n σ τ (rowVertex n (.e, k)) (sVertex n) 5 :=
          ReachMax.one_step hstep_ek (gamePriority_rowVertex hn hvp_ek)
        have h2 : ReachMax n σ τ (fVertex n k) (sVertex n) 6 :=
          ReachMax.step_eq hstep_fk h1 (by rw [gamePriority_fVertex n k (by omega) hkn]; omega)
        have h3 : ReachMax n σ τ (gVertex n k) (sVertex n) (2 * k + 7) :=
          ReachMax.step_eq hstep_gk h2 (by rw [gamePriority_gVertex n k (by omega) hkn]; omega)
        have h4 : ReachMax n σ τ (decisionVertex n .a k) (sVertex n) (2 * k + 7) :=
          ReachMax.step_eq hstep_ak h3 (by rw [hp_ak]; omega)
        exact ⟨2 * k + 7, le_rfl, by omega, h4⟩
      · have hft : fTarget n π c_max b_max k = hVertex n k := by
          unfold fTarget
          rw [if_neg (by simp [hek_f]), if_neg (by simp [hdk_t]), if_neg (by simp [hdk_t]),
              if_neg (by omega), if_neg (fun h => hall h.2.2)]
        have hstep_fk : step (parityGame n) σ τ (fVertex n k) = hVertex n k := by
          rw [step_fVertex_phaseTau σ π c_max b_max k (by omega) hkn, hft]
        have hstep_hk : step (parityGame n) σ τ (hVertex n k) = decisionVertex n .a (k + 1) :=
          step_hVertex hτ (by omega) hkn
        have h1 : ReachMax n σ τ (hVertex n k) (decisionVertex n .a (k + 1)) (2 * k + 8) :=
          ReachMax.one_step hstep_hk (gamePriority_hVertex n k (by omega) hkn)
        have h2 : ReachMax n σ τ (fVertex n k) (decisionVertex n .a (k + 1)) (2 * k + 8) :=
          ReachMax.step_eq hstep_fk h1 (by rw [gamePriority_fVertex n k (by omega) hkn]; omega)
        have h3 : ReachMax n σ τ (gVertex n k) (decisionVertex n .a (k + 1)) (2 * k + 8) :=
          ReachMax.step_eq hstep_gk h2 (by rw [gamePriority_gVertex n k (by omega) hkn]; omega)
        have h4 : ReachMax n σ τ (decisionVertex n .a k) (decisionVertex n .a (k + 1)) (2 * k + 8) :=
          ReachMax.step_eq hstep_ak h3 (by rw [hp_ak]; omega)
        have hkc' : k + 1 < c_max := by
          by_contra hge
          apply hall
          intro r hr
          rw [Finset.mem_Ico] at hr
          omega
        rcases reachMax_a_to_s_of_exists_true hn hc hac_t d (k + 1) (by omega) (by omega) hkc'
          (fun r hr1 hr2 => hinv r (by omega) hr2) hall with ⟨ms, hge, hodd, hreach⟩
        exact ⟨ms, by omega, hodd, h4.trans_eq hreach (by omega)⟩

lemma valueLT_e_false_or_hVertex {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hd : i = 1 ∨ π .d i = true) (hei : π .e i = false) :
    if c_max < i then
      ValueLT (parityGame n)
        (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
          (decisionVertex n .e i))
        (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
          (hVertex n i))
    else if i < c_max ∧ π .a c_max = true ∧
        ∀ k ∈ Finset.Ico (i + 1) c_max, π .a k = false then
      ValueLT (parityGame n)
        (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
          (decisionVertex n .e i))
        (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
          (hVertex n i))
    else
      ValueLT (parityGame n)
        (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
          (hVertex n i))
        (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
          (decisionVertex n .e i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hc := hV.hc_range
  have hvp_e : ValidRow n (.e, i) := ⟨hi1, hin⟩
  have hstep_e : step (parityGame n) σ τ (decisionVertex n .e i) = sVertex n := by
    rw [decisionVertex_eq_rowVertex hvp_e, step_rowVertex hn π τ hvp_e, hei]; rfl
  have hp_e : gamePriority n (decisionVertex n .e i) = 5 := by
    rw [decisionVertex_eq_rowVertex hvp_e, gamePriority_rowVertex hn hvp_e]
  have hh_ai1 : ReachMax n σ τ (hVertex n i) (decisionVertex n .a (i + 1)) (2 * i + 8) :=
    ReachMax.one_step (step_hVertex hτ hi1 hin) (gamePriority_hVertex n i hi1 hin)
  split_ifs with hci hcond
  · have hi2 : 2 ≤ i := by omega
    have hai : π .a i = false := by
      cases h : π .a i
      · rfl
      · have := hV.ha_e i hi2 hin h (by omega); rw [hei] at this; cases this
    have he_ac : ReachMax n σ τ (decisionVertex n .e i) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
      ReachMax.step_eq hstep_e (reachMax_s_to_a_cmax hn hV) (by rw [hp_e]; omega)
    rcases reachMax_a_ladder_general hn hV (i - (c_max + 1)) (c_max + 1) i rfl
      (by omega) (by omega) (by omega) (Or.inl hci) with ⟨ma, hma, hac_ai⟩
    have hvp_ai : ValidRow n (.a, i) := ⟨hi2, hin⟩
    have hstep_ai : step (parityGame n) σ τ (decisionVertex n .a i) = decisionVertex n .a (i + 1) := by
      rw [decisionVertex_eq_rowVertex hvp_ai, step_rowVertex hn π τ hvp_ai, hai]; rfl
    have hp_ai : gamePriority n (decisionVertex n .a i) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp_ai, gamePriority_rowVertex hn hvp_ai]
    have hai_step : ReachMax n σ τ (decisionVertex n .a i) (decisionVertex n .a (i + 1)) 3 :=
      ReachMax.one_step hstep_ai hp_ai
    have he_ai1 : ReachMax n σ τ (decisionVertex n .e i) (decisionVertex n .a (i + 1))
        (max (2 * c_max + 8) ma) :=
      (he_ac.trans hac_ai).trans_eq hai_step (by omega)
    have hlt : max (2 * c_max + 8) ma < 2 * i + 8 := by
      rcases hma with hle3 | ⟨_, _, hle⟩ <;> omega
    exact valueLT_of_reachMax_even he_ai1 hh_ai1
      (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (i + 1)))
      hlt (by omega) (by omega)
  · rcases hcond with ⟨hic, hac_t, hall⟩
    have hc2 : 2 ≤ c_max := by omega
    have he_gc : ReachMax n σ τ (decisionVertex n .e i) (gVertex n c_max) 8 :=
      ReachMax.step_eq hstep_e (reachMax_s_to_g_cmax hn hV hτ) (by rw [hp_e]; omega)
    have hai1_ac := reachMax_a_ladder_all_false hn τ (c_max - (i + 1)) (i + 1) c_max rfl
      (by omega) (by omega) (by omega)
      (fun r hr1 hr2 => hall r (Finset.mem_Ico.mpr ⟨hr1, hr2⟩))
    have hvp_ac : ValidRow n (.a, c_max) := ⟨hc2, hc.2⟩
    have hstep_ac : step (parityGame n) σ τ (decisionVertex n .a c_max) = gVertex n c_max := by
      rw [decisionVertex_eq_rowVertex hvp_ac, step_rowVertex hn π τ hvp_ac, hac_t]; rfl
    have hp_ac : gamePriority n (decisionVertex n .a c_max) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp_ac, gamePriority_rowVertex hn hvp_ac]
    have hac_gc : ReachMax n σ τ (decisionVertex n .a c_max) (gVertex n c_max) 3 :=
      ReachMax.one_step hstep_ac hp_ac
    have hh_ac : ReachMax n σ τ (hVertex n i) (decisionVertex n .a c_max) (2 * i + 8) :=
      hh_ai1.trans_eq hai1_ac (by split_ifs <;> omega)
    have hh_gc : ReachMax n σ τ (hVertex n i) (gVertex n c_max) (2 * i + 8) :=
      hh_ac.trans_eq hac_gc (by omega)
    exact valueLT_of_reachMax_even he_gc hh_gc
      (cyclePriority_eq_one_of_valid hn hV (gVertex n c_max))
      (by omega) (by omega) (by omega)
  · have hic : i < c_max := by
      by_contra hge
      have h_eq : i = c_max := by omega
      have := hV.hc_e
      rw [← h_eq, hei] at this; cases this
    have hc2 : 2 ≤ c_max := by omega
    by_cases hac_f : π .a c_max = false
    · rcases reachMax_a_ladder_general hn hV (c_max - (i + 1)) (i + 1) c_max rfl
        (by omega) (by omega) (by omega) (Or.inr (Or.inl hac_f)) with ⟨ma, hma, hai1_ac⟩
      have hvp_ac : ValidRow n (.a, c_max) := ⟨hc2, hc.2⟩
      have hstep_ac : step (parityGame n) σ τ (decisionVertex n .a c_max) = decisionVertex n .a (c_max + 1) := by
        rw [decisionVertex_eq_rowVertex hvp_ac, step_rowVertex hn π τ hvp_ac, hac_f]; rfl
      have hp_ac : gamePriority n (decisionVertex n .a c_max) = 3 := by
        rw [decisionVertex_eq_rowVertex hvp_ac, gamePriority_rowVertex hn hvp_ac]
      have hac_step : ReachMax n σ τ (decisionVertex n .a c_max) (decisionVertex n .a (c_max + 1)) 3 :=
        ReachMax.one_step hstep_ac hp_ac
      have hh_ac1 : ReachMax n σ τ (hVertex n i) (decisionVertex n .a (c_max + 1))
          (max (2 * i + 8) ma) :=
        (hh_ai1.trans hai1_ac).trans_eq hac_step (by omega)
      have he_ac1 : ReachMax n σ τ (decisionVertex n .e i) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
        ReachMax.step_eq hstep_e (reachMax_s_to_a_cmax hn hV) (by rw [hp_e]; omega)
      have hlt : max (2 * i + 8) ma < 2 * c_max + 8 := by
        rcases hma with hle3 | ⟨_, _, hle⟩ <;> omega
      exact valueLT_of_reachMax_even hh_ac1 he_ac1
        (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (c_max + 1)))
        hlt (by omega) (by omega)
    · have hac_t : π .a c_max = true := by cases h : π .a c_max <;> [exact False.elim (hac_f h); rfl]
      have hnot_all : ¬ ∀ k ∈ Finset.Ico (i + 1) c_max, π .a k = false :=
        fun hall => hcond ⟨hic, hac_t, hall⟩
      have hic' : i + 1 < c_max := by
        by_contra hge
        apply hnot_all
        intro k hk
        rw [Finset.mem_Ico] at hk
        omega
      have hinv := hV.he_false_lt_cmax i hi1 hic hd hei hac_t
      rcases reachMax_a_to_s_of_exists_true hn hc.2 hac_t (c_max - (i + 1)) (i + 1) rfl
        (by omega) hic' (fun r hr1 hr2 => hinv r (by omega) hr2) hnot_all with ⟨ms_h, hge, hodd, hai1_s⟩
      have hh_s : ReachMax n σ τ (hVertex n i) (sVertex n) ms_h :=
        hh_ai1.trans_eq hai1_s (by omega)
      have he_s : ReachMax n σ τ (decisionVertex n .e i) (sVertex n) 5 :=
        ReachMax.one_step hstep_e hp_e
      exact valueLT_of_reachMax_odd hh_s he_s
        (cyclePriority_eq_one_of_valid hn hV (sVertex n))
        (by omega) (by omega) hodd

lemma bellman_fVertex_of_valid {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max)
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {w : Fin (vertices n)} (hw : w ∈ gameSuccessors n (fVertex n i)) :
    ((parityGame n).owner w = false ∧
      gamePriority n w = 5 ∧
      gamePriority n (fVertex n i) = 6 ∧
      policyStrategy n π w = fVertex n i) ∨
    ValueLE (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (phaseTau n π c_max b_max (fVertex n i)))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max) w) := by
  rw [phaseTau_fVertex n π c_max b_max i hi1 hin]
  have hd_cycle : 2 ≤ i → π .d i = true →
      (parityGame n).owner (decisionVertex n .d i) = false ∧
      gamePriority n (decisionVertex n .d i) = 5 ∧
      gamePriority n (fVertex n i) = 6 ∧
      policyStrategy n π (decisionVertex n .d i) = fVertex n i := by
    intro hi2 hdi
    have hvp : ValidRow n (.d, i) := ⟨hi2, hin⟩
    rw [decisionVertex_eq_rowVertex hvp]
    refine ⟨owner_rowVertex hn hvp, gamePriority_rowVertex hn hvp, gamePriority_fVertex n i hi1 hin, ?_⟩
    rw [policyStrategy_rowVertex hn π hvp, hdi]; rfl
  have he_cycle : π .e i = true →
      (parityGame n).owner (decisionVertex n .e i) = false ∧
      gamePriority n (decisionVertex n .e i) = 5 ∧
      gamePriority n (fVertex n i) = 6 ∧
      policyStrategy n π (decisionVertex n .e i) = fVertex n i := by
    intro hei
    have hvp : ValidRow n (.e, i) := ⟨hi1, hin⟩
    rw [decisionVertex_eq_rowVertex hvp]
    refine ⟨owner_rowVertex hn hvp, gamePriority_rowVertex hn hvp, gamePriority_fVertex n i hi1 hin, ?_⟩
    rw [policyStrategy_rowVertex hn π hvp, hei]; rfl
  have hw_cases : w = hVertex n i ∨ (2 ≤ i ∧ w = decisionVertex n .d i) ∨ w = decisionVertex n .e i := by
    rw [gameSuccessors_fVertex n i hi1 hin] at hw
    by_cases hi_eq_1 : i = 1
    · subst hi_eq_1
      rw [if_pos rfl] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · left; rfl
      · right; right; rfl
    · rw [if_neg hi_eq_1] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · left; rfl
      · right; left; exact ⟨by omega, rfl⟩
      · right; right; rfl
  have hd_not : ¬ ((i = 1 ∨ π .d i = true) ∧ π .e i = true) →
      ¬ (1 < i ∧ π .d i = false ∧ π .e i = true) →
      ¬ (1 < i ∧ π .d i = false ∧ π .e i = false) →
      (i = 1 ∨ π .d i = true) ∧ π .e i = false := by
    intro h1 h2 h3
    have hd : i = 1 ∨ π .d i = true := by
      by_cases hi_eq_1 : i = 1
      · exact Or.inl hi_eq_1
      · right
        cases h : π .d i
        · exfalso
          cases he : π .e i
          · exact h3 ⟨by omega, h, he⟩
          · exact h2 ⟨by omega, h, he⟩
        · rfl
    have hei : π .e i = false := by
      cases he : π .e i
      · rfl
      · exact False.elim (h1 ⟨hd, he⟩)
    exact ⟨hd, hei⟩
  unfold fTarget
  split_ifs with h1 h2 h3 h4 h5 h6
  · rcases hw_cases with rfl | ⟨hi2, rfl⟩ | rfl
    · right; exact valueLE_refl (parityGame n) _
    · left
      rcases h1.1 with rfl | hdi
      · omega
      · exact hd_cycle hi2 hdi
    · left; exact he_cycle h1.2
  · rcases hw_cases with rfl | ⟨_, rfl⟩ | rfl
    · right; exact valueLT_asymm (valueLT_d_false_hVertex hn hV (by omega) hin h2.2.1)
    · right; exact valueLE_refl (parityGame n) _
    · left; exact he_cycle h2.2.2
  · have hde := valueLT_d_false_e_false_of_cmax_eq_bmax hn hV (by omega) hin h3.2.1 h3.2.2 h4.1 h4.2
    have hdh := valueLT_d_false_hVertex hn hV (by omega) hin h3.2.1
    rcases hw_cases with rfl | ⟨_, rfl⟩ | rfl
    · right; exact valueLT_asymm hdh
    · right; exact valueLE_refl (parityGame n) _
    · right; exact valueLT_asymm hde
  · have hed := valueLT_e_false_d_false_of_not_cmax_eq_bmax hn hV (by omega) hin h3.2.1 h3.2.2 h4
    have hdh := valueLT_d_false_hVertex hn hV (by omega) hin h3.2.1
    rcases hw_cases with rfl | ⟨_, rfl⟩ | rfl
    · right; exact valueLT_asymm (valueLT_trans hed hdh)
    · right; exact valueLT_asymm hed
    · right; exact valueLE_refl (parityGame n) _
  · have ⟨hd, hei⟩ := hd_not h1 h2 h3
    have hcmp := valueLT_e_false_or_hVertex hn hV hi1 hin hd hei
    rw [if_pos h5] at hcmp
    rcases hw_cases with rfl | ⟨hi2, rfl⟩ | rfl
    · right; exact valueLT_asymm hcmp
    · left
      rcases hd with rfl | hdi
      · omega
      · exact hd_cycle hi2 hdi
    · right; exact valueLE_refl (parityGame n) _
  · have ⟨hd, hei⟩ := hd_not h1 h2 h3
    have hcmp := valueLT_e_false_or_hVertex hn hV hi1 hin hd hei
    rw [if_neg h5, if_pos h6] at hcmp
    rcases hw_cases with rfl | ⟨hi2, rfl⟩ | rfl
    · right; exact valueLT_asymm hcmp
    · left
      rcases hd with rfl | hdi
      · omega
      · exact hd_cycle hi2 hdi
    · right; exact valueLE_refl (parityGame n) _
  · have ⟨hd, hei⟩ := hd_not h1 h2 h3
    have hcmp := valueLT_e_false_or_hVertex hn hV hi1 hin hd hei
    rw [if_neg h5, if_neg h6] at hcmp
    rcases hw_cases with rfl | ⟨hi2, rfl⟩ | rfl
    · right; exact valueLE_refl (parityGame n) _
    · left
      rcases hd with rfl | hdi
      · omega
      · exact hd_cycle hi2 hdi
    · right; exact valueLT_asymm hcmp

lemma bellman_all_of_valid {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max)
    (x : Fin (vertices n)) (hown : (parityGame n).owner x = true)
    (w : Fin (vertices n)) (hw : w ∈ gameSuccessors n x) :
    ((parityGame n).owner w = false ∧
      gamePriority n w = 5 ∧
      gamePriority n x = 6 ∧
      policyStrategy n π w = x) ∨
    ValueLE (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (phaseTau n π c_max b_max x))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max) w) := by
  have hown' : rows n ≤ x.val := by
    change decide (rows n ≤ x.val) = true at hown
    rwa [decide_eq_true_eq] at hown
  by_cases hxf : x.val < rows n + n
  · set i := x.val - rows n + 1
    have hx_eq : x = fVertex n i := by
      ext; rw [val_fVertex n i (by omega) (by omega)]; omega
    rw [hx_eq] at hw ⊢
    exact bellman_fVertex_of_valid hn hV (by omega) (by omega) hw
  · right
    have hτ := phaseTau_legal n π c_max b_max x hown
    change phaseTau n π c_max b_max x ∈ gameSuccessors n x at hτ
    have hnot : ¬ x.val < rows n := by omega
    unfold gameSuccessors at hw hτ
    rw [dif_neg hnot, if_neg hxf] at hw hτ
    have hw_eq : w = phaseTau n π c_max b_max x := by
      split_ifs at hw hτ <;>
        (rw [Finset.mem_singleton] at hw hτ; exact hw.trans hτ.symm)
    rw [hw_eq]
    exact valueLE_refl (parityGame n) _

theorem valEq_value_of_valid {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (v : Fin (vertices n)) :
    ValEq (parityGame n)
      (value (parityGame n) (policyStrategy n π) v)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max) v) :=
  valEq_value_playValue_of_bellman
    (policyStrategy_legal n π)
    (phaseTau_legal n π c_max b_max)
    (reachMax_sink_of_valid hn hV)
    (bellman_all_of_valid hn hV)
    (fun _ hτ' x => cyclePriority_one_or_six_of_valid hn hV hτ' x)
    v

lemma edge_rowVertex_actionTarget {n : ℕ} (hn : 3 ≤ n) {k : Kind} {i : ℕ}
    (hvp : ValidRow n (k, i)) (b : Bool) :
    (parityGame n).edge (rowVertex n (k, i)) (actionTarget n ⟨k, i, b⟩) := by
  change actionTarget n ⟨k, i, b⟩ ∈ gameSuccessors n (rowVertex n (k, i))
  unfold gameSuccessors
  rw [dif_pos (val_rowVertex_lt_rows hn hvp), rowName_rowVertex hn hvp]
  cases b <;> simp

lemma improving_row_iff {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) {k : Kind} {i : ℕ} (hvp : ValidRow n (k, i)) (b : Bool) :
    FriedmannMultiplicity.Improving (parityGame n) (policyStrategy n π)
      (rowVertex n (k, i)) (actionTarget n ⟨k, i, b⟩) ↔
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (actionTarget n ⟨k, i, π k i⟩))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (actionTarget n ⟨k, i, b⟩)) := by
  unfold FriedmannMultiplicity.Improving
  rw [policyStrategy_rowVertex hn π hvp]
  have hown := owner_rowVertex hn hvp
  have hedge := edge_rowVertex_actionTarget hn hvp b
  have hveq1 := valEq_value_of_valid hn hV (actionTarget n ⟨k, i, π k i⟩)
  have hveq2 := valEq_value_of_valid hn hV (actionTarget n ⟨k, i, b⟩)
  constructor
  · rintro ⟨_, _, hlt⟩
    exact valueLT_of_valueLT_of_valEq (valueLT_of_valEq_of_valueLT (valEq_symm hveq1) hlt) hveq2
  · intro hlt
    exact ⟨hown, hedge,
      valueLT_of_valueLT_of_valEq (valueLT_of_valEq_of_valueLT hveq1 hlt) (valEq_symm hveq2)⟩

lemma improving_row_iff_of_valueLT {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) {k : Kind} {i : ℕ} (hvp : ValidRow n (k, i))
    (opt b : Bool)
    (hlt : ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (actionTarget n ⟨k, i, !opt⟩))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (actionTarget n ⟨k, i, opt⟩))) :
    FriedmannMultiplicity.Improving (parityGame n) (policyStrategy n π)
      (rowVertex n (k, i)) (actionTarget n ⟨k, i, b⟩) ↔
    (π k i = !opt ∧ b = opt) := by
  rw [improving_row_iff hn hV hvp b]
  constructor
  · intro h
    cases hpi : π k i <;> cases hb : b <;> cases hopt : opt <;>
      (rw [hpi, hb] at h; rw [hopt] at hlt)
    · exact False.elim (valueLT_asymm h h)
    · exact False.elim (valueLT_asymm h h)
    · exact False.elim (valueLT_asymm hlt h)
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact False.elim (valueLT_asymm hlt h)
    · exact False.elim (valueLT_asymm h h)
    · exact False.elim (valueLT_asymm h h)
  · rintro ⟨hpi, hb⟩
    rwa [hpi, hb]

end PhaseOptimality

/-! ### Part 5a: Binary Counter, Cursor Policy, Validity, and Step/Wrap Transitions -/

section CursorPolicy

def bit (b i : ℕ) : Bool := b.testBit (i - 1)

def nuAux (n b : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => if bit b (n - (k + 1)) == !bit b 1 then n - (k + 1) else nuAux n b k

def nu (n b : ℕ) : ℕ := nuAux n b (n - 2)

lemma testBit_zero_eq (x : ℕ) : x.testBit 0 = decide (x % 2 = 1) := by
  rw [Nat.testBit_zero]

lemma exists_testBit_true_of_pos : ∀ (d x : ℕ), 0 < x → x < 2 ^ d → ∃ k < d, x.testBit k = true
  | 0, x, hx0, hxd => by simp at hxd; omega
  | d + 1, x, hx0, hxd => by
    by_cases hmod : x % 2 = 1
    · refine ⟨0, by omega, ?_⟩
      rw [Nat.testBit_zero, decide_eq_true_iff]
      exact hmod
    · have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      have hdiv_pos : 0 < x / 2 := by omega
      have hdiv_lt : x / 2 < 2 ^ d := by omega
      obtain ⟨k, hk, htb⟩ := exists_testBit_true_of_pos d (x / 2) hdiv_pos hdiv_lt
      refine ⟨k + 1, by omega, ?_⟩
      rw [Nat.testBit_succ]
      exact htb

lemma exists_testBit_false_of_lt : ∀ (d x : ℕ), x + 1 < 2 ^ d → ∃ k < d, x.testBit k = false
  | 0, x, hxd => by simp at hxd
  | d + 1, x, hxd => by
    by_cases hmod : x % 2 = 0
    · refine ⟨0, by omega, ?_⟩
      rw [Nat.testBit_zero, decide_eq_false_iff_not]
      omega
    · have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      have hdiv_lt : x / 2 + 1 < 2 ^ d := by omega
      obtain ⟨k, hk, htb⟩ := exists_testBit_false_of_lt d (x / 2) hdiv_lt
      refine ⟨k + 1, by omega, ?_⟩
      rw [Nat.testBit_succ]
      exact htb

lemma testBit_succ_Carry : ∀ (d x : ℕ),
    (∀ k < d, x.testBit k = true) → x.testBit d = false →
    (∀ k < d, (x + 1).testBit k = false) ∧
    (x + 1).testBit d = true ∧
    (∀ k > d, (x + 1).testBit k = x.testBit k)
  | 0, x, _, h0 => by
    rw [Nat.testBit_zero, decide_eq_false_iff_not] at h0
    have hmod : (x + 1) % 2 = 1 := by omega
    have hdiv : (x + 1) / 2 = x / 2 := by omega
    refine ⟨fun k hk => by omega, ?_, ?_⟩
    · rw [Nat.testBit_zero, decide_eq_true_iff]
      exact hmod
    · intro k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
  | d + 1, x, hlt, hd => by
    have h0 : x.testBit 0 = true := hlt 0 (by omega)
    rw [Nat.testBit_zero, decide_eq_true_iff] at h0
    have hmod : (x + 1) % 2 = 0 := by omega
    have hdiv : (x + 1) / 2 = x / 2 + 1 := by omega
    have hlt' : ∀ k < d, (x / 2).testBit k = true := by
      intro k hk
      have := hlt (k + 1) (by omega)
      rwa [Nat.testBit_succ] at this
    have hd' : (x / 2).testBit d = false := by
      rwa [Nat.testBit_succ] at hd
    obtain ⟨ih1, ih2, ih3⟩ := testBit_succ_Carry d (x / 2) hlt' hd'
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [Nat.testBit_zero, decide_eq_false_iff_not]
        omega
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Nat.testBit_succ, hdiv]
        exact ih1 k' (by omega)
    · rw [Nat.testBit_succ, hdiv]
      exact ih2
    · intro k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
      exact ih3 k' (by omega)

lemma nuAux_bounds (n b : ℕ) : ∀ k ≤ n - 2, n - k ≤ nuAux n b k ∧ nuAux n b k ≤ n
  | 0, _ => by unfold nuAux; omega
  | k + 1, hk => by
    unfold nuAux
    have ih := nuAux_bounds n b k (by omega)
    split_ifs <;> omega

lemma bit_lt_nuAux (n b : ℕ) : ∀ k ≤ n - 2, ∀ j, n - k ≤ j → j < nuAux n b k →
    bit b j = bit b 1
  | 0, _, j, hj1, hj2 => by unfold nuAux at hj2; omega
  | k + 1, hk, j, hj1, hj2 => by
    unfold nuAux at hj2
    split_ifs at hj2 with h
    · omega
    · simp only [beq_iff_eq] at h
      by_cases hjeq : j = n - (k + 1)
      · rw [hjeq]
        cases h1 : bit b 1 <;> cases hi : bit b (n - (k + 1)) <;> simp_all
      · exact bit_lt_nuAux n b k (by omega) j (by omega) hj2

lemma bit_nuAux (n b : ℕ) : ∀ k ≤ n - 2,
    (∃ j, n - k ≤ j ∧ j ≤ n ∧ bit b j = !bit b 1) →
    bit b (nuAux n b k) = !bit b 1
  | 0, _, ⟨j, hj1, hj2, hbit⟩ => by
    unfold nuAux
    have hjn : j = n := by omega
    rwa [← hjn]
  | k + 1, hk, ⟨j, hj1, hj2, hbit⟩ => by
    unfold nuAux
    split_ifs with h
    · exact of_decide_eq_true h
    · simp only [beq_iff_eq] at h
      have hjne : j ≠ n - (k + 1) := by
        intro heq
        rw [← heq] at h
        exact h hbit
      exact bit_nuAux n b k (by omega) ⟨j, by omega, hj2, hbit⟩

lemma nu_range {n b : ℕ} (hn : 3 ≤ n) : 2 ≤ nu n b ∧ nu n b ≤ n := by
  unfold nu
  have h := nuAux_bounds n b (n - 2) (by omega)
  omega

lemma bit_lt_nu {n b : ℕ} (hn : 3 ≤ n) {j : ℕ} (hj2 : 2 ≤ j) (hjlt : j < nu n b) :
    bit b j = bit b 1 := by
  unfold nu at hjlt
  exact bit_lt_nuAux n b (n - 2) (by omega) j (by omega) hjlt

lemma bit_nu {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2) :
    bit b (nu n b) = !bit b 1 := by
  unfold nu
  apply bit_nuAux n b (n - 2) (by omega)
  cases h1 : bit b 1
  · have h0 : b.testBit 0 = false := h1
    obtain ⟨k, hk, htb⟩ := exists_testBit_true_of_pos n b (by omega) (by omega)
    have hk0 : k ≠ 0 := by
      intro rfl
      rw [h0] at htb
      cases htb
    refine ⟨k + 1, by omega, by omega, ?_⟩
    exact htb
  · have h0 : b.testBit 0 = true := h1
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    obtain ⟨k, hk, htb⟩ := exists_testBit_false_of_lt n b (by omega)
    have hk0 : k ≠ 0 := by
      intro rfl
      rw [h0] at htb
      cases htb
    refine ⟨k + 1, by omega, by omega, ?_⟩
    exact htb

lemma nu_eq_of_isMin {n b m : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (hm2 : 2 ≤ m) (_hmn : m ≤ n) (hbit : bit b m = !bit b 1)
    (hlt : ∀ j, 2 ≤ j → j < m → bit b j = bit b 1) :
    nu n b = m := by
  have hrng := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  rcases Nat.lt_trichotomy (nu n b) m with h1 | h2 | h3
  · have := hlt (nu n b) hrng.1 h1
    rw [this] at hnu
    cases hbit1 : bit b 1 <;> (rw [hbit1] at hnu; cases hnu)
  · exact h2
  · have := bit_lt_nu hn hm2 h3
    rw [this] at hbit
    cases hbit1 : bit b 1 <;> (rw [hbit1] at hbit; cases hbit)

lemma bit_succ_of_even {b : ℕ} (h1 : bit b 1 = false) :
    bit (b + 1) 1 = true ∧ ∀ i, 2 ≤ i → bit (b + 1) i = bit b i := by
  have h0 : b.testBit 0 = false := h1
  have hCarry := testBit_succ_Carry 0 b (fun k hk => by omega) h0
  refine ⟨hCarry.2.1, ?_⟩
  intro i hi2
  exact hCarry.2.2 (i - 1) (by omega)

lemma nu_succ_of_even {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 3)
    (h1 : bit b 1 = false) :
    2 ≤ nu n (b + 1) ∧ nu n (b + 1) ≤ n ∧ bit b (nu n (b + 1)) = false := by
  have hpow : 3 ≤ 2 ^ n := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have hrng := nu_range (b := b + 1) hn
  have hnu := bit_nu hn (by omega : 1 ≤ b + 1) (by omega : b + 1 ≤ 2 ^ n - 2)
  have hev := bit_succ_of_even h1
  rw [hev.1, hev.2 (nu n (b + 1)) hrng.1] at hnu
  exact ⟨hrng.1, hrng.2, hnu⟩

lemma bit_succ_of_odd {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (h1 : bit b 1 = true) :
    (∀ i, 1 ≤ i → i < nu n b → bit (b + 1) i = false) ∧
    bit (b + 1) (nu n b) = true ∧
    (∀ i, nu n b < i → bit (b + 1) i = bit b i) ∧
    nu n (b + 1) = nu n b := by
  have hrng := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  rw [h1] at hnu
  have hlt : ∀ k < nu n b - 1, b.testBit k = true := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact h1
    · have hbk := bit_lt_nu (n := n) (b := b) hn (j := k + 1) (by omega) (by omega)
      rw [h1] at hbk
      exact hbk
  have hd : b.testBit (nu n b - 1) = false := hnu
  obtain ⟨hC1, hC2, hC3⟩ := testBit_succ_Carry (nu n b - 1) b hlt hd
  have P1 : ∀ i, 1 ≤ i → i < nu n b → bit (b + 1) i = false := by
    intro i hi1 hilt
    exact hC1 (i - 1) (by omega)
  have P2 : bit (b + 1) (nu n b) = true := hC2
  have P3 : ∀ i, nu n b < i → bit (b + 1) i = bit b i := by
    intro i hilt
    exact hC3 (i - 1) (by omega)
  refine ⟨P1, P2, P3, ?_⟩
  have hb1_false : bit (b + 1) 1 = false := P1 1 (by omega) (by omega)
  have haux : ∀ k ≤ n - 2, n - k ≤ nu n b → nuAux n (b + 1) k = nu n b := by
    intro k
    induction k with
    | zero =>
      intro _ hle
      unfold nuAux
      omega
    | succ k ih =>
      intro hk hle
      unfold nuAux
      have hi_ge : 2 ≤ n - (k + 1) := by omega
      rcases Nat.lt_trichotomy (n - (k + 1)) (nu n b) with hlt_i | heq_i | hgt_i
      · rw [P1 (n - (k + 1)) (by omega) hlt_i, hb1_false]
        exact ih (by omega) (by omega)
      · rw [heq_i, P2, hb1_false]
        rfl
      · omega
  unfold nu
  exact haux (n - 2) (by omega) (by omega)

def cursorCMax (n b j : ℕ) : ℕ :=
  if bit b 1 then
    if 4 * n + 2 * nu n b - 8 < j then nu n b else 1
  else
    if 4 * n + 2 * nu n b - 9 < j then 1 else nu n b

def cursorBMax (n b j : ℕ) : ℕ :=
  if nu n b < n then
    if bit b 1 then
      if 4 * nu n b - 5 < j then nu n b else 1
    else
      if 4 * nu n b - 4 < j then 1 else nu n b
  else 1

def cursorBit (n b j : ℕ) (k : Kind) (i : ℕ) : Bool :=
  match k with
  | .a =>
    if bit b 1 then
      if i = nu n b then decide (8 * n - 8 + 2 * (n - nu n b) < j)
      else if i < nu n b then decide (j ≤ 8 * n - 8 + 2 * (n - i) + 1)
      else bit b i
    else bit b i
  | .b => decide (i = cursorBMax n b j)
  | .c => decide (i = cursorCMax n b j)
  | .d =>
    if !bit b i && (if bit b 1 then decide (nu n b < i) else true) then
      decide (j ≤ 4 * i - 7 || 7 * n + i - 9 < j)
    else true
  | .e =>
    if bit b 1 then
      if i < nu n b then decide (j ≤ 6 * n + i - 8)
      else if i = nu n b then decide (4 * nu n b - 6 < j)
      else if !bit b i then decide (4 * i - 6 < j && j ≤ 6 * n + i - 8)
      else true
    else
      if i = 1 then decide (0 < j)
      else if !bit b i then decide (4 * i - 6 < j && j ≤ 6 * n + i - 8)
      else true

def sweepSwitch (n b : ℕ) (v : Name) : Bool :=
  match v.kind, v.one with
  | .e, true =>
    if bit b 1 then decide (v.level = nu n b) || (decide (nu n b < v.level) && !bit b v.level)
    else decide (v.level = 1) || !bit b v.level
  | .b, true => if bit b 1 then decide (v.level = nu n b) else false
  | .b, false => if bit b 1 then false else decide (v.level = nu n b)
  | .d, false =>
    if bit b 1 then decide (nu n b < v.level) && !bit b v.level else !bit b v.level
  | .c, true => if bit b 1 then decide (v.level = nu n b) else false
  | .c, false => if bit b 1 then false else decide (v.level = nu n b)
  | .e, false =>
    if bit b 1 then decide (v.level < nu n b) || (decide (nu n b < v.level) && !bit b v.level)
    else decide (2 ≤ v.level) && !bit b v.level
  | .d, true =>
    if bit b 1 then decide (nu n b < v.level) && !bit b v.level else !bit b v.level
  | .a, true => if bit b 1 then decide (v.level = nu n b) else false
  | .a, false => if bit b 1 then decide (v.level < nu n b) else false

lemma cursorPolicy_hc_e {n b j : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2) :
    cursorBit n b j .e (cursorCMax n b j) = true := by
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  unfold cursorBit cursorCMax
  dsimp only
  cases h1 : bit b 1 <;>
    simp only [h1, Bool.false_eq_true, ite_true, ite_false] at hnu ⊢
  · by_cases hjc : 4 * n + 2 * nu n b - 9 < j
    · rw [if_pos hjc, if_pos rfl, decide_eq_true_iff]
      omega
    · rw [if_neg hjc, if_neg (by omega), if_neg (by simp [hnu])]
  · by_cases hjc : 4 * n + 2 * nu n b - 8 < j
    · rw [if_pos hjc, if_neg (by omega), if_pos rfl, decide_eq_true_iff]
      omega
    · rw [if_neg hjc, if_pos (by omega), decide_eq_true_iff]
      omega

lemma cursorPolicy_hc_d {n b j : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (hc2 : 2 ≤ cursorCMax n b j) :
    cursorBit n b j .d (cursorCMax n b j) = true := by
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  unfold cursorCMax at hc2 ⊢
  unfold cursorBit
  dsimp only
  cases h1 : bit b 1 <;>
    simp only [h1, Bool.false_eq_true, ite_true, ite_false] at hc2 hnu ⊢
  · by_cases hjc : 4 * n + 2 * nu n b - 9 < j
    · rw [if_pos hjc] at hc2; omega
    · rw [if_neg hjc, if_neg (by simp [hnu])]
  · by_cases hjc : 4 * n + 2 * nu n b - 8 < j
    · rw [if_pos hjc, if_neg (by simp)]
    · rw [if_neg hjc] at hc2; omega

lemma cursorPolicy_hb_ed {n b j : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (hb2' : 2 ≤ cursorBMax n b j) :
    cursorBit n b j .e (cursorBMax n b j) = true ∧
      cursorBit n b j .d (cursorBMax n b j) = true := by
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  unfold cursorBMax at hb2' ⊢
  by_cases hmn : nu n b < n
  · rw [if_pos hmn] at hb2' ⊢
    cases h1 : bit b 1 <;>
      simp only [h1, Bool.false_eq_true, ite_true, ite_false] at hb2' hnu ⊢
    · by_cases hjb : 4 * nu n b - 4 < j
      · rw [if_pos hjb] at hb2'; omega
      · rw [if_neg hjb]
        unfold cursorBit
        dsimp only
        simp only [h1, hnu, Bool.false_eq_true, ite_true, ite_false]
        rw [if_neg (by omega : nu n b ≠ 1)]
        simp
    · by_cases hjb : 4 * nu n b - 5 < j
      · rw [if_pos hjb]
        unfold cursorBit
        dsimp only
        simp only [h1, hnu, ite_true]
        simp; omega
      · rw [if_neg hjb] at hb2'; omega
  · rw [if_neg hmn] at hb2'; omega

lemma cursorPolicy_valid {n b j : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2) :
    ValidPhasePolicy n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j) := by
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  refine
    { hc_range := by
        unfold cursorCMax
        split_ifs <;> omega
      hc_iff := by
        intro i _ _
        unfold cursorBit; dsimp only
        exact decide_eq_true_iff
      hc_e := cursorPolicy_hc_e hn hb1 hb2
      hc_d := cursorPolicy_hc_d hn hb1 hb2
      hb_range := by
        unfold cursorBMax
        split_ifs <;> omega
      hb_iff := by
        intro i _ _
        unfold cursorBit; dsimp only
        exact decide_eq_true_iff
      hb_ed := cursorPolicy_hb_ed hn hb1 hb2
      ha_d := by
        intro i hi2 hin ha
        unfold cursorBit at ha ⊢
        dsimp only at ha ⊢
        cases h1 : bit b 1 <;>
          simp only [h1, Bool.false_eq_true, ite_true, ite_false] at ha ⊢
        · simp [ha]
        · split_ifs with hcond
          · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
            rw [if_neg (by omega), if_neg (by omega), hcond.1] at ha
            cases ha
          · rfl
      ha_e := by
        intro i hi2 hin ha hci
        unfold cursorBit at ha ⊢
        dsimp only at ha ⊢
        unfold cursorCMax at hci
        cases h1 : bit b 1 <;>
          simp only [h1, Bool.false_eq_true, ite_true, ite_false] at ha hci ⊢
        · simp [ha, show i ≠ 1 by omega]
        · rcases Nat.lt_trichotomy i (nu n b) with hilt | rfl | higt
          · rw [if_pos hilt, decide_eq_true_iff]
            split_ifs at hci <;> omega
          · rw [if_pos rfl, decide_eq_true_iff] at ha
            rw [if_neg (by omega), if_pos rfl, decide_eq_true_iff]
            omega
          · rw [if_neg (by omega), if_neg (by omega)] at ha ⊢
            simp [ha]
      hd_false := by
        intro i hi2 hin hd
        unfold cursorBit at hd
        dsimp only at hd
        unfold cursorCMax cursorBMax
        cases h1 : bit b 1 <;>
          simp only [h1, Bool.false_eq_true, ite_true, ite_false] at hd hnu ⊢
        · split_ifs at hd with hnotb
          · simp only [Bool.and_true, Bool.not_eq_true'] at hnotb
            simp only [decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, not_or] at hd
            have him : i ≠ nu n b := by
              intro rfl
              rw [hnotb] at hnu
              cases hnu
            rcases Nat.lt_or_gt_of_ne him with hilt | higt
            · by_cases hjc : 4 * n + 2 * nu n b - 9 < j
              · left; rw [if_pos hjc]; omega
              · right
                rw [if_neg hjc]
                refine ⟨hilt, ?_, ?_, ?_⟩
                · split_ifs <;> omega
                · unfold cursorBit; dsimp only
                  simp only [h1, Bool.false_eq_true, ite_true, ite_false, decide_eq_true_eq]
                  omega
                · intro k hk2 hkm
                  unfold cursorBit; dsimp only
                  simp only [h1, Bool.false_eq_true, ite_false]
                  have hbk := bit_lt_nu hn hk2 hkm
                  rwa [h1] at hbk
            · left; split_ifs <;> omega
        · split_ifs at hd with hcond
          · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
            simp only [decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, not_or] at hd
            left
            split_ifs <;> omega
      hd_he_false := by
        intro i hi2 hin hd he hnot_cb
        unfold cursorBit at hd he
        dsimp only at hd he
        unfold cursorCMax cursorBMax at hnot_cb ⊢
        cases h1 : bit b 1 <;>
          simp only [h1, Bool.false_eq_true, ite_true, ite_false] at hd he hnot_cb hnu ⊢
        · split_ifs at hd with hnotb
          · simp only [Bool.and_true, Bool.not_eq_true'] at hnotb
            simp only [decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, not_or] at hd
            rw [if_neg (by omega : i ≠ 1), if_pos (by simp [hnotb])] at he
            simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq, not_and] at he
            by_cases hj_eq : j = 4 * i - 6
            · right
              have hjc : ¬ (4 * n + 2 * nu n b - 9 < j) := by omega
              rw [if_neg hjc]
              have him : i ≠ nu n b := by
                intro rfl
                rw [hnotb] at hnu
                cases hnu
              refine ⟨?_, hm.1, ?_, ?_, ?_⟩
              · split_ifs <;> omega
              · unfold cursorBit; dsimp only
                simp only [h1, Bool.false_eq_true, ite_true, ite_false, decide_eq_true_eq]
                omega
              · unfold cursorBit; dsimp only
                simp only [h1, Bool.false_eq_true, ite_false]
                exact hnu
              · intro k hk2 hkm
                unfold cursorBit; dsimp only
                simp only [h1, Bool.false_eq_true, ite_false]
                have hbk := bit_lt_nu hn hk2 hkm
                rwa [h1] at hbk
            · exfalso
              apply hnot_cb
              split_ifs <;> omega
        · split_ifs at hd with hcond
          · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
            obtain ⟨hnotb, hmi⟩ := hcond
            simp only [decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, not_or] at hd
            rw [if_neg (by omega : ¬ i < nu n b), if_neg (by omega : i ≠ nu n b),
              if_pos (by simp [hnotb])] at he
            simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq, not_and] at he
            by_cases hj_eq : j = 4 * i - 6
            · left
              have hjc : ¬ (4 * n + 2 * nu n b - 8 < j) := by omega
              have hmn : nu n b < n := by omega
              have hjb : 4 * nu n b - 5 < j := by omega
              rw [if_neg hjc, if_pos hmn, if_pos hjb]
              refine ⟨by omega, hmi, ?_⟩
              unfold cursorBit; dsimp only
              simp only [h1, ite_true, decide_eq_false_iff_not]
              omega
            · exfalso
              apply hnot_cb
              split_ifs <;> omega
      he_false_lt_cmax := by
        intro i hi1 hic _ he hac k hik hkc hak
        unfold cursorCMax at hic hac hkc
        cases h1 : bit b 1 <;>
          simp only [h1, Bool.false_eq_true, ite_true, ite_false] at hic hac hkc
        · split_ifs at hic hkc with hjc
          · omega
          · unfold cursorBit at hak; dsimp only at hak
            simp only [h1, Bool.false_eq_true, ite_false] at hak
            have hbk := bit_lt_nu hn (by omega : 2 ≤ k) hkc
            rw [h1] at hbk
            rw [hbk] at hak
            cases hak
        · split_ifs at hic hac hkc with hjc
          · unfold cursorBit at hac hak ⊢; dsimp only at hac hak ⊢
            simp only [h1, ite_true, decide_eq_true_eq] at hac
            simp only [h1, ite_true]
            refine ⟨?_, ?_⟩
            · rw [if_pos hkc, decide_eq_false_iff_not]
              omega
            · split_ifs with hcond
              · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
                omega
              · rfl
          · omega }

lemma cols_pos {n : ℕ} (hn : 3 ≤ n) : 0 < cols n := by
  unfold cols; omega

lemma sub_one_lt_cols {n : ℕ} (hn : 3 ≤ n) : cols n - 1 < cols n := by
  unfold cols; omega

lemma columnName_eq_of_columnRank_eq {n : ℕ} (hn : 3 ≤ n) (j : Fin (cols n))
    {k : Kind} {i : ℕ} (hp : ValidRow n (k, i)) (one : Bool)
    (hrank : j.val = columnRank n ⟨k, i, one⟩) :
    columnName n j = ⟨k, i, one⟩ := by
  have hlt := columnRank_lt_cols hn (k, i) hp one
  have hj : j = ⟨columnRank n ⟨k, i, one⟩ % cols n, Nat.mod_lt _ (cols_pos hn)⟩ := by
    apply Fin.ext
    dsimp only
    rw [hrank, Nat.mod_eq_of_lt hlt]
  rw [hj]
  exact columnName_columnRank hn (k, i) hp one _

lemma val_ne_columnRank_of_ne {n : ℕ} (hn : 3 ≤ n) (j : Fin (cols n))
    {k : Kind} {i : ℕ} (hp : ValidRow n (k, i)) (one : Bool)
    (hne : (k, i) ≠ ((columnName n j).kind, (columnName n j).level)) :
    j.val ≠ columnRank n ⟨k, i, one⟩ := by
  intro hrank
  have heq := columnName_eq_of_columnRank_eq hn j hp one hrank
  apply hne
  rw [heq]

lemma cursorBit_step_other {n b : ℕ} (hn : 3 ≤ n) (j : Fin (cols n))
    {k : Kind} {i : ℕ} (hp : ValidRow n (k, i))
    (hne : (k, i) ≠ ((columnName n j).kind, (columnName n j).level)) :
    cursorBit n b (j.val + 1) k i = cursorBit n b j.val k i := by
  have hm := nu_range (b := b) hn
  have hneF := val_ne_columnRank_of_ne hn j hp false hne
  have hneT := val_ne_columnRank_of_ne hn j hp true hne
  cases k <;> unfold ValidRow at hp <;> unfold columnRank at hneF hneT <;>
    dsimp only at hp hneF hneT <;>
    unfold cursorBit cursorBMax cursorCMax <;> dsimp only
  · split_ifs <;> try rfl
    · congr 1; apply propext; omega
    · congr 1; apply propext; omega
  · congr 1; apply propext
    split_ifs <;> omega
  · congr 1; apply propext
    split_ifs <;> omega
  · split_ifs <;> try rfl
    all_goals
      congr 1; apply propext
      simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  · split_ifs with h1 h2 h3 h4 <;> try rfl
    · congr 1; apply propext; omega
    · rw [if_neg (by omega : ¬ i = 1)] at hneT
      congr 1; apply propext; omega
    · rw [if_neg (by omega : ¬ i = 1)] at hneT
      congr 1; apply propext
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    · rw [if_pos ‹i = 1›] at hneT
      congr 1; apply propext; omega
    · rw [if_neg ‹¬ i = 1›] at hneT
      congr 1; apply propext
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

lemma cursorBit_step_same {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (j : Fin (cols n)) :
    let v := columnName n j
    cursorBit n b (j.val + 1) v.kind v.level =
      (if sweepSwitch n b v then v.one else cursorBit n b j.val v.kind v.level) ∧
    (sweepSwitch n b v = true → cursorBit n b j.val v.kind v.level = !v.one) := by
  dsimp only
  set v := columnName n j
  have hv_valid : ValidRow n (v.kind, v.level) := columnName_valid hn j
  have hv_rank : j.val = columnRank n v := (columnRank_columnName hn j).symm
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  rcases v with ⟨k, i, one⟩
  dsimp only at hv_valid hv_rank ⊢
  rw [hv_rank]
  clear hv_rank j
  cases k <;> cases one <;>
    unfold ValidRow at hv_valid <;>
    unfold cursorBit cursorBMax cursorCMax sweepSwitch columnRank <;>
    dsimp only at hv_valid ⊢ <;>
    cases h1 : bit b 1 <;>
    simp only [Bool.false_eq_true, ite_true, ite_false]
  · -- .a, false, bit b 1 = false
    simp
  · -- .a, false, bit b 1 = true
    rcases Nat.lt_trichotomy i (nu n b) with hilt | rfl | higt
    · simp [hilt, show i ≠ nu n b by omega]
    · simp
    · simp [show i ≠ nu n b by omega, show ¬ i < nu n b by omega]
  · -- .a, true, bit b 1 = false
    simp
  · -- .a, true, bit b 1 = true
    rcases Nat.lt_trichotomy i (nu n b) with hilt | rfl | higt
    · simp [hilt, show i ≠ nu n b by omega]
    · simp
    · simp [show i ≠ nu n b by omega, show ¬ i < nu n b by omega]
  · -- .b, false, bit b 1 = false
    by_cases him : i = nu n b
    · subst him; simp; split_ifs <;> omega
    · simp [him]; split_ifs <;> omega
  · -- .b, false, bit b 1 = true
    simp; split_ifs <;> omega
  · -- .b, true, bit b 1 = false
    simp; split_ifs <;> omega
  · -- .b, true, bit b 1 = true
    by_cases him : i = nu n b
    · subst him; simp; split_ifs <;> omega
    · simp [him]; split_ifs <;> omega
  · -- .c, false, bit b 1 = false
    by_cases him : i = nu n b
    · subst him; simp; omega
    · simp [him]; split_ifs <;> omega
  · -- .c, false, bit b 1 = true
    simp; split_ifs <;> omega
  · -- .c, true, bit b 1 = false
    simp; split_ifs <;> omega
  · -- .c, true, bit b 1 = true
    by_cases him : i = nu n b
    · subst him; simp; omega
    · simp [him]; split_ifs <;> omega
  · -- .d, false, bit b 1 = false
    cases hbi : bit b i <;> (simp; try omega)
  · -- .d, false, bit b 1 = true
    cases hbi : bit b i <;> by_cases hmi : nu n b < i <;> (simp [hmi]; try omega)
  · -- .d, true, bit b 1 = false
    cases hbi : bit b i <;> (simp; try omega)
  · -- .d, true, bit b 1 = true
    cases hbi : bit b i <;> by_cases hmi : nu n b < i <;> (simp [hmi]; try omega)
  · -- .e, false, bit b 1 = false
    by_cases hi1 : i = 1
    · subst hi1; simp; omega
    · have hi2 : 2 ≤ i := by omega
      cases hbi : bit b i <;> (simp [hi1, hi2]; try omega)
  · -- .e, false, bit b 1 = true
    rcases Nat.lt_trichotomy i (nu n b) with hilt | rfl | higt
    · simp [hilt, show ¬ nu n b < i by omega]; omega
    · simp; omega
    · cases hbi : bit b i <;> (simp [higt, show i ≠ nu n b by omega, show ¬ i < nu n b by omega]; try omega)
  · -- .e, true, bit b 1 = false
    by_cases hi1 : i = 1
    · subst hi1; simp
    · cases hbi : bit b i <;> (simp [hi1]; try omega)
  · -- .e, true, bit b 1 = true
    by_cases hi1 : i = 1
    · subst hi1
      simp [show 1 < nu n b by omega, show 1 ≠ nu n b by omega, show ¬ nu n b < 1 by omega]; omega
    · rcases Nat.lt_trichotomy i (nu n b) with hilt | rfl | higt
      · simp [hi1, hilt, show i ≠ nu n b by omega, show ¬ nu n b < i by omega]; omega
      · simp [hi1]; omega
      · cases hbi : bit b i <;>
          (simp [hi1, higt, show i ≠ nu n b by omega, show ¬ i < nu n b by omega]; try omega)

lemma columnName_lastCol {n : ℕ} (hn : 3 ≤ n) :
    columnName n ⟨cols n - 1, sub_one_lt_cols hn⟩ = ⟨.a, 2, false⟩ := by
  apply columnName_eq_of_columnRank_eq hn _ (by dsimp [ValidRow]; omega) false
  dsimp [columnRank, cols]
  omega

lemma cursorBit_wrap {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 3) :
    let j_last : Fin (cols n) := ⟨cols n - 1, sub_one_lt_cols hn⟩
    let v := columnName n j_last
    (∀ k i, ValidRow n (k, i) → (k, i) ≠ (v.kind, v.level) →
      cursorBit n (b + 1) 0 k i = cursorBit n b (cols n - 1) k i) ∧
    cursorBit n (b + 1) 0 v.kind v.level =
      (if sweepSwitch n b v then v.one else cursorBit n b (cols n - 1) v.kind v.level) ∧
    (sweepSwitch n b v = true → cursorBit n b (cols n - 1) v.kind v.level = !v.one) := by
  have hpow : 3 ≤ 2 ^ n := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have hb2' : b ≤ 2 ^ n - 2 := by omega
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2'
  have hm_succ := nu_range (b := b + 1) hn
  have hnu_succ := bit_nu hn (by omega : 1 ≤ b + 1) (by omega : b + 1 ≤ 2 ^ n - 2)
  dsimp only
  rw [columnName_lastCol hn]
  dsimp only
  have hjl : cols n - 1 = 10 * n - 11 := by unfold cols; omega
  rw [hjl]
  refine ⟨?_, ?_, ?_⟩
  · intro k i hp hne
    cases h1 : bit b 1
    · have hev := bit_succ_of_even h1
      cases k <;> unfold ValidRow at hp <;>
        unfold cursorBit cursorBMax cursorCMax <;>
        dsimp only at hp ⊢ <;>
        simp only [h1, hev.1, Bool.false_eq_true, ite_true, ite_false]
      · -- .a
        have hi2 : 2 < i := by
          by_contra hle
          apply hne
          ext <;> [rfl; omega]
        rw [hev.2 i (by omega)]
        rcases Nat.lt_trichotomy i (nu n (b + 1)) with hilt | rfl | higt
        · have hbi := bit_lt_nu (b := b + 1) hn (by omega : 2 ≤ i) hilt
          rw [hev.1, hev.2 i (by omega)] at hbi
          rw [if_neg (by omega), if_pos hilt, hbi]
          simp
        · rw [hev.1, hev.2 (nu n (b + 1)) hm_succ.1] at hnu_succ
          rw [if_pos rfl, hnu_succ]
          simp
        · rw [if_neg (by omega), if_neg (by omega)]
      · -- .b
        congr 2
        split_ifs <;> omega
      · -- .c
        congr 2
        split_ifs <;> omega
      · -- .d
        rw [hev.2 i (by omega)]
        split_ifs <;> simp <;> omega
      · -- .e
        by_cases hi1 : i = 1
        · subst hi1
          rw [if_pos (by omega : 1 < nu n (b + 1))]
          simp; omega
        · have hi2 : 2 ≤ i := by omega
          rw [if_neg hi1]
          rcases Nat.lt_trichotomy i (nu n (b + 1)) with hilt | rfl | higt
          · have hbi := bit_lt_nu (b := b + 1) hn hi2 hilt
            rw [hev.1, hev.2 i hi2] at hbi
            rw [if_pos hilt, hbi]
            simp
          · rw [hev.1, hev.2 (nu n (b + 1)) hm_succ.1] at hnu_succ
            rw [if_neg (by omega), if_pos rfl, hnu_succ]
            simp; omega
          · rw [if_neg (by omega), if_neg (by omega), hev.2 i hi2]
            cases bit b i <;> (simp; try omega)
    · obtain ⟨hodd1, hodd2, hodd3, hodd_nu⟩ := bit_succ_of_odd hn hb1 hb2' h1
      have hb1_succ : bit (b + 1) 1 = false := hodd1 1 (by omega) hm.1
      cases k <;> unfold ValidRow at hp <;>
        unfold cursorBit cursorBMax cursorCMax <;>
        dsimp only at hp ⊢ <;>
        simp only [h1, hb1_succ, hodd_nu, Bool.false_eq_true, ite_true, ite_false]
      · -- .a
        have hi2 : 2 < i := by
          by_contra hle
          apply hne
          ext <;> [rfl; omega]
        rcases Nat.lt_trichotomy i (nu n b) with hilt | rfl | higt
        · rw [hodd1 i (by omega) hilt, if_neg (by omega), if_pos hilt]
          symm
          rw [decide_eq_false_iff_not]
          omega
        · rw [hodd2, if_pos rfl]
          symm
          rw [decide_eq_true_iff]
          omega
        · rw [hodd3 i higt, if_neg (by omega), if_neg (by omega)]
      · -- .b
        congr 2
        split_ifs <;> omega
      · -- .c
        congr 2
        split_ifs <;> omega
      · -- .d
        split_ifs <;> simp <;> omega
      · -- .e
        by_cases hi1 : i = 1
        · subst hi1
          rw [if_pos (by omega : 1 < nu n b)]
          simp; omega
        · rw [if_neg hi1]
          rcases Nat.lt_trichotomy i (nu n b) with hilt | rfl | higt
          · rw [hodd1 i (by omega) hilt, if_pos hilt]
            simp; omega
          · rw [hodd2]
            simp; omega
          · rw [hodd3 i higt]
            have hnot_lt : ¬ i < nu n b := by omega
            have hnot_eq : ¬ i = nu n b := by omega
            rw [if_neg hnot_lt, if_neg hnot_eq]
            cases bit b i <;> (simp; try omega)
  · unfold cursorBit sweepSwitch
    dsimp only
    cases h1 : bit b 1
    · have hev := bit_succ_of_even h1
      simp only [hev.1, Bool.false_eq_true, ite_true, ite_false]
      by_cases hm2 : 2 = nu n (b + 1)
      · rw [if_pos hm2]
        rw [hev.1, ← hm2, hev.2 2 (by omega)] at hnu_succ
        rw [hnu_succ]
        simp
      · have h2lt : 2 < nu n (b + 1) := by omega
        rw [if_neg hm2, if_pos h2lt]
        have hb2_eq := bit_lt_nu (b := b + 1) hn (by omega : 2 ≤ 2) h2lt
        rw [hev.1, hev.2 2 (by omega)] at hb2_eq
        rw [hb2_eq]
        simp
    · obtain ⟨hodd1, hodd2, _, _⟩ := bit_succ_of_odd hn hb1 hb2' h1
      have hb1_succ : bit (b + 1) 1 = false := hodd1 1 (by omega) hm.1
      simp only [hb1_succ, Bool.false_eq_true, ite_true, ite_false]
      by_cases hm2 : 2 = nu n b
      · rw [← hm2] at hodd2
        rw [hodd2, if_pos hm2]
        simp [← hm2]; omega
      · have h2lt : 2 < nu n b := by omega
        rw [hodd1 2 (by omega) h2lt, if_pos (by simp [h2lt])]
  · intro hsw
    unfold sweepSwitch at hsw
    unfold cursorBit
    dsimp only at hsw ⊢
    cases h1 : bit b 1
    · rw [h1] at hsw; cases hsw
    · simp only [h1, ite_true, decide_eq_true_eq] at hsw ⊢
      rw [if_neg (by omega), if_pos hsw]
      simp; omega

lemma policyStrategy_eq_of_validRow_eq {n : ℕ} (hn : 3 ≤ n) {π π' : Kind → ℕ → Bool}
    (h : ∀ k i, ValidRow n (k, i) → π' k i = π k i) :
    policyStrategy n π' = policyStrategy n π := by
  funext x
  unfold policyStrategy
  by_cases hx : x.val < rows n
  · rw [dif_pos hx, dif_pos hx]
    dsimp only
    set r := rowName n ⟨x.val, hx⟩
    have hvp : ValidRow n (r.1, r.2) := rowName_valid hn ⟨x.val, hx⟩
    rw [h r.1 r.2 hvp]
  · rw [dif_neg hx, dif_neg hx]

lemma policyStrategy_eq_update_of_validRow {n : ℕ} (hn : 3 ≤ n) {π π' : Kind → ℕ → Bool}
    (j : Fin (cols n))
    (h_other : ∀ k i, ValidRow n (k, i) →
      (k, i) ≠ ((columnName n j).kind, (columnName n j).level) → π' k i = π k i)
    (h_same : π' (columnName n j).kind (columnName n j).level = (columnName n j).one) :
    policyStrategy n π' =
      Function.update (policyStrategy n π) (actionSource n j) (actionTarget n (columnName n j)) := by
  funext x
  rw [actionSource_eq_rowVertex hn j]
  set v := columnName n j
  have hv_valid := columnName_valid hn j
  by_cases hx_eq : x = rowVertex n (v.kind, v.level)
  · subst hx_eq
    rw [Function.update_self, policyStrategy_rowVertex hn π' hv_valid, h_same]
  · rw [Function.update_of_ne hx_eq]
    unfold policyStrategy
    by_cases hx : x.val < rows n
    · rw [dif_pos hx, dif_pos hx]
      dsimp only
      set r := rowName n ⟨x.val, hx⟩
      have hr_valid : ValidRow n (r.1, r.2) := rowName_valid hn ⟨x.val, hx⟩
      have hne : (r.1, r.2) ≠ (v.kind, v.level) := by
        intro heq
        apply hx_eq
        rw [← heq]
        ext
        rw [val_rowVertex hn hr_valid, rowRank_rowName hn ⟨x.val, hx⟩]
      rw [h_other r.1 r.2 hr_valid hne]
    · rw [dif_neg hx, dif_neg hx]

end CursorPolicy

/-! ### Part 5b: Exact Single-Column Improvement Characterization and Terminal Non-Improvability -/

section CursorOptimality

lemma valueLT_a_true_of_ed {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (hi2 : 2 ≤ i) (hin : i ≤ n)
    (hdi : π .d i = true) (hei : π .e i = true) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .a (i + 1)))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (gVertex n i)) := by
  have hg := reachMax_g_f_h_of_ed (n := n) c_max b_max i (by omega) hin hei (fun _ => hdi)
  exact valueLT_of_reachMax_even (ReachMax.refl _) hg
    (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (i + 1)))
    (by omega) (by omega) (by omega)

lemma valueLT_a_false_of_cmax_lt {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (hi2 : 2 ≤ i) (hin : i ≤ n)
    (hdi : π .d i = true) (hei : π .e i = false) (hai : π .a i = false) (hci : c_max < i) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (gVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .a (i + 1))) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hc := hV.hc_range
  have hft : fTarget n π c_max b_max i = decisionVertex n .e i := by
    unfold fTarget
    rw [if_neg (by simp [hei]), if_neg (by simp [hdi]), if_neg (by simp [hdi]), if_pos hci]
  have hvp_e : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hstep_g : step (parityGame n) σ τ (gVertex n i) = fVertex n i :=
    step_gVertex hτ (by omega) hin
  have hstep_f : step (parityGame n) σ τ (fVertex n i) = rowVertex n (.e, i) := by
    rw [step_fVertex_phaseTau σ π c_max b_max i (by omega) hin, hft, decisionVertex_eq_rowVertex hvp_e]
  have hstep_e : step (parityGame n) σ τ (rowVertex n (.e, i)) = sVertex n := by
    rw [step_rowVertex hn π τ hvp_e, hei]; rfl
  have he_ac : ReachMax n σ τ (rowVertex n (.e, i)) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
    ReachMax.step_eq hstep_e (reachMax_s_to_a_cmax hn hV)
      (by rw [gamePriority_rowVertex hn hvp_e]; dsimp only; omega)
  have hf_ac : ReachMax n σ τ (fVertex n i) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
    ReachMax.step_eq hstep_f he_ac (by rw [gamePriority_fVertex n i (by omega) hin]; omega)
  have hg_ac : ReachMax n σ τ (gVertex n i) (decisionVertex n .a (c_max + 1)) (2 * i + 7) :=
    ReachMax.step_eq hstep_g hf_ac (by rw [gamePriority_gVertex n i (by omega) hin]; omega)
  rcases reachMax_a_ladder_general hn hV (i - (c_max + 1)) (c_max + 1) i rfl
    (by omega) (by omega) (by omega) (Or.inl hci) with ⟨ma, hma, hac_ai⟩
  have hvp_ai : ValidRow n (.a, i) := ⟨hi2, hin⟩
  have hstep_ai : step (parityGame n) σ τ (decisionVertex n .a i) = decisionVertex n .a (i + 1) := by
    rw [decisionVertex_eq_rowVertex hvp_ai, step_rowVertex hn π τ hvp_ai, hai]; rfl
  have hp_ai : gamePriority n (decisionVertex n .a i) = 3 := by
    rw [decisionVertex_eq_rowVertex hvp_ai, gamePriority_rowVertex hn hvp_ai]
  have hai_step : ReachMax n σ τ (decisionVertex n .a i) (decisionVertex n .a (i + 1)) 3 :=
    ReachMax.one_step hstep_ai hp_ai
  have hg_ai1 : ReachMax n σ τ (gVertex n i) (decisionVertex n .a (i + 1)) (2 * i + 7) := by
    have hma_le : ma ≤ 2 * i + 6 := by rcases hma with hle3 | ⟨_, _, hle⟩ <;> omega
    exact (hg_ac.trans hac_ai).trans_eq hai_step (by omega)
  exact valueLT_of_reachMax_odd hg_ai1 (ReachMax.refl _)
    (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (i + 1)))
    (by omega) (by omega) (by omega)

lemma valueLT_a_false_of_lt_cmax {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (hi2 : 2 ≤ i) (hin : i ≤ n)
    (hdi : π .d i = true) (hei : π .e i = false) (hic : i < c_max) (hac : π .a c_max = true)
    (hall : ∀ k ∈ Finset.Ico (i + 1) c_max, π .a k = false) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (gVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .a (i + 1))) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hc := hV.hc_range
  have hft : fTarget n π c_max b_max i = decisionVertex n .e i := by
    unfold fTarget
    rw [if_neg (by simp [hei]), if_neg (by simp [hdi]), if_neg (by simp [hdi]),
        if_neg (by omega), if_pos ⟨hic, hac, hall⟩]
  have hvp_e : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hstep_g : step (parityGame n) σ τ (gVertex n i) = fVertex n i :=
    step_gVertex hτ (by omega) hin
  have hstep_f : step (parityGame n) σ τ (fVertex n i) = rowVertex n (.e, i) := by
    rw [step_fVertex_phaseTau σ π c_max b_max i (by omega) hin, hft, decisionVertex_eq_rowVertex hvp_e]
  have hstep_e : step (parityGame n) σ τ (rowVertex n (.e, i)) = sVertex n := by
    rw [step_rowVertex hn π τ hvp_e, hei]; rfl
  have he_gc : ReachMax n σ τ (rowVertex n (.e, i)) (gVertex n c_max) 8 :=
    ReachMax.step_eq hstep_e (reachMax_s_to_g_cmax hn hV hτ)
      (by rw [gamePriority_rowVertex hn hvp_e]; dsimp only; omega)
  have hf_gc : ReachMax n σ τ (fVertex n i) (gVertex n c_max) 8 :=
    ReachMax.step_eq hstep_f he_gc (by rw [gamePriority_fVertex n i (by omega) hin]; omega)
  have hg_gc : ReachMax n σ τ (gVertex n i) (gVertex n c_max) (2 * i + 7) :=
    ReachMax.step_eq hstep_g hf_gc (by rw [gamePriority_gVertex n i (by omega) hin]; omega)
  have hai1_ac := reachMax_a_ladder_all_false hn τ (c_max - (i + 1)) (i + 1) c_max rfl
    (by omega) (by omega) (by omega)
    (fun r hr1 hr2 => hall r (Finset.mem_Ico.mpr ⟨hr1, hr2⟩))
  have hvp_ac : ValidRow n (.a, c_max) := ⟨by omega, hc.2⟩
  have hstep_ac : step (parityGame n) σ τ (decisionVertex n .a c_max) = gVertex n c_max := by
    rw [decisionVertex_eq_rowVertex hvp_ac, step_rowVertex hn π τ hvp_ac, hac]; rfl
  have hp_ac : gamePriority n (decisionVertex n .a c_max) = 3 := by
    rw [decisionVertex_eq_rowVertex hvp_ac, gamePriority_rowVertex hn hvp_ac]
  have hac_gc : ReachMax n σ τ (decisionVertex n .a c_max) (gVertex n c_max) 3 :=
    ReachMax.one_step hstep_ac hp_ac
  have hai1_gc : ReachMax n σ τ (decisionVertex n .a (i + 1)) (gVertex n c_max) 3 :=
    hai1_ac.trans_eq hac_gc (by split_ifs <;> omega)
  exact valueLT_of_reachMax_odd hg_gc hai1_gc
    (cyclePriority_eq_one_of_valid hn hV (gVertex n c_max))
    (by omega) (by omega) (by omega)

lemma reachMax_b_pred_to_g {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (τ : Fin (vertices n) → Fin (vertices n))
    (hi2 : 2 ≤ i) (hin : i ≤ n) :
    ∃ m0, m0 ≤ 3 ∧
      ReachMax n (policyStrategy n π) τ (decisionVertex n .b (i - 1)) (gVertex n (bEff b_max i)) m0 := by
  have hb := hV.hb_range
  have hbe := bEff_range hb.1 hi2
  by_cases hi_eq_2 : i = 2
  · subst hi_eq_2
    have hbe1 : bEff b_max 2 = 1 := by omega
    rw [hbe1, show 2 - 1 = 1 from rfl, decisionVertex_b_one n]
    exact ⟨0, by omega, ReachMax.refl _⟩
  · refine ⟨3, le_rfl, ?_⟩
    exact reachMax_b_ladder hn hV τ hi2 hin (i - 1 - max 2 (bEff b_max i)) (i - 1)
      rfl (by omega) le_rfl

lemma reachMax_c_pred_to_g {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i : ℕ}
    (hV : ValidPhasePolicy n π c_max b_max) (τ : Fin (vertices n) → Fin (vertices n))
    (hi2 : 2 ≤ i) (hin : i ≤ n) :
    ∃ m0, m0 ≤ 3 ∧
      ReachMax n (policyStrategy n π) τ (decisionVertex n .c (i - 1)) (gVertex n (bEff c_max i)) m0 := by
  have hc := hV.hc_range
  have hce := bEff_range hc.1 hi2
  by_cases hi_eq_2 : i = 2
  · subst hi_eq_2
    have hce1 : bEff c_max 2 = 1 := by omega
    rw [hce1, show 2 - 1 = 1 from rfl, decisionVertex_c_one n]
    exact ⟨0, by omega, ReachMax.refl _⟩
  · refine ⟨3, le_rfl, ?_⟩
    exact reachMax_c_ladder hn hV τ hi2 (by omega) (i - 1 - max 2 (bEff c_max i)) (i - 1)
      rfl (by omega) le_rfl

lemma reachMax_u_to_a_of_to_g {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max m i m0 : ℕ}
    {u : Fin (vertices n)} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hm1 : 1 ≤ m) (hmi : m < i) (hm0 : m0 ≤ 3)
    (hu : ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max) u (gVertex n m) m0)
    (hm_ed : 2 ≤ m → π .e m = true ∧ π .d m = true)
    (hcond : c_max < i ∨ (m = 1 ∧ π .e 1 = true ∧ ∀ r, 2 ≤ r → r < i → π .a r = true → π .e r = true)) :
    ∃ M, (10 ≤ M ∧ M % 2 = 0 ∧ M ≤ 2 * i + 6) ∧
      ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max) u (decisionVertex n .a i) M := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  by_cases hm2 : 2 ≤ m
  · have hmed := hm_ed hm2
    have hci : c_max < i := by rcases hcond with h | ⟨hm_eq, _, _⟩ <;> [exact h; omega]
    have hg_a := reachMax_g_f_h_of_ed (n := n) c_max b_max m hm1 (by omega) hmed.1 (fun _ => hmed.2)
    have hu_am : ReachMax n σ τ u (decisionVertex n .a (m + 1)) (2 * m + 8) :=
      hu.trans_eq hg_a (by omega)
    rcases reachMax_a_ladder_general hn hV (i - (m + 1)) (m + 1) i rfl
      (by omega) (by omega) (by omega) (Or.inl hci) with ⟨ma, hma, hreach_a⟩
    refine ⟨max (2 * m + 8) ma, ?_, hu_am.trans hreach_a⟩
    rcases hma with hle3 | ⟨h10, hev, hle⟩
    · exact ⟨by omega, by rw [Nat.max_eq_left (by omega)]; omega, by omega⟩
    · refine ⟨by omega, ?_, by omega⟩
      by_cases hcmp : ma ≤ 2 * m + 8
      · rw [Nat.max_eq_left hcmp]; omega
      · rw [Nat.max_eq_right (by omega)]; exact hev
  · have hm_eq_1 : m = 1 := by omega
    subst hm_eq_1
    rcases reachMax_g1 hn hV with hg1 | ⟨he1_f, hc2, hg1⟩
    · have hu_a2 : ReachMax n σ τ u (decisionVertex n .a 2) 10 :=
        hu.trans_eq hg1 (by omega)
      have ha_cond : c_max < i ∨ π .a c_max = false ∨
          ∀ r, 2 ≤ r → r < i → π .a r = true → π .e r = true := by
        rcases hcond with hci | ⟨_, _, hae⟩
        · exact Or.inl hci
        · exact Or.inr (Or.inr hae)
      rcases reachMax_a_ladder_general hn hV (i - 2) 2 i rfl
        le_rfl hi2 (by omega) ha_cond with ⟨ma, hma, hreach_a⟩
      refine ⟨max 10 ma, ?_, hu_a2.trans hreach_a⟩
      rcases hma with hle3 | ⟨h10, hev, hle⟩
      · exact ⟨by omega, by rw [Nat.max_eq_left (by omega)], by omega⟩
      · refine ⟨by omega, ?_, by omega⟩
        by_cases hcmp : ma ≤ 10
        · rw [Nat.max_eq_left hcmp]
        · rw [Nat.max_eq_right (by omega)]; exact hev
    · have hci : c_max < i := by
        rcases hcond with h | ⟨_, he1_t, _⟩
        · exact h
        · rw [he1_f] at he1_t; cases he1_t
      have hu_ac : ReachMax n σ τ u (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
        hu.trans_eq hg1 (by omega)
      rcases reachMax_a_ladder_general hn hV (i - (c_max + 1)) (c_max + 1) i rfl
        (by omega) (by omega) (by omega) (Or.inl hci) with ⟨ma, hma, hreach_a⟩
      refine ⟨max (2 * c_max + 8) ma, ?_, hu_ac.trans hreach_a⟩
      rcases hma with hle3 | ⟨h10, hev, hle⟩
      · exact ⟨by omega, by rw [Nat.max_eq_left (by omega)]; omega, by omega⟩
      · refine ⟨by omega, ?_, by omega⟩
        by_cases hcmp : ma ≤ 2 * c_max + 8
        · rw [Nat.max_eq_left hcmp]; omega
        · rw [Nat.max_eq_right (by omega)]; exact hev

lemma valueLT_g_u_of_a_true {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i M : ℕ}
    {u : Fin (vertices n)} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hai : π .a i = true)
    (hM : 10 ≤ M ∧ M % 2 = 0 ∧ M ≤ 2 * i + 6)
    (hu : ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max) u (decisionVertex n .a i) M) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (gVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max) u) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hvp_ai : ValidRow n (.a, i) := ⟨hi2, hin⟩
  have hstep_ai : step (parityGame n) σ τ (decisionVertex n .a i) = gVertex n i := by
    rw [decisionVertex_eq_rowVertex hvp_ai, step_rowVertex hn π τ hvp_ai, hai]; rfl
  have hp_ai : gamePriority n (decisionVertex n .a i) = 3 := by
    rw [decisionVertex_eq_rowVertex hvp_ai, gamePriority_rowVertex hn hvp_ai]
  have hai_g : ReachMax n σ τ (decisionVertex n .a i) (gVertex n i) 3 :=
    ReachMax.one_step hstep_ai hp_ai
  have hu_g : ReachMax n σ τ u (gVertex n i) M :=
    hu.trans_eq hai_g (by omega)
  exact valueLT_of_reachMax_even (ReachMax.refl _) hu_g
    (cyclePriority_eq_one_of_valid hn hV (gVertex n i))
    (by omega) (by omega) hM.2.1

lemma valueLT_u_f_of_a_true {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i M : ℕ}
    {u : Fin (vertices n)} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hai : π .a i = true)
    (hM : 10 ≤ M ∧ M % 2 = 0 ∧ M ≤ 2 * i + 6)
    (hu : ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max) u (decisionVertex n .a i) M) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max) u)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (fVertex n i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hvp_ai : ValidRow n (.a, i) := ⟨hi2, hin⟩
  have hstep_ai : step (parityGame n) σ τ (decisionVertex n .a i) = gVertex n i := by
    rw [decisionVertex_eq_rowVertex hvp_ai, step_rowVertex hn π τ hvp_ai, hai]; rfl
  have hp_ai : gamePriority n (decisionVertex n .a i) = 3 := by
    rw [decisionVertex_eq_rowVertex hvp_ai, gamePriority_rowVertex hn hvp_ai]
  have hai_g : ReachMax n σ τ (decisionVertex n .a i) (gVertex n i) 3 :=
    ReachMax.one_step hstep_ai hp_ai
  have hg_f : ReachMax n σ τ (gVertex n i) (fVertex n i) (2 * i + 7) :=
    ReachMax.one_step (step_gVertex hτ (by omega) hin) (gamePriority_gVertex n i (by omega) hin)
  have hu_f : ReachMax n σ τ u (fVertex n i) (2 * i + 7) := by
    have hM_le := hM.2.2
    exact (hu.trans hai_g).trans_eq hg_f (by omega)
  exact valueLT_of_reachMax_odd hu_f (ReachMax.refl _)
    (cyclePriority_eq_one_of_valid hn hV (fVertex n i))
    (by omega) (by omega) (by omega)

lemma valueLT_u_g_of_a_false_ed {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool} {c_max b_max i M : ℕ}
    {u : Fin (vertices n)} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hai : π .a i = false) (hdi : π .d i = true) (hei : π .e i = true)
    (hM : 10 ≤ M ∧ M % 2 = 0 ∧ M ≤ 2 * i + 6)
    (hu : ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max) u (decisionVertex n .a i) M) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max) u)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (gVertex n i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hvp_ai : ValidRow n (.a, i) := ⟨hi2, hin⟩
  have hstep_ai : step (parityGame n) σ τ (decisionVertex n .a i) = decisionVertex n .a (i + 1) := by
    rw [decisionVertex_eq_rowVertex hvp_ai, step_rowVertex hn π τ hvp_ai, hai]; rfl
  have hp_ai : gamePriority n (decisionVertex n .a i) = 3 := by
    rw [decisionVertex_eq_rowVertex hvp_ai, gamePriority_rowVertex hn hvp_ai]
  have hai_step : ReachMax n σ τ (decisionVertex n .a i) (decisionVertex n .a (i + 1)) 3 :=
    ReachMax.one_step hstep_ai hp_ai
  have hu_ai1 : ReachMax n σ τ u (decisionVertex n .a (i + 1)) M :=
    hu.trans_eq hai_step (by omega)
  have hg_ai1 := reachMax_g_f_h_of_ed (n := n) c_max b_max i (by omega) hin hei (fun _ => hdi)
  exact valueLT_of_reachMax_even hu_ai1 hg_ai1
    (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (i + 1)))
    (by omega) (by omega) (by omega)

lemma valueLT_g_u_of_a_false_d_false_e_true {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i M : ℕ} {u : Fin (vertices n)} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hai : π .a i = false) (hdi : π .d i = false) (hei : π .e i = true)
    (hM : 10 ≤ M ∧ M % 2 = 0 ∧ M ≤ 2 * i + 6)
    (hu : ReachMax n (policyStrategy n π) (phaseTau n π c_max b_max) u (decisionVertex n .a i) M) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (gVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max) u) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hvp_ai : ValidRow n (.a, i) := ⟨hi2, hin⟩
  have hstep_ai : step (parityGame n) σ τ (decisionVertex n .a i) = decisionVertex n .a (i + 1) := by
    rw [decisionVertex_eq_rowVertex hvp_ai, step_rowVertex hn π τ hvp_ai, hai]; rfl
  have hp_ai : gamePriority n (decisionVertex n .a i) = 3 := by
    rw [decisionVertex_eq_rowVertex hvp_ai, gamePriority_rowVertex hn hvp_ai]
  have hai_step : ReachMax n σ τ (decisionVertex n .a i) (decisionVertex n .a (i + 1)) 3 :=
    ReachMax.one_step hstep_ai hp_ai
  have hu_ai1 : ReachMax n σ τ u (decisionVertex n .a (i + 1)) M :=
    hu.trans_eq hai_step (by omega)
  have hft : fTarget n π c_max b_max i = decisionVertex n .d i := by
    unfold fTarget
    rw [if_neg (by simp [hdi]; omega), if_pos ⟨by omega, hdi, hei⟩]
  have hvp_d : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hstep_g : step (parityGame n) σ τ (gVertex n i) = fVertex n i :=
    step_gVertex hτ (by omega) hin
  have hstep_f : step (parityGame n) σ τ (fVertex n i) = rowVertex n (.d, i) := by
    rw [step_fVertex_phaseTau σ π c_max b_max i (by omega) hin, hft, decisionVertex_eq_rowVertex hvp_d]
  rcases reachMax_d_false_to_a hn hV hi2 hin hdi with ⟨md, ⟨_, _, hmd_le⟩, hd_ai1⟩
  have hf_ai1 : ReachMax n σ τ (fVertex n i) (decisionVertex n .a (i + 1)) md :=
    ReachMax.step_eq hstep_f hd_ai1 (by rw [gamePriority_fVertex n i (by omega) hin]; omega)
  have hg_ai1 : ReachMax n σ τ (gVertex n i) (decisionVertex n .a (i + 1)) (2 * i + 7) :=
    ReachMax.step_eq hstep_g hf_ai1 (by rw [gamePriority_gVertex n i (by omega) hin]; omega)
  exact valueLT_of_reachMax_odd hg_ai1 hu_ai1
    (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (i + 1)))
    (by omega) (by omega) (by omega)

lemma valueLT_d_true_of_d_false_e_false {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i : ℕ} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hdi : π .d i = false) (hei : π .e i = false)
    (hci : c_max < i) (hbc : b_max = c_max) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .b (i - 1)))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (fVertex n i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hft : fTarget n π c_max b_max i = decisionVertex n .d i := by
    unfold fTarget
    rw [if_neg (by simp [hei]), if_neg (by simp [hei]), if_pos ⟨by omega, hdi, hei⟩,
        if_pos ⟨hci, hbc⟩]
  have hvp_d : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hstep_f : step (parityGame n) σ τ (fVertex n i) = rowVertex n (.d, i) := by
    rw [step_fVertex_phaseTau σ π c_max b_max i (by omega) hin, hft, decisionVertex_eq_rowVertex hvp_d]
  have hstep_d : step (parityGame n) σ τ (rowVertex n (.d, i)) = decisionVertex n .b (i - 1) := by
    rw [step_rowVertex hn π τ hvp_d, hdi]; rfl
  have hd_b : ReachMax n σ τ (rowVertex n (.d, i)) (decisionVertex n .b (i - 1)) 5 :=
    ReachMax.one_step hstep_d (gamePriority_rowVertex hn hvp_d)
  have hf_b : ReachMax n σ τ (fVertex n i) (decisionVertex n .b (i - 1)) 6 :=
    ReachMax.step_eq hstep_f hd_b (by rw [gamePriority_fVertex n i (by omega) hin]; omega)
  exact valueLT_of_reachMax_even (ReachMax.refl _) hf_b
    (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .b (i - 1)))
    (by omega) (by omega) (by omega)

lemma valueLT_d_true_of_bmax_one_cmax_one_e_false {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i : ℕ} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hdi : π .d i = true) (hei : π .e i = false)
    (hc1 : c_max = 1) (hb1 : b_max = 1) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .b (i - 1)))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (fVertex n i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hft : fTarget n π c_max b_max i = decisionVertex n .e i := by
    unfold fTarget
    rw [if_neg (by simp [hei]), if_neg (by simp [hdi]), if_neg (by simp [hdi]),
        if_pos (by omega : c_max < i)]
  have hvp_e : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hstep_f : step (parityGame n) σ τ (fVertex n i) = rowVertex n (.e, i) := by
    rw [step_fVertex_phaseTau σ π c_max b_max i (by omega) hin, hft, decisionVertex_eq_rowVertex hvp_e]
  have hstep_e : step (parityGame n) σ τ (rowVertex n (.e, i)) = sVertex n := by
    rw [step_rowVertex hn π τ hvp_e, hei]; rfl
  have he_g : ReachMax n σ τ (rowVertex n (.e, i)) (gVertex n c_max) 8 :=
    ReachMax.step_eq hstep_e (reachMax_s_to_g_cmax hn hV hτ)
      (by rw [gamePriority_rowVertex hn hvp_e]; dsimp only; omega)
  have hf_g : ReachMax n σ τ (fVertex n i) (gVertex n c_max) 8 :=
    ReachMax.step_eq hstep_f he_g (by rw [gamePriority_fVertex n i (by omega) hin]; omega)
  rcases reachMax_b_pred_to_g hn hV τ hi2 hin with ⟨m0, hm0, hb_g⟩
  have hbe : bEff b_max i = c_max := by unfold bEff; split_ifs <;> omega
  rw [hbe] at hb_g
  exact valueLT_of_reachMax_even hb_g hf_g
    (cyclePriority_eq_one_of_valid hn hV (gVertex n c_max))
    (by omega) (by omega) (by omega)

lemma valueLT_d_false_of_switch {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i : ℕ} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hei : π .e i = false)
    (hft : fTarget n π c_max b_max i = decisionVertex n .e i)
    (hcases : (c_max < b_max ∧ b_max < i ∧ π .a b_max = false) ∨
      (bEff b_max i = 1 ∧ 2 ≤ c_max ∧ π .e 1 = true ∧ π .a c_max = true ∧
        ∀ r, 2 ≤ r → r < c_max → π .a r = false)) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (fVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (decisionVertex n .b (i - 1))) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hc := hV.hc_range
  have hb := hV.hb_range
  have hvp_e : ValidRow n (.e, i) := ⟨by omega, hin⟩
  have hstep_f : step (parityGame n) σ τ (fVertex n i) = rowVertex n (.e, i) := by
    rw [step_fVertex_phaseTau σ π c_max b_max i (by omega) hin, hft, decisionVertex_eq_rowVertex hvp_e]
  have hstep_e : step (parityGame n) σ τ (rowVertex n (.e, i)) = sVertex n := by
    rw [step_rowVertex hn π τ hvp_e, hei]; rfl
  have he_s : ReachMax n σ τ (rowVertex n (.e, i)) (sVertex n) 5 :=
    ReachMax.one_step hstep_e (gamePriority_rowVertex hn hvp_e)
  have hf_s : ReachMax n σ τ (fVertex n i) (sVertex n) 6 :=
    ReachMax.step_eq hstep_f he_s (by rw [gamePriority_fVertex n i (by omega) hin]; omega)
  rcases reachMax_b_pred_to_g hn hV τ hi2 hin with ⟨m0, hm0, hb_g⟩
  rcases hcases with ⟨hcb, hbi, hab_f⟩ | ⟨hbe1, hc2, he1_t, hac_t, haf⟩
  · have hbe : bEff b_max i = b_max := by unfold bEff; rw [if_pos hbi]
    rw [hbe] at hb_g
    have hbed := hV.hb_ed (by omega)
    have hg_ab := reachMax_g_f_h_of_ed (n := n) c_max b_max b_max hb.1 (by omega) hbed.1 (fun _ => hbed.2)
    have hb_ab : ReachMax n σ τ (decisionVertex n .b (i - 1)) (decisionVertex n .a (b_max + 1)) (2 * b_max + 8) :=
      hb_g.trans_eq hg_ab (by omega)
    have hf_ac : ReachMax n σ τ (fVertex n i) (decisionVertex n .a (c_max + 1)) (2 * c_max + 8) :=
      hf_s.trans_eq (reachMax_s_to_a_cmax hn hV) (by omega)
    rcases reachMax_a_ladder_general hn hV (b_max - (c_max + 1)) (c_max + 1) b_max rfl
      (by omega) (by omega) (by omega) (Or.inl hcb) with ⟨ma, hma, hac_ab⟩
    have hvp_ab : ValidRow n (.a, b_max) := ⟨by omega, by omega⟩
    have hstep_ab : step (parityGame n) σ τ (decisionVertex n .a b_max) = decisionVertex n .a (b_max + 1) := by
      rw [decisionVertex_eq_rowVertex hvp_ab, step_rowVertex hn π τ hvp_ab, hab_f]; rfl
    have hp_ab : gamePriority n (decisionVertex n .a b_max) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp_ab, gamePriority_rowVertex hn hvp_ab]
    have hab_step : ReachMax n σ τ (decisionVertex n .a b_max) (decisionVertex n .a (b_max + 1)) 3 :=
      ReachMax.one_step hstep_ab hp_ab
    have hf_ab : ReachMax n σ τ (fVertex n i) (decisionVertex n .a (b_max + 1))
        (max (2 * c_max + 8) ma) :=
      (hf_ac.trans hac_ab).trans_eq hab_step (by omega)
    have hlt : max (2 * c_max + 8) ma < 2 * b_max + 8 := by
      rcases hma with hle3 | ⟨_, _, hle⟩ <;> omega
    exact valueLT_of_reachMax_even hf_ab hb_ab
      (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (b_max + 1)))
      hlt (by omega) (by omega)
  · rw [hbe1] at hb_g
    have hg1_a2 := reachMax_g_f_h_of_ed (n := n) c_max b_max 1 le_rfl (by omega) he1_t (fun h => by omega)
    have hb_a2 : ReachMax n σ τ (decisionVertex n .b (i - 1)) (decisionVertex n .a 2) 10 :=
      hb_g.trans_eq hg1_a2 (by omega)
    have ha2_ac := reachMax_a_ladder_all_false hn τ (c_max - 2) 2 c_max rfl
      le_rfl hc2 (by omega) haf
    have hvp_ac : ValidRow n (.a, c_max) := ⟨hc2, hc.2⟩
    have hstep_ac : step (parityGame n) σ τ (decisionVertex n .a c_max) = gVertex n c_max := by
      rw [decisionVertex_eq_rowVertex hvp_ac, step_rowVertex hn π τ hvp_ac, hac_t]; rfl
    have hp_ac : gamePriority n (decisionVertex n .a c_max) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp_ac, gamePriority_rowVertex hn hvp_ac]
    have hac_g : ReachMax n σ τ (decisionVertex n .a c_max) (gVertex n c_max) 3 :=
      ReachMax.one_step hstep_ac hp_ac
    have hb_gc : ReachMax n σ τ (decisionVertex n .b (i - 1)) (gVertex n c_max) 10 :=
      (hb_a2.trans ha2_ac).trans_eq hac_g (by split_ifs <;> omega)
    have hf_gc : ReachMax n σ τ (fVertex n i) (gVertex n c_max) 8 :=
      hf_s.trans_eq (reachMax_s_to_g_cmax hn hV hτ) (by omega)
    exact valueLT_of_reachMax_even hf_gc hb_gc
      (cyclePriority_eq_one_of_valid hn hV (gVertex n c_max))
      (by omega) (by omega) (by omega)

lemma valueLT_e_true_of_fTarget_eq_e {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i : ℕ} (hV : ValidPhasePolicy n π c_max b_max)
    (hi1 : 1 ≤ i) (hin : i ≤ n) (hei : π .e i = false)
    (hft : fTarget n π c_max b_max i = decisionVertex n .e i) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (sVertex n))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (fVertex n i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hvp_e : ValidRow n (.e, i) := ⟨hi1, hin⟩
  have hstep_f : step (parityGame n) σ τ (fVertex n i) = rowVertex n (.e, i) := by
    rw [step_fVertex_phaseTau σ π c_max b_max i hi1 hin, hft, decisionVertex_eq_rowVertex hvp_e]
  have hstep_e : step (parityGame n) σ τ (rowVertex n (.e, i)) = sVertex n := by
    rw [step_rowVertex hn π τ hvp_e, hei]; rfl
  have he_s : ReachMax n σ τ (rowVertex n (.e, i)) (sVertex n) 5 :=
    ReachMax.one_step hstep_e (gamePriority_rowVertex hn hvp_e)
  have hf_s : ReachMax n σ τ (fVertex n i) (sVertex n) 6 :=
    ReachMax.step_eq hstep_f he_s (by rw [gamePriority_fVertex n i hi1 hin]; omega)
  exact valueLT_of_reachMax_even (ReachMax.refl _) hf_s
    (cyclePriority_eq_one_of_valid hn hV (sVertex n))
    (by omega) (by omega) (by omega)

lemma valueLT_e_false_of_lt_cmax_a_false {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i : ℕ} (hV : ValidPhasePolicy n π c_max b_max)
    (hi1 : 1 ≤ i) (hin : i ≤ n) (hic : i < c_max) (hac_f : π .a c_max = false)
    (hei : π .e i = true) (hd : i = 1 ∨ π .d i = true) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (fVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (sVertex n)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hc := hV.hc_range
  have hft : fTarget n π c_max b_max i = hVertex n i := by
    unfold fTarget
    rw [if_pos ⟨hd, hei⟩]
  have hstep_f : step (parityGame n) σ τ (fVertex n i) = hVertex n i := by
    rw [step_fVertex_phaseTau σ π c_max b_max i hi1 hin, hft]
  have hh_ai1 : ReachMax n σ τ (hVertex n i) (decisionVertex n .a (i + 1)) (2 * i + 8) :=
    ReachMax.one_step (step_hVertex hτ hi1 hin) (gamePriority_hVertex n i hi1 hin)
  have hf_ai1 : ReachMax n σ τ (fVertex n i) (decisionVertex n .a (i + 1)) (2 * i + 8) :=
    ReachMax.step_eq hstep_f hh_ai1 (by rw [gamePriority_fVertex n i hi1 hin]; omega)
  rcases reachMax_a_ladder_general hn hV (c_max - (i + 1)) (i + 1) c_max rfl
    (by omega) (by omega) (by omega) (Or.inr (Or.inl hac_f)) with ⟨ma, hma, hai1_ac⟩
  have hvp_ac : ValidRow n (.a, c_max) := ⟨by omega, hc.2⟩
  have hstep_ac : step (parityGame n) σ τ (decisionVertex n .a c_max) = decisionVertex n .a (c_max + 1) := by
    rw [decisionVertex_eq_rowVertex hvp_ac, step_rowVertex hn π τ hvp_ac, hac_f]; rfl
  have hp_ac : gamePriority n (decisionVertex n .a c_max) = 3 := by
    rw [decisionVertex_eq_rowVertex hvp_ac, gamePriority_rowVertex hn hvp_ac]
  have hac_step : ReachMax n σ τ (decisionVertex n .a c_max) (decisionVertex n .a (c_max + 1)) 3 :=
    ReachMax.one_step hstep_ac hp_ac
  have hf_ac1 : ReachMax n σ τ (fVertex n i) (decisionVertex n .a (c_max + 1)) (max (2 * i + 8) ma) :=
    (hf_ai1.trans hai1_ac).trans_eq hac_step (by omega)
  have hs_ac1 := reachMax_s_to_a_cmax hn hV
  have hlt : max (2 * i + 8) ma < 2 * c_max + 8 := by
    rcases hma with hle3 | ⟨_, _, hle⟩ <;> omega
  exact valueLT_of_reachMax_even hf_ac1 hs_ac1
    (cyclePriority_eq_one_of_valid hn hV (decisionVertex n .a (c_max + 1)))
    hlt (by omega) (by omega)

lemma valueLT_e_false_of_d_false_cmax_eq_bmax {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i : ℕ} (hV : ValidPhasePolicy n π c_max b_max)
    (hi2 : 2 ≤ i) (hin : i ≤ n) (hdi : π .d i = false) (hei : π .e i = true)
    (hci : c_max < i) (hbc : b_max = c_max) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (fVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (sVertex n)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hft : fTarget n π c_max b_max i = decisionVertex n .d i := by
    unfold fTarget
    rw [if_neg (by simp [hdi]; omega), if_pos ⟨by omega, hdi, hei⟩]
  have hvp_d : ValidRow n (.d, i) := ⟨hi2, hin⟩
  have hstep_f : step (parityGame n) σ τ (fVertex n i) = rowVertex n (.d, i) := by
    rw [step_fVertex_phaseTau σ π c_max b_max i (by omega) hin, hft, decisionVertex_eq_rowVertex hvp_d]
  have hd_g := reachMax_d_to_g_bEff hn hV τ hi2 hin hdi
  have hbe : bEff b_max i = c_max := by unfold bEff; rw [if_pos (by omega), hbc]
  rw [hbe] at hd_g
  have hf_gc : ReachMax n σ τ (fVertex n i) (gVertex n c_max) 6 :=
    ReachMax.step_eq hstep_f hd_g (by rw [gamePriority_fVertex n i (by omega) hin]; omega)
  have hs_gc := reachMax_s_to_g_cmax hn hV hτ
  exact valueLT_of_reachMax_even hf_gc hs_gc
    (cyclePriority_eq_one_of_valid hn hV (gVertex n c_max))
    (by omega) (by omega) (by omega)

lemma valueLT_e_true_of_eq_cmax_or_gt_cmax_a_true {n : ℕ} (hn : 3 ≤ n) {π : Kind → ℕ → Bool}
    {c_max b_max i : ℕ} (hV : ValidPhasePolicy n π c_max b_max)
    (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hcases : i = c_max ∨ (c_max < i ∧ π .a i = true)) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (sVertex n))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n π) (phaseTau n π c_max b_max)
        (fVertex n i)) := by
  set σ := policyStrategy n π
  set τ := phaseTau n π c_max b_max
  have hτ := phaseTau_legal n π c_max b_max
  have hc := hV.hc_range
  have hg_f : ReachMax n σ τ (gVertex n i) (fVertex n i) (2 * i + 7) :=
    ReachMax.one_step (step_gVertex hτ hi1 hin) (gamePriority_gVertex n i hi1 hin)
  rcases hcases with rfl | ⟨hci, hai⟩
  · have hs_f : ReachMax n σ τ (sVertex n) (fVertex n i) (2 * i + 7) :=
      (reachMax_s_to_g_cmax hn hV hτ).trans_eq hg_f (by omega)
    exact valueLT_of_reachMax_odd hs_f (ReachMax.refl _)
      (cyclePriority_eq_one_of_valid hn hV (fVertex n i))
      (by omega) (by omega) (by omega)
  · have hi2 : 2 ≤ i := by omega
    have hs_ac := reachMax_s_to_a_cmax hn hV
    rcases reachMax_a_ladder_general hn hV (i - (c_max + 1)) (c_max + 1) i rfl
      (by omega) (by omega) (by omega) (Or.inl hci) with ⟨ma, hma, hac_ai⟩
    have hvp_ai : ValidRow n (.a, i) := ⟨hi2, hin⟩
    have hstep_ai : step (parityGame n) σ τ (decisionVertex n .a i) = gVertex n i := by
      rw [decisionVertex_eq_rowVertex hvp_ai, step_rowVertex hn π τ hvp_ai, hai]; rfl
    have hp_ai : gamePriority n (decisionVertex n .a i) = 3 := by
      rw [decisionVertex_eq_rowVertex hvp_ai, gamePriority_rowVertex hn hvp_ai]
    have hai_g : ReachMax n σ τ (decisionVertex n .a i) (gVertex n i) 3 :=
      ReachMax.one_step hstep_ai hp_ai
    have hs_f : ReachMax n σ τ (sVertex n) (fVertex n i) (2 * i + 7) := by
      have hma_le : ma ≤ 2 * i + 6 := by rcases hma with hle3 | ⟨_, _, hle⟩ <;> omega
      exact ((hs_ac.trans hac_ai).trans hai_g).trans_eq hg_f (by omega)
    exact valueLT_of_reachMax_odd hs_f (ReachMax.refl _)
      (cyclePriority_eq_one_of_valid hn hV (fVertex n i))
      (by omega) (by omega) (by omega)

lemma cursorBit_e_one_of_pos_lt {n b j : ℕ} (hn : 3 ≤ n) (hj0 : 0 < j) (hj6 : j < 6 * n - 7) :
    cursorBit n b j .e 1 = true := by
  have hm := nu_range (b := b) hn
  unfold cursorBit
  dsimp only
  cases h1 : bit b 1 <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · rw [decide_eq_true_iff]
    omega
  · rw [if_pos (by omega : 1 < nu n b), decide_eq_true_iff]
    omega

lemma cursorBit_a_imp_e_of_lt {n b j r : ℕ} (hn : 3 ≤ n) (hj6 : j < 6 * n - 7)
    (hr2 : 2 ≤ r) (hrn : r ≤ n) (har : cursorBit n b j .a r = true) :
    cursorBit n b j .e r = true := by
  unfold cursorBit at har ⊢
  dsimp only at har ⊢
  cases h1 : bit b 1
  · simp only [h1, Bool.false_eq_true, ite_false] at har ⊢
    rw [if_neg (by omega), if_neg (by simp [har])]
  · simp only [h1, ite_true] at har ⊢
    split_ifs at har with hreq hrlt
    · rw [decide_eq_true_iff] at har
      omega
    · rw [if_pos hrlt, decide_eq_true_iff]
      omega
    · rw [if_neg hrlt, if_neg hreq, if_neg (by simp [har])]

lemma improving_at_cursor_a {n b i : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (one : Bool) (hv_valid : ValidRow n (.a, i)) (j : ℕ)
    (hv_rank : columnRank n ⟨.a, i, one⟩ = j)
    (hpi : cursorBit n b j .a i = !one) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.a, i, !one⟩))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.a, i, one⟩)) ↔
    sweepSwitch n b ⟨.a, i, one⟩ = true := by
  have hV := cursorPolicy_valid hn hb1 hb2 (j := j)
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  have hi2 : 2 ≤ i := hv_valid.1
  have hin : i ≤ n := hv_valid.2
  unfold columnRank at hv_rank
  have hj_gt : 7 * n + i - 9 < j := by
    cases one <;> dsimp only at hv_rank <;> omega
  have hdi : cursorBit n b j .d i = true := by
    unfold cursorBit
    dsimp only
    have h_or : decide (j ≤ 4 * i - 7 || 7 * n + i - 9 < j) = true := by
      simp only [decide_eq_true_eq, Bool.or_eq_true]
      right; exact hj_gt
    rw [h_or, ite_self]
  cases one <;> dsimp only at hv_rank ⊢ <;>
    simp only [Bool.not_false, Bool.not_true] at hpi ⊢
  · -- one = false
    change ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (gVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (decisionVertex n .a (i + 1))) ↔ _
    by_cases hsw : sweepSwitch n b ⟨.a, i, false⟩ = true
    · refine ⟨fun _ => hsw, fun _ => ?_⟩
      unfold sweepSwitch at hsw
      dsimp only at hsw
      cases h1 : bit b 1
      · rw [h1] at hsw; cases hsw
      · simp only [h1, ite_true, decide_eq_true_eq] at hsw
        have hei : cursorBit n b j .e i = false := by
          unfold cursorBit; dsimp only
          simp only [h1, ite_true]
          rw [if_pos hsw, decide_eq_false_iff_not]
          omega
        have hc_eq : cursorCMax n b j = nu n b := by
          unfold cursorCMax
          simp only [h1, ite_true]
          rw [if_pos (by omega)]
        have hic : i < cursorCMax n b j := by omega
        have hac : cursorBit n b j .a (cursorCMax n b j) = true := by
          rw [hc_eq]
          unfold cursorBit; dsimp only
          simp only [h1, ite_true, decide_eq_true_eq]
          omega
        have hall : ∀ k ∈ Finset.Ico (i + 1) (cursorCMax n b j), cursorBit n b j .a k = false := by
          intro k hk
          rw [hc_eq, Finset.mem_Ico] at hk
          unfold cursorBit; dsimp only
          simp only [h1, ite_true]
          rw [if_neg (by omega), if_pos hk.2, decide_eq_false_iff_not]
          omega
        exact valueLT_a_false_of_lt_cmax hn hV hi2 hin hdi hei hic hac hall
    · have hsw_f : sweepSwitch n b ⟨.a, i, false⟩ = false := by
        cases h : sweepSwitch n b ⟨.a, i, false⟩ <;> [rfl; exact False.elim (hsw h)]
      rw [hsw_f]
      simp only [Bool.false_eq_true, iff_false]
      have hei : cursorBit n b j .e i = true := by
        unfold sweepSwitch at hsw_f
        unfold cursorBit at hpi ⊢
        dsimp only at hsw_f hpi ⊢
        cases h1 : bit b 1
        · simp only [h1, Bool.false_eq_true, ite_false] at hsw_f hpi ⊢
          rw [if_neg (by omega), if_neg (by simp [hpi])]
        · simp only [h1, ite_true] at hsw_f hpi ⊢
          rw [decide_eq_false_iff_not] at hsw_f
          rw [if_neg hsw_f] at hpi ⊢
          by_cases heq : i = nu n b
          · rw [if_pos heq, decide_eq_true_iff]
            omega
          · rw [if_neg heq] at hpi ⊢
            rw [if_neg (by simp [hpi])]
      exact valueLT_asymm (valueLT_a_true_of_ed hn hV hi2 hin hdi hei)
  · -- one = true
    change ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (decisionVertex n .a (i + 1)))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (gVertex n i)) ↔ _
    by_cases hsw : sweepSwitch n b ⟨.a, i, true⟩ = true
    · refine ⟨fun _ => hsw, fun _ => ?_⟩
      unfold sweepSwitch at hsw
      dsimp only at hsw
      cases h1 : bit b 1
      · rw [h1] at hsw; cases hsw
      · simp only [h1, ite_true, decide_eq_true_eq] at hsw
        have hei : cursorBit n b j .e i = true := by
          unfold cursorBit; dsimp only
          simp only [h1, ite_true]
          rw [if_neg (by omega), if_pos hsw, decide_eq_true_iff]
          omega
        exact valueLT_a_true_of_ed hn hV hi2 hin hdi hei
    · have hsw_f : sweepSwitch n b ⟨.a, i, true⟩ = false := by
        cases h : sweepSwitch n b ⟨.a, i, true⟩ <;> [rfl; exact False.elim (hsw h)]
      rw [hsw_f]
      simp only [Bool.false_eq_true, iff_false]
      have ⟨hei, hci⟩ : cursorBit n b j .e i = false ∧ cursorCMax n b j < i := by
        unfold sweepSwitch at hsw_f
        unfold cursorBit cursorCMax at hpi ⊢
        dsimp only at hsw_f hpi ⊢
        cases h1 : bit b 1
        · simp only [h1, Bool.false_eq_true, ite_false] at hsw_f hpi ⊢
          refine ⟨?_, ?_⟩
          · rw [if_neg (by omega), if_pos (by simp [hpi])]
            simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
            omega
          · rw [if_pos (by omega)]
            omega
        · simp only [h1, ite_true] at hsw_f hpi ⊢
          rw [decide_eq_false_iff_not] at hsw_f
          rw [if_neg hsw_f] at hpi
          have hnot_lt : ¬ i < nu n b := by
            intro hlt
            rw [if_pos hlt, decide_eq_false_iff_not] at hpi
            omega
          rw [if_neg hnot_lt] at hpi
          refine ⟨?_, ?_⟩
          · rw [if_neg hnot_lt, if_neg hsw_f, if_pos (by simp [hpi])]
            simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
            omega
          · rw [if_pos (by omega)]
            omega
      exact valueLT_asymm (valueLT_a_false_of_cmax_lt hn hV hi2 hin hdi hei hpi hci)

lemma improving_at_cursor_bc_aux {n b i j M : ℕ} (hn : 3 ≤ n)
    (hi2 : 2 ≤ i) (hin : i ≤ n)
    (hj_lo : 4 * i - 5 ≤ j) (hj_hi : j < 6 * n - 7)
    (hV : ValidPhasePolicy n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
    (hnu : bit b (nu n b) = !bit b 1)
    {u : Fin (vertices n)}
    (hM : 10 ≤ M ∧ M % 2 = 0 ∧ M ≤ 2 * i + 6)
    (hu : ReachMax n (policyStrategy n (cursorBit n b j))
      (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
      u (decisionVertex n .a i) M)
    (one : Bool)
    (hi_nu_of_false : one = false → i = nu n b) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (if !one then gVertex n i else u))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (if one then gVertex n i else u)) ↔
    (if one then
      if bit b 1 then decide (i = nu n b) else false
    else
      if bit b 1 then false else decide (i = nu n b)) = true := by
  have hm := nu_range (b := b) hn
  cases one <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  · -- one = false
    have hi_nu : i = nu n b := hi_nu_of_false rfl
    cases h1 : bit b 1 <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · have hsw_t : decide (i = nu n b) = true := decide_eq_true hi_nu
      simp only [hsw_t, iff_true]
      have hai : cursorBit n b j .a i = true := by
        unfold cursorBit; dsimp only
        simp only [h1, Bool.false_eq_true, ite_false, hi_nu, hnu]
        rfl
      exact valueLT_g_u_of_a_true hn hV hi2 hin hai hM hu
    · simp only [iff_false]
      have hai : cursorBit n b j .a i = false := by
        unfold cursorBit; dsimp only
        simp only [h1, ite_true, if_pos hi_nu, decide_eq_false_iff_not]
        omega
      have hdi : cursorBit n b j .d i = true := by
        unfold cursorBit; dsimp only
        simp only [h1, ite_true, hi_nu, lt_irrefl, decide_false, Bool.and_false,
          Bool.false_eq_true, ite_false]
      have hei : cursorBit n b j .e i = true := by
        unfold cursorBit; dsimp only
        simp only [h1, ite_true]
        rw [if_neg (by omega), if_pos hi_nu, decide_eq_true_iff]
        omega
      exact valueLT_asymm (valueLT_u_g_of_a_false_ed hn hV hi2 hin hai hdi hei hM hu)
  · -- one = true
    by_cases hsw : (if bit b 1 then decide (i = nu n b) else false) = true
    · refine ⟨fun _ => hsw, fun _ => ?_⟩
      cases h1 : bit b 1
      · rw [h1] at hsw; cases hsw
      · simp only [h1, ite_true, decide_eq_true_eq] at hsw
        have hai : cursorBit n b j .a i = false := by
          unfold cursorBit; dsimp only
          simp only [h1, ite_true, if_pos hsw, decide_eq_false_iff_not]
          omega
        have hdi : cursorBit n b j .d i = true := by
          unfold cursorBit; dsimp only
          simp only [h1, ite_true, hsw, lt_irrefl, decide_false, Bool.and_false,
            Bool.false_eq_true, ite_false]
        have hei : cursorBit n b j .e i = true := by
          unfold cursorBit; dsimp only
          simp only [h1, ite_true]
          rw [if_neg (by omega), if_pos hsw, decide_eq_true_iff]
          omega
        exact valueLT_u_g_of_a_false_ed hn hV hi2 hin hai hdi hei hM hu
    · have hsw_f : (if bit b 1 then decide (i = nu n b) else false) = false := by
        cases h : (if bit b 1 then decide (i = nu n b) else false) <;>
          [rfl; exact False.elim (hsw h)]
      rw [hsw_f]
      simp only [Bool.false_eq_true, iff_false]
      by_cases hai : cursorBit n b j .a i = true
      · exact valueLT_asymm (valueLT_g_u_of_a_true hn hV hi2 hin hai hM hu)
      · have hai_f : cursorBit n b j .a i = false := by
          cases h : cursorBit n b j .a i <;> [rfl; exact False.elim (hai h)]
        have ⟨hdi_f, hei_t⟩ : cursorBit n b j .d i = false ∧ cursorBit n b j .e i = true := by
          unfold cursorBit at hai_f ⊢
          dsimp only at hai_f ⊢
          cases h1 : bit b 1
          · simp only [h1, Bool.false_eq_true, ite_false] at hsw_f hai_f ⊢
            refine ⟨?_, ?_⟩
            · rw [if_pos (by simp [hai_f])]
              simp only [decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq]
              omega
            · rw [if_neg (by omega), if_pos (by simp [hai_f])]
              simp only [decide_eq_true_eq, Bool.and_eq_true]
              omega
          · simp only [h1, ite_true] at hsw_f hai_f ⊢
            rw [decide_eq_false_iff_not] at hsw_f
            rw [if_neg hsw_f] at hai_f
            have hnot_lt : ¬ i < nu n b := by
              intro hlt
              rw [if_pos hlt, decide_eq_false_iff_not] at hai_f
              omega
            rw [if_neg hnot_lt] at hai_f
            have hgt : nu n b < i := by omega
            refine ⟨?_, ?_⟩
            · rw [if_pos (by simp [hai_f, hgt])]
              simp only [decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq]
              omega
            · rw [if_neg hnot_lt, if_neg hsw_f, if_pos (by simp [hai_f])]
              simp only [decide_eq_true_eq, Bool.and_eq_true]
              omega
        exact valueLT_asymm (valueLT_g_u_of_a_false_d_false_e_true hn hV hi2 hin hai_f hdi_f hei_t hM hu)

lemma improving_at_cursor_b {n b i : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (one : Bool) (hv_valid : ValidRow n (.b, i)) (j : ℕ)
    (hv_rank : columnRank n ⟨.b, i, one⟩ = j)
    (hpi : cursorBit n b j .b i = !one) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.b, i, !one⟩))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.b, i, one⟩)) ↔
    sweepSwitch n b ⟨.b, i, one⟩ = true := by
  have hV := cursorPolicy_valid hn hb1 hb2 (j := j)
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  have hi2 : 2 ≤ i := hv_valid.1
  have hin : i ≤ n - 1 := hv_valid.2
  unfold columnRank at hv_rank
  have hj_lo : 4 * i - 5 ≤ j := by cases one <;> dsimp only at hv_rank <;> omega
  have hj_hi : j < 6 * n - 7 := by cases one <;> dsimp only at hv_rank <;> omega
  have hbe_rng := bEff_range hV.hb_range.1 hi2
  rcases reachMax_b_pred_to_g hn hV
    (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j)) hi2 (by omega)
    with ⟨m0, hm0, hb_g⟩
  have hbe_ed : 2 ≤ bEff (cursorBMax n b j) i →
      cursorBit n b j .e (bEff (cursorBMax n b j) i) = true ∧
      cursorBit n b j .d (bEff (cursorBMax n b j) i) = true := by
    intro hbe2
    have heq := (bEff_eq_self_of_ge_two hbe2).1
    rw [heq]
    exact hV.hb_ed (heq ▸ hbe2)
  have hcond : cursorCMax n b j < i ∨
      (bEff (cursorBMax n b j) i = 1 ∧ cursorBit n b j .e 1 = true ∧
        ∀ r, 2 ≤ r → r < i → cursorBit n b j .a r = true → cursorBit n b j .e r = true) := by
    by_cases hci : cursorCMax n b j < i
    · exact Or.inl hci
    · right
      refine ⟨?_, cursorBit_e_one_of_pos_lt hn (by omega) hj_hi,
        fun r hr2 hri => cursorBit_a_imp_e_of_lt hn hj_hi hr2 (by omega)⟩
      unfold cursorCMax at hci
      unfold bEff cursorBMax
      split_ifs at hci ⊢ <;> omega
  rcases reachMax_u_to_a_of_to_g hn hV hi2 (by omega) hbe_rng.1 hbe_rng.2.1 hm0 hb_g hbe_ed hcond
    with ⟨M, hM, hu⟩
  have hi_nu_of_false : one = false → i = nu n b := by
    intro hone
    subst hone
    unfold cursorBit at hpi
    simp only [Bool.not_false, decide_eq_true_eq] at hpi
    unfold cursorBMax at hpi
    split_ifs at hpi <;> omega
  have haux := improving_at_cursor_bc_aux hn hi2 (by omega) hj_lo hj_hi hV hnu hM hu one hi_nu_of_false
  cases one <;> exact haux

lemma improving_at_cursor_c {n b i : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (one : Bool) (hv_valid : ValidRow n (.c, i)) (j : ℕ)
    (hv_rank : columnRank n ⟨.c, i, one⟩ = j)
    (hpi : cursorBit n b j .c i = !one) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.c, i, !one⟩))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.c, i, one⟩)) ↔
    sweepSwitch n b ⟨.c, i, one⟩ = true := by
  have hV := cursorPolicy_valid hn hb1 hb2 (j := j)
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  have hi2 : 2 ≤ i := hv_valid.1
  have hin : i ≤ n := hv_valid.2
  unfold columnRank at hv_rank
  have hj_lo : 4 * i - 5 ≤ j := by cases one <;> dsimp only at hv_rank <;> omega
  have hj_hi : j < 6 * n - 7 := by cases one <;> dsimp only at hv_rank <;> omega
  have hce_rng := bEff_range hV.hc_range.1 hi2
  rcases reachMax_c_pred_to_g hn hV
    (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j)) hi2 hin
    with ⟨m0, hm0, hc_g⟩
  have hce_ed : 2 ≤ bEff (cursorCMax n b j) i →
      cursorBit n b j .e (bEff (cursorCMax n b j) i) = true ∧
      cursorBit n b j .d (bEff (cursorCMax n b j) i) = true := by
    intro hce2
    have heq := (bEff_eq_self_of_ge_two hce2).1
    rw [heq]
    exact ⟨hV.hc_e, hV.hc_d (heq ▸ hce2)⟩
  have hcond : cursorCMax n b j < i ∨
      (bEff (cursorCMax n b j) i = 1 ∧ cursorBit n b j .e 1 = true ∧
        ∀ r, 2 ≤ r → r < i → cursorBit n b j .a r = true → cursorBit n b j .e r = true) := by
    by_cases hci : cursorCMax n b j < i
    · exact Or.inl hci
    · right
      refine ⟨by unfold bEff; rw [if_neg hci], cursorBit_e_one_of_pos_lt hn (by omega) hj_hi,
        fun r hr2 hri => cursorBit_a_imp_e_of_lt hn hj_hi hr2 (by omega)⟩
  rcases reachMax_u_to_a_of_to_g hn hV hi2 hin hce_rng.1 hce_rng.2.1 hm0 hc_g hce_ed hcond
    with ⟨M, hM, hu⟩
  have hi_nu_of_false : one = false → i = nu n b := by
    intro hone
    subst hone
    unfold cursorBit at hpi
    simp only [Bool.not_false, decide_eq_true_eq] at hpi
    unfold cursorCMax at hpi
    split_ifs at hpi <;> omega
  have haux := improving_at_cursor_bc_aux hn hi2 hin hj_lo hj_hi hV hnu hM hu one hi_nu_of_false
  cases one <;> exact haux

lemma improving_at_cursor_d {n b i : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (one : Bool) (hv_valid : ValidRow n (.d, i)) (j : ℕ)
    (hv_rank : columnRank n ⟨.d, i, one⟩ = j)
    (hpi : cursorBit n b j .d i = !one) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.d, i, !one⟩))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.d, i, one⟩)) ↔
    sweepSwitch n b ⟨.d, i, one⟩ = true := by
  have hV := cursorPolicy_valid hn hb1 hb2 (j := j)
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  have hi2 : 2 ≤ i := hv_valid.1
  have hin : i ≤ n := hv_valid.2
  unfold columnRank at hv_rank
  cases one <;> dsimp only at hv_rank ⊢ <;>
    simp only [Bool.not_false, Bool.not_true] at hpi ⊢
  · -- one = false (j = 4 * (i - 2) + 1, hpi : cursorBit n b j .d i = true)
    change ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (fVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (decisionVertex n .b (i - 1))) ↔ _
    by_cases hsw : sweepSwitch n b ⟨.d, i, false⟩ = true
    · refine ⟨fun _ => hsw, fun _ => ?_⟩
      unfold sweepSwitch at hsw
      dsimp only at hsw
      cases h1 : bit b 1 <;>
        simp only [h1, Bool.false_eq_true, ite_true, ite_false, Bool.and_eq_true,
          Bool.not_eq_true', decide_eq_true_eq] at hsw
      · -- bit b 1 = false, bit b i = false
        have hei : cursorBit n b j .e i = false := by
          unfold cursorBit; dsimp only
          simp only [h1, Bool.false_eq_true, ite_false]
          rw [if_neg (by omega), if_pos (by simp [hsw])]
          simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
          omega
        have hc_eq : cursorCMax n b j = nu n b := by
          unfold cursorCMax
          simp only [h1, Bool.false_eq_true, ite_false]
          rw [if_neg (by omega)]
        have hine : i ≠ nu n b := by
          intro rfl
          rw [h1] at hnu
          rw [hsw] at hnu
          cases hnu
        have hft : fTarget n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j) i =
            decisionVertex n .e i := by
          unfold fTarget
          rw [if_neg (by simp [hei]), if_neg (by simp [hpi]), if_neg (by simp [hpi])]
          by_cases hci : cursorCMax n b j < i
          · rw [if_pos hci]
          · have hic : i < cursorCMax n b j := by omega
            have hac : cursorBit n b j .a (cursorCMax n b j) = true := by
              rw [hc_eq]
              unfold cursorBit; dsimp only
              simp only [h1, Bool.false_eq_true, ite_false, hnu]
              rfl
            have hall : ∀ k ∈ Finset.Ico (i + 1) (cursorCMax n b j), cursorBit n b j .a k = false := by
              intro k hk
              rw [hc_eq, Finset.mem_Ico] at hk
              unfold cursorBit; dsimp only
              simp only [h1, Bool.false_eq_true, ite_false]
              exact (bit_lt_nu hn (by omega) hk.2).trans h1
            rw [if_neg hci, if_pos ⟨hic, hac, hall⟩]
        apply valueLT_d_false_of_switch hn hV hi2 hin hei hft
        right
        refine ⟨?_, by omega, cursorBit_e_one_of_pos_lt hn (by omega) (by omega), ?_, ?_⟩
        · unfold bEff cursorBMax
          simp only [h1, Bool.false_eq_true, ite_false]
          split_ifs <;> omega
        · rw [hc_eq]
          unfold cursorBit; dsimp only
          simp only [h1, Bool.false_eq_true, ite_false, hnu]
          rfl
        · intro r hr2 hrc
          rw [hc_eq] at hrc
          unfold cursorBit; dsimp only
          simp only [h1, Bool.false_eq_true, ite_false]
          exact (bit_lt_nu hn hr2 hrc).trans h1
      · -- bit b 1 = true, nu n b < i, bit b i = false
        rcases hsw with ⟨hgt, hbi_f⟩
        have hei : cursorBit n b j .e i = false := by
          unfold cursorBit; dsimp only
          simp only [h1, ite_true]
          rw [if_neg (by omega), if_neg (by omega), if_pos (by simp [hbi_f])]
          simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
          omega
        have hc1 : cursorCMax n b j = 1 := by
          unfold cursorCMax
          simp only [h1, ite_true]
          rw [if_neg (by omega)]
        have hb_eq : cursorBMax n b j = nu n b := by
          unfold cursorBMax
          simp only [h1, ite_true]
          rw [if_pos (by omega), if_pos (by omega)]
        have hft : fTarget n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j) i =
            decisionVertex n .e i := by
          unfold fTarget
          rw [if_neg (by simp [hei]), if_neg (by simp [hpi]), if_neg (by simp [hpi]),
              if_pos (by omega : cursorCMax n b j < i)]
        apply valueLT_d_false_of_switch hn hV hi2 hin hei hft
        left
        refine ⟨by omega, by omega, ?_⟩
        rw [hb_eq]
        unfold cursorBit; dsimp only
        simp only [h1, ite_true, decide_eq_false_iff_not]
        omega
    · have hsw_f : sweepSwitch n b ⟨.d, i, false⟩ = false := by
        cases h : sweepSwitch n b ⟨.d, i, false⟩ <;> [rfl; exact False.elim (hsw h)]
      rw [hsw_f]
      simp only [Bool.false_eq_true, iff_false]
      by_cases hcase1 : bit b 1 = true ∧ i = nu n b
      · rcases hcase1 with ⟨h1, rfl⟩
        have hei : cursorBit n b j .e (nu n b) = false := by
          unfold cursorBit; dsimp only
          simp only [h1, ite_true, lt_irrefl, ite_false, decide_eq_false_iff_not]
          omega
        have hc1 : cursorCMax n b j = 1 := by
          unfold cursorCMax
          simp only [h1, ite_true]
          rw [if_neg (by omega)]
        have hb1_eq : cursorBMax n b j = 1 := by
          unfold cursorBMax; split_ifs <;> omega
        exact valueLT_asymm (valueLT_d_true_of_bmax_one_cmax_one_e_false hn hV hi2 hin hpi hei hc1 hb1_eq)
      · have hai : cursorBit n b j .a i = true := by
          unfold sweepSwitch at hsw_f
          unfold cursorBit
          dsimp only at hsw_f ⊢
          cases h1 : bit b 1
          · simp only [h1, Bool.false_eq_true, ite_false] at hcase1 hsw_f ⊢
            cases hbi : bit b i <;> [ (rw [hbi] at hsw_f; cases hsw_f); rfl ]
          · simp only [h1, ite_true, true_and] at hcase1 hsw_f ⊢
            rw [if_neg hcase1]
            by_cases hlt : i < nu n b
            · rw [if_pos hlt, decide_eq_true_iff]
              omega
            · rw [if_neg hlt]
              have hgt : nu n b < i := by omega
              rw [decide_eq_true hgt, Bool.true_and, Bool.not_eq_false'] at hsw_f
              exact hsw_f
        have hj_hi : j < 6 * n - 7 := by omega
        have hbe_rng := bEff_range hV.hb_range.1 hi2
        rcases reachMax_b_pred_to_g hn hV
          (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j)) hi2 hin
          with ⟨m0, hm0, hb_g⟩
        have hbe_ed : 2 ≤ bEff (cursorBMax n b j) i →
            cursorBit n b j .e (bEff (cursorBMax n b j) i) = true ∧
            cursorBit n b j .d (bEff (cursorBMax n b j) i) = true := by
          intro hbe2
          have heq := (bEff_eq_self_of_ge_two hbe2).1
          rw [heq]
          exact hV.hb_ed (heq ▸ hbe2)
        have hcond : cursorCMax n b j < i ∨
            (bEff (cursorBMax n b j) i = 1 ∧ cursorBit n b j .e 1 = true ∧
              ∀ r, 2 ≤ r → r < i → cursorBit n b j .a r = true → cursorBit n b j .e r = true) := by
          by_cases hci : cursorCMax n b j < i
          · exact Or.inl hci
          · right
            refine ⟨?_, cursorBit_e_one_of_pos_lt hn (by omega) hj_hi,
              fun r hr2 hri => cursorBit_a_imp_e_of_lt hn hj_hi hr2 (by omega)⟩
            unfold cursorCMax at hci
            unfold bEff cursorBMax
            split_ifs at hci ⊢ <;> omega
        rcases reachMax_u_to_a_of_to_g hn hV hi2 hin hbe_rng.1 hbe_rng.2.1 hm0 hb_g hbe_ed hcond
          with ⟨M, hM, hu⟩
        exact valueLT_asymm (valueLT_u_f_of_a_true hn hV hi2 hin hai hM hu)
  · -- one = true (j = 7 * n - 7 + (i - 2), hpi : cursorBit n b j .d i = false)
    have hsw : sweepSwitch n b ⟨.d, i, true⟩ = true := by
      unfold cursorBit at hpi
      unfold sweepSwitch
      dsimp only at hpi ⊢
      cases h1 : bit b 1
      · simp only [h1, Bool.false_eq_true, ite_false] at hpi ⊢
        cases hbi : bit b i <;> [rfl; (rw [hbi] at hpi; cases hpi)]
      · simp only [h1, ite_true] at hpi ⊢
        by_cases hgt : nu n b < i
        · cases hbi : bit b i
          · simp [hgt]
          · rw [hbi] at hpi; cases hpi
        · rw [decide_eq_false hgt, Bool.and_false, if_neg (by simp)] at hpi
          cases hpi
    refine ⟨fun _ => hsw, fun _ => ?_⟩
    unfold sweepSwitch at hsw
    dsimp only at hsw
    have ⟨hei, hci, hbc⟩ :
        cursorBit n b j .e i = false ∧
        cursorCMax n b j < i ∧
        cursorBMax n b j = cursorCMax n b j := by
      unfold cursorBit cursorCMax cursorBMax
      dsimp only
      cases h1 : bit b 1
      · simp only [h1, Bool.false_eq_true, ite_false, Bool.not_eq_true'] at hsw ⊢
        refine ⟨?_, ?_, ?_⟩
        · rw [if_neg (by omega), if_pos (by simp [hsw])]
          simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
          omega
        · rw [if_pos (by omega)]
          omega
        · split_ifs <;> omega
      · simp only [h1, ite_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hsw ⊢
        rcases hsw with ⟨hgt, hbi_f⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [if_neg (by omega), if_neg (by omega), if_pos (by simp [hbi_f])]
          simp only [decide_eq_false_iff_not]
          omega
        · rw [if_pos (by omega)]
          exact hgt
        · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    exact valueLT_d_true_of_d_false_e_false hn hV hi2 hin hpi hei hci hbc

lemma improving_at_cursor_e {n b i : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (one : Bool) (hv_valid : ValidRow n (.e, i)) (j : ℕ)
    (hv_rank : columnRank n ⟨.e, i, one⟩ = j)
    (hpi : cursorBit n b j .e i = !one) :
    ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.e, i, !one⟩))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (actionTarget n ⟨.e, i, one⟩)) ↔
    sweepSwitch n b ⟨.e, i, one⟩ = true := by
  have hV := cursorPolicy_valid hn hb1 hb2 (j := j)
  have hm := nu_range (b := b) hn
  have hnu := bit_nu hn hb1 hb2
  have hi1 : 1 ≤ i := hv_valid.1
  have hin : i ≤ n := hv_valid.2
  unfold columnRank at hv_rank
  cases one <;> dsimp only at hv_rank ⊢ <;>
    simp only [Bool.not_false, Bool.not_true] at hpi ⊢
  · -- one = false (j = 6 * n - 7 + (i - 1), hpi : cursorBit n b j .e i = true)
    change ValueLT (parityGame n)
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (fVertex n i))
      (FriedmannParity.playValue (parityGame n) (policyStrategy n (cursorBit n b j))
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        (sVertex n)) ↔ _
    by_cases hsw : sweepSwitch n b ⟨.e, i, false⟩ = true
    · refine ⟨fun _ => hsw, fun _ => ?_⟩
      unfold sweepSwitch at hsw
      dsimp only at hsw
      by_cases hlt_case : bit b 1 = true ∧ i < nu n b
      · rcases hlt_case with ⟨h1, hilt⟩
        have hc_eq : cursorCMax n b j = nu n b := by
          unfold cursorCMax
          simp only [h1, ite_true]
          rw [if_pos (by omega)]
        have hac_f : cursorBit n b j .a (cursorCMax n b j) = false := by
          rw [hc_eq]
          unfold cursorBit; dsimp only
          simp only [h1, ite_true, decide_eq_false_iff_not]
          omega
        have hd : i = 1 ∨ cursorBit n b j .d i = true := by
          by_cases hi_eq_1 : i = 1
          · exact Or.inl hi_eq_1
          · right
            unfold cursorBit; dsimp only
            simp only [h1, ite_true]
            rw [if_neg (by simp; omega)]
        exact valueLT_e_false_of_lt_cmax_a_false hn hV hi1 hin (by omega) hac_f hpi hd
      · have ⟨hi2, hbi_f, hgt_imp⟩ : 2 ≤ i ∧ bit b i = false ∧ (bit b 1 = true → nu n b < i) := by
          cases h1 : bit b 1
          · simp only [h1, Bool.false_eq_true, ite_false, Bool.and_eq_true,
              Bool.not_eq_true', decide_eq_true_eq] at hsw
            exact ⟨hsw.1, hsw.2, fun h => by cases h⟩
          · simp only [h1, ite_true, true_and, Bool.or_eq_true, Bool.and_eq_true,
              Bool.not_eq_true', decide_eq_true_eq] at hlt_case hsw
            rcases hsw with hlt | ⟨hgt, hbi_f⟩
            · exact False.elim (hlt_case hlt)
            · exact ⟨by omega, hbi_f, fun _ => hgt⟩
        have hdi_f : cursorBit n b j .d i = false := by
          unfold cursorBit; dsimp only
          cases h1 : bit b 1 <;> simp only [Bool.false_eq_true, ite_true, ite_false]
          · rw [if_pos (by simp [hbi_f])]
            simp only [decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq]
            omega
          · have hgt := hgt_imp h1
            rw [if_pos (by simp [hbi_f, hgt])]
            simp only [decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq]
            omega
        have ⟨hci, hbc⟩ : cursorCMax n b j < i ∧ cursorBMax n b j = cursorCMax n b j := by
          unfold cursorCMax cursorBMax
          cases h1 : bit b 1 <;> simp only [Bool.false_eq_true, ite_true, ite_false]
          · refine ⟨by rw [if_pos (by omega)]; omega, ?_⟩
            split_ifs <;> omega
          · have hgt := hgt_imp h1
            refine ⟨by rw [if_pos (by omega)]; exact hgt, ?_⟩
            rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
        exact valueLT_e_false_of_d_false_cmax_eq_bmax hn hV hi2 hin hdi_f hpi hci hbc
    · have hsw_f : sweepSwitch n b ⟨.e, i, false⟩ = false := by
        cases h : sweepSwitch n b ⟨.e, i, false⟩ <;> [rfl; exact False.elim (hsw h)]
      rw [hsw_f]
      simp only [Bool.false_eq_true, iff_false]
      have hcases : i = cursorCMax n b j ∨ (cursorCMax n b j < i ∧ cursorBit n b j .a i = true) := by
        unfold sweepSwitch at hsw_f
        unfold cursorCMax cursorBit
        dsimp only at hsw_f ⊢
        cases h1 : bit b 1
        · simp only [h1, Bool.false_eq_true, ite_false] at hsw_f ⊢
          rw [if_pos (by omega)]
          by_cases hi_eq_1 : i = 1
          · exact Or.inl hi_eq_1
          · right
            refine ⟨by omega, ?_⟩
            rw [decide_eq_true (by omega : 2 ≤ i), Bool.true_and, Bool.not_eq_false'] at hsw_f
            exact hsw_f
        · simp only [h1, ite_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hsw_f ⊢
          rw [if_pos (by omega)]
          rcases hsw_f with ⟨hnot_lt, hnot_gt⟩
          by_cases heq : i = nu n b
          · exact Or.inl heq
          · right
            have hgt : nu n b < i := by omega
            rw [decide_eq_true hgt, Bool.true_and, Bool.not_eq_false'] at hnot_gt
            refine ⟨hgt, ?_⟩
            rw [if_neg heq, if_neg hnot_lt]
            exact hnot_gt
      exact valueLT_asymm (valueLT_e_true_of_eq_cmax_or_gt_cmax_a_true hn hV hi1 hin hcases)
  · -- one = true (hpi : cursorBit n b j .e i = false)
    have hsw : sweepSwitch n b ⟨.e, i, true⟩ = true := by
      unfold cursorBit at hpi
      unfold sweepSwitch
      dsimp only at hpi ⊢
      cases h1 : bit b 1
      · simp only [h1, Bool.false_eq_true, ite_false] at hpi ⊢
        by_cases hi_eq_1 : i = 1
        · simp [hi_eq_1]
        · rw [if_neg hi_eq_1] at hv_rank hpi
          cases hbi : bit b i <;> [simp [hi_eq_1]; (rw [hbi] at hpi; cases hpi)]
      · simp only [h1, ite_true] at hpi ⊢
        by_cases hlt : i < nu n b
        · rw [if_pos hlt, decide_eq_false_iff_not] at hpi
          split_ifs at hv_rank <;> omega
        · by_cases heq : i = nu n b
          · simp [heq]
          · have hgt : nu n b < i := by omega
            rw [if_neg hlt, if_neg heq] at hpi
            cases hbi : bit b i
            · simp [hgt]
            · rw [hbi] at hpi; cases hpi
    refine ⟨fun _ => hsw, fun _ => ?_⟩
    have hft : fTarget n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j) i =
        decisionVertex n .e i := by
      unfold sweepSwitch at hsw
      dsimp only at hsw
      unfold fTarget
      rw [if_neg (by simp [hpi]), if_neg (by simp [hpi])]
      by_cases hd_f : 1 < i ∧ cursorBit n b j .d i = false ∧ cursorBit n b j .e i = false
      · rw [if_pos hd_f]
        have hnot_cb : ¬ (cursorCMax n b j < i ∧ cursorBMax n b j = cursorCMax n b j) := by
          have hi2 : 2 ≤ i := by omega
          rw [if_neg (by omega : ¬ i = 1)] at hv_rank
          unfold cursorCMax cursorBMax
          cases h1 : bit b 1
          · simp only [Bool.false_eq_true, ite_false]
            rw [if_neg (by omega)]
            intro ⟨hgt, hbc⟩
            split_ifs at hbc <;> omega
          · simp only [ite_true]
            rw [if_neg (by omega)]
            intro ⟨_, hbc⟩
            unfold cursorBit at hd_f
            dsimp only at hd_f
            simp only [h1, ite_true] at hd_f
            have hgt : nu n b < i := by
              by_contra hle
              rw [if_neg (by simp [hle])] at hd_f
              exact Bool.false_ne_true hd_f.2.1.symm
            rw [if_pos (by omega), if_pos (by omega)] at hbc
            omega
        rw [if_neg hnot_cb]
      · rw [if_neg hd_f]
        by_cases hci : cursorCMax n b j < i
        · rw [if_pos hci]
        · rw [if_neg hci]
          have h1_f : bit b 1 = false := by
            cases h1 : bit b 1
            · rfl
            · exfalso
              unfold cursorCMax at hci
              simp only [h1, ite_true] at hci hsw
              rw [if_neg (by split_ifs at hv_rank <;> omega)] at hci
              simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsw
              rcases hsw with rfl | ⟨hgt, _⟩ <;> omega
          have hc_eq : cursorCMax n b j = nu n b := by
            unfold cursorCMax
            simp only [h1_f, Bool.false_eq_true, ite_false]
            rw [if_neg (by split_ifs at hv_rank <;> omega)]
          have hic : i < cursorCMax n b j := by
            simp only [h1_f, Bool.false_eq_true, ite_false, Bool.or_eq_true,
              Bool.not_eq_true', decide_eq_true_eq] at hsw
            rcases hsw with rfl | hbi_f
            · omega
            · have hine : i ≠ nu n b := by
                intro rfl
                rw [h1_f] at hnu
                rw [hbi_f] at hnu
                cases hnu
              omega
          have hac : cursorBit n b j .a (cursorCMax n b j) = true := by
            rw [hc_eq]
            unfold cursorBit; dsimp only
            simp only [h1_f, Bool.false_eq_true, ite_false, hnu]
            rfl
          have hall : ∀ k ∈ Finset.Ico (i + 1) (cursorCMax n b j), cursorBit n b j .a k = false := by
            intro k hk
            rw [hc_eq, Finset.mem_Ico] at hk
            unfold cursorBit; dsimp only
            simp only [h1_f, Bool.false_eq_true, ite_false]
            exact (bit_lt_nu hn (by omega) hk.2).trans h1_f
          rw [if_pos ⟨hic, hac, hall⟩]
    exact valueLT_e_true_of_fTarget_eq_e hn hV hi1 hin hpi hft

lemma improving_at_cursor_iff {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (j : Fin (cols n)) :
    FriedmannMultiplicity.Improving (parityGame n)
      (policyStrategy n (cursorBit n b j.val))
      (actionSource n j) (actionTarget n (columnName n j)) ↔
    sweepSwitch n b (columnName n j) = true := by
  have hV := cursorPolicy_valid hn hb1 hb2 (j := j.val)
  have hv_valid := columnName_valid hn j
  have hv_rank := columnRank_columnName hn j
  rw [actionSource_eq_rowVertex hn j, improving_row_iff hn hV hv_valid (columnName n j).one]
  rcases hv : columnName n j with ⟨k, i, one⟩
  rw [hv] at hv_valid hv_rank
  dsimp only at hv_valid ⊢
  by_cases hpi : cursorBit n b j.val k i = one
  · constructor
    · intro hlt
      rw [hpi] at hlt
      exact False.elim (valueLT_asymm hlt hlt)
    · intro hsw
      have hnot := (cursorBit_step_same hn hb1 hb2 j).2
      rw [hv] at hnot
      have hpi_not := hnot hsw
      dsimp only at hpi_not
      rw [hpi] at hpi_not
      cases one <;> cases hpi_not
  · have hpi_not : cursorBit n b j.val k i = !one := by
      cases h1 : cursorBit n b j.val k i <;> cases h2 : one <;> simp_all
    rw [hpi_not]
    cases k
    · exact improving_at_cursor_a hn hb1 hb2 one hv_valid j.val hv_rank hpi_not
    · exact improving_at_cursor_b hn hb1 hb2 one hv_valid j.val hv_rank hpi_not
    · exact improving_at_cursor_c hn hb1 hb2 one hv_valid j.val hv_rank hpi_not
    · exact improving_at_cursor_d hn hb1 hb2 one hv_valid j.val hv_rank hpi_not
    · exact improving_at_cursor_e hn hb1 hb2 one hv_valid j.val hv_rank hpi_not

lemma testBit_two_pow_sub_one : ∀ (d k : ℕ), k < d → (2 ^ d - 1).testBit k = true
  | 0, _, hk => by omega
  | d + 1, k, hk => by
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have hpos : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [Nat.testBit_zero, decide_eq_true_iff]
      omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hdiv : (2 ^ (d + 1) - 1) / 2 = 2 ^ d - 1 := by omega
      rw [Nat.testBit_succ, hdiv]
      exact testBit_two_pow_sub_one d k' (by omega)

lemma bit_two_pow_sub_two {n : ℕ} (hn : 3 ≤ n) :
    bit (2 ^ n - 2) 1 = false ∧
    (∀ i, 2 ≤ i → i ≤ n → bit (2 ^ n - 2) i = true) ∧
    nu n (2 ^ n - 2) = 2 := by
  have hpow : 8 ≤ 2 ^ n := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have h1 : bit (2 ^ n - 2) 1 = false := by
    change (2 ^ n - 2).testBit 0 = false
    rw [Nat.testBit_zero, decide_eq_false_iff_not]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  have hev := bit_succ_of_even h1
  have hsucc : 2 ^ n - 2 + 1 = 2 ^ n - 1 := by omega
  have hi : ∀ i, 2 ≤ i → i ≤ n → bit (2 ^ n - 2) i = true := by
    intro i hi2 hin
    have h_eq := (hev.2 i hi2).symm
    rw [hsucc] at h_eq
    rw [h_eq]
    exact testBit_two_pow_sub_one n (i - 1) (by omega)
  have hnu : nu n (2 ^ n - 2) = 2 := by
    apply nu_eq_of_isMin hn (by omega) le_rfl le_rfl (by omega)
    · rw [hi 2 le_rfl (by omega), h1]; rfl
    · intro j hj2 hjlt; omega
  exact ⟨h1, hi, hnu⟩

lemma not_improvable_terminal {n : ℕ} (hn : 3 ≤ n) :
    ¬ FriedmannMultiplicity.Improvable (parityGame n)
      (policyStrategy n (cursorBit n (2 ^ n - 2) (4 * n - 3))) := by
  have hpow : 8 ≤ 2 ^ n := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have hb1 : 1 ≤ 2 ^ n - 2 := by omega
  have hb2 : 2 ^ n - 2 ≤ 2 ^ n - 2 := le_rfl
  set b := 2 ^ n - 2
  set j := 4 * n - 3
  have hV := cursorPolicy_valid hn hb1 hb2 (j := j)
  obtain ⟨hbit1, hbiti, hnu2⟩ := bit_two_pow_sub_two hn
  have hc1 : cursorCMax n b j = 1 := by
    unfold cursorCMax
    rw [hbit1, hnu2]
    simp only [Bool.false_eq_true, ite_false]
    rw [if_pos (by omega)]
  have hb_max1 : cursorBMax n b j = 1 := by
    unfold cursorBMax
    rw [hbit1, hnu2]
    simp only [Bool.false_eq_true, ite_false]
    split_ifs <;> omega
  have ha_t : ∀ i, 2 ≤ i → i ≤ n → cursorBit n b j .a i = true := by
    intro i hi2 hin
    unfold cursorBit; dsimp only
    rw [if_neg (by rw [hbit1]; decide)]
    exact hbiti i hi2 hin
  have hd_t : ∀ i, 2 ≤ i → i ≤ n → cursorBit n b j .d i = true := by
    intro i hi2 hin
    unfold cursorBit; dsimp only
    rw [hbiti i hi2 hin]
    rfl
  have hb_f : ∀ i, 2 ≤ i → i ≤ n - 1 → cursorBit n b j .b i = false := by
    intro i hi2 _
    unfold cursorBit; dsimp only
    rw [hb_max1, decide_eq_false_iff_not]
    omega
  have hc_f : ∀ i, 2 ≤ i → i ≤ n → cursorBit n b j .c i = false := by
    intro i hi2 _
    unfold cursorBit; dsimp only
    rw [hc1, decide_eq_false_iff_not]
    omega
  have he_t : ∀ i, 1 ≤ i → i ≤ n → cursorBit n b j .e i = true := by
    intro i hi1 hin
    unfold cursorBit; dsimp only
    rw [hbit1]
    simp only [Bool.false_eq_true, ite_false]
    by_cases hi1_eq : i = 1
    · rw [if_pos hi1_eq, decide_eq_true_iff]
      omega
    · rw [if_neg hi1_eq, hbiti i (by omega) hin]
      rfl
  intro ⟨v, w, himp⟩
  have howner : (parityGame n).owner v = false := himp.1
  have hv : v.val < rows n := by
    unfold parityGame at howner
    dsimp only at howner
    rw [decide_eq_false_iff_not] at howner
    omega
  set r : Fin (rows n) := ⟨v.val, hv⟩
  have hp_r : ValidRow n (rowName n r) := rowName_valid hn r
  have hv_eq : v = rowVertex n (rowName n r) := by
    apply Fin.ext
    rw [val_rowVertex hn hp_r, rowRank_rowName hn r]
  have hw_mem : w ∈ gameSuccessors n v := himp.2.1
  unfold gameSuccessors at hw_mem
  rw [dif_pos hv] at hw_mem
  dsimp only at hw_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem
  have ⟨one, hw_eq⟩ : ∃ one : Bool, w = actionTarget n ⟨(rowName n r).1, (rowName n r).2, one⟩ := by
    rcases hw_mem with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  rw [hv_eq, hw_eq] at himp
  rcases hr_eq : rowName n r with ⟨k, i⟩
  have hp : ValidRow n (k, i) := hr_eq ▸ hp_r
  rw [hr_eq] at himp
  rw [improving_row_iff hn hV hp one] at himp
  by_cases hpi : cursorBit n b j k i = one
  · rw [hpi] at himp
    exact valueLT_asymm himp himp
  · cases k <;> unfold ValidRow at hp <;> dsimp only at hp
    · have hai := ha_t i hp.1 hp.2
      have hone : one = false := by cases one <;> simp_all
      rw [hai, hone] at himp
      exact valueLT_asymm
        (valueLT_a_true_of_ed hn hV hp.1 hp.2 (hd_t i hp.1 hp.2) (he_t i (by omega) hp.2)) himp
    · have hbi := hb_f i hp.1 hp.2
      have hone : one = true := by cases one <;> simp_all
      rw [hbi, hone] at himp
      have hbe_rng := bEff_range hV.hb_range.1 hp.1
      rcases reachMax_b_pred_to_g hn hV
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        hp.1 (by omega) with ⟨m0, hm0, hb_g⟩
      have hbe1 : bEff (cursorBMax n b j) i = 1 := by unfold bEff; rw [hb_max1, ite_self]
      have hbe_ed : 2 ≤ bEff (cursorBMax n b j) i →
          cursorBit n b j .e (bEff (cursorBMax n b j) i) = true ∧
          cursorBit n b j .d (bEff (cursorBMax n b j) i) = true := fun _ => by omega
      have hcond : cursorCMax n b j < i ∨
          (bEff (cursorBMax n b j) i = 1 ∧ cursorBit n b j .e 1 = true ∧
            ∀ q, 2 ≤ q → q < i → cursorBit n b j .a q = true → cursorBit n b j .e q = true) :=
        Or.inl (by omega)
      rcases reachMax_u_to_a_of_to_g hn hV hp.1 (by omega) hbe_rng.1 hbe_rng.2.1 hm0 hb_g hbe_ed hcond
        with ⟨M, hM, hu⟩
      exact valueLT_asymm (valueLT_g_u_of_a_true hn hV hp.1 (by omega) (ha_t i hp.1 (by omega)) hM hu) himp
    · have hci := hc_f i hp.1 hp.2
      have hone : one = true := by cases one <;> simp_all
      rw [hci, hone] at himp
      have hce_rng := bEff_range hV.hc_range.1 hp.1
      rcases reachMax_c_pred_to_g hn hV
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        hp.1 hp.2 with ⟨m0, hm0, hc_g⟩
      have hce1 : bEff (cursorCMax n b j) i = 1 := by unfold bEff; rw [hc1, ite_self]
      have hce_ed : 2 ≤ bEff (cursorCMax n b j) i →
          cursorBit n b j .e (bEff (cursorCMax n b j) i) = true ∧
          cursorBit n b j .d (bEff (cursorCMax n b j) i) = true := fun _ => by omega
      have hcond : cursorCMax n b j < i ∨
          (bEff (cursorCMax n b j) i = 1 ∧ cursorBit n b j .e 1 = true ∧
            ∀ q, 2 ≤ q → q < i → cursorBit n b j .a q = true → cursorBit n b j .e q = true) :=
        Or.inl (by omega)
      rcases reachMax_u_to_a_of_to_g hn hV hp.1 hp.2 hce_rng.1 hce_rng.2.1 hm0 hc_g hce_ed hcond
        with ⟨M, hM, hu⟩
      exact valueLT_asymm (valueLT_g_u_of_a_true hn hV hp.1 hp.2 (ha_t i hp.1 hp.2) hM hu) himp
    · have hdi := hd_t i hp.1 hp.2
      have hone : one = false := by cases one <;> simp_all
      rw [hdi, hone] at himp
      have hbe_rng := bEff_range hV.hb_range.1 hp.1
      rcases reachMax_b_pred_to_g hn hV
        (phaseTau n (cursorBit n b j) (cursorCMax n b j) (cursorBMax n b j))
        hp.1 hp.2 with ⟨m0, hm0, hb_g⟩
      have hbe1 : bEff (cursorBMax n b j) i = 1 := by unfold bEff; rw [hb_max1, ite_self]
      have hbe_ed : 2 ≤ bEff (cursorBMax n b j) i →
          cursorBit n b j .e (bEff (cursorBMax n b j) i) = true ∧
          cursorBit n b j .d (bEff (cursorBMax n b j) i) = true := fun _ => by omega
      have hcond : cursorCMax n b j < i ∨
          (bEff (cursorBMax n b j) i = 1 ∧ cursorBit n b j .e 1 = true ∧
            ∀ q, 2 ≤ q → q < i → cursorBit n b j .a q = true → cursorBit n b j .e q = true) :=
        Or.inl (by omega)
      rcases reachMax_u_to_a_of_to_g hn hV hp.1 hp.2 hbe_rng.1 hbe_rng.2.1 hm0 hb_g hbe_ed hcond
        with ⟨M, hM, hu⟩
      exact valueLT_asymm (valueLT_u_f_of_a_true hn hV hp.1 hp.2 (ha_t i hp.1 hp.2) hM hu) himp
    · have hei := he_t i hp.1 hp.2
      have hone : one = false := by cases one <;> simp_all
      rw [hei, hone] at himp
      have hcases : i = cursorCMax n b j ∨ (cursorCMax n b j < i ∧ cursorBit n b j .a i = true) := by
        by_cases hi1_eq : i = 1
        · left; omega
        · right; exact ⟨by omega, ha_t i (by omega) hp.2⟩
      exact valueLT_asymm (valueLT_e_true_of_eq_cmax_or_gt_cmax_a_true hn hV hp.1 hp.2 hcases) himp

end CursorOptimality

/-! ### Part 6: Clockwise Sweep Trajectory and Exponential Lower Bound -/

section RunConstruction

def ReachRun (n : ℕ) (s₀ s₁ : ParityState n) (k : ℕ) : Prop :=
  ∃ s : ℕ → ParityState n,
    s 0 = s₀ ∧ s k = s₁ ∧
    (∀ t ≤ k, FriedmannParity.Legal (parityGame n) false (s t).strategy) ∧
    (∀ t < k, parityStep n (s t) (s (t + 1)))

lemma ReachRun.refl {n : ℕ} (s₀ : ParityState n)
    (hleg : FriedmannParity.Legal (parityGame n) false s₀.strategy) :
    ReachRun n s₀ s₀ 0 :=
  ⟨fun _ => s₀, rfl, rfl, fun _ _ => hleg, fun _ ht => by omega⟩

lemma ReachRun.of_eq {n : ℕ} {s₀ s₁ : ParityState n}
    (heq : s₀ = s₁) (hleg : FriedmannParity.Legal (parityGame n) false s₀.strategy) :
    ReachRun n s₀ s₁ 0 := by
  subst heq
  exact ReachRun.refl s₀ hleg

lemma ReachRun.step {n : ℕ} {s₀ s₁ : ParityState n}
    (hleg₀ : FriedmannParity.Legal (parityGame n) false s₀.strategy)
    (hleg₁ : FriedmannParity.Legal (parityGame n) false s₁.strategy)
    (hstep : parityStep n s₀ s₁) :
    ReachRun n s₀ s₁ 1 := by
  refine ⟨fun t => if t = 0 then s₀ else s₁, rfl, rfl, ?_, ?_⟩
  · intro t _
    dsimp only
    by_cases h0 : t = 0
    · rw [if_pos h0]; exact hleg₀
    · rw [if_neg h0]; exact hleg₁
  · intro t ht
    dsimp only
    have ht0 : t = 0 := by omega
    subst ht0
    exact hstep

lemma ReachRun.trans {n k₁ k₂ : ℕ} {s₀ s₁ s₂ : ParityState n}
    (h₁ : ReachRun n s₀ s₁ k₁) (h₂ : ReachRun n s₁ s₂ k₂) :
    ReachRun n s₀ s₂ (k₁ + k₂) := by
  rcases h₁ with ⟨f₁, hf₁0, hf₁k, hleg₁, hstep₁⟩
  rcases h₂ with ⟨f₂, hf₂0, hf₂k, hleg₂, hstep₂⟩
  refine ⟨fun t => if t ≤ k₁ then f₁ t else f₂ (t - k₁),
    by simp [hf₁0], ?_, ?_, ?_⟩
  · dsimp only
    by_cases hk₂ : k₂ = 0
    · subst hk₂; simp [hf₁k, ← hf₂0, hf₂k]
    · rw [if_neg (by omega), Nat.add_sub_cancel_left, hf₂k]
  · intro t ht
    dsimp only
    split_ifs with hle
    · exact hleg₁ t hle
    · exact hleg₂ (t - k₁) (by omega)
  · intro t ht
    dsimp only
    by_cases hlt : t < k₁
    · rw [if_pos (by omega : t ≤ k₁), if_pos (by omega : t + 1 ≤ k₁)]
      exact hstep₁ t hlt
    · by_cases heq : t = k₁
      · subst heq
        rw [if_pos le_rfl, if_neg (by omega), hf₁k, ← hf₂0]
        have hsub : t + 1 - t = 1 := by omega
        rw [hsub]
        exact hstep₂ 0 (by omega)
      · rw [if_neg (by omega), if_neg (by omega)]
        have hsub : t + 1 - k₁ = (t - k₁) + 1 := by omega
        rw [hsub]
        exact hstep₂ (t - k₁) (by omega)

lemma cyclicDistance_eq_of_le {n : ℕ} (last j : Fin (cols n)) (hle : last.val ≤ j.val) :
    cyclicDistance (order n) last j = j.val - last.val := by
  unfold cyclicDistance order
  dsimp only [Equiv.refl_apply]
  have h1 : j.val + cols n - last.val = cols n + (j.val - last.val) := by omega
  rw [h1, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

lemma cyclicDistance_eq_of_lt {n : ℕ} (last j : Fin (cols n)) (hlt : j.val < last.val) :
    cyclicDistance (order n) last j = cols n + j.val - last.val := by
  unfold cyclicDistance order
  dsimp only [Equiv.refl_apply]
  have h1 : j.val + cols n - last.val = cols n + j.val - last.val := by omega
  rw [h1]
  exact Nat.mod_eq_of_lt (by omega)

lemma cyclicDistance_ge_of_not_between_le {n : ℕ} (last j k : Fin (cols n))
    (hle : last.val ≤ j.val) (hnot : ¬ (last.val ≤ k.val ∧ k.val < j.val)) :
    cyclicDistance (order n) last j ≤ cyclicDistance (order n) last k := by
  rw [cyclicDistance_eq_of_le last j hle]
  by_cases hkl : last.val ≤ k.val
  · rw [cyclicDistance_eq_of_le last k hkl]
    omega
  · rw [cyclicDistance_eq_of_lt last k (by omega)]
    omega

lemma cyclicDistance_ge_of_not_between_lt {n : ℕ} (last j k : Fin (cols n))
    (hlt : j.val < last.val) (hnot : ¬ (last.val ≤ k.val ∨ k.val < j.val)) :
    cyclicDistance (order n) last j ≤ cyclicDistance (order n) last k := by
  rw [cyclicDistance_eq_of_lt last j hlt, cyclicDistance_eq_of_lt last k (by omega)]
  omega

lemma not_improving_of_strategy_eq {n : ℕ} (σ : Fin (vertices n) → Fin (vertices n))
    (v w : Fin (vertices n)) (heq : σ v = w) :
    ¬ FriedmannMultiplicity.Improving (parityGame n) σ v w := by
  intro h
  have hlt := h.2.2
  rw [heq] at hlt
  exact valueLT_asymm hlt hlt

lemma policyStrategy_cursorBit_succ_of_false {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (j : Fin (cols n)) (hsw : sweepSwitch n b (columnName n j) = false) :
    policyStrategy n (cursorBit n b (j.val + 1)) = policyStrategy n (cursorBit n b j.val) := by
  apply policyStrategy_eq_of_validRow_eq hn
  intro k i hp
  by_cases hne : (k, i) = ((columnName n j).kind, (columnName n j).level)
  · rcases Prod.ext_iff.mp hne with ⟨rfl, rfl⟩
    have hsame := (cursorBit_step_same hn hb1 hb2 j).1
    simp only [hsame, hsw, Bool.false_eq_true, ite_false]
  · exact cursorBit_step_other hn j hp hne

lemma policyStrategy_cursorBit_succ_of_true {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    (j : Fin (cols n)) (hsw : sweepSwitch n b (columnName n j) = true) :
    policyStrategy n (cursorBit n b (j.val + 1)) =
      Function.update (policyStrategy n (cursorBit n b j.val))
        (actionSource n j) (actionTarget n (columnName n j)) := by
  apply policyStrategy_eq_update_of_validRow hn j
  · intro k i hp hne
    exact cursorBit_step_other hn j hp hne
  · have hsame := (cursorBit_step_same hn hb1 hb2 j).1
    simp only [hsame, hsw, ite_true]

lemma policyStrategy_cursorBit_eq_of_no_switch {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    {j₁ : ℕ} : ∀ {j₂ : ℕ}, j₁ ≤ j₂ → j₂ ≤ cols n →
    (∀ r : Fin (cols n), j₁ ≤ r.val → r.val < j₂ → sweepSwitch n b (columnName n r) = false) →
    policyStrategy n (cursorBit n b j₂) = policyStrategy n (cursorBit n b j₁)
  | 0, hle, _, _ => by
    have : j₁ = 0 := by omega
    subst this; rfl
  | m + 1, hle, hj₂, hno => by
    by_cases heq : j₁ = m + 1
    · subst heq; rfl
    · have hle' : j₁ ≤ m := by omega
      have hstep := policyStrategy_cursorBit_succ_of_false hn hb1 hb2 ⟨m, by omega⟩
        (hno ⟨m, by omega⟩ hle' (Nat.lt_succ_self m))
      have ih := policyStrategy_cursorBit_eq_of_no_switch hn hb1 hb2 hle' (by omega)
        (fun r hr1 hr2 => hno r hr1 (by omega))
      exact hstep.trans ih

lemma policyStrategy_cursorBit_wrap {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 3) :
    policyStrategy n (cursorBit n (b + 1) 0) = policyStrategy n (cursorBit n b (cols n)) := by
  have hpow : 8 ≤ 2 ^ n := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have hb2' : b ≤ 2 ^ n - 2 := by omega
  let j_last : Fin (cols n) := ⟨cols n - 1, sub_one_lt_cols hn⟩
  have hjl : j_last.val + 1 = cols n := by
    dsimp [j_last]; have := cols_pos hn; omega
  rw [← hjl]
  obtain ⟨hw_other, hw_same, _⟩ := cursorBit_wrap hn hb1 hb2
  apply policyStrategy_eq_of_validRow_eq hn
  intro k i hp
  by_cases hne : (k, i) = ((columnName n j_last).kind, (columnName n j_last).level)
  · rcases Prod.ext_iff.mp hne with ⟨rfl, rfl⟩
    have hsame := (cursorBit_step_same hn hb1 hb2' j_last).1
    rw [hw_same, hsame]
  · have hother := cursorBit_step_other (b := b) hn j_last hp hne
    rw [hw_other k i hp hne, hother]

def CursorState (n b c : ℕ) (last : Fin (cols n)) : ParityState n where
  strategy := policyStrategy n (cursorBit n b c)
  last := last

lemma cursorState_legal {n b c : ℕ} (last : Fin (cols n)) :
    FriedmannParity.Legal (parityGame n) false (CursorState n b c last).strategy :=
  policyStrategy_legal n (cursorBit n b c)

def Phase2Inv (n b c : ℕ) (last : Fin (cols n)) : Prop :=
  last.val < c ∧ c ≤ cols n ∧
  policyStrategy n (cursorBit n b (last.val + 1)) (actionSource n last) =
    actionTarget n (columnName n last) ∧
  ∀ r : Fin (cols n), last.val < r.val → r.val < c → sweepSwitch n b (columnName n r) = false

def Phase1Inv (n b c : ℕ) (last : Fin (cols n)) : Prop :=
  c ≤ last.val ∧
  (∀ r : Fin (cols n), last.val ≤ r.val →
    ¬ FriedmannMultiplicity.Improving (parityGame n)
      (policyStrategy n (cursorBit n b 0))
      (actionSource n r) (actionTarget n (columnName n r))) ∧
  (∀ r : Fin (cols n), r.val < c → sweepSwitch n b (columnName n r) = false)

lemma phase2_step_col {n b c : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    {last : Fin (cols n)} (hc : c < cols n) (hP2 : Phase2Inv n b c last) :
    let jc : Fin (cols n) := ⟨c, hc⟩
    if sweepSwitch n b (columnName n jc) = true then
      Phase2Inv n b (c + 1) jc ∧
      ReachRun n (CursorState n b c last) (CursorState n b (c + 1) jc) 1
    else
      Phase2Inv n b (c + 1) last ∧
      CursorState n b (c + 1) last = CursorState n b c last := by
  dsimp only
  set jc : Fin (cols n) := ⟨c, hc⟩
  rcases hP2 with ⟨hlt, _, hlast_eq, hno⟩
  by_cases hsw : sweepSwitch n b (columnName n jc) = true
  · rw [if_pos hsw]
    have h_upd := policyStrategy_cursorBit_succ_of_true hn hb1 hb2 jc hsw
    have hP2_next : Phase2Inv n b (c + 1) jc := by
      refine ⟨by dsimp [jc]; omega, by omega, ?_, ?_⟩
      · rw [h_upd, Function.update_self]
      · intro r hr1 hr2
        dsimp [jc] at hr1
        omega
    refine ⟨hP2_next, ReachRun.step (cursorState_legal last) (cursorState_legal jc) ?_⟩
    refine ⟨jc, ?_, ?_, h_upd, rfl⟩
    · exact (improving_at_cursor_iff hn hb1 hb2 jc).mpr hsw
    · intro k hk_imp
      apply cyclicDistance_ge_of_not_between_le last jc k (by dsimp [jc]; omega)
      intro ⟨hkl, hkc⟩
      dsimp [jc] at hkc
      by_cases hk_eq : k = last
      · subst hk_eq
        have h_strat_eq := policyStrategy_cursorBit_eq_of_no_switch hn hb1 hb2
          (by omega : k.val + 1 ≤ c) (by omega) hno
        change FriedmannMultiplicity.Improving (parityGame n)
          (policyStrategy n (cursorBit n b c)) (actionSource n k) (actionTarget n (columnName n k)) at hk_imp
        rw [h_strat_eq] at hk_imp
        exact not_improving_of_strategy_eq _ _ _ hlast_eq hk_imp
      · have hkl_lt : last.val < k.val := by
          have : k.val ≠ last.val := fun h => hk_eq (Fin.ext h)
          omega
        have h_strat_eq := policyStrategy_cursorBit_eq_of_no_switch hn hb1 hb2
          (by omega : k.val ≤ c) (by omega) (fun r hr1 hr2 => hno r (by omega) hr2)
        change FriedmannMultiplicity.Improving (parityGame n)
          (policyStrategy n (cursorBit n b c)) (actionSource n k) (actionTarget n (columnName n k)) at hk_imp
        rw [h_strat_eq, improving_at_cursor_iff hn hb1 hb2 k] at hk_imp
        rw [hno k hkl_lt hkc] at hk_imp
        cases hk_imp
  · rw [if_neg hsw]
    have hsw_f : sweepSwitch n b (columnName n jc) = false := by
      cases h : sweepSwitch n b (columnName n jc) <;> [rfl; exact False.elim (hsw h)]
    have h_eq := policyStrategy_cursorBit_succ_of_false hn hb1 hb2 jc hsw_f
    refine ⟨⟨by omega, by omega, hlast_eq, ?_⟩, ?_⟩
    · intro r hr1 hr2
      by_cases hrc : r.val < c
      · exact hno r hr1 hrc
      · have hr_eq : r = jc := Fin.ext (by dsimp [jc]; omega)
        rw [hr_eq]
        exact hsw_f
    · unfold CursorState
      change (⟨policyStrategy n (cursorBit n b (jc.val + 1)), last⟩ : ParityState n) =
        ⟨policyStrategy n (cursorBit n b jc.val), last⟩
      rw [h_eq]

lemma phase2_advance {n b c₁ : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    {last₀ : Fin (cols n)} (hP2 : Phase2Inv n b c₁ last₀) :
    ∀ {c₂ : ℕ}, c₁ ≤ c₂ → c₂ ≤ cols n →
    (Phase2Inv n b c₂ last₀ ∧
      (∀ r : Fin (cols n), c₁ ≤ r.val → r.val < c₂ → sweepSwitch n b (columnName n r) = false) ∧
      CursorState n b c₂ last₀ = CursorState n b c₁ last₀) ∨
    (∃ last' k, c₁ ≤ last'.val ∧ 1 ≤ k ∧ Phase2Inv n b c₂ last' ∧
      ReachRun n (CursorState n b c₁ last₀) (CursorState n b c₂ last') k)
  | 0, hle, _ => by
    have : c₁ = 0 := by omega
    subst this
    exact Or.inl ⟨hP2, fun _ _ hr2 => by omega, rfl⟩
  | c + 1, hle, hc₂ => by
    by_cases heq : c₁ = c + 1
    · subst heq
      exact Or.inl ⟨hP2, fun _ hr1 hr2 => by omega, rfl⟩
    · have hle' : c₁ ≤ c := by omega
      have hc_lt : c < cols n := by omega
      let jc : Fin (cols n) := ⟨c, hc_lt⟩
      rcases phase2_advance hn hb1 hb2 hP2 hle' (by omega) with
        ⟨hP2_c, hno_c, heq_c⟩ | ⟨last', k, hlast_ge, hk1, hP2_c, hrun_c⟩
      · have hstep := phase2_step_col hn hb1 hb2 hc_lt hP2_c
        dsimp only at hstep
        by_cases hsw : sweepSwitch n b (columnName n jc) = true
        · rw [if_pos hsw] at hstep
          right
          refine ⟨jc, 1, hle', le_rfl, hstep.1, ?_⟩
          rw [← heq_c]
          exact hstep.2
        · rw [if_neg hsw] at hstep
          have hsw_f : sweepSwitch n b (columnName n jc) = false := by
            cases h : sweepSwitch n b (columnName n jc) <;> [rfl; exact False.elim (hsw h)]
          left
          refine ⟨hstep.1, ?_, hstep.2.trans heq_c⟩
          intro r hr1 hr2
          by_cases hrc : r.val < c
          · exact hno_c r hr1 hrc
          · have hr_eq : r = jc := Fin.ext (by dsimp [jc]; omega)
            rw [hr_eq]
            exact hsw_f
      · have hstep := phase2_step_col hn hb1 hb2 hc_lt hP2_c
        dsimp only at hstep
        by_cases hsw : sweepSwitch n b (columnName n jc) = true
        · rw [if_pos hsw] at hstep
          right
          exact ⟨jc, k + 1, hle', by omega, hstep.1, hrun_c.trans hstep.2⟩
        · rw [if_neg hsw] at hstep
          right
          refine ⟨last', k, hlast_ge, hk1, hstep.1, ?_⟩
          rw [hstep.2]
          exact hrun_c

lemma phase2_advance_of_switch {n b c₁ c₂ : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    {last₀ : Fin (cols n)} (hP2 : Phase2Inv n b c₁ last₀) (hc₂ : c₂ ≤ cols n)
    {j_wit : Fin (cols n)} (hw1 : c₁ ≤ j_wit.val) (hw2 : j_wit.val < c₂)
    (hsw : sweepSwitch n b (columnName n j_wit) = true) :
    ∃ last' k, c₁ ≤ last'.val ∧ 1 ≤ k ∧ Phase2Inv n b c₂ last' ∧
      ReachRun n (CursorState n b c₁ last₀) (CursorState n b c₂ last') k := by
  rcases phase2_advance hn hb1 hb2 hP2 (by omega : c₁ ≤ c₂) hc₂ with
    ⟨_, hno, _⟩ | h_right
  · exfalso
    have hf := hno j_wit hw1 hw2
    rw [hsw] at hf
    cases hf
  · exact h_right

lemma phase2_to_phase1_wrap {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 3)
    {last : Fin (cols n)} (hP2 : Phase2Inv n b (cols n) last) :
    CursorState n b (cols n) last = CursorState n (b + 1) 0 last ∧
    Phase1Inv n (b + 1) 0 last := by
  have hpow : 8 ≤ 2 ^ n := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have hb2' : b ≤ 2 ^ n - 2 := by omega
  have hwrap := policyStrategy_cursorBit_wrap hn hb1 hb2
  refine ⟨by unfold CursorState; rw [hwrap], Nat.zero_le _, ?_, fun _ hr => by omega⟩
  intro r hr_ge
  rw [hwrap]
  rcases hP2 with ⟨hlt, _, hlast_eq, hno⟩
  by_cases hr_eq : r = last
  · subst hr_eq
    have h_strat_eq := policyStrategy_cursorBit_eq_of_no_switch hn hb1 hb2'
      (by omega : r.val + 1 ≤ cols n) le_rfl hno
    rw [h_strat_eq]
    exact not_improving_of_strategy_eq _ _ _ hlast_eq
  · have hr_gt : last.val < r.val := by
      have : r.val ≠ last.val := fun h => hr_eq (Fin.ext h)
      omega
    have h_strat_eq := policyStrategy_cursorBit_eq_of_no_switch hn hb1 hb2'
      (by omega : r.val ≤ cols n) le_rfl (fun q hq1 hq2 => hno q (by omega) hq2)
    rw [h_strat_eq, improving_at_cursor_iff hn hb1 hb2' r, hno r hr_gt r.isLt]
    exact Bool.false_ne_true

lemma phase1_step_col {n b c : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    {last : Fin (cols n)} (hc : c < last.val) (hP1 : Phase1Inv n b c last) :
    let jc : Fin (cols n) := ⟨c, by omega⟩
    if sweepSwitch n b (columnName n jc) = true then
      Phase2Inv n b (c + 1) jc ∧
      ReachRun n (CursorState n b c last) (CursorState n b (c + 1) jc) 1
    else
      Phase1Inv n b (c + 1) last ∧
      CursorState n b (c + 1) last = CursorState n b c last := by
  dsimp only
  set jc : Fin (cols n) := ⟨c, by omega⟩
  rcases hP1 with ⟨_, hno_after, hno_before⟩
  by_cases hsw : sweepSwitch n b (columnName n jc) = true
  · rw [if_pos hsw]
    have h_upd := policyStrategy_cursorBit_succ_of_true hn hb1 hb2 jc hsw
    have hP2_next : Phase2Inv n b (c + 1) jc := by
      refine ⟨by dsimp [jc]; omega, by omega, ?_, ?_⟩
      · rw [h_upd, Function.update_self]
      · intro r hr1 hr2
        dsimp [jc] at hr1
        omega
    refine ⟨hP2_next, ReachRun.step (cursorState_legal last) (cursorState_legal jc) ?_⟩
    refine ⟨jc, ?_, ?_, h_upd, rfl⟩
    · exact (improving_at_cursor_iff hn hb1 hb2 jc).mpr hsw
    · intro k hk_imp
      apply cyclicDistance_ge_of_not_between_lt last jc k hc
      intro h_or
      have h_strat_0 := policyStrategy_cursorBit_eq_of_no_switch hn hb1 hb2
        (Nat.zero_le c) (by omega) (fun r _ hr2 => hno_before r hr2)
      change FriedmannMultiplicity.Improving (parityGame n)
        (policyStrategy n (cursorBit n b c)) (actionSource n k) (actionTarget n (columnName n k)) at hk_imp
      rcases h_or with hkl | hkc
      · rw [h_strat_0] at hk_imp
        exact hno_after k hkl hk_imp
      · dsimp [jc] at hkc
        have h_strat_k := policyStrategy_cursorBit_eq_of_no_switch hn hb1 hb2
          (by omega : k.val ≤ c) (by omega) (fun r _ hr2 => hno_before r hr2)
        rw [h_strat_k, improving_at_cursor_iff hn hb1 hb2 k] at hk_imp
        rw [hno_before k hkc] at hk_imp
        cases hk_imp
  · rw [if_neg hsw]
    have hsw_f : sweepSwitch n b (columnName n jc) = false := by
      cases h : sweepSwitch n b (columnName n jc) <;> [rfl; exact False.elim (hsw h)]
    have h_eq := policyStrategy_cursorBit_succ_of_false hn hb1 hb2 jc hsw_f
    refine ⟨⟨by omega, hno_after, ?_⟩, ?_⟩
    · intro r hr
      by_cases hrc : r.val < c
      · exact hno_before r hrc
      · have hr_eq : r = jc := Fin.ext (by dsimp [jc]; omega)
        rw [hr_eq]
        exact hsw_f
    · unfold CursorState
      change (⟨policyStrategy n (cursorBit n b (jc.val + 1)), last⟩ : ParityState n) =
        ⟨policyStrategy n (cursorBit n b jc.val), last⟩
      rw [h_eq]

lemma phase1_advance {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    {last₀ : Fin (cols n)} (hP1 : Phase1Inv n b 0 last₀) :
    ∀ {c : ℕ}, c ≤ last₀.val →
    (Phase1Inv n b c last₀ ∧ CursorState n b c last₀ = CursorState n b 0 last₀) ∨
    (∃ last' k, 1 ≤ k ∧ Phase2Inv n b c last' ∧
      ReachRun n (CursorState n b 0 last₀) (CursorState n b c last') k)
  | 0, _ => Or.inl ⟨hP1, rfl⟩
  | c + 1, hle => by
    have hc_lt : c < last₀.val := by omega
    have hc_cols : c < cols n := by omega
    let jc : Fin (cols n) := ⟨c, hc_cols⟩
    rcases phase1_advance hn hb1 hb2 hP1 (by omega : c ≤ last₀.val) with
      ⟨hP1_c, heq_c⟩ | ⟨last', k, hk1, hP2_c, hrun_c⟩
    · have hstep := phase1_step_col hn hb1 hb2 hc_lt hP1_c
      dsimp only at hstep
      by_cases hsw : sweepSwitch n b (columnName n jc) = true
      · rw [if_pos hsw] at hstep
        right
        refine ⟨jc, 1, le_rfl, hstep.1, ?_⟩
        rw [← heq_c]
        exact hstep.2
      · rw [if_neg hsw] at hstep
        left
        exact ⟨hstep.1, hstep.2.trans heq_c⟩
    · have hstep := phase2_step_col hn hb1 hb2 hc_cols hP2_c
      dsimp only at hstep
      by_cases hsw : sweepSwitch n b (columnName n jc) = true
      · rw [if_pos hsw] at hstep
        right
        exact ⟨jc, k + 1, by omega, hstep.1, hrun_c.trans hstep.2⟩
      · rw [if_neg hsw] at hstep
        right
        refine ⟨last', k, hk1, hstep.1, ?_⟩
        rw [hstep.2]
        exact hrun_c

lemma exists_switch_block1 {n b : ℕ} (hn : 3 ≤ n) (_hb1 : 1 ≤ b) (_hb2 : b ≤ 2 ^ n - 2) :
    ∃ j : Fin (cols n),
      (bit b 1 = true → 1 ≤ j.val) ∧
      j.val < 4 * n - 5 ∧
      sweepSwitch n b (columnName n j) = true := by
  have hm := nu_range (b := b) hn
  cases h1 : bit b 1
  · let j : Fin (cols n) := ⟨0, cols_pos hn⟩
    refine ⟨j, (fun h => by cases h), show 0 < 4 * n - 5 by omega, ?_⟩
    rw [columnName_of_val j 0 rfl, if_pos rfl]
    unfold sweepSwitch
    dsimp only
    rw [h1]
    rfl
  · have hp : ValidRow n (.e, nu n b) := ⟨by omega, hm.2⟩
    let j : Fin (cols n) := ⟨columnRank n ⟨.e, nu n b, true⟩ % cols n, Nat.mod_lt _ (cols_pos hn)⟩
    have hj_eq : j.val = columnRank n ⟨.e, nu n b, true⟩ :=
      Nat.mod_eq_of_lt (columnRank_lt_cols hn (.e, nu n b) hp true)
    have hname : columnName n j = ⟨.e, nu n b, true⟩ :=
      columnName_columnRank hn (.e, nu n b) hp true _
    refine ⟨j, ?_, ?_, ?_⟩
    · intro _
      rw [hj_eq]
      unfold columnRank; dsimp only
      rw [if_neg (by omega)]
      omega
    · rw [hj_eq]
      unfold columnRank; dsimp only
      rw [if_neg (by omega)]
      omega
    · rw [hname]
      unfold sweepSwitch; dsimp only
      simp [h1]

lemma exists_switch_block2 {n b : ℕ} (hn : 3 ≤ n) (_hb1 : 1 ≤ b) (_hb2 : b ≤ 2 ^ n - 2) :
    ∃ j : Fin (cols n),
      4 * n - 5 ≤ j.val ∧
      (nu n b = 2 ∧ bit b 1 = false → j.val < 4 * n - 3) ∧
      sweepSwitch n b (columnName n j) = true := by
  have hm := nu_range (b := b) hn
  have hp : ValidRow n (.c, nu n b) := hm
  let j : Fin (cols n) := ⟨columnRank n ⟨.c, nu n b, bit b 1⟩ % cols n, Nat.mod_lt _ (cols_pos hn)⟩
  have hj_eq : j.val = columnRank n ⟨.c, nu n b, bit b 1⟩ :=
    Nat.mod_eq_of_lt (columnRank_lt_cols hn (.c, nu n b) hp (bit b 1))
  have hname : columnName n j = ⟨.c, nu n b, bit b 1⟩ :=
    columnName_columnRank hn (.c, nu n b) hp (bit b 1) _
  refine ⟨j, ?_, ?_, ?_⟩
  · rw [hj_eq]
    cases bit b 1 <;> (unfold columnRank; dsimp only; omega)
  · intro ⟨hnu2, h1⟩
    rw [hj_eq, hnu2, h1]
    unfold columnRank; dsimp only; omega
  · rw [hname]
    unfold sweepSwitch
    cases h1 : bit b 1 <;> simp

lemma phase1_to_phase2_block1 {n b : ℕ} (hn : 3 ≤ n) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 ^ n - 2)
    {last₀ : Fin (cols n)} (hP1 : Phase1Inv n b 0 last₀) (hlast : 4 * n - 5 ≤ last₀.val) :
    ∃ last' k, 1 ≤ k ∧ Phase2Inv n b (4 * n - 5) last' ∧
      ReachRun n (CursorState n b 0 last₀) (CursorState n b (4 * n - 5) last') k := by
  rcases phase1_advance hn hb1 hb2 hP1 hlast with ⟨hP1_end, _⟩ | h_right
  · exfalso
    obtain ⟨j_e, _, hje_lt, hje_sw⟩ := exists_switch_block1 hn hb1 hb2
    have hf := hP1_end.2.2 j_e hje_lt
    rw [hje_sw] at hf
    cases hf
  · exact h_right

lemma bit_one_vals {n : ℕ} (hn : 3 ≤ n) :
    bit 1 1 = true ∧ (∀ i, 2 ≤ i → bit 1 i = false) ∧ nu n 1 = 2 := by
  have hpow : 8 ≤ 2 ^ n := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have h1 : bit 1 1 = true := rfl
  have hi : ∀ i, 2 ≤ i → bit 1 i = false := by
    intro i hi2
    unfold bit
    obtain ⟨k, hk⟩ : ∃ k, i - 1 = k + 1 := ⟨i - 2, by omega⟩
    rw [hk, Nat.testBit_succ]
    simp
  have hnu : nu n 1 = 2 := by
    apply nu_eq_of_isMin hn le_rfl (by omega) le_rfl (by omega)
    · rw [hi 2 le_rfl, h1]; rfl
    · intro j hj2 hjlt; omega
  exact ⟨h1, hi, hnu⟩

lemma initialParityState_eq_cursorState {n : ℕ} (hn : 3 ≤ n) :
    initialParityState n hn = CursorState n 1 1 ⟨0, cols_pos hn⟩ := by
  obtain ⟨hbit1, hbiti, hnu2⟩ := bit_one_vals hn
  unfold initialParityState CursorState
  congr 1
  funext v
  unfold initialStrategy policyStrategy
  by_cases hv : v.val < rows n
  · rw [dif_pos hv, dif_pos hv]
    dsimp only
    set r := rowName n ⟨v.val, hv⟩
    have hr_valid : ValidRow n r := rowName_valid hn ⟨v.val, hv⟩
    rcases r with ⟨k, i⟩
    congr 2
    dsimp only at hr_valid ⊢
    symm
    cases k <;> unfold ValidRow at hr_valid <;> dsimp only at hr_valid
    · -- .a
      have h_init : initialBit (.a, i) = false := rfl
      rw [h_init]
      unfold cursorBit; dsimp only
      simp only [hbit1, hnu2, ite_true]
      by_cases hi2 : i = 2
      · rw [if_pos hi2, decide_eq_false_iff_not]; omega
      · rw [if_neg hi2, if_neg (by omega), hbiti i hr_valid.1]
    · -- .b
      have h_init : initialBit (.b, i) = false := rfl
      rw [h_init]
      unfold cursorBit cursorBMax; dsimp only
      simp only [hbit1, hnu2, ite_true]
      split_ifs <;> (rw [decide_eq_false_iff_not]; omega)
    · -- .c
      have h_init : initialBit (.c, i) = false := rfl
      rw [h_init]
      unfold cursorBit cursorCMax; dsimp only
      simp only [hbit1, hnu2, ite_true]
      rw [if_neg (by omega), decide_eq_false_iff_not]; omega
    · -- .d
      have h_init : initialBit (.d, i) = true := rfl
      rw [h_init]
      unfold cursorBit; dsimp only
      have h_or : decide (1 ≤ 4 * i - 7 || 7 * n + i - 9 < 1) = true := by
        simp only [decide_eq_true_eq, Bool.or_eq_true]
        left; omega
      rw [h_or, ite_self]
    · -- .e
      unfold cursorBit; dsimp only
      simp only [hbit1, hnu2, ite_true]
      by_cases hi1 : i = 1
      · subst hi1
        have h_init : initialBit (.e, 1) = true := rfl
        rw [h_init, if_pos (by omega), decide_eq_true_iff]
        omega
      · have h_init : initialBit (.e, i) = false := by
          unfold initialBit; dsimp only
          simp [hi1]
        rw [h_init, if_neg (by omega)]
        by_cases hi2 : i = 2
        · rw [if_pos hi2, decide_eq_false_iff_not]; omega
        · rw [if_neg hi2, if_pos (by rw [hbiti i (by omega)]; rfl)]
          simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
          omega
  · rw [dif_neg hv, dif_neg hv]

lemma phase2Inv_init {n : ℕ} (hn : 3 ≤ n) :
    Phase2Inv n 1 1 ⟨0, cols_pos hn⟩ := by
  obtain ⟨hbit1, _, hnu2⟩ := bit_one_vals hn
  let last₀ : Fin (cols n) := ⟨0, cols_pos hn⟩
  have hname : columnName n last₀ = ⟨.e, 1, true⟩ := by
    rw [columnName_of_val last₀ 0 rfl, if_pos rfl]
  have hp : ValidRow n (.e, 1) := ⟨le_rfl, by omega⟩
  refine ⟨show 0 < 1 by omega, by have := cols_pos hn; omega, ?_, ?_⟩
  · change policyStrategy n (cursorBit n 1 1) (actionSource n last₀) =
      actionTarget n (columnName n last₀)
    rw [actionSource_eq_rowVertex hn last₀, hname,
        policyStrategy_rowVertex hn (cursorBit n 1 1) hp]
    have he1 : cursorBit n 1 1 .e 1 = true := by
      unfold cursorBit; dsimp only
      simp only [hbit1, hnu2, ite_true]
      rw [if_pos (by omega), decide_eq_true_iff]
      omega
    rw [he1]
  · intro r hr1 hr2
    change 0 < r.val at hr1
    omega

lemma reachRun_sweeps {n : ℕ} (hn : 3 ≤ n) :
    ∀ b, 1 ≤ b → b ≤ 2 ^ n - 3 →
    ∃ (last : Fin (cols n)) (k : ℕ),
      2 * b ≤ k ∧
      4 * n - 5 ≤ last.val ∧
      Phase2Inv n b (cols n) last ∧
      ReachRun n (initialParityState n hn) (CursorState n b (cols n) last) k
  | 0, hb1, _ => by omega
  | 1, _, hb2 => by
    have hpow : 8 ≤ 2 ^ n := by
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      omega
    have hb2' : 1 ≤ 2 ^ n - 2 := by omega
    obtain ⟨hbit1, _, _⟩ := bit_one_vals hn
    obtain ⟨j_e, hje1, hje_lt, hje_sw⟩ := exists_switch_block1 hn le_rfl hb2'
    obtain ⟨last₁, k₁, _, hk₁, hP2_1, hrun₁⟩ :=
      phase2_advance_of_switch hn le_rfl hb2' (phase2Inv_init hn)
        (by unfold cols; omega) (hje1 hbit1) hje_lt hje_sw
    obtain ⟨j_c, hjc_ge, _, hjc_sw⟩ := exists_switch_block2 hn le_rfl hb2'
    obtain ⟨last₂, k₂, hlast₂, hk₂, hP2_2, hrun₂⟩ :=
      phase2_advance_of_switch hn le_rfl hb2' hP2_1 le_rfl hjc_ge j_c.isLt hjc_sw
    refine ⟨last₂, k₁ + k₂, by omega, hlast₂, hP2_2, ?_⟩
    rw [initialParityState_eq_cursorState hn]
    exact hrun₁.trans hrun₂
  | b + 2, _, hb2 => by
    have hpow : 8 ≤ 2 ^ n := by
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      omega
    have hb_le : b + 1 ≤ 2 ^ n - 3 := by omega
    have hb2_le : b + 2 ≤ 2 ^ n - 2 := by omega
    obtain ⟨last₀, k₀, hk₀, hlast₀, hP2_0, hrun₀⟩ :=
      reachRun_sweeps hn (b + 1) (by omega) hb_le
    obtain ⟨heq_wrap, hP1_0⟩ := phase2_to_phase1_wrap hn (by omega) hb_le hP2_0
    obtain ⟨last₁, k₁, hk₁, hP2_1, hrun₁⟩ :=
      phase1_to_phase2_block1 hn (by omega) hb2_le hP1_0 hlast₀
    obtain ⟨j_c, hjc_ge, _, hjc_sw⟩ := exists_switch_block2 hn (by omega : 1 ≤ b + 2) hb2_le
    obtain ⟨last₂, k₂, hlast₂, hk₂, hP2_2, hrun₂⟩ :=
      phase2_advance_of_switch hn (by omega) hb2_le hP2_1 le_rfl hjc_ge j_c.isLt hjc_sw
    refine ⟨last₂, k₀ + k₁ + k₂, by omega, hlast₂, hP2_2, ?_⟩
    rw [heq_wrap] at hrun₀
    exact (hrun₀.trans hrun₁).trans hrun₂

theorem parity_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → ParityState n), parityRun n hn s T ∧ 2 ^ n ≤ T := by
  have hpow : 8 ≤ 2 ^ n := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  set b_end := 2 ^ n - 2
  have hb_prev1 : 1 ≤ 2 ^ n - 3 := by omega
  have hb_prev2 : 2 ^ n - 3 ≤ 2 ^ n - 3 := le_rfl
  obtain ⟨last₀, k₀, hk₀, hlast₀, hP2_0, hrun₀⟩ :=
    reachRun_sweeps hn (2 ^ n - 3) hb_prev1 hb_prev2
  have hsucc : 2 ^ n - 3 + 1 = b_end := by omega
  obtain ⟨heq_wrap, hP1_0⟩ := phase2_to_phase1_wrap hn hb_prev1 hb_prev2 hP2_0
  rw [hsucc] at heq_wrap hP1_0
  have hb_end1 : 1 ≤ b_end := by omega
  have hb_end2 : b_end ≤ 2 ^ n - 2 := le_rfl
  obtain ⟨last₁, k₁, hk₁, hP2_1, hrun₁⟩ :=
    phase1_to_phase2_block1 hn hb_end1 hb_end2 hP1_0 hlast₀
  obtain ⟨hbit1_end, _, hnu2_end⟩ := bit_two_pow_sub_two hn
  obtain ⟨j_c, hjc_ge, hjc_lt, hjc_sw⟩ := exists_switch_block2 hn hb_end1 hb_end2
  obtain ⟨last₂, k₂, _, hk₂, _, hrun₂⟩ :=
    phase2_advance_of_switch hn hb_end1 hb_end2 hP2_1
      (by unfold cols; omega : 4 * n - 3 ≤ cols n)
      hjc_ge (hjc_lt ⟨hnu2_end, hbit1_end⟩) hjc_sw
  rw [heq_wrap] at hrun₀
  have hrun_total := (hrun₀.trans hrun₁).trans hrun₂
  rcases hrun_total with ⟨s, hs0, hsT, hleg, hstep⟩
  refine ⟨k₀ + k₁ + k₂, s, ⟨hs0, hleg, hstep, ?_⟩, by omega⟩
  rw [hsT]
  exact not_improvable_terminal hn

end RunConstruction

end FriedmannCunningham

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → FriedmannCunningham.ParityState n),
      FriedmannCunningham.parityRun n hn s T ∧ 2 ^ n ≤ T :=
  FriedmannCunningham.parity_lower_bound n hn
