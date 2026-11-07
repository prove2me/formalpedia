-- Prove2me | solution 1 for FriedmannCunningham.counterstrategy
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T03:56:53.149552+00:00
-- url     : https://prove2.me/submissions/e2cf0085-fa7f-4980-b3fc-fa67948e47f6

import Definitions.Def_friedmann_cunningham
import Mathlib.Data.Fintype.Pigeonhole

set_option autoImplicit false

namespace FriedmannCunningham

open FriedmannMultiplicity

/-! ### Part 1: Total Preorder of `FriedmannMultiplicity.ValueLE` -/

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

end GeneralOrder

/-! ### Part 2: General Finite-Orbit and `playValue` Unfolding Lemmas -/

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
lemma exists_pos_play_eq_self_of_mem_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v)) :
    ∃ L > 0, FriedmannParity.play G σ τ w L = w := by
  rw [mem_recurring_iff] at hw
  rcases hw 0 with ⟨t₀, _, ht₀⟩
  rcases hw (t₀ + 1) with ⟨k, htk, hk⟩
  refine ⟨k - t₀, by omega, ?_⟩
  have hadd : t₀ + (k - t₀) = k := by omega
  rw [← ht₀, ← play_add, hadd, hk, ht₀]

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

lemma playValue_eq_of_eq_cycleLeader {G : FriedmannParity.Game V} {σ τ : V → V} {u : V}
    (hu : u = cycleLeader G σ τ u) :
    FriedmannParity.playValue G σ τ u =
      ⟨(FriedmannParity.playValue G σ τ u).cyclePriority, ∅, 0⟩ := by
  have hlen : (FriedmannParity.playValue G σ τ u).length = 0 := by
    have h0 : (FriedmannParity.playValue G σ τ u).length ≤ 0 :=
      length_le_of_play_eq_cycleLeader G σ τ u hu
    omega
  have hpath : (FriedmannParity.playValue G σ τ u).path = ∅ := by
    ext x
    rw [mem_playValue_path_iff, hlen]
    simp
  cases h : FriedmannParity.playValue G σ τ u
  simp only [h] at hlen hpath ⊢
  subst hlen hpath
  rfl

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

/-! ### Part 3: Specific Priority and Cycle Leader Properties of `parityGame n` -/

section ParityGameProperties

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

lemma gamePriority_eq_one_iff (n : ℕ) (v : Fin (vertices n)) :
    gamePriority n v = 1 ↔ v = sinkVertex n := by
  have hv := v.isLt
  unfold vertices at hv
  rw [gamePriority_eq, eq_sinkVertex_iff]
  unfold rows at hv ⊢
  split_ifs <;> omega

lemma eq_of_gamePriority_eq_of_gt_six (n : ℕ) {u v : Fin (vertices n)}
    (hgt : 6 < gamePriority n u) (heq : gamePriority n u = gamePriority n v) :
    u = v := by
  have hu := u.isLt
  have hv := v.isLt
  unfold vertices rows at hu hv
  apply Fin.ext
  rw [gamePriority_eq] at hgt heq
  rw [gamePriority_eq] at heq
  unfold rows at hgt heq
  split_ifs at hgt heq <;> omega

lemma gamePriority_sVertex (n : ℕ) : gamePriority n (sVertex n) = 8 := by
  rw [gamePriority_eq, val_sVertex]
  unfold rows
  split_ifs <;> omega

lemma gamePriority_gVertex_gt_six (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    6 < gamePriority n (gVertex n i) := by
  rw [gamePriority_eq, val_gVertex n i hi1 hin]
  unfold rows
  split_ifs <;> omega

lemma gamePriority_hVertex_gt_six (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    6 < gamePriority n (hVertex n i) := by
  rw [gamePriority_eq, val_hVertex n i hi1 hin]
  unfold rows
  split_ifs <;> omega

lemma gamePriority_fVertex (n i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    gamePriority n (fVertex n i) = 6 := by
  rw [gamePriority_eq, val_fVertex n i hi1 hin]
  unfold rows
  split_ifs <;> omega

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

lemma sinkVertex_notMem_recurring_of_one_lt_sup {n : ℕ}
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v : Fin (vertices n)}
    (hgt : 1 < (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n)) :
    sinkVertex n ∉ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) := by
  intro hsink
  rcases exists_recurring_eq_sup (parityGame n) σ τ v with ⟨w, hw, hpw⟩
  have hwsink := eq_sinkVertex_of_sinkVertex_mem_recurring hσ hτ hsink hw
  have hp1 : (parityGame n).priority w = 1 := (gamePriority_eq_one_iff n w).mpr hwsink
  rw [hp1] at hpw
  change 1 = (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
    (gamePriority n) at hpw
  omega

lemma notMem_recurring_of_sup_le_six {n : ℕ}
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    {v x : Fin (vertices n)}
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6)
    (hx : 6 < gamePriority n x) :
    x ∉ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) := by
  intro hmem
  have hle' : gamePriority n x ≤
      (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
        (gamePriority n) :=
    Finset.le_sup hmem
  omega

lemma step_val_of_lt_a {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v x : Fin (vertices n)}
    (h1 : 1 < (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n))
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6)
    (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v))
    (hval : x.val < n - 1) :
    x.val < n - 2 ∧ (step (parityGame n) σ τ x).val = x.val + 1 := by
  have hxrows : x.val < rows n := by unfold rows; omega
  have hstep_mem : step (parityGame n) σ τ x ∈
      FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) :=
    step_mem_recurring hx
  have hsucc := step_mem_gameSuccessors hσ hτ x
  unfold gameSuccessors at hsucc
  rw [dif_pos hxrows] at hsucc
  have hrow : rowName n ⟨x.val, hxrows⟩ = (.a, x.val + 2) := by
    unfold rowName
    simp [hval]
  rw [hrow] at hsucc
  simp only [Finset.mem_insert, Finset.mem_singleton, actionTarget] at hsucc
  rcases hsucc with hsucc | hsucc
  · unfold decisionVertex at hsucc
    by_cases hlast : x.val + 2 + 1 = n + 1
    · rw [if_pos ⟨rfl, hlast⟩] at hsucc
      rw [hsucc] at hstep_mem
      exact False.elim (sinkVertex_notMem_recurring_of_one_lt_sup hσ hτ h1 hstep_mem)
    · rw [if_neg (fun h => hlast h.2), if_neg (by simp)] at hsucc
      refine ⟨by omega, ?_⟩
      rw [hsucc]
      dsimp only [rowRank]
      rw [val_vertexCode n _ (by unfold vertices rows; omega)]
      omega
  · rw [hsucc] at hstep_mem
    exact False.elim (notMem_recurring_of_sup_le_six hle
      (gamePriority_gVertex_gt_six n (x.val + 2) (by omega) (by omega)) hstep_mem)

lemma not_val_lt_a_of_mem_recurring {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v : Fin (vertices n)}
    (h1 : 1 < (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n))
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6) :
    ∀ d : ℕ, ∀ x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v),
      n - 1 - d ≤ x.val → x.val < n - 1 → False
  | 0, x, _, hge, hlt => by omega
  | d + 1, x, hx, hge, hlt => by
    have ⟨hlt', hstep⟩ := step_val_of_lt_a hn hσ hτ h1 hle hx hlt
    exact not_val_lt_a_of_mem_recurring hn hσ hτ h1 hle d
      (step (parityGame n) σ τ x) (step_mem_recurring hx) (by omega) (by omega)

lemma step_val_of_lt_b {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v x : Fin (vertices n)}
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6)
    (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v))
    (hge : n - 1 ≤ x.val) (hlt : x.val < (n - 1) + (n - 2)) :
    n - 1 < x.val ∧ (step (parityGame n) σ τ x).val = x.val - 1 := by
  have hxrows : x.val < rows n := by unfold rows; omega
  have hstep_mem : step (parityGame n) σ τ x ∈
      FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) :=
    step_mem_recurring hx
  have hsucc := step_mem_gameSuccessors hσ hτ x
  unfold gameSuccessors at hsucc
  rw [dif_pos hxrows] at hsucc
  have hrow : rowName n ⟨x.val, hxrows⟩ = (.b, x.val - (n - 1) + 2) := by
    unfold rowName
    have hnot : ¬ x.val < n - 1 := by omega
    simp [hnot, hlt]
  rw [hrow] at hsucc
  simp only [Finset.mem_insert, Finset.mem_singleton, actionTarget] at hsucc
  rcases hsucc with hsucc | hsucc
  · unfold decisionVertex at hsucc
    by_cases hfirst : x.val - (n - 1) + 2 - 1 = 1
    · rw [if_neg (by simp), if_pos ⟨Or.inl rfl, hfirst⟩] at hsucc
      rw [hsucc] at hstep_mem
      exact False.elim (notMem_recurring_of_sup_le_six hle
        (gamePriority_gVertex_gt_six n 1 (by omega) (by omega)) hstep_mem)
    · rw [if_neg (by simp), if_neg (fun h => hfirst h.2)] at hsucc
      refine ⟨by omega, ?_⟩
      rw [hsucc]
      dsimp only [rowRank]
      rw [val_vertexCode n _ (by unfold vertices rows; omega)]
      omega
  · rw [hsucc] at hstep_mem
    exact False.elim (notMem_recurring_of_sup_le_six hle
      (gamePriority_gVertex_gt_six n (x.val - (n - 1) + 2) (by omega) (by omega)) hstep_mem)

lemma not_val_lt_b_of_mem_recurring {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v : Fin (vertices n)}
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6) :
    ∀ d : ℕ, ∀ x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v),
      n - 1 ≤ x.val → x.val < (n - 1) + d → x.val < (n - 1) + (n - 2) → False
  | 0, x, _, hge, hlt, _ => by omega
  | d + 1, x, hx, hge, hlt, hltb => by
    have ⟨hgt, hstep⟩ := step_val_of_lt_b hn hσ hτ hle hx hge hltb
    exact not_val_lt_b_of_mem_recurring hn hσ hτ hle d
      (step (parityGame n) σ τ x) (step_mem_recurring hx) (by omega) (by omega) (by omega)

lemma step_val_of_lt_c {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v x : Fin (vertices n)}
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6)
    (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v))
    (hge : (n - 1) + (n - 2) ≤ x.val) (hlt : x.val < 2 * (n - 1) + (n - 2)) :
    (n - 1) + (n - 2) < x.val ∧ (step (parityGame n) σ τ x).val = x.val - 1 := by
  have hxrows : x.val < rows n := by unfold rows; omega
  have hstep_mem : step (parityGame n) σ τ x ∈
      FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) :=
    step_mem_recurring hx
  have hsucc := step_mem_gameSuccessors hσ hτ x
  unfold gameSuccessors at hsucc
  rw [dif_pos hxrows] at hsucc
  have hrow : rowName n ⟨x.val, hxrows⟩ = (.c, x.val - ((n - 1) + (n - 2)) + 2) := by
    unfold rowName
    have hnot1 : ¬ x.val < n - 1 := by omega
    have hnot2 : ¬ x.val < (n - 1) + (n - 2) := by omega
    simp [hnot1, hnot2, hlt]
  rw [hrow] at hsucc
  simp only [Finset.mem_insert, Finset.mem_singleton, actionTarget] at hsucc
  rcases hsucc with hsucc | hsucc
  · unfold decisionVertex at hsucc
    by_cases hfirst : x.val - ((n - 1) + (n - 2)) + 2 - 1 = 1
    · rw [if_neg (by simp), if_pos ⟨Or.inr rfl, hfirst⟩] at hsucc
      rw [hsucc] at hstep_mem
      exact False.elim (notMem_recurring_of_sup_le_six hle
        (gamePriority_gVertex_gt_six n 1 (by omega) (by omega)) hstep_mem)
    · rw [if_neg (by simp), if_neg (fun h => hfirst h.2)] at hsucc
      refine ⟨by omega, ?_⟩
      rw [hsucc]
      dsimp only [rowRank]
      rw [val_vertexCode n _ (by unfold vertices rows; omega)]
      omega
  · rw [hsucc] at hstep_mem
    exact False.elim (notMem_recurring_of_sup_le_six hle
      (gamePriority_gVertex_gt_six n (x.val - ((n - 1) + (n - 2)) + 2) (by omega) (by omega))
      hstep_mem)

lemma not_val_lt_c_of_mem_recurring {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v : Fin (vertices n)}
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6) :
    ∀ d : ℕ, ∀ x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v),
      (n - 1) + (n - 2) ≤ x.val →
      x.val < (n - 1) + (n - 2) + d →
      x.val < 2 * (n - 1) + (n - 2) → False
  | 0, x, _, hge, hlt, _ => by omega
  | d + 1, x, hx, hge, hlt, hltc => by
    have ⟨hgt, hstep⟩ := step_val_of_lt_c hn hσ hτ hle hx hge hltc
    exact not_val_lt_c_of_mem_recurring hn hσ hτ hle d
      (step (parityGame n) σ τ x) (step_mem_recurring hx) (by omega) (by omega) (by omega)

lemma val_ge_abc_of_mem_recurring {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v x : Fin (vertices n)}
    (h1 : 1 < (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n))
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6)
    (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)) :
    2 * (n - 1) + (n - 2) ≤ x.val := by
  by_contra hlt
  by_cases ha : x.val < n - 1
  · exact not_val_lt_a_of_mem_recurring hn hσ hτ h1 hle (n - 1) x hx (by omega) ha
  · by_cases hb : x.val < (n - 1) + (n - 2)
    · exact not_val_lt_b_of_mem_recurring hn hσ hτ hle (n - 2) x hx (by omega) hb hb
    · exact not_val_lt_c_of_mem_recurring hn hσ hτ hle (n - 1) x hx (by omega)
        (by omega) (by omega)

lemma step_of_d_mem_recurring {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v x : Fin (vertices n)}
    (h1 : 1 < (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n))
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6)
    (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v))
    (hge : 2 * (n - 1) + (n - 2) ≤ x.val)
    (hlt : x.val < 3 * (n - 1) + (n - 2)) :
    σ x = fVertex n (x.val - (2 * (n - 1) + (n - 2)) + 2) ∧
    step (parityGame n) σ τ x = fVertex n (x.val - (2 * (n - 1) + (n - 2)) + 2) := by
  have hxrows : x.val < rows n := by unfold rows; omega
  have hown : (parityGame n).owner x = false := by
    change decide (rows n ≤ x.val) = false
    simp [hxrows]
  have hstep_eq : step (parityGame n) σ τ x = σ x := if_pos hown
  have hstep_mem : step (parityGame n) σ τ x ∈
      FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) :=
    step_mem_recurring hx
  have hsucc := step_mem_gameSuccessors hσ hτ x
  unfold gameSuccessors at hsucc
  rw [dif_pos hxrows] at hsucc
  have hrow : rowName n ⟨x.val, hxrows⟩ = (.d, x.val - (2 * (n - 1) + (n - 2)) + 2) := by
    unfold rowName
    have hnot1 : ¬ x.val < n - 1 := by omega
    have hnot2 : ¬ x.val < (n - 1) + (n - 2) := by omega
    have hnot3 : ¬ x.val < 2 * (n - 1) + (n - 2) := by omega
    simp [hnot1, hnot2, hnot3, hlt]
  rw [hrow] at hsucc
  simp only [Finset.mem_insert, Finset.mem_singleton, actionTarget] at hsucc
  rcases hsucc with hsucc | hsucc
  · unfold decisionVertex at hsucc
    by_cases hfirst : x.val - (2 * (n - 1) + (n - 2)) + 2 - 1 = 1
    · rw [if_neg (by simp), if_pos ⟨Or.inl rfl, hfirst⟩] at hsucc
      rw [hsucc] at hstep_mem
      exact False.elim (notMem_recurring_of_sup_le_six hle
        (gamePriority_gVertex_gt_six n 1 (by omega) (by omega)) hstep_mem)
    · rw [if_neg (by simp), if_neg (fun h => hfirst h.2)] at hsucc
      have hge_abc := val_ge_abc_of_mem_recurring hn hσ hτ h1 hle hstep_mem
      rw [hsucc] at hge_abc
      dsimp only [rowRank] at hge_abc
      rw [val_vertexCode n _ (by unfold vertices rows; omega)] at hge_abc
      omega
  · exact ⟨hstep_eq.symm.trans hsucc, hsucc⟩

lemma step_of_e_mem_recurring {n : ℕ}
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v x : Fin (vertices n)}
    (hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6)
    (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v))
    (hge : 3 * (n - 1) + (n - 2) ≤ x.val)
    (hlt : x.val < rows n) :
    σ x = fVertex n (x.val - (3 * (n - 1) + (n - 2)) + 1) ∧
    step (parityGame n) σ τ x = fVertex n (x.val - (3 * (n - 1) + (n - 2)) + 1) := by
  have hown : (parityGame n).owner x = false := by
    change decide (rows n ≤ x.val) = false
    simp [hlt]
  have hstep_eq : step (parityGame n) σ τ x = σ x := if_pos hown
  have hstep_mem : step (parityGame n) σ τ x ∈
      FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) :=
    step_mem_recurring hx
  have hsucc := step_mem_gameSuccessors hσ hτ x
  unfold gameSuccessors at hsucc
  rw [dif_pos hlt] at hsucc
  have hrow : rowName n ⟨x.val, hlt⟩ = (.e, x.val - (3 * (n - 1) + (n - 2)) + 1) := by
    unfold rowName
    have hnot1 : ¬ x.val < n - 1 := by omega
    have hnot2 : ¬ x.val < (n - 1) + (n - 2) := by omega
    have hnot3 : ¬ x.val < 2 * (n - 1) + (n - 2) := by omega
    have hnot4 : ¬ x.val < 3 * (n - 1) + (n - 2) := by omega
    simp [hnot1, hnot2, hnot3, hnot4]
  rw [hrow] at hsucc
  simp only [Finset.mem_insert, Finset.mem_singleton, actionTarget] at hsucc
  rcases hsucc with hsucc | hsucc
  · rw [hsucc] at hstep_mem
    have hs : 6 < gamePriority n (sVertex n) := by rw [gamePriority_sVertex]; omega
    exact False.elim (notMem_recurring_of_sup_le_six hle hs hstep_mem)
  · exact ⟨hstep_eq.symm.trans hsucc, hsucc⟩

lemma playValue_cyclePriority_cases {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    (v : Fin (vertices n)) :
    (FriedmannParity.playValue (parityGame n) σ τ v).cyclePriority = 1 ∨
    (FriedmannParity.playValue (parityGame n) σ τ v).cyclePriority = 6 ∨
    6 < (FriedmannParity.playValue (parityGame n) σ τ v).cyclePriority := by
  let w := cycleLeader (parityGame n) σ τ v
  have hw : w ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) :=
    cycleLeader_mem_recurring (parityGame n) σ τ v
  have hpw : (FriedmannParity.playValue (parityGame n) σ τ v).cyclePriority = gamePriority n w :=
    playValue_cyclePriority_eq_priority_cycleLeader (parityGame n) σ τ v
  have hsup : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) = gamePriority n w :=
    (priority_cycleLeader (parityGame n) σ τ v).symm
  have hpos : 1 ≤ gamePriority n w := by
    rw [gamePriority_eq]; split_ifs <;> omega
  by_cases hgt6 : 6 < gamePriority n w
  · right; right; omega
  · by_cases heq6 : gamePriority n w = 6
    · right; left; omega
    · by_cases heq1 : gamePriority n w = 1
      · left; omega
      · have h1 : 1 < (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
            (gamePriority n) := by omega
        have hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
            (gamePriority n) ≤ 6 := by omega
        have hlt_rows : w.val < rows n := by
          have hw_lt := w.isLt
          unfold vertices rows at hw_lt ⊢
          rw [gamePriority_eq] at hgt6 heq6 heq1
          unfold rows at hgt6 heq6 heq1
          split_ifs at hgt6 heq6 heq1 <;> omega
        have hge_abc := val_ge_abc_of_mem_recurring hn hσ hτ h1 hle hw
        by_cases hd : w.val < 3 * (n - 1) + (n - 2)
        · have ⟨_, hstep⟩ := step_of_d_mem_recurring hn hσ hτ h1 hle hw hge_abc hd
          have hmem : fVertex n (w.val - (2 * (n - 1) + (n - 2)) + 2) ∈
              FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) := by
            rw [← hstep]; exact step_mem_recurring hw
          have hpf : gamePriority n (fVertex n (w.val - (2 * (n - 1) + (n - 2)) + 2)) = 6 :=
            gamePriority_fVertex n _ (by omega) (by omega)
          have hle_sup : gamePriority n (fVertex n (w.val - (2 * (n - 1) + (n - 2)) + 2)) ≤
              (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
                (gamePriority n) :=
            Finset.le_sup hmem
          omega
        · have ⟨_, hstep⟩ := step_of_e_mem_recurring hσ hτ hle hw (by omega) hlt_rows
          have hmem : fVertex n (w.val - (3 * (n - 1) + (n - 2)) + 1) ∈
              FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) := by
            rw [← hstep]; exact step_mem_recurring hw
          have hpf : gamePriority n (fVertex n (w.val - (3 * (n - 1) + (n - 2)) + 1)) = 6 :=
            gamePriority_fVertex n _ (by unfold rows at hlt_rows; omega)
              (by unfold rows at hlt_rows; omega)
          have hle_sup : gamePriority n (fVertex n (w.val - (3 * (n - 1) + (n - 2)) + 1)) ≤
              (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
                (gamePriority n) :=
            Finset.le_sup hmem
          omega

lemma priority_six_two_cycle {n : ℕ} (hn : 3 ≤ n)
    {σ τ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ : FriedmannParity.Legal (parityGame n) true τ)
    {v w : Fin (vertices n)}
    (hw : w ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v))
    (hsup : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) = 6)
    (hpw : gamePriority n w = 6) :
    let u := step (parityGame n) σ τ w
    (parityGame n).owner u = false ∧ gamePriority n u = 5 ∧ σ u = w := by
  dsimp only
  have h1 : 1 < (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) := by omega
  have hle : (FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v)).sup
      (gamePriority n) ≤ 6 := by omega
  have hw_range : rows n ≤ w.val ∧ w.val < rows n + n := by
    have hw_lt := w.isLt
    unfold vertices rows at hw_lt ⊢
    rw [gamePriority_eq] at hpw
    unfold rows at hpw
    split_ifs at hpw <;> omega
  have hnot_rows : ¬ w.val < rows n := by omega
  let i := w.val - rows n + 1
  have hi1 : 1 ≤ i := by omega
  have hin : i ≤ n := by omega
  have hwf : fVertex n i = w := by
    apply Fin.ext
    rw [val_fVertex n i hi1 hin]
    omega
  have hu_mem : step (parityGame n) σ τ w ∈
      FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ v) :=
    step_mem_recurring hw
  have hsucc := step_mem_gameSuccessors hσ hτ w
  unfold gameSuccessors at hsucc
  rw [dif_neg hnot_rows, if_pos hw_range.2] at hsucc
  have handle_e : step (parityGame n) σ τ w = decisionVertex n .e i →
      (parityGame n).owner (step (parityGame n) σ τ w) = false ∧
      gamePriority n (step (parityGame n) σ τ w) = 5 ∧
      σ (step (parityGame n) σ τ w) = w := by
    intro hue
    have hval_u : (step (parityGame n) σ τ w).val = 3 * (n - 1) + (n - 2) + (i - 1) := by
      rw [hue]
      unfold decisionVertex
      rw [if_neg (by simp), if_neg (by simp)]
      dsimp only [rowRank]
      exact val_vertexCode n _ (by unfold vertices rows; omega)
    have hlt_rows : (step (parityGame n) σ τ w).val < rows n := by unfold rows; omega
    have hown : (parityGame n).owner (step (parityGame n) σ τ w) = false := by
      change decide (rows n ≤ (step (parityGame n) σ τ w).val) = false
      simp [hlt_rows]
    have hpu : gamePriority n (step (parityGame n) σ τ w) = 5 := by
      rw [gamePriority_eq]
      unfold rows at hlt_rows ⊢
      split_ifs <;> omega
    have ⟨hσu, _⟩ := step_of_e_mem_recurring hσ hτ hle hu_mem (by omega) hlt_rows
    have hi_eq : (step (parityGame n) σ τ w).val - (3 * (n - 1) + (n - 2)) + 1 = i := by omega
    rw [hi_eq, hwf] at hσu
    exact ⟨hown, hpu, hσu⟩
  by_cases hi_one : i = 1
  · rw [if_pos hi_one] at hsucc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsucc
    rcases hsucc with hsucc | hsucc
    · rw [hsucc] at hu_mem
      exact False.elim (notMem_recurring_of_sup_le_six hle
        (gamePriority_hVertex_gt_six n i hi1 hin) hu_mem)
    · exact handle_e hsucc
  · rw [if_neg hi_one] at hsucc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsucc
    rcases hsucc with hsucc | hsucc | hsucc
    · rw [hsucc] at hu_mem
      exact False.elim (notMem_recurring_of_sup_le_six hle
        (gamePriority_hVertex_gt_six n i hi1 hin) hu_mem)
    · have hval_u : (step (parityGame n) σ τ w).val = 2 * (n - 1) + (n - 2) + (i - 2) := by
        rw [hsucc]
        unfold decisionVertex
        rw [if_neg (by simp), if_neg (by simp)]
        dsimp only [rowRank]
        exact val_vertexCode n _ (by unfold vertices rows at hw_range ⊢; omega)
      have hlt_rows : (step (parityGame n) σ τ w).val < rows n := by
        dsimp only [i] at hval_u; unfold rows at hw_range ⊢; omega
      have hown : (parityGame n).owner (step (parityGame n) σ τ w) = false := by
        change decide (rows n ≤ (step (parityGame n) σ τ w).val) = false
        simp [hlt_rows]
      have hpu : gamePriority n (step (parityGame n) σ τ w) = 5 := by
        rw [gamePriority_eq]
        dsimp only [i] at hval_u
        unfold rows at hw_range hlt_rows ⊢
        split_ifs <;> omega
      have ⟨hσu, _⟩ := step_of_d_mem_recurring hn hσ hτ h1 hle hu_mem
        (by dsimp only [i] at hval_u hi_one; omega)
        (by dsimp only [i] at hval_u; unfold rows at hw_range; omega)
      have hi_eq : (step (parityGame n) σ τ w).val - (2 * (n - 1) + (n - 2)) + 2 = i := by
        dsimp only [i] at hval_u hi_one ⊢; omega
      rw [hi_eq, hwf] at hσu
      exact ⟨hown, hpu, hσu⟩
    · exact handle_e hsucc

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

end ParityGameProperties

/-! ### Part 4: Two-Strategy Minimum and Global Optimal Counterstrategy -/

section Counterstrategy

section GeneralHelpers

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma le_play_of_le_step_on_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v),
      F (step G σ τ y) ≤ F y) :
    ∀ d : ℕ, ∀ y ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v),
      F (FriedmannParity.play G σ τ y d) ≤ F y
  | 0, y, _ => le_rfl
  | d + 1, y, hy => by
    rw [play_succ]
    exact le_trans
      (le_play_of_le_step_on_recurring F hstep d (step G σ τ y) (step_mem_recurring hy))
      (hstep y hy)

omit [DecidableEq V] in
lemma eq_of_le_step_on_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v),
      F (step G σ τ y) ≤ F y)
    {x : V} (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v)) :
    F (step G σ τ x) = F x := by
  rcases exists_pos_play_eq_self_of_mem_recurring hx with ⟨L, hL, hplayL⟩
  have hL1 : (L - 1) + 1 = L := by omega
  rw [← hL1, play_succ] at hplayL
  have hle1 := hstep x hx
  have hle2 := le_play_of_le_step_on_recurring F hstep (L - 1)
    (step G σ τ x) (step_mem_recurring hx)
  rw [hplayL] at hle2
  omega

omit [DecidableEq V] in
lemma play_le_of_step_le_on_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v),
      F y ≤ F (step G σ τ y)) :
    ∀ d : ℕ, ∀ y ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v),
      F y ≤ F (FriedmannParity.play G σ τ y d)
  | 0, y, _ => le_rfl
  | d + 1, y, hy => by
    rw [play_succ]
    exact le_trans (hstep y hy)
      (play_le_of_step_le_on_recurring F hstep d (step G σ τ y) (step_mem_recurring hy))

omit [DecidableEq V] in
lemma eq_of_step_le_on_recurring {G : FriedmannParity.Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v),
      F y ≤ F (step G σ τ y))
    {x : V} (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v)) :
    F (step G σ τ x) = F x := by
  rcases exists_pos_play_eq_self_of_mem_recurring hx with ⟨L, hL, hplayL⟩
  have hL1 : (L - 1) + 1 = L := by omega
  rw [← hL1, play_succ] at hplayL
  have hle1 := hstep x hx
  have hle2 := play_le_of_step_le_on_recurring F hstep (L - 1)
    (step G σ τ x) (step_mem_recurring hx)
  rw [hplayL] at hle2
  omega

omit [Fintype V] [DecidableEq V] in
lemma le_play_int {G : FriedmannParity.Game V} {σ τ : V → V}
    (F : V → ℤ) (hstep : ∀ y, F (step G σ τ y) ≤ F y) :
    ∀ d : ℕ, ∀ y : V, F (FriedmannParity.play G σ τ y d) ≤ F y
  | 0, _ => le_rfl
  | d + 1, y => by
    rw [play_succ]
    exact le_trans (le_play_int F hstep d (step G σ τ y)) (hstep y)

omit [DecidableEq V] in
lemma eq_on_recurring_of_le_step_int {G : FriedmannParity.Game V} {σ τ : V → V} {v : V}
    (F : V → ℤ) (hstep : ∀ y, F (step G σ τ y) ≤ F y)
    {x w : V}
    (hx : x ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v))
    (hw : w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ v)) :
    F x = F w := by
  have hwx : w ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ x) := by
    rwa [recurring_eq_of_mem_recurring hx]
  have hxw : x ∈ FriedmannParity.recurring (FriedmannParity.play G σ τ w) := by
    rwa [recurring_eq_of_mem_recurring hw]
  rcases exists_play_eq_of_mem_recurring hwx with ⟨d₁, hd₁⟩
  rcases exists_play_eq_of_mem_recurring hxw with ⟨d₂, hd₂⟩
  have h1 := le_play_int F hstep d₁ x
  have h2 := le_play_int F hstep d₂ w
  rw [hd₁] at h1
  rw [hd₂] at h2
  omega

omit [Fintype V] [DecidableEq V] in
lemma reward_cyclePriority_le_of_valueLE {G : FriedmannParity.Game V}
    {a b : FriedmannParity.Valuation V} (hab : ValueLE G a b) :
    FriedmannParity.reward a.cyclePriority ≤ FriedmannParity.reward b.cyclePriority := by
  by_contra hgt
  exact hab (Or.inl (by omega))

omit [Fintype V] [DecidableEq V] in
lemma count_le_or_ge_of_valueLE {G : FriedmannParity.Game V}
    {a b : FriedmannParity.Valuation V} {q : ℕ}
    (hab : ValueLE G a b)
    (hp : a.cyclePriority = b.cyclePriority)
    (hgt : ∀ q', q < q' → count G a.path q' = count G b.path q') :
    (q % 2 = 0 → count G a.path q ≤ count G b.path q) ∧
    (q % 2 = 1 → count G b.path q ≤ count G a.path q) := by
  constructor
  · intro he
    by_contra hlt
    apply hab
    right; left
    refine ⟨hp.symm, q, by omega, fun q' hq' => (hgt q' hq').symm, Or.inl ⟨he, by omega⟩⟩
  · intro ho
    by_contra hlt
    apply hab
    right; left
    refine ⟨hp.symm, q, by omega, fun q' hq' => (hgt q' hq').symm, Or.inr ⟨ho, by omega⟩⟩

omit [Fintype V] [DecidableEq V] in
lemma length_le_of_valueLE_odd {G : FriedmannParity.Game V}
    {a b : FriedmannParity.Valuation V}
    (hab : ValueLE G a b)
    (hp : a.cyclePriority = b.cyclePriority)
    (hseq : SetEquivalent G a.path b.path)
    (hodd : a.cyclePriority % 2 = 1) :
    a.length ≤ b.length := by
  by_contra hlt
  apply hab
  right; right
  exact ⟨hp.symm, setEquivalent_symm hseq, Or.inl ⟨hp ▸ hodd, by omega⟩⟩

lemma count_playValue_eq_zero_of_le_cyclePriority
    {G : FriedmannParity.Game V} {σ τ : V → V} {v : V} {q : ℕ}
    (hq : q ≤ (FriedmannParity.playValue G σ τ v).cyclePriority) :
    count G (FriedmannParity.playValue G σ τ v).path q = 0 := by
  classical
  unfold count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu
  rw [mem_playValue_path_iff] at hu
  omega

omit [DecidableEq V] in
lemma count_eq_zero_of_univ_sup_lt {G : FriedmannParity.Game V} (A : Finset V) {q : ℕ}
    (hq : Finset.univ.sup G.priority < q) : count G A q = 0 :=
  count_eq_zero_of_sup_lt (lt_of_le_of_lt (Finset.sup_mono (Finset.subset_univ A)) hq)

end GeneralHelpers

noncomputable def minStrategy (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) : Fin (vertices n) := by
  classical
  exact if ValueLE (parityGame n)
      (FriedmannParity.playValue (parityGame n) σ τ₁ x)
      (FriedmannParity.playValue (parityGame n) σ τ₂ x)
    then τ₁ x else τ₂ x

noncomputable def minVal (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) : FriedmannParity.Valuation (Fin (vertices n)) := by
  classical
  exact if ValueLE (parityGame n)
      (FriedmannParity.playValue (parityGame n) σ τ₁ x)
      (FriedmannParity.playValue (parityGame n) σ τ₂ x)
    then FriedmannParity.playValue (parityGame n) σ τ₁ x
    else FriedmannParity.playValue (parityGame n) σ τ₂ x

noncomputable def chosenStrategy (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) : Fin (vertices n) → Fin (vertices n) := by
  classical
  exact if ValueLE (parityGame n)
      (FriedmannParity.playValue (parityGame n) σ τ₁ x)
      (FriedmannParity.playValue (parityGame n) σ τ₂ x)
    then τ₁ else τ₂

lemma minStrategy_legal {n : ℕ} {σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n)}
    (hτ₁ : FriedmannParity.Legal (parityGame n) true τ₁)
    (hτ₂ : FriedmannParity.Legal (parityGame n) true τ₂) :
    FriedmannParity.Legal (parityGame n) true (minStrategy n σ τ₁ τ₂) := by
  intro x hx
  unfold minStrategy
  split_ifs
  · exact hτ₁ x hx
  · exact hτ₂ x hx

lemma chosenStrategy_legal {n : ℕ} {σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n)}
    (hτ₁ : FriedmannParity.Legal (parityGame n) true τ₁)
    (hτ₂ : FriedmannParity.Legal (parityGame n) true τ₂)
    (x : Fin (vertices n)) :
    FriedmannParity.Legal (parityGame n) true (chosenStrategy n σ τ₁ τ₂ x) := by
  unfold chosenStrategy
  split_ifs
  · exact hτ₁
  · exact hτ₂

lemma minVal_le_left (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) :
    ValueLE (parityGame n) (minVal n σ τ₁ τ₂ x)
      (FriedmannParity.playValue (parityGame n) σ τ₁ x) := by
  unfold minVal
  split_ifs with h
  · exact valueLE_refl (parityGame n) _
  · rcases valueLE_total (parityGame n)
      (FriedmannParity.playValue (parityGame n) σ τ₁ x)
      (FriedmannParity.playValue (parityGame n) σ τ₂ x) with h1 | h2
    · exact False.elim (h h1)
    · exact h2

lemma minVal_le_right (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) :
    ValueLE (parityGame n) (minVal n σ τ₁ τ₂ x)
      (FriedmannParity.playValue (parityGame n) σ τ₂ x) := by
  unfold minVal
  split_ifs with h
  · exact h
  · exact valueLE_refl (parityGame n) _

lemma minVal_eq_playValue_chosenStrategy (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) :
    minVal n σ τ₁ τ₂ x =
      FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x) x := by
  unfold minVal chosenStrategy
  split_ifs <;> rfl

lemma step_minStrategy_eq_chosenStrategy (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) :
    step (parityGame n) σ (minStrategy n σ τ₁ τ₂) x =
      step (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x) x := by
  unfold step minStrategy chosenStrategy
  split_ifs <;> rfl

lemma minVal_step_le_chosenStrategy (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) :
    ValueLE (parityGame n)
      (minVal n σ τ₁ τ₂ (step (parityGame n) σ (minStrategy n σ τ₁ τ₂) x))
      (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
        (step (parityGame n) σ (minStrategy n σ τ₁ τ₂) x)) := by
  unfold chosenStrategy
  split_ifs
  · exact minVal_le_left n σ τ₁ τ₂ _
  · exact minVal_le_right n σ τ₁ τ₂ _

lemma chosenStrategy_step_cyclePriority (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) :
    (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
      (step (parityGame n) σ (minStrategy n σ τ₁ τ₂) x)).cyclePriority =
    (minVal n σ τ₁ τ₂ x).cyclePriority := by
  rw [step_minStrategy_eq_chosenStrategy, playValue_cyclePriority_step,
    ← minVal_eq_playValue_chosenStrategy]

lemma reward_minVal_step_le (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (x : Fin (vertices n)) :
    FriedmannParity.reward
      (minVal n σ τ₁ τ₂ (step (parityGame n) σ (minStrategy n σ τ₁ τ₂) x)).cyclePriority ≤
    FriedmannParity.reward (minVal n σ τ₁ τ₂ x).cyclePriority := by
  have hle := reward_cyclePriority_le_of_valueLE (minVal_step_le_chosenStrategy n σ τ₁ τ₂ x)
  rwa [chosenStrategy_step_cyclePriority] at hle

lemma minVal_cyclePriority_eq_on_recurring (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    {v x w : Fin (vertices n)}
    (hx : x ∈ FriedmannParity.recurring
      (FriedmannParity.play (parityGame n) σ (minStrategy n σ τ₁ τ₂) v))
    (hw : w ∈ FriedmannParity.recurring
      (FriedmannParity.play (parityGame n) σ (minStrategy n σ τ₁ τ₂) v)) :
    (minVal n σ τ₁ τ₂ x).cyclePriority = (minVal n σ τ₁ τ₂ w).cyclePriority := by
  apply reward_injective
  exact eq_on_recurring_of_le_step_int
    (fun y => FriedmannParity.reward (minVal n σ τ₁ τ₂ y).cyclePriority)
    (reward_minVal_step_le n σ τ₁ τ₂) hx hw

lemma count_minVal_eq_above_max (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (v : Fin (vertices n)) :
    let τ₃ := minStrategy n σ τ₁ τ₂
    let m := minVal n σ τ₁ τ₂
    let R₃ := FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ₃ v)
    let w₃ := cycleLeader (parityGame n) σ τ₃ v
    let p₃ := (FriedmannParity.playValue (parityGame n) σ τ₃ v).cyclePriority
    let p_star := (m w₃).cyclePriority
    let M := Finset.univ.sup (gamePriority n) + max p₃ p_star + 1
    ∀ d : ℕ, ∀ q : ℕ, M - d ≤ q → max p₃ p_star < q →
      ∀ x ∈ R₃,
        count (parityGame n) (m (step (parityGame n) σ τ₃ x)).path q =
          count (parityGame n)
            (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
              (step (parityGame n) σ τ₃ x)).path q ∧
        count (parityGame n) (m (step (parityGame n) σ τ₃ x)).path q =
          count (parityGame n) (m x).path q := by
  intro τ₃ m R₃ w₃ p₃ p_star M d
  have hw₃ : w₃ ∈ R₃ := cycleLeader_mem_recurring (parityGame n) σ τ₃ v
  induction d with
  | zero =>
    intro q hMq _ x _
    have hsup : Finset.univ.sup (parityGame n).priority < q := by
      change Finset.univ.sup (gamePriority n) < q
      omega
    rw [count_eq_zero_of_univ_sup_lt _ hsup,
      count_eq_zero_of_univ_sup_lt _ hsup,
      count_eq_zero_of_univ_sup_lt _ hsup]
    exact ⟨rfl, rfl⟩
  | succ d ih =>
    intro q hMq hmaxq
    by_cases hMq' : M - d ≤ q
    · exact ih q hMq' hmaxq
    · have hgt : ∀ x ∈ R₃, ∀ q', q < q' →
          count (parityGame n) (m (step (parityGame n) σ τ₃ x)).path q' =
            count (parityGame n)
              (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
                (step (parityGame n) σ τ₃ x)).path q' := by
        intro x hx q' hq'
        exact (ih q' (by omega) (by omega) x hx).1
      have hmx_eq : ∀ x ∈ R₃,
          count (parityGame n) (m x).path q =
            count (parityGame n)
              (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
                (step (parityGame n) σ τ₃ x)).path q := by
        intro x hx
        have hpx : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring n σ τ₁ τ₂ hx hw₃
        have hp_lt_q : (FriedmannParity.playValue (parityGame n) σ
            (chosenStrategy n σ τ₁ τ₂ x) x).cyclePriority < q := by
          rw [← minVal_eq_playValue_chosenStrategy]
          change (m x).cyclePriority < q
          omega
        have hcnt := count_playValue_step hp_lt_q
        rw [← minVal_eq_playValue_chosenStrategy,
          ← step_minStrategy_eq_chosenStrategy] at hcnt
        have hle_p3 : (parityGame n).priority x ≤ p₃ := Finset.le_sup hx
        have hne_q : (parityGame n).priority x ≠ q := by omega
        rw [if_neg hne_q, Nat.add_zero] at hcnt
        exact hcnt
      have hcp_eq : ∀ x ∈ R₃,
          (m (step (parityGame n) σ τ₃ x)).cyclePriority =
            (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
              (step (parityGame n) σ τ₃ x)).cyclePriority := by
        intro x hx
        have h1 : (m (step (parityGame n) σ τ₃ x)).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring n σ τ₁ τ₂ (step_mem_recurring hx) hw₃
        have h2 : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring n σ τ₁ τ₂ hx hw₃
        rw [h1, chosenStrategy_step_cyclePriority]
        exact h2.symm
      rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
      · have hstep_le : ∀ x ∈ R₃,
            count (parityGame n) (m (step (parityGame n) σ τ₃ x)).path q ≤
              count (parityGame n) (m x).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_valueLE
            (minVal_step_le_chosenStrategy n σ τ₁ τ₂ x)
            (hcp_eq x hx) (hgt x hx)).1 hpar
        intro x hx
        have heq := eq_of_le_step_on_recurring
          (fun y => count (parityGame n) (m y).path q) hstep_le hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩
      · have hstep_ge : ∀ x ∈ R₃,
            count (parityGame n) (m x).path q ≤
              count (parityGame n) (m (step (parityGame n) σ τ₃ x)).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_valueLE
            (minVal_step_le_chosenStrategy n σ τ₁ τ₂ x)
            (hcp_eq x hx) (hgt x hx)).2 hpar
        intro x hx
        have heq := eq_of_step_le_on_recurring
          (fun y => count (parityGame n) (m y).path q) hstep_ge hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩

lemma reward_playValue_minStrategy_le (n : ℕ) (σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n))
    (v : Fin (vertices n)) :
    FriedmannParity.reward
      (FriedmannParity.playValue (parityGame n) σ (minStrategy n σ τ₁ τ₂) v).cyclePriority ≤
    FriedmannParity.reward
      (minVal n σ τ₁ τ₂ (cycleLeader (parityGame n) σ (minStrategy n σ τ₁ τ₂) v)).cyclePriority := by
  let τ₃ := minStrategy n σ τ₁ τ₂
  let m := minVal n σ τ₁ τ₂
  let R₃ := FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ₃ v)
  let w₃ := cycleLeader (parityGame n) σ τ₃ v
  let p₃ := (FriedmannParity.playValue (parityGame n) σ τ₃ v).cyclePriority
  let p_star := (m w₃).cyclePriority
  change FriedmannParity.reward p₃ ≤ FriedmannParity.reward p_star
  have hw₃ : w₃ ∈ R₃ := cycleLeader_mem_recurring (parityGame n) σ τ₃ v
  have hpw₃ : (parityGame n).priority w₃ = p₃ :=
    (playValue_cyclePriority_eq_priority_cycleLeader (parityGame n) σ τ₃ v).symm
  have habove : ∀ q : ℕ, max p₃ p_star < q → ∀ x ∈ R₃,
      count (parityGame n) (m (step (parityGame n) σ τ₃ x)).path q =
        count (parityGame n)
          (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
            (step (parityGame n) σ τ₃ x)).path q := by
    intro q hq x hx
    let M := Finset.univ.sup (gamePriority n) + max p₃ p_star + 1
    have hMM : M - M ≤ q := by simp
    exact (count_minVal_eq_above_max n σ τ₁ τ₂ v M q hMM hq x hx).1
  have hcp_eq : ∀ x ∈ R₃,
      (m (step (parityGame n) σ τ₃ x)).cyclePriority =
        (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
          (step (parityGame n) σ τ₃ x)).cyclePriority := by
    intro x hx
    have h1 : (m (step (parityGame n) σ τ₃ x)).cyclePriority = p_star :=
      minVal_cyclePriority_eq_on_recurring n σ τ₁ τ₂ (step_mem_recurring hx) hw₃
    have h2 : (m x).cyclePriority = p_star :=
      minVal_cyclePriority_eq_on_recurring n σ τ₁ τ₂ hx hw₃
    rw [h1, chosenStrategy_step_cyclePriority]
    exact h2.symm
  rcases lt_trichotomy p₃ p_star with hlt | heq | hgt
  · rcases Nat.mod_two_eq_zero_or_one p_star with hpar | hpar
    · unfold FriedmannParity.reward
      split_ifs <;> omega
    · exfalso
      have hseq : ∀ x ∈ R₃, SetEquivalent (parityGame n)
          (m (step (parityGame n) σ τ₃ x)).path
          (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
            (step (parityGame n) σ τ₃ x)).path := by
        intro x hx q
        by_cases hq : p_star < q
        · exact habove q (by omega) x hx
        · have h1 : (m (step (parityGame n) σ τ₃ x)).cyclePriority = p_star :=
            minVal_cyclePriority_eq_on_recurring n σ τ₁ τ₂ (step_mem_recurring hx) hw₃
          have h2 : (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
              (step (parityGame n) σ τ₃ x)).cyclePriority = p_star :=
            (hcp_eq x hx).symm.trans h1
          have h1' : (FriedmannParity.playValue (parityGame n) σ
              (chosenStrategy n σ τ₁ τ₂ (step (parityGame n) σ τ₃ x))
              (step (parityGame n) σ τ₃ x)).cyclePriority = p_star := by
            rw [← minVal_eq_playValue_chosenStrategy]
            exact h1
          change count (parityGame n) (minVal n σ τ₁ τ₂ (step (parityGame n) σ τ₃ x)).path q = _
          rw [minVal_eq_playValue_chosenStrategy,
            count_playValue_eq_zero_of_le_cyclePriority (by omega),
            count_playValue_eq_zero_of_le_cyclePriority (by omega)]
      have hlen_step : ∀ x ∈ R₃,
          (m (step (parityGame n) σ τ₃ x)).length ≤
            (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
              (step (parityGame n) σ τ₃ x)).length ∧
          (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
              (step (parityGame n) σ τ₃ x)).length + 1 = (m x).length := by
        intro x hx
        have h1 : (m (step (parityGame n) σ τ₃ x)).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring n σ τ₁ τ₂ (step_mem_recurring hx) hw₃
        have h2 : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring n σ τ₁ τ₂ hx hw₃
        have hlen_le := length_le_of_valueLE_odd
          (minVal_step_le_chosenStrategy n σ τ₁ τ₂ x)
          (hcp_eq x hx) (hseq x hx) (by rw [h1]; exact hpar)
        have hx_ne : x ≠ cycleLeader (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x) x := by
          intro hcl
          have hpx : (parityGame n).priority x = p_star := by
            have hpcl := playValue_cyclePriority_eq_priority_cycleLeader
              (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x) x
            rw [← minVal_eq_playValue_chosenStrategy] at hpcl
            change (m x).cyclePriority = _ at hpcl
            rw [h2, ← hcl] at hpcl
            exact hpcl.symm
          have hpx_le : (parityGame n).priority x ≤ p₃ := Finset.le_sup hx
          omega
        have hlen_eq := playValue_length_eq_succ_of_ne_cycleLeader hx_ne
        rw [← minVal_eq_playValue_chosenStrategy,
          ← step_minStrategy_eq_chosenStrategy] at hlen_eq
        exact ⟨hlen_le, hlen_eq.symm⟩
      have hstep_le : ∀ x ∈ R₃, (m (step (parityGame n) σ τ₃ x)).length ≤ (m x).length := by
        intro x hx
        have ⟨h1, h2⟩ := hlen_step x hx
        omega
      have heq_w3 := eq_of_le_step_on_recurring (fun y => (m y).length) hstep_le hw₃
      have ⟨h1, h2⟩ := hlen_step w₃ hw₃
      omega
  · rw [heq]
  · rcases Nat.mod_two_eq_zero_or_one p₃ with hpar | hpar
    · exfalso
      have hstep_rel : ∀ x ∈ R₃,
          count (parityGame n) (m (step (parityGame n) σ τ₃ x)).path p₃ ≤
            count (parityGame n)
              (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
                (step (parityGame n) σ τ₃ x)).path p₃ ∧
          count (parityGame n) (m x).path p₃ =
            count (parityGame n)
              (FriedmannParity.playValue (parityGame n) σ (chosenStrategy n σ τ₁ τ₂ x)
                (step (parityGame n) σ τ₃ x)).path p₃ +
              (if (parityGame n).priority x = p₃ then 1 else 0) := by
        intro x hx
        have hle_cnt := (count_le_or_ge_of_valueLE
          (minVal_step_le_chosenStrategy n σ τ₁ τ₂ x)
          (hcp_eq x hx)
          (fun q' hq' => habove q' (by omega) x hx)).1 hpar
        have h2 : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring n σ τ₁ τ₂ hx hw₃
        have hp_lt : (FriedmannParity.playValue (parityGame n) σ
            (chosenStrategy n σ τ₁ τ₂ x) x).cyclePriority < p₃ := by
          rw [← minVal_eq_playValue_chosenStrategy]
          change (m x).cyclePriority < p₃
          rw [h2]
          exact hgt
        have hcnt := count_playValue_step hp_lt
        rw [← minVal_eq_playValue_chosenStrategy,
          ← step_minStrategy_eq_chosenStrategy] at hcnt
        exact ⟨hle_cnt, hcnt⟩
      have hstep_le : ∀ x ∈ R₃,
          count (parityGame n) (m (step (parityGame n) σ τ₃ x)).path p₃ ≤
            count (parityGame n) (m x).path p₃ := by
        intro x hx
        have ⟨h1, h2⟩ := hstep_rel x hx
        omega
      have heq_w3 := eq_of_le_step_on_recurring
        (fun y => count (parityGame n) (m y).path p₃) hstep_le hw₃
      have ⟨h1, h2⟩ := hstep_rel w₃ hw₃
      rw [if_pos hpw₃] at h2
      omega
    · unfold FriedmannParity.reward
      split_ifs <;> omega

lemma cycleLeader_eq_of_same_cyclePriority {n : ℕ} (hn : 3 ≤ n)
    {σ τ_a τ_b : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ_a : FriedmannParity.Legal (parityGame n) true τ_a)
    {x : Fin (vertices n)}
    (hcp : (FriedmannParity.playValue (parityGame n) σ τ_a x).cyclePriority =
      (FriedmannParity.playValue (parityGame n) σ τ_b x).cyclePriority)
    (hstep : step (parityGame n) σ τ_a x = step (parityGame n) σ τ_b x)
    (hcl_a : x = cycleLeader (parityGame n) σ τ_a x) :
    x = cycleLeader (parityGame n) σ τ_b x := by
  let p := (FriedmannParity.playValue (parityGame n) σ τ_a x).cyclePriority
  let w_b := cycleLeader (parityGame n) σ τ_b x
  have hpx : gamePriority n x = p := by
    have h := playValue_cyclePriority_eq_priority_cycleLeader (parityGame n) σ τ_a x
    rw [← hcl_a] at h
    exact h.symm
  have hpw_b : gamePriority n w_b = p := by
    have h := playValue_cyclePriority_eq_priority_cycleLeader (parityGame n) σ τ_b x
    rw [← hcp] at h
    exact h.symm
  rcases playValue_cyclePriority_cases hn hσ hτ_a x with hp1 | hp6 | hpgt6
  · have hx1 : x = sinkVertex n := (gamePriority_eq_one_iff n x).mp (hpx.trans hp1)
    have hwb1 : w_b = sinkVertex n := (gamePriority_eq_one_iff n w_b).mp (hpw_b.trans hp1)
    exact hx1.trans hwb1.symm
  · have hx_rec : x ∈ FriedmannParity.recurring (FriedmannParity.play (parityGame n) σ τ_a x) := by
      have h := cycleLeader_mem_recurring (parityGame n) σ τ_a x
      rwa [← hcl_a] at h
    have ⟨hu_own, hu_p, hσu⟩ := priority_six_two_cycle hn hσ hτ_a hx_rec hp6 (hpx.trans hp6)
    exact (cycleLeader_eq_of_two_cycle hu_own hu_p (hpx.trans hp6) hσu hstep.symm).symm
  · exact eq_of_gamePriority_eq_of_gt_six n (by rw [hpx]; exact hpgt6) (hpx.trans hpw_b.symm)

lemma valueLE_playValue_minStrategy {n : ℕ} (hn : 3 ≤ n)
    {σ τ₁ τ₂ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (hτ₁ : FriedmannParity.Legal (parityGame n) true τ₁)
    (hτ₂ : FriedmannParity.Legal (parityGame n) true τ₂)
    (v : Fin (vertices n)) :
    ValueLE (parityGame n)
      (FriedmannParity.playValue (parityGame n) σ (minStrategy n σ τ₁ τ₂) v)
      (minVal n σ τ₁ τ₂ v) := by
  let τ₃ := minStrategy n σ τ₁ τ₂
  have hτ₃ : FriedmannParity.Legal (parityGame n) true τ₃ := minStrategy_legal hτ₁ hτ₂
  let π₃ := FriedmannParity.play (parityGame n) σ τ₃ v
  let w₃ := cycleLeader (parityGame n) σ τ₃ v
  let p₃ := (FriedmannParity.playValue (parityGame n) σ τ₃ v).cyclePriority
  let k := (FriedmannParity.playValue (parityGame n) σ τ₃ v).length
  have hcl_play : ∀ t : ℕ, cycleLeader (parityGame n) σ τ₃ (π₃ t) = w₃ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      dsimp only [π₃] at ih ⊢
      rw [play_succ', cycleLeader_step, ih]
  have hcp_play : ∀ t : ℕ,
      (FriedmannParity.playValue (parityGame n) σ τ₃ (π₃ t)).cyclePriority = p₃ := by
    intro t
    rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl_play t,
      ← playValue_cyclePriority_eq_priority_cycleLeader]
  have hbase_w3 : ValueLE (parityGame n)
      (FriedmannParity.playValue (parityGame n) σ τ₃ w₃) (minVal n σ τ₁ τ₂ w₃) := by
    have hrew : FriedmannParity.reward p₃ ≤
        FriedmannParity.reward (minVal n σ τ₁ τ₂ w₃).cyclePriority :=
      reward_playValue_minStrategy_le n σ τ₁ τ₂ v
    have hcl_w3 : w₃ = cycleLeader (parityGame n) σ τ₃ w₃ := by
      have h := hcl_play k
      dsimp only [π₃, k] at h
      rw [play_playValue_length] at h
      exact h.symm
    have hcp_w3 : (FriedmannParity.playValue (parityGame n) σ τ₃ w₃).cyclePriority = p₃ := by
      have h := hcp_play k
      dsimp only [π₃, k] at h
      rw [play_playValue_length] at h
      exact h
    rcases lt_or_eq_of_le hrew with hlt | heq
    · rw [valueLE_iff]
      right; left
      rw [hcp_w3]
      exact hlt
    · have hp_eq : p₃ = (minVal n σ τ₁ τ₂ w₃).cyclePriority := reward_injective heq
      let τ₀ := chosenStrategy n σ τ₁ τ₂ w₃
      have hτ₀ : FriedmannParity.Legal (parityGame n) true τ₀ :=
        chosenStrategy_legal hτ₁ hτ₂ w₃
      have hcp_0 : (FriedmannParity.playValue (parityGame n) σ τ₃ w₃).cyclePriority =
          (FriedmannParity.playValue (parityGame n) σ τ₀ w₃).cyclePriority := by
        rw [hcp_w3, ← minVal_eq_playValue_chosenStrategy, hp_eq]
      have hcl_0 : w₃ = cycleLeader (parityGame n) σ τ₀ w₃ :=
        cycleLeader_eq_of_same_cyclePriority hn hσ hτ₃ hcp_0
          (step_minStrategy_eq_chosenStrategy n σ τ₁ τ₂ w₃) hcl_w3
      have hval_3 := playValue_eq_of_eq_cycleLeader hcl_w3
      have hval_0 := playValue_eq_of_eq_cycleLeader hcl_0
      rw [minVal_eq_playValue_chosenStrategy]
      change ValueLE (parityGame n)
        (FriedmannParity.playValue (parityGame n) σ τ₃ w₃)
        (FriedmannParity.playValue (parityGame n) σ τ₀ w₃)
      rw [hval_3, hval_0, hcp_0]
      exact valueLE_refl (parityGame n) _
  have hind : ∀ d : ℕ, d ≤ k →
      ValueLE (parityGame n)
        (FriedmannParity.playValue (parityGame n) σ τ₃ (π₃ (k - d)))
        (minVal n σ τ₁ τ₂ (π₃ (k - d))) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hk0 : k - 0 = k := by omega
      rw [hk0]
      dsimp only [π₃, k]
      rw [play_playValue_length]
      exact hbase_w3
    | succ d ih =>
      intro hd
      let t := k - (d + 1)
      have ht_lt : t < k := by omega
      have ht_succ : t + 1 = k - d := by omega
      let x := π₃ t
      let x' := step (parityGame n) σ τ₃ x
      have hx'_eq : x' = π₃ (k - d) := by
        dsimp only [x', x, π₃]
        rw [← play_succ', ht_succ]
      have ih' : ValueLE (parityGame n)
          (FriedmannParity.playValue (parityGame n) σ τ₃ x') (minVal n σ τ₁ τ₂ x') := by
        rw [hx'_eq]
        exact ih (by omega)
      let τ_i := chosenStrategy n σ τ₁ τ₂ x
      have hτ_i : FriedmannParity.Legal (parityGame n) true τ_i :=
        chosenStrategy_legal hτ₁ hτ₂ x
      have hm_step : ValueLE (parityGame n) (minVal n σ τ₁ τ₂ x')
          (FriedmannParity.playValue (parityGame n) σ τ_i (step (parityGame n) σ τ_i x)) := by
        dsimp only [x', τ_i]
        rw [← step_minStrategy_eq_chosenStrategy]
        exact minVal_step_le_chosenStrategy n σ τ₁ τ₂ x
      have hle_step : ValueLE (parityGame n)
          (FriedmannParity.playValue (parityGame n) σ τ₃ x')
          (FriedmannParity.playValue (parityGame n) σ τ_i (step (parityGame n) σ τ_i x)) :=
        valueLE_trans ih' hm_step
      have hrew_le : FriedmannParity.reward
          (FriedmannParity.playValue (parityGame n) σ τ₃ x).cyclePriority ≤
          FriedmannParity.reward (minVal n σ τ₁ τ₂ x).cyclePriority := by
        have h := reward_cyclePriority_le_of_valueLE hle_step
        dsimp only [x', τ_i] at h
        rw [playValue_cyclePriority_step, playValue_cyclePriority_step,
          ← minVal_eq_playValue_chosenStrategy] at h
        exact h
      rcases lt_or_eq_of_le hrew_le with hlt | heq
      · rw [valueLE_iff]
        right; left
        exact hlt
      · have hp_eq : (FriedmannParity.playValue (parityGame n) σ τ₃ x).cyclePriority =
            (minVal n σ τ₁ τ₂ x).cyclePriority :=
          reward_injective heq
        have hx_ne_w3 : x ≠ cycleLeader (parityGame n) σ τ₃ x := by
          rw [hcl_play t]
          exact play_ne_cycleLeader_of_lt_length ht_lt
        have hx_ne_i : x ≠ cycleLeader (parityGame n) σ τ_i x := by
          intro hcl_i
          have hcp_i : (FriedmannParity.playValue (parityGame n) σ τ_i x).cyclePriority =
              (FriedmannParity.playValue (parityGame n) σ τ₃ x).cyclePriority := by
            dsimp only [τ_i]
            rw [← minVal_eq_playValue_chosenStrategy, hp_eq]
          exact hx_ne_w3 (cycleLeader_eq_of_same_cyclePriority hn hσ hτ_i hcp_i
            (step_minStrategy_eq_chosenStrategy n σ τ₁ τ₂ x).symm hcl_i)
        have hval_3 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_w3
        have hnot_3 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_w3
        have hval_i := playValue_eq_prepend_of_ne_cycleLeader hx_ne_i
        have hnot_i := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_i
        change ValueLE (parityGame n)
          (FriedmannParity.playValue (parityGame n) σ τ₃ x) (minVal n σ τ₁ τ₂ x)
        rw [minVal_eq_playValue_chosenStrategy, hval_3]
        change ValueLE (parityGame n)
          (prepend (parityGame n) x (FriedmannParity.playValue (parityGame n) σ τ₃ x'))
          (FriedmannParity.playValue (parityGame n) σ τ_i x)
        rw [hval_i]
        apply valueLE_prepend
        · dsimp only [x', τ_i]
          rw [playValue_cyclePriority_step, playValue_cyclePriority_step,
            ← minVal_eq_playValue_chosenStrategy, hp_eq]
        · exact hnot_3
        · exact hnot_i
        · exact hle_step
  have h0 := hind k le_rfl
  have hkk : k - k = 0 := by omega
  rw [hkk] at h0
  exact h0

lemma gameSuccessors_nonempty (n : ℕ) (v : Fin (vertices n)) :
    (gameSuccessors n v).Nonempty := by
  unfold gameSuccessors
  dsimp only
  split_ifs <;> simp

noncomputable def defaultOpponent (n : ℕ) (v : Fin (vertices n)) : Fin (vertices n) :=
  (gameSuccessors_nonempty n v).choose

lemma defaultOpponent_legal (n : ℕ) :
    FriedmannParity.Legal (parityGame n) true (defaultOpponent n) := by
  intro v _
  exact (gameSuccessors_nonempty n v).choose_spec

lemma exists_counterstrategy_list {n : ℕ} (hn : 3 ≤ n)
    {σ : Fin (vertices n) → Fin (vertices n)}
    (hσ : FriedmannParity.Legal (parityGame n) false σ)
    (L : List (Fin (vertices n) → Fin (vertices n))) :
    ∃ τ : Fin (vertices n) → Fin (vertices n),
      FriedmannParity.Legal (parityGame n) true τ ∧
      ∀ τ' ∈ L, FriedmannParity.Legal (parityGame n) true τ' →
        ∀ v, ValueLE (parityGame n)
          (FriedmannParity.playValue (parityGame n) σ τ v)
          (FriedmannParity.playValue (parityGame n) σ τ' v) := by
  induction L with
  | nil =>
    refine ⟨defaultOpponent n, defaultOpponent_legal n, ?_⟩
    intro τ' hmem
    nomatch hmem
  | cons τ₁ L ih =>
    rcases ih with ⟨τ₂, hτ₂, hle₂⟩
    by_cases hτ₁ : FriedmannParity.Legal (parityGame n) true τ₁
    · refine ⟨minStrategy n σ τ₁ τ₂, minStrategy_legal hτ₁ hτ₂, ?_⟩
      intro τ' hmem hleg v
      have hmin := valueLE_playValue_minStrategy hn hσ hτ₁ hτ₂ v
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [heq]
        exact valueLE_trans hmin (minVal_le_left n σ τ₁ τ₂ v)
      · exact valueLE_trans hmin
          (valueLE_trans (minVal_le_right n σ τ₁ τ₂ v) (hle₂ τ' hmem' hleg v))
    · refine ⟨τ₂, hτ₂, ?_⟩
      intro τ' hmem hleg v
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [heq] at hleg
        exact False.elim (hτ₁ hleg)
      · exact hle₂ τ' hmem' hleg v

end Counterstrategy

/-- Lemma 1 on the explicit repeated-priority family. A single legal opponent
strategy minimizes the multiplicity valuation from every starting vertex. -/
theorem counterstrategy (n : ℕ) (hn : 3 ≤ n)
    (σ : Fin (vertices n) → Fin (vertices n))
    (hσ : FriedmannParity.Legal (parityGame n) false σ) :
    ∃ τ : Fin (vertices n) → Fin (vertices n),
      FriedmannParity.Legal (parityGame n) true τ ∧
      ∀ v τ', FriedmannParity.Legal (parityGame n) true τ' →
        FriedmannMultiplicity.ValueLE (parityGame n)
          (FriedmannParity.playValue (parityGame n) σ τ v)
          (FriedmannParity.playValue (parityGame n) σ τ' v) := by
  rcases exists_counterstrategy_list hn hσ
      (Finset.univ : Finset (Fin (vertices n) → Fin (vertices n))).toList with
    ⟨τ, hτ, hle⟩
  refine ⟨τ, hτ, ?_⟩
  intro v τ' hτ'
  exact hle τ' (Finset.mem_toList.mpr (Finset.mem_univ τ')) hτ' v

end FriedmannCunningham

open FriedmannCunningham

theorem solution (n : ℕ) (hn : 3 ≤ n)
    (σ : Fin (vertices n) → Fin (vertices n))
    (hσ : FriedmannParity.Legal (parityGame n) false σ) :
    ∃ τ : Fin (vertices n) → Fin (vertices n),
      FriedmannParity.Legal (parityGame n) true τ ∧
      ∀ v τ', FriedmannParity.Legal (parityGame n) true τ' →
        FriedmannMultiplicity.ValueLE (parityGame n)
          (FriedmannParity.playValue (parityGame n) σ τ v)
          (FriedmannParity.playValue (parityGame n) σ τ' v) :=
  counterstrategy n hn σ hσ

