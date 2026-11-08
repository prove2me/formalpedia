-- Prove2me | solution 1 for FriedmannParity.sink_discounted_order
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T01:39:50.971204+00:00
-- url     : https://prove2.me/submissions/ad4884a4-92fb-45f7-871d-573bc834c4b9

import Definitions.Def_friedmann_payoff
import Definitions.Def_friedmann_parity
import Definitions.Def_friedmann_multiplicity
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith

set_option autoImplicit false

section Mod_counterstrategy
set_option autoImplicit false

namespace FriedmannParity

open FriedmannMultiplicity

/-! ### Part 1: Total Preorder of `FriedmannMultiplicity.ValueLE` and Bridge to `FriedmannParity` -/

lemma reward_injective : Function.Injective reward := by
  intro p q hpq
  unfold reward at hpq
  split_ifs at hpq <;> omega

section GeneralOrder

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma setEquivalent_refl (G : Game V) (A : Finset V) : SetEquivalent G A A :=
  fun _ => rfl

omit [Fintype V] [DecidableEq V] in
lemma setEquivalent_symm {G : Game V} {A B : Finset V} (h : SetEquivalent G A B) :
    SetEquivalent G B A :=
  fun p => (h p).symm

omit [Fintype V] [DecidableEq V] in
lemma setEquivalent_trans {G : Game V} {A B C : Finset V}
    (h1 : SetEquivalent G A B) (h2 : SetEquivalent G B C) :
    SetEquivalent G A C :=
  fun p => (h1 p).trans (h2 p)

omit [Fintype V] [DecidableEq V] in
lemma not_multiplicity_setLT_of_setEquivalent {G : Game V} {A B : Finset V}
    (h : SetEquivalent G A B) : ¬ FriedmannMultiplicity.SetLT G A B := by
  rintro ⟨p, hpne, _, _⟩
  exact hpne (h p)

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_congr_left {G : Game V} {A A' B : Finset V}
    (hA : SetEquivalent G A A') (h : FriedmannMultiplicity.SetLT G A B) :
    FriedmannMultiplicity.SetLT G A' B := by
  rcases h with ⟨p, hpne, hgt, hpar⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← hA p]; exact hpne
  · intro q hq; rw [← hA q]; exact hgt q hq
  · rcases hpar with ⟨he, hlt⟩ | ⟨ho, hlt⟩
    · left; rw [← hA p]; exact ⟨he, hlt⟩
    · right; rw [← hA p]; exact ⟨ho, hlt⟩

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_congr_right {G : Game V} {A B B' : Finset V}
    (hB : SetEquivalent G B B') (h : FriedmannMultiplicity.SetLT G A B) :
    FriedmannMultiplicity.SetLT G A B' := by
  rcases h with ⟨p, hpne, hgt, hpar⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← hB p]; exact hpne
  · intro q hq; rw [← hB q]; exact hgt q hq
  · rcases hpar with ⟨he, hlt⟩ | ⟨ho, hlt⟩
    · left; rw [← hB p]; exact ⟨he, hlt⟩
    · right; rw [← hB p]; exact ⟨ho, hlt⟩

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_asymm {G : Game V} {A B : Finset V}
    (h1 : FriedmannMultiplicity.SetLT G A B) (h2 : FriedmannMultiplicity.SetLT G B A) : False := by
  rcases h1 with ⟨p₁, hpne₁, hgt₁, hpar₁⟩
  rcases h2 with ⟨p₂, hpne₂, hgt₂, hpar₂⟩
  rcases lt_trichotomy p₁ p₂ with hlt | rfl | hgt
  · exact hpne₂ (hgt₁ p₂ hlt).symm
  · rcases hpar₁ with ⟨he₁, hlt₁⟩ | ⟨ho₁, hlt₁⟩ <;>
    rcases hpar₂ with ⟨he₂, hlt₂⟩ | ⟨ho₂, hlt₂⟩ <;> omega
  · exact hpne₁ (hgt₂ p₁ hgt).symm

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_trans {G : Game V} {A B C : Finset V}
    (h1 : FriedmannMultiplicity.SetLT G A B) (h2 : FriedmannMultiplicity.SetLT G B C) :
    FriedmannMultiplicity.SetLT G A C := by
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
lemma count_eq_zero_of_sup_lt {G : Game V} {A : Finset V} {q : ℕ}
    (hq : A.sup G.priority < q) : count G A q = 0 := by
  classical
  unfold count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v hv
  have hle : G.priority v ≤ A.sup G.priority := Finset.le_sup hv
  omega

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_setLT_trichotomy_aux (G : Game V) (A B : Finset V) :
    ∀ M : ℕ, (∀ q, M < q → count G A q = count G B q) →
      SetEquivalent G A B ∨ FriedmannMultiplicity.SetLT G A B ∨ FriedmannMultiplicity.SetLT G B A
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
    · apply multiplicity_setLT_trichotomy_aux G A B M
      intro q hq
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hq) with rfl | hq'
      · exact heq
      · exact hgt q hq'
    · right; rcases Nat.mod_two_eq_zero_or_one (M + 1) with hpar | hpar
      · right; exact ⟨M + 1, by omega, fun q hq => (hgt q hq).symm, Or.inl ⟨hpar, hgt1⟩⟩
      · left; exact ⟨M + 1, by omega, hgt, Or.inr ⟨hpar, hgt1⟩⟩

omit [Fintype V] in
lemma multiplicity_setLT_trichotomy (G : Game V) (A B : Finset V) :
    SetEquivalent G A B ∨ FriedmannMultiplicity.SetLT G A B ∨ FriedmannMultiplicity.SetLT G B A := by
  apply multiplicity_setLT_trichotomy_aux G A B ((A ∪ B).sup G.priority)
  intro q hq
  have hA : A.sup G.priority < q :=
    lt_of_le_of_lt (Finset.sup_mono Finset.subset_union_left) hq
  have hB : B.sup G.priority < q :=
    lt_of_le_of_lt (Finset.sup_mono Finset.subset_union_right) hq
  rw [count_eq_zero_of_sup_lt hA, count_eq_zero_of_sup_lt hB]

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_asymm {G : Game V} {a b : Valuation V}
    (h1 : FriedmannMultiplicity.ValueLT G a b) (h2 : FriedmannMultiplicity.ValueLT G b a) : False := by
  rcases h1 with hr1 | ⟨hp1, hs1⟩ | ⟨hp1, heq1, hl1⟩ <;>
  rcases h2 with hr2 | ⟨hp2, hs2⟩ | ⟨hp2, heq2, hl2⟩
  · omega
  · rw [hp2] at hr1; omega
  · rw [hp2] at hr1; omega
  · rw [hp1] at hr2; omega
  · exact multiplicity_setLT_asymm hs1 hs2
  · exact not_multiplicity_setLT_of_setEquivalent (setEquivalent_symm heq2) hs1
  · rw [hp1] at hr2; omega
  · exact not_multiplicity_setLT_of_setEquivalent (setEquivalent_symm heq1) hs2
  · rcases hl1 with ⟨ho1, hlt1⟩ | ⟨he1, hlt1⟩ <;>
    rcases hl2 with ⟨ho2, hlt2⟩ | ⟨he2, hlt2⟩ <;> omega

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_irrefl (G : Game V) (a : Valuation V) :
    ¬ FriedmannMultiplicity.ValueLT G a a :=
  fun h => multiplicity_valueLT_asymm h h

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLE_refl (G : Game V) (a : Valuation V) :
    FriedmannMultiplicity.ValueLE G a a :=
  multiplicity_valueLT_irrefl G a

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLE_total (G : Game V) (a b : Valuation V) :
    FriedmannMultiplicity.ValueLE G a b ∨ FriedmannMultiplicity.ValueLE G b a := by
  by_cases h : FriedmannMultiplicity.ValueLT G b a
  · right; exact fun h' => multiplicity_valueLT_asymm h h'
  · left; exact h

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_trans {G : Game V} {a b c : Valuation V}
    (h1 : FriedmannMultiplicity.ValueLT G a b) (h2 : FriedmannMultiplicity.ValueLT G b c) :
    FriedmannMultiplicity.ValueLT G a c := by
  rcases h1 with hr1 | ⟨hp1, hs1⟩ | ⟨hp1, heq1, hl1⟩ <;>
  rcases h2 with hr2 | ⟨hp2, hs2⟩ | ⟨hp2, heq2, hl2⟩
  · left; omega
  · left; rw [← hp2]; exact hr1
  · left; rw [← hp2]; exact hr1
  · left; rw [hp1]; exact hr2
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_trans hs1 hs2⟩
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_congr_right heq2 hs1⟩
  · left; rw [hp1]; exact hr2
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_congr_left (setEquivalent_symm heq1) hs2⟩
  · right; right
    refine ⟨hp1.trans hp2, setEquivalent_trans heq1 heq2, ?_⟩
    rw [← hp1] at hl2
    rcases hl1 with ⟨ho1, hlt1⟩ | ⟨he1, hlt1⟩ <;>
    rcases hl2 with ⟨ho2, hlt2⟩ | ⟨he2, hlt2⟩
    · left; exact ⟨ho1, by omega⟩
    · omega
    · omega
    · right; exact ⟨he1, by omega⟩

def ValEq (G : Game V) (a b : Valuation V) : Prop :=
  a.cyclePriority = b.cyclePriority ∧
  SetEquivalent G a.path b.path ∧
  a.length = b.length

omit [Fintype V] in
lemma multiplicity_valueLT_trichotomy (G : Game V) (a b : Valuation V) :
    ValEq G a b ∨ FriedmannMultiplicity.ValueLT G a b ∨ FriedmannMultiplicity.ValueLT G b a := by
  rcases lt_trichotomy (reward a.cyclePriority) (reward b.cyclePriority) with hlt | heq | hgt
  · right; left; exact Or.inl hlt
  · have hp : a.cyclePriority = b.cyclePriority := reward_injective heq
    rcases multiplicity_setLT_trichotomy G a.path b.path with hseq | hslt | hsgt
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
lemma multiplicity_valueLE_iff (G : Game V) (a b : Valuation V) :
    FriedmannMultiplicity.ValueLE G a b ↔ ValEq G a b ∨ FriedmannMultiplicity.ValueLT G a b := by
  constructor
  · intro h
    rcases multiplicity_valueLT_trichotomy G a b with heq | hlt | hgt
    · exact Or.inl heq
    · exact Or.inr hlt
    · exact False.elim (h hgt)
  · rintro (⟨hp, hseq, hlen⟩ | hlt) hgt
    · rcases hgt with hr | ⟨_, hslt⟩ | ⟨_, _, hl⟩
      · rw [hp] at hr; omega
      · exact not_multiplicity_setLT_of_setEquivalent (setEquivalent_symm hseq) hslt
      · rcases hl with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega
    · exact multiplicity_valueLT_asymm hlt hgt

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_of_valEq_of_valueLT {G : Game V} {a b c : Valuation V}
    (h1 : ValEq G a b) (h2 : FriedmannMultiplicity.ValueLT G b c) :
    FriedmannMultiplicity.ValueLT G a c := by
  rcases h1 with ⟨hp1, hseq1, hlen1⟩
  rcases h2 with hr2 | ⟨hp2, hs2⟩ | ⟨hp2, heq2, hl2⟩
  · left; rw [hp1]; exact hr2
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_congr_left (setEquivalent_symm hseq1) hs2⟩
  · right; right
    refine ⟨hp1.trans hp2, setEquivalent_trans hseq1 heq2, ?_⟩
    rw [hp1, hlen1]; exact hl2

omit [Fintype V] [DecidableEq V] in
lemma multiplicity_valueLT_of_valueLT_of_valEq {G : Game V} {a b c : Valuation V}
    (h1 : FriedmannMultiplicity.ValueLT G a b) (h2 : ValEq G b c) :
    FriedmannMultiplicity.ValueLT G a c := by
  rcases h2 with ⟨hp2, hseq2, hlen2⟩
  rcases h1 with hr1 | ⟨hp1, hs1⟩ | ⟨hp1, heq1, hl1⟩
  · left; rw [← hp2]; exact hr1
  · right; left; exact ⟨hp1.trans hp2, multiplicity_setLT_congr_right hseq2 hs1⟩
  · right; right
    refine ⟨hp1.trans hp2, setEquivalent_trans heq1 hseq2, ?_⟩
    rw [← hlen2]; exact hl1

omit [Fintype V] [DecidableEq V] in
lemma valEq_trans {G : Game V} {a b c : Valuation V}
    (h1 : ValEq G a b) (h2 : ValEq G b c) : ValEq G a c :=
  ⟨h1.1.trans h2.1, setEquivalent_trans h1.2.1 h2.2.1, h1.2.2.trans h2.2.2⟩

omit [Fintype V] in
lemma multiplicity_valueLE_trans {G : Game V} {a b c : Valuation V}
    (h1 : FriedmannMultiplicity.ValueLE G a b) (h2 : FriedmannMultiplicity.ValueLE G b c) :
    FriedmannMultiplicity.ValueLE G a c := by
  rw [multiplicity_valueLE_iff] at h1 h2 ⊢
  rcases h1 with heq1 | hlt1 <;> rcases h2 with heq2 | hlt2
  · exact Or.inl (valEq_trans heq1 heq2)
  · exact Or.inr (multiplicity_valueLT_of_valEq_of_valueLT heq1 hlt2)
  · exact Or.inr (multiplicity_valueLT_of_valueLT_of_valEq hlt1 heq2)
  · exact Or.inr (multiplicity_valueLT_trans hlt1 hlt2)

/-! #### Injective Priority Bridge between `FriedmannParity` and `FriedmannMultiplicity` -/

omit [Fintype V] [DecidableEq V] in
lemma exists_of_count_pos {G : Game V} {A : Finset V} {p : ℕ}
    (h : 0 < count G A p) : ∃ w ∈ A, G.priority w = p := by
  classical
  unfold count at h
  rcases Finset.card_pos.mp h with ⟨w, hw⟩
  rw [Finset.mem_filter] at hw
  exact ⟨w, hw.1, hw.2⟩

omit [Fintype V] in
lemma count_priority_eq_ite_of_injective {G : Game V} (hinj : Function.Injective G.priority)
    (A : Finset V) (u : V) :
    count G A (G.priority u) = if u ∈ A then 1 else 0 := by
  classical
  unfold count
  have hfilt : A.filter (fun v => G.priority v = G.priority u) = if u ∈ A then {u} else ∅ := by
    ext v
    simp only [Finset.mem_filter, hinj.eq_iff]
    split_ifs with hu
    · simp only [Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hu, h⟩⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro hv rfl
      exact hu hv
  rw [hfilt]
  split_ifs <;> simp

omit [Fintype V] [DecidableEq V] in
lemma count_le_one_of_injective {G : Game V} (hinj : Function.Injective G.priority)
    (A : Finset V) (p : ℕ) : count G A p ≤ 1 := by
  classical
  unfold count
  rw [Finset.card_le_one]
  intro u hu v hv
  rw [Finset.mem_filter] at hu hv
  exact hinj (hu.2.trans hv.2.symm)

omit [Fintype V] in
lemma mem_symmDiff_iff_count_ne {G : Game V} (hinj : Function.Injective G.priority)
    (A B : Finset V) (u : V) :
    u ∈ (A \ B) ∪ (B \ A) ↔ count G A (G.priority u) ≠ count G B (G.priority u) := by
  rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff,
      count_priority_eq_ite_of_injective hinj A u,
      count_priority_eq_ite_of_injective hinj B u]
  by_cases huA : u ∈ A <;> by_cases huB : u ∈ B <;> simp [huA, huB]

omit [Fintype V] in
lemma setEquivalent_iff_eq {G : Game V} (hinj : Function.Injective G.priority)
    (A B : Finset V) : SetEquivalent G A B ↔ A = B := by
  constructor
  · intro h
    ext u
    have hu := h (G.priority u)
    rw [count_priority_eq_ite_of_injective hinj A u,
        count_priority_eq_ite_of_injective hinj B u] at hu
    by_cases huA : u ∈ A <;> by_cases huB : u ∈ B <;> simp_all
  · rintro rfl
    exact fun _ => rfl

omit [Fintype V] in
lemma setLT_iff_multiplicity_setLT {G : Game V} (hinj : Function.Injective G.priority)
    (A B : Finset V) : SetLT G A B ↔ FriedmannMultiplicity.SetLT G A B := by
  constructor
  · rintro ⟨w, hw_mem, hw_max, hw_par⟩
    refine ⟨G.priority w, (mem_symmDiff_iff_count_ne hinj A B w).mp hw_mem, ?_, ?_⟩
    · intro q hq
      by_contra hne
      have hpos : 0 < count G A q ∨ 0 < count G B q := by omega
      rcases hpos with hA | hB
      · rcases exists_of_count_pos hA with ⟨u, _, rfl⟩
        have hu_mem : u ∈ (A \ B) ∪ (B \ A) :=
          (mem_symmDiff_iff_count_ne hinj A B u).mpr hne
        have hle := hw_max u hu_mem
        omega
      · rcases exists_of_count_pos hB with ⟨u, _, rfl⟩
        have hu_mem : u ∈ (A \ B) ∪ (B \ A) :=
          (mem_symmDiff_iff_count_ne hinj A B u).mpr hne
        have hle := hw_max u hu_mem
        omega
    · rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hw_mem
      rw [count_priority_eq_ite_of_injective hinj A w,
          count_priority_eq_ite_of_injective hinj B w]
      rcases hw_par with ⟨he, hwB⟩ | ⟨ho, hwA⟩
      · left
        have hwA : w ∉ A := by
          rcases hw_mem with ⟨_, hnB⟩ | ⟨_, hnA⟩
          · exact False.elim (hnB hwB)
          · exact hnA
        simp [he, hwA, hwB]
      · right
        have hwB : w ∉ B := by
          rcases hw_mem with ⟨_, hnB⟩ | ⟨_, hnA⟩
          · exact hnB
          · exact False.elim (hnA hwA)
        simp [ho, hwA, hwB]
  · rintro ⟨p, hp_ne, hp_max, hp_par⟩
    have hpos : 0 < count G A p ∨ 0 < count G B p := by omega
    have hex : ∃ w, G.priority w = p := by
      rcases hpos with hA | hB
      · rcases exists_of_count_pos hA with ⟨w, _, hw⟩; exact ⟨w, hw⟩
      · rcases exists_of_count_pos hB with ⟨w, _, hw⟩; exact ⟨w, hw⟩
    rcases hex with ⟨w, rfl⟩
    have hw_mem : w ∈ (A \ B) ∪ (B \ A) :=
      (mem_symmDiff_iff_count_ne hinj A B w).mpr hp_ne
    refine ⟨w, hw_mem, ?_, ?_⟩
    · intro u hu_mem
      have hu_ne := (mem_symmDiff_iff_count_ne hinj A B u).mp hu_mem
      by_contra hlt
      exact hu_ne (hp_max (G.priority u) (by omega))
    · rw [count_priority_eq_ite_of_injective hinj A w,
          count_priority_eq_ite_of_injective hinj B w] at hp_par
      rcases hp_par with ⟨he, hlt⟩ | ⟨ho, hlt⟩
      · left
        refine ⟨he, ?_⟩
        by_cases hwB : w ∈ B
        · exact hwB
        · simp [hwB] at hlt
      · right
        refine ⟨ho, ?_⟩
        by_cases hwA : w ∈ A
        · exact hwA
        · simp [hwA] at hlt

omit [Fintype V] in
lemma valEq_iff_eq {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValEq G a b ↔ a = b := by
  unfold ValEq
  rw [setEquivalent_iff_eq hinj]
  cases a; cases b
  simp

omit [Fintype V] in
lemma valueLT_iff_multiplicity_valueLT {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValueLT G a b ↔ FriedmannMultiplicity.ValueLT G a b := by
  unfold ValueLT FriedmannMultiplicity.ValueLT
  rw [setLT_iff_multiplicity_setLT hinj, setEquivalent_iff_eq hinj]

omit [Fintype V] in
lemma valueLE_iff_multiplicity_valueLE {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValueLE G a b ↔ FriedmannMultiplicity.ValueLE G a b := by
  unfold ValueLE
  rw [multiplicity_valueLE_iff, valEq_iff_eq hinj, valueLT_iff_multiplicity_valueLT hinj]

omit [Fintype V] in
lemma valueLT_asymm {G : Game V} (hinj : Function.Injective G.priority)
    {a b : Valuation V} (h1 : ValueLT G a b) (h2 : ValueLT G b a) : False := by
  rw [valueLT_iff_multiplicity_valueLT hinj] at h1 h2
  exact multiplicity_valueLT_asymm h1 h2

omit [Fintype V] in
lemma valueLT_irrefl {G : Game V} (hinj : Function.Injective G.priority)
    (a : Valuation V) : ¬ ValueLT G a a :=
  fun h => valueLT_asymm hinj h h

omit [Fintype V] in
lemma valueLT_trans {G : Game V} (hinj : Function.Injective G.priority)
    {a b c : Valuation V} (h1 : ValueLT G a b) (h2 : ValueLT G b c) : ValueLT G a c := by
  rw [valueLT_iff_multiplicity_valueLT hinj] at h1 h2 ⊢
  exact multiplicity_valueLT_trans h1 h2

omit [Fintype V] in
lemma valueLT_trichotomy {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : a = b ∨ ValueLT G a b ∨ ValueLT G b a := by
  rw [← valEq_iff_eq hinj, valueLT_iff_multiplicity_valueLT hinj,
      valueLT_iff_multiplicity_valueLT hinj]
  exact multiplicity_valueLT_trichotomy G a b

omit [Fintype V] in
lemma valueLE_refl (G : Game V) (a : Valuation V) : ValueLE G a a :=
  Or.inl rfl

omit [Fintype V] in
lemma valueLE_iff_not_valueLT {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValueLE G a b ↔ ¬ ValueLT G b a := by
  rw [valueLE_iff_multiplicity_valueLE hinj]
  unfold FriedmannMultiplicity.ValueLE
  rw [valueLT_iff_multiplicity_valueLT hinj]

omit [Fintype V] in
lemma valueLE_total {G : Game V} (hinj : Function.Injective G.priority)
    (a b : Valuation V) : ValueLE G a b ∨ ValueLE G b a := by
  rw [valueLE_iff_multiplicity_valueLE hinj, valueLE_iff_multiplicity_valueLE hinj]
  exact multiplicity_valueLE_total G a b

omit [Fintype V] in
lemma valueLE_trans {G : Game V} (hinj : Function.Injective G.priority)
    {a b c : Valuation V} (h1 : ValueLE G a b) (h2 : ValueLE G b c) : ValueLE G a c := by
  rw [valueLE_iff_multiplicity_valueLE hinj] at h1 h2 ⊢
  exact multiplicity_valueLE_trans h1 h2

omit [Fintype V] in
lemma valueLE_antisymm {G : Game V} (hinj : Function.Injective G.priority)
    {a b : Valuation V} (h1 : ValueLE G a b) (h2 : ValueLE G b a) : a = b := by
  rcases h1 with rfl | hlt1
  · rfl
  · rcases h2 with rfl | hlt2
    · rfl
    · exact False.elim (valueLT_asymm hinj hlt1 hlt2)

omit [Fintype V] in
lemma valueLT_of_valueLE_of_valueLT {G : Game V} (hinj : Function.Injective G.priority)
    {a b c : Valuation V} (h1 : ValueLE G a b) (h2 : ValueLT G b c) : ValueLT G a c := by
  rcases h1 with rfl | hlt1
  · exact h2
  · exact valueLT_trans hinj hlt1 h2

omit [Fintype V] in
lemma valueLT_of_valueLT_of_valueLE {G : Game V} (hinj : Function.Injective G.priority)
    {a b c : Valuation V} (h1 : ValueLT G a b) (h2 : ValueLE G b c) : ValueLT G a c := by
  rcases h2 with rfl | hlt2
  · exact h1
  · exact valueLT_trans hinj h1 hlt2

end GeneralOrder

/-! ### Part 2: General Finite-Orbit and `playValue` Unfolding Lemmas -/

section GeneralOrbit

variable {V : Type} [Fintype V] [DecidableEq V]

def step (G : Game V) (σ τ : V → V) (w : V) : V :=
  if G.owner w = false then σ w else τ w

omit [Fintype V] [DecidableEq V] in
lemma play_eq_iterate (G : Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    play G σ τ v t = (step G σ τ)^[t] v :=
  rfl

omit [Fintype V] [DecidableEq V] in
lemma play_zero (G : Game V) (σ τ : V → V) (v : V) :
    play G σ τ v 0 = v :=
  rfl

omit [Fintype V] [DecidableEq V] in
lemma play_succ (G : Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    play G σ τ v (t + 1) = play G σ τ (step G σ τ v) t :=
  Function.iterate_succ_apply (step G σ τ) t v

omit [Fintype V] [DecidableEq V] in
lemma play_succ' (G : Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    play G σ τ v (t + 1) = step G σ τ (play G σ τ v t) :=
  Function.iterate_succ_apply' (step G σ τ) t v

omit [Fintype V] [DecidableEq V] in
lemma play_add (G : Game V) (σ τ : V → V) (v : V) (a b : ℕ) :
    play G σ τ v (a + b) = play G σ τ (play G σ τ v a) b := by
  simp only [play_eq_iterate]
  rw [Nat.add_comm, Function.iterate_add_apply]

omit [DecidableEq V] in
lemma mem_recurring_iff {π : ℕ → V} {w : V} :
    w ∈ recurring π ↔ ∀ t, ∃ k, t ≤ k ∧ π k = w := by
  classical
  unfold recurring
  simp

omit [DecidableEq V] in
lemma recurring_step (G : Game V) (σ τ : V → V) (v : V) :
    recurring (play G σ τ (step G σ τ v)) = recurring (play G σ τ v) := by
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
lemma recurring_play (G : Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    recurring (play G σ τ (play G σ τ v t)) = recurring (play G σ τ v) := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [play_succ, ih, recurring_step]

omit [DecidableEq V] in
lemma recurring_nonempty (G : Game V) (σ τ : V → V) (v : V) :
    (recurring (play G σ τ v)).Nonempty := by
  classical
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hnot : ∀ w : V, ∃ t, ∀ k, t ≤ k → play G σ τ v k ≠ w := by
    intro w
    have hw : w ∉ recurring (play G σ τ v) := by simp [h]
    rw [mem_recurring_iff] at hw
    simpa using hw
  choose B hB using hnot
  let T := Finset.univ.sup B
  let w := play G σ τ v T
  have hle : B w ≤ T := Finset.le_sup (Finset.mem_univ w)
  exact hB w T hle rfl

omit [DecidableEq V] in
lemma exists_play_eq_of_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) :
    ∃ k, play G σ τ v k = w := by
  rw [mem_recurring_iff] at hw
  rcases hw 0 with ⟨k, _, hk⟩
  exact ⟨k, hk⟩

omit [DecidableEq V] in
lemma step_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) :
    step G σ τ w ∈ recurring (play G σ τ v) := by
  rw [mem_recurring_iff] at hw ⊢
  intro t
  rcases hw t with ⟨k, htk, hk⟩
  refine ⟨k + 1, by omega, ?_⟩
  rw [play_succ', hk]

omit [DecidableEq V] in
lemma play_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) (s : ℕ) :
    play G σ τ w s ∈ recurring (play G σ τ v) := by
  induction s with
  | zero => exact hw
  | succ s ih =>
    rw [play_succ']
    exact step_mem_recurring ih

omit [DecidableEq V] in
lemma exists_pos_play_eq_self_of_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) :
    ∃ L > 0, play G σ τ w L = w := by
  rw [mem_recurring_iff] at hw
  rcases hw 0 with ⟨t₀, _, ht₀⟩
  rcases hw (t₀ + 1) with ⟨k, htk, hk⟩
  refine ⟨k - t₀, by omega, ?_⟩
  have hadd : t₀ + (k - t₀) = k := by omega
  rw [← ht₀, ← play_add, hadd, hk, ht₀]

omit [DecidableEq V] in
lemma recurring_eq_of_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v)) :
    recurring (play G σ τ w) = recurring (play G σ τ v) := by
  rcases exists_play_eq_of_mem_recurring hw with ⟨t₀, rfl⟩
  exact recurring_play G σ τ v t₀

omit [DecidableEq V] in
lemma exists_recurring_eq_sup (G : Game V) (σ τ : V → V) (v : V) :
    ∃ w, w ∈ recurring (play G σ τ v) ∧
      G.priority w = (recurring (play G σ τ v)).sup G.priority := by
  rcases Finset.exists_mem_eq_sup (recurring (play G σ τ v))
    (recurring_nonempty G σ τ v) G.priority with ⟨w, hw, hp⟩
  exact ⟨w, hw, hp.symm⟩

noncomputable def cycleLeader (G : Game V) (σ τ : V → V) (v : V) : V := by
  classical
  let π := play G σ τ v
  let p := (recurring π).sup G.priority
  exact if h : ∃ w, w ∈ recurring π ∧ G.priority w = p
    then Classical.choose h else v

omit [DecidableEq V] in
lemma cycleLeader_eq_choose (G : Game V) (σ τ : V → V) (v : V) :
    cycleLeader G σ τ v = Classical.choose (exists_recurring_eq_sup G σ τ v) := by
  unfold cycleLeader
  dsimp only
  rw [dif_pos (exists_recurring_eq_sup G σ τ v)]

omit [DecidableEq V] in
lemma cycleLeader_mem_recurring (G : Game V) (σ τ : V → V) (v : V) :
    cycleLeader G σ τ v ∈ recurring (play G σ τ v) := by
  rw [cycleLeader_eq_choose]
  exact (Classical.choose_spec (exists_recurring_eq_sup G σ τ v)).1

omit [DecidableEq V] in
lemma priority_cycleLeader (G : Game V) (σ τ : V → V) (v : V) :
    G.priority (cycleLeader G σ τ v) =
      (recurring (play G σ τ v)).sup G.priority := by
  rw [cycleLeader_eq_choose]
  exact (Classical.choose_spec (exists_recurring_eq_sup G σ τ v)).2

omit [DecidableEq V] in
lemma cycleLeader_step (G : Game V) (σ τ : V → V) (v : V) :
    cycleLeader G σ τ (step G σ τ v) = cycleLeader G σ τ v := by
  rw [cycleLeader_eq_choose, cycleLeader_eq_choose]
  have hrec := recurring_step G σ τ v
  congr! 2
  all_goals rw [hrec]

omit [Fintype V] [DecidableEq V] in
lemma exists_lt_of_play_eq_of_add {G : Game V} {σ τ : V → V} {v w : V} {i j : ℕ}
    (hij : i < j) (heq : play G σ τ v i = play G σ τ v j) :
    ∀ d : ℕ, play G σ τ v (i + d) = w →
      ∃ r < j, play G σ τ v r = w := by
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
lemma exists_lt_of_play_eq_of_mem_recurring {G : Game V} {σ τ : V → V} {v w : V}
    (hw : w ∈ recurring (play G σ τ v))
    {i j : ℕ} (hij : i < j)
    (heq : play G σ τ v i = play G σ τ v j) :
    ∃ r < j, play G σ τ v r = w := by
  rw [mem_recurring_iff] at hw
  rcases hw i with ⟨k, hik, hk⟩
  have hk' : i + (k - i) = k := by omega
  rw [← hk'] at hk
  exact exists_lt_of_play_eq_of_add hij heq (k - i) hk

omit [DecidableEq V] in
lemma exists_play_eq_cycleLeader (G : Game V) (σ τ : V → V) (v : V) :
    ∃ k : ℕ, play G σ τ v k = cycleLeader G σ τ v :=
  exists_play_eq_of_mem_recurring (cycleLeader_mem_recurring G σ τ v)

lemma playValue_cyclePriority (G : Game V) (σ τ : V → V) (v : V) :
    (playValue G σ τ v).cyclePriority =
      (recurring (play G σ τ v)).sup G.priority :=
  rfl

lemma playValue_cyclePriority_eq_priority_cycleLeader
    (G : Game V) (σ τ : V → V) (v : V) :
    (playValue G σ τ v).cyclePriority = G.priority (cycleLeader G σ τ v) :=
  (priority_cycleLeader G σ τ v).symm

lemma playValue_cyclePriority_step (G : Game V) (σ τ : V → V) (v : V) :
    (playValue G σ τ (step G σ τ v)).cyclePriority =
      (playValue G σ τ v).cyclePriority := by
  simp only [playValue_cyclePriority, recurring_step]

lemma playValue_length_eq_find (G : Game V) (σ τ : V → V) (v : V) :
    (playValue G σ τ v).length =
      Nat.find (exists_play_eq_cycleLeader G σ τ v) := by
  classical
  change (if h : ∃ k : ℕ, play G σ τ v k = cycleLeader G σ τ v
    then Nat.find h else 0) = _
  rw [dif_pos (exists_play_eq_cycleLeader G σ τ v)]

lemma play_playValue_length (G : Game V) (σ τ : V → V) (v : V) :
    play G σ τ v (playValue G σ τ v).length =
      cycleLeader G σ τ v := by
  rw [playValue_length_eq_find]
  exact Nat.find_spec (exists_play_eq_cycleLeader G σ τ v)

lemma play_ne_cycleLeader_of_lt_length {G : Game V} {σ τ : V → V} {v : V} {t : ℕ}
    (ht : t < (playValue G σ τ v).length) :
    play G σ τ v t ≠ cycleLeader G σ τ v := by
  rw [playValue_length_eq_find] at ht
  exact Nat.find_min (exists_play_eq_cycleLeader G σ τ v) ht

lemma length_le_of_play_eq_cycleLeader (G : Game V) (σ τ : V → V) (v : V) {t : ℕ}
    (ht : play G σ τ v t = cycleLeader G σ τ v) :
    (playValue G σ τ v).length ≤ t := by
  rw [playValue_length_eq_find]
  exact Nat.find_min' (exists_play_eq_cycleLeader G σ τ v) ht

lemma play_injective_of_le_length (G : Game V) (σ τ : V → V) (v : V) {i j : ℕ}
    (hi : i ≤ (playValue G σ τ v).length)
    (hj : j ≤ (playValue G σ τ v).length)
    (heq : play G σ τ v i = play G σ τ v j) :
    i = j := by
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · rcases exists_lt_of_play_eq_of_mem_recurring (cycleLeader_mem_recurring G σ τ v) hlt heq with
      ⟨r, hrj, hr⟩
    exact False.elim (play_ne_cycleLeader_of_lt_length (lt_of_lt_of_le hrj hj) hr)
  · rfl
  · rcases exists_lt_of_play_eq_of_mem_recurring (cycleLeader_mem_recurring G σ τ v) hgt heq.symm with
      ⟨r, hri, hr⟩
    exact False.elim (play_ne_cycleLeader_of_lt_length (lt_of_lt_of_le hri hi) hr)

lemma mem_playValue_path_iff {G : Game V} {σ τ : V → V} {v u : V} :
    u ∈ (playValue G σ τ v).path ↔
      (∃ t < (playValue G σ τ v).length, play G σ τ v t = u) ∧
      (playValue G σ τ v).cyclePriority < G.priority u := by
  classical
  change u ∈ ((Finset.range (playValue G σ τ v).length).image
    (play G σ τ v)).filter
    (fun w => (playValue G σ τ v).cyclePriority < G.priority w) ↔ _
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]

lemma playValue_path_eq_empty_of_mem_recurring {G : Game V} {σ τ : V → V} {v x : V}
    (hx : x ∈ recurring (play G σ τ v)) :
    (playValue G σ τ x).path = ∅ := by
  ext u
  rw [mem_playValue_path_iff]
  simp only [Finset.notMem_empty, iff_false, not_and]
  rintro ⟨t, _, rfl⟩
  have hmem : play G σ τ x t ∈ recurring (play G σ τ x) :=
    play_mem_recurring (by rw [recurring_eq_of_mem_recurring hx]; exact hx) t
  have hle : G.priority (play G σ τ x t) ≤ (playValue G σ τ x).cyclePriority :=
    Finset.le_sup hmem
  omega

lemma playValue_eq_of_eq_cycleLeader {G : Game V} {σ τ : V → V} {u : V}
    (hu : u = cycleLeader G σ τ u) :
    playValue G σ τ u = ⟨(playValue G σ τ u).cyclePriority, ∅, 0⟩ := by
  have hlen : (playValue G σ τ u).length = 0 := by
    have h0 : (playValue G σ τ u).length ≤ 0 :=
      length_le_of_play_eq_cycleLeader G σ τ u hu
    omega
  have hpath : (playValue G σ τ u).path = ∅ := by
    ext x
    rw [mem_playValue_path_iff, hlen]
    simp
  cases h : playValue G σ τ u
  simp only [h] at hlen hpath ⊢
  subst hlen hpath
  rfl

noncomputable def prepend (G : Game V) (u : V) (a : Valuation V) : Valuation V := by
  classical
  exact ⟨a.cyclePriority,
    if a.cyclePriority < G.priority u then insert u a.path else a.path,
    a.length + 1⟩

lemma playValue_length_eq_succ_of_ne_cycleLeader {G : Game V} {σ τ : V → V} {u : V}
    (hu : u ≠ cycleLeader G σ τ u) :
    (playValue G σ τ u).length =
      (playValue G σ τ (step G σ τ u)).length + 1 := by
  have hpos : 0 < (playValue G σ τ u).length := by
    by_contra h0
    have hzero : (playValue G σ τ u).length = 0 := by omega
    have hplay := play_playValue_length G σ τ u
    rw [hzero, play_zero] at hplay
    exact hu hplay
  have hle1 : (playValue G σ τ (step G σ τ u)).length ≤
      (playValue G σ τ u).length - 1 := by
    apply length_le_of_play_eq_cycleLeader G σ τ (step G σ τ u)
    rw [cycleLeader_step, ← play_succ]
    have h1 : (playValue G σ τ u).length - 1 + 1 = (playValue G σ τ u).length := by omega
    rw [h1]
    exact play_playValue_length G σ τ u
  have hle2 : (playValue G σ τ u).length ≤
      (playValue G σ τ (step G σ τ u)).length + 1 := by
    apply length_le_of_play_eq_cycleLeader G σ τ u
    rw [play_succ, ← cycleLeader_step]
    exact play_playValue_length G σ τ (step G σ τ u)
  omega

lemma notMem_playValue_step_path_of_ne_cycleLeader {G : Game V} {σ τ : V → V} {u : V}
    (hu : u ≠ cycleLeader G σ τ u) :
    u ∉ (playValue G σ τ (step G σ τ u)).path := by
  rw [mem_playValue_path_iff]
  rintro ⟨⟨t, ht, hplay⟩, _⟩
  have hlen : (playValue G σ τ u).length =
      (playValue G σ τ (step G σ τ u)).length + 1 :=
    playValue_length_eq_succ_of_ne_cycleLeader hu
  rw [← play_succ] at hplay
  have h0 : play G σ τ u (t + 1) = play G σ τ u 0 := hplay
  have hinj := play_injective_of_le_length G σ τ u (by omega) (by omega) h0
  omega

lemma playValue_eq_prepend_of_ne_cycleLeader {G : Game V} {σ τ : V → V} {u : V}
    (hu : u ≠ cycleLeader G σ τ u) :
    playValue G σ τ u = prepend G u (playValue G σ τ (step G σ τ u)) := by
  classical
  have hcp := (playValue_cyclePriority_step G σ τ u).symm
  have hlen : (playValue G σ τ u).length =
      (playValue G σ τ (step G σ τ u)).length + 1 :=
    playValue_length_eq_succ_of_ne_cycleLeader hu
  have hpath : (playValue G σ τ u).path =
      if (playValue G σ τ (step G σ τ u)).cyclePriority < G.priority u
      then insert u (playValue G σ τ (step G σ τ u)).path
      else (playValue G σ τ (step G σ τ u)).path := by
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
  cases hpv : playValue G σ τ u
  cases hpv' : playValue G σ τ (step G σ τ u)
  simp only [hpv, hpv'] at hcp hlen hpath ⊢
  congr!

omit [Fintype V] in
lemma count_insert_of_notMem {G : Game V} {A : Finset V} {u : V}
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
lemma count_prepend_of_notMem {G : Game V} {a : Valuation V}
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
lemma multiplicity_valueLE_prepend {G : Game V} {a b : Valuation V} {u : V}
    (hp : a.cyclePriority = b.cyclePriority) (hua : u ∉ a.path) (hub : u ∉ b.path)
    (hab : FriedmannMultiplicity.ValueLE G a b) :
    FriedmannMultiplicity.ValueLE G (prepend G u a) (prepend G u b) := by
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

lemma count_playValue_step {G : Game V} {σ τ : V → V} {u : V} {q : ℕ}
    (hq : (playValue G σ τ u).cyclePriority < q) :
    count G (playValue G σ τ u).path q =
      count G (playValue G σ τ (step G σ τ u)).path q +
        (if G.priority u = q then 1 else 0) := by
  by_cases hu : u = cycleLeader G σ τ u
  · have hpu : G.priority u = (playValue G σ τ u).cyclePriority := by
      rw [playValue_cyclePriority_eq_priority_cycleLeader, ← hu]
    have hne : G.priority u ≠ q := by omega
    have humem : u ∈ recurring (play G σ τ u) := by
      have hmem := cycleLeader_mem_recurring G σ τ u
      rwa [← hu] at hmem
    have hp1 : (playValue G σ τ u).path = ∅ :=
      playValue_path_eq_empty_of_mem_recurring humem
    have hp2 : (playValue G σ τ (step G σ τ u)).path = ∅ :=
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

lemma cycleLeader_eq_of_cyclePriority_eq {G : Game V} (hinj : Function.Injective G.priority)
    {σ₁ τ₁ σ₂ τ₂ : V → V} {v₁ v₂ : V}
    (hcp : (playValue G σ₁ τ₁ v₁).cyclePriority = (playValue G σ₂ τ₂ v₂).cyclePriority) :
    cycleLeader G σ₁ τ₁ v₁ = cycleLeader G σ₂ τ₂ v₂ := by
  apply hinj
  rw [← playValue_cyclePriority_eq_priority_cycleLeader,
      ← playValue_cyclePriority_eq_priority_cycleLeader, hcp]

end GeneralOrbit

/-! ### Part 3: Two-Strategy Minimum and Global Optimal Counterstrategy -/

section Counterstrategy

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma le_play_of_le_step_on_recurring {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ recurring (play G σ τ v), F (step G σ τ y) ≤ F y) :
    ∀ d : ℕ, ∀ y ∈ recurring (play G σ τ v), F (play G σ τ y d) ≤ F y
  | 0, y, _ => le_rfl
  | d + 1, y, hy => by
    rw [play_succ]
    exact le_trans
      (le_play_of_le_step_on_recurring F hstep d (step G σ τ y) (step_mem_recurring hy))
      (hstep y hy)

omit [DecidableEq V] in
lemma eq_of_le_step_on_recurring {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ recurring (play G σ τ v), F (step G σ τ y) ≤ F y)
    {x : V} (hx : x ∈ recurring (play G σ τ v)) :
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
lemma play_le_of_step_le_on_recurring {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ recurring (play G σ τ v), F y ≤ F (step G σ τ y)) :
    ∀ d : ℕ, ∀ y ∈ recurring (play G σ τ v), F y ≤ F (play G σ τ y d)
  | 0, y, _ => le_rfl
  | d + 1, y, hy => by
    rw [play_succ]
    exact le_trans (hstep y hy)
      (play_le_of_step_le_on_recurring F hstep d (step G σ τ y) (step_mem_recurring hy))

omit [DecidableEq V] in
lemma eq_of_step_le_on_recurring {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℕ)
    (hstep : ∀ y ∈ recurring (play G σ τ v), F y ≤ F (step G σ τ y))
    {x : V} (hx : x ∈ recurring (play G σ τ v)) :
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
lemma le_play_int {G : Game V} {σ τ : V → V}
    (F : V → ℤ) (hstep : ∀ y, F (step G σ τ y) ≤ F y) :
    ∀ d : ℕ, ∀ y : V, F (play G σ τ y d) ≤ F y
  | 0, _ => le_rfl
  | d + 1, y => by
    rw [play_succ]
    exact le_trans (le_play_int F hstep d (step G σ τ y)) (hstep y)

omit [DecidableEq V] in
lemma eq_on_recurring_of_le_step_int {G : Game V} {σ τ : V → V} {v : V}
    (F : V → ℤ) (hstep : ∀ y, F (step G σ τ y) ≤ F y)
    {x w : V}
    (hx : x ∈ recurring (play G σ τ v))
    (hw : w ∈ recurring (play G σ τ v)) :
    F x = F w := by
  have hwx : w ∈ recurring (play G σ τ x) := by
    rwa [recurring_eq_of_mem_recurring hx]
  have hxw : x ∈ recurring (play G σ τ w) := by
    rwa [recurring_eq_of_mem_recurring hw]
  rcases exists_play_eq_of_mem_recurring hwx with ⟨d₁, hd₁⟩
  rcases exists_play_eq_of_mem_recurring hxw with ⟨d₂, hd₂⟩
  have h1 := le_play_int F hstep d₁ x
  have h2 := le_play_int F hstep d₂ w
  rw [hd₁] at h1
  rw [hd₂] at h2
  omega

omit [Fintype V] [DecidableEq V] in
lemma reward_cyclePriority_le_of_multiplicity_valueLE {G : Game V}
    {a b : Valuation V} (hab : FriedmannMultiplicity.ValueLE G a b) :
    reward a.cyclePriority ≤ reward b.cyclePriority := by
  by_contra hgt
  exact hab (Or.inl (by omega))

omit [Fintype V] in
lemma reward_cyclePriority_le_of_valueLE {G : Game V}
    {a b : Valuation V} (hab : ValueLE G a b) :
    reward a.cyclePriority ≤ reward b.cyclePriority := by
  rcases hab with rfl | hr | ⟨hp, _⟩ | ⟨hp, _⟩
  · exact le_rfl
  · omega
  · rw [hp]
  · rw [hp]

omit [Fintype V] [DecidableEq V] in
lemma count_le_or_ge_of_multiplicity_valueLE {G : Game V}
    {a b : Valuation V} {q : ℕ}
    (hab : FriedmannMultiplicity.ValueLE G a b)
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
lemma length_le_of_multiplicity_valueLE_odd {G : Game V}
    {a b : Valuation V}
    (hab : FriedmannMultiplicity.ValueLE G a b)
    (hp : a.cyclePriority = b.cyclePriority)
    (hseq : SetEquivalent G a.path b.path)
    (hodd : a.cyclePriority % 2 = 1) :
    a.length ≤ b.length := by
  by_contra hlt
  apply hab
  right; right
  exact ⟨hp.symm, setEquivalent_symm hseq, Or.inl ⟨hp ▸ hodd, by omega⟩⟩

omit [Fintype V] [DecidableEq V] in
lemma length_ge_of_multiplicity_valueLE_even {G : Game V}
    {a b : Valuation V}
    (hab : FriedmannMultiplicity.ValueLE G a b)
    (hp : a.cyclePriority = b.cyclePriority)
    (hseq : SetEquivalent G a.path b.path)
    (heven : a.cyclePriority % 2 = 0) :
    b.length ≤ a.length := by
  by_contra hlt
  apply hab
  right; right
  exact ⟨hp.symm, setEquivalent_symm hseq, Or.inr ⟨hp ▸ heven, by omega⟩⟩

lemma count_playValue_eq_zero_of_le_cyclePriority
    {G : Game V} {σ τ : V → V} {v : V} {q : ℕ}
    (hq : q ≤ (playValue G σ τ v).cyclePriority) :
    count G (playValue G σ τ v).path q = 0 := by
  classical
  unfold count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu
  rw [mem_playValue_path_iff] at hu
  omega

omit [DecidableEq V] in
lemma count_eq_zero_of_univ_sup_lt {G : Game V} (A : Finset V) {q : ℕ}
    (hq : Finset.univ.sup G.priority < q) : count G A q = 0 :=
  count_eq_zero_of_sup_lt (lt_of_le_of_lt (Finset.sup_mono (Finset.subset_univ A)) hq)

noncomputable def minStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) : V := by
  classical
  exact if FriedmannMultiplicity.ValueLE G (playValue G σ τ₁ x) (playValue G σ τ₂ x)
    then τ₁ x else τ₂ x

noncomputable def minVal (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) : Valuation V := by
  classical
  exact if FriedmannMultiplicity.ValueLE G (playValue G σ τ₁ x) (playValue G σ τ₂ x)
    then playValue G σ τ₁ x else playValue G σ τ₂ x

noncomputable def chosenStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) : V → V := by
  classical
  exact if FriedmannMultiplicity.ValueLE G (playValue G σ τ₁ x) (playValue G σ τ₂ x)
    then τ₁ else τ₂

lemma minStrategy_legal {G : Game V} {σ τ₁ τ₂ : V → V}
    (hτ₁ : Legal G true τ₁) (hτ₂ : Legal G true τ₂) :
    Legal G true (minStrategy G σ τ₁ τ₂) := by
  intro x hx
  unfold minStrategy
  split_ifs
  · exact hτ₁ x hx
  · exact hτ₂ x hx

lemma chosenStrategy_legal {G : Game V} {σ τ₁ τ₂ : V → V}
    (hτ₁ : Legal G true τ₁) (hτ₂ : Legal G true τ₂) (x : V) :
    Legal G true (chosenStrategy G σ τ₁ τ₂ x) := by
  unfold chosenStrategy
  split_ifs
  · exact hτ₁
  · exact hτ₂

lemma minVal_le_left (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    FriedmannMultiplicity.ValueLE G (minVal G σ τ₁ τ₂ x) (playValue G σ τ₁ x) := by
  unfold minVal
  split_ifs with h
  · exact multiplicity_valueLE_refl G _
  · rcases multiplicity_valueLE_total G (playValue G σ τ₁ x) (playValue G σ τ₂ x) with h1 | h2
    · exact False.elim (h h1)
    · exact h2

lemma minVal_le_right (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    FriedmannMultiplicity.ValueLE G (minVal G σ τ₁ τ₂ x) (playValue G σ τ₂ x) := by
  unfold minVal
  split_ifs with h
  · exact h
  · exact multiplicity_valueLE_refl G _

lemma minVal_eq_playValue_chosenStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    minVal G σ τ₁ τ₂ x = playValue G σ (chosenStrategy G σ τ₁ τ₂ x) x := by
  unfold minVal chosenStrategy
  split_ifs <;> rfl

lemma step_minStrategy_eq_chosenStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    step G σ (minStrategy G σ τ₁ τ₂) x = step G σ (chosenStrategy G σ τ₁ τ₂ x) x := by
  unfold step minStrategy chosenStrategy
  split_ifs <;> rfl

lemma minVal_step_le_chosenStrategy (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    FriedmannMultiplicity.ValueLE G
      (minVal G σ τ₁ τ₂ (step G σ (minStrategy G σ τ₁ τ₂) x))
      (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ (minStrategy G σ τ₁ τ₂) x)) := by
  unfold chosenStrategy
  split_ifs
  · exact minVal_le_left G σ τ₁ τ₂ _
  · exact minVal_le_right G σ τ₁ τ₂ _

lemma chosenStrategy_step_cyclePriority (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ (minStrategy G σ τ₁ τ₂) x)).cyclePriority =
      (minVal G σ τ₁ τ₂ x).cyclePriority := by
  rw [step_minStrategy_eq_chosenStrategy, playValue_cyclePriority_step,
      ← minVal_eq_playValue_chosenStrategy]

lemma reward_minVal_step_le (G : Game V) (σ τ₁ τ₂ : V → V) (x : V) :
    reward (minVal G σ τ₁ τ₂ (step G σ (minStrategy G σ τ₁ τ₂) x)).cyclePriority ≤
      reward (minVal G σ τ₁ τ₂ x).cyclePriority := by
  have hle := reward_cyclePriority_le_of_multiplicity_valueLE (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
  rwa [chosenStrategy_step_cyclePriority] at hle

lemma minVal_cyclePriority_eq_on_recurring (G : Game V) (σ τ₁ τ₂ : V → V)
    {v x w : V}
    (hx : x ∈ recurring (play G σ (minStrategy G σ τ₁ τ₂) v))
    (hw : w ∈ recurring (play G σ (minStrategy G σ τ₁ τ₂) v)) :
    (minVal G σ τ₁ τ₂ x).cyclePriority = (minVal G σ τ₁ τ₂ w).cyclePriority := by
  apply reward_injective
  exact eq_on_recurring_of_le_step_int
    (fun y => reward (minVal G σ τ₁ τ₂ y).cyclePriority)
    (reward_minVal_step_le G σ τ₁ τ₂) hx hw

lemma count_minVal_eq_above_max (G : Game V) (σ τ₁ τ₂ : V → V) (v : V) :
    let τ₃ := minStrategy G σ τ₁ τ₂
    let m := minVal G σ τ₁ τ₂
    let R₃ := recurring (play G σ τ₃ v)
    let w₃ := cycleLeader G σ τ₃ v
    let p₃ := (playValue G σ τ₃ v).cyclePriority
    let p_star := (m w₃).cyclePriority
    let M := Finset.univ.sup G.priority + max p₃ p_star + 1
    ∀ d : ℕ, ∀ q : ℕ, M - d ≤ q → max p₃ p_star < q →
      ∀ x ∈ R₃,
        count G (m (step G σ τ₃ x)).path q =
          count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path q ∧
        count G (m (step G σ τ₃ x)).path q =
          count G (m x).path q := by
  intro τ₃ m R₃ w₃ p₃ p_star M d
  have hw₃ : w₃ ∈ R₃ := cycleLeader_mem_recurring G σ τ₃ v
  induction d with
  | zero =>
    intro q hMq _ x _
    have hsup : Finset.univ.sup G.priority < q := by omega
    rw [count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup,
        count_eq_zero_of_univ_sup_lt _ hsup]
    exact ⟨rfl, rfl⟩
  | succ d ih =>
    intro q hMq hmaxq
    by_cases hMq' : M - d ≤ q
    · exact ih q hMq' hmaxq
    · have hgt : ∀ x ∈ R₃, ∀ q', q < q' →
          count G (m (step G σ τ₃ x)).path q' =
            count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path q' := by
        intro x hx q' hq'
        exact (ih q' (by omega) (by omega) x hx).1
      have hmx_eq : ∀ x ∈ R₃,
          count G (m x).path q =
            count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path q := by
        intro x hx
        have hpx : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
        have hp_lt_q : (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) x).cyclePriority < q := by
          rw [← minVal_eq_playValue_chosenStrategy]
          change (m x).cyclePriority < q
          omega
        have hcnt := count_playValue_step hp_lt_q
        rw [← minVal_eq_playValue_chosenStrategy,
            ← step_minStrategy_eq_chosenStrategy] at hcnt
        have hle_p3 : G.priority x ≤ p₃ := Finset.le_sup hx
        have hne_q : G.priority x ≠ q := by omega
        rw [if_neg hne_q, Nat.add_zero] at hcnt
        exact hcnt
      have hcp_eq : ∀ x ∈ R₃,
          (m (step G σ τ₃ x)).cyclePriority =
            (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).cyclePriority := by
        intro x hx
        have h1 : (m (step G σ τ₃ x)).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ (step_mem_recurring hx) hw₃
        have h2 : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
        rw [h1, chosenStrategy_step_cyclePriority]
        exact h2.symm
      rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
      · have hstep_le : ∀ x ∈ R₃,
            count G (m (step G σ τ₃ x)).path q ≤ count G (m x).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
            (hcp_eq x hx) (hgt x hx)).1 hpar
        intro x hx
        have heq := eq_of_le_step_on_recurring
          (fun y => count G (m y).path q) hstep_le hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩
      · have hstep_ge : ∀ x ∈ R₃,
            count G (m x).path q ≤ count G (m (step G σ τ₃ x)).path q := by
          intro x hx
          rw [hmx_eq x hx]
          exact (count_le_or_ge_of_multiplicity_valueLE
            (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
            (hcp_eq x hx) (hgt x hx)).2 hpar
        intro x hx
        have heq := eq_of_step_le_on_recurring
          (fun y => count G (m y).path q) hstep_ge hx
        exact ⟨heq.trans (hmx_eq x hx), heq⟩

lemma reward_playValue_minStrategy_le (G : Game V) (σ τ₁ τ₂ : V → V) (v : V) :
    reward (playValue G σ (minStrategy G σ τ₁ τ₂) v).cyclePriority ≤
      reward (minVal G σ τ₁ τ₂ (cycleLeader G σ (minStrategy G σ τ₁ τ₂) v)).cyclePriority := by
  let τ₃ := minStrategy G σ τ₁ τ₂
  let m := minVal G σ τ₁ τ₂
  let R₃ := recurring (play G σ τ₃ v)
  let w₃ := cycleLeader G σ τ₃ v
  let p₃ := (playValue G σ τ₃ v).cyclePriority
  let p_star := (m w₃).cyclePriority
  change reward p₃ ≤ reward p_star
  have hw₃ : w₃ ∈ R₃ := cycleLeader_mem_recurring G σ τ₃ v
  have hpw₃ : G.priority w₃ = p₃ :=
    (playValue_cyclePriority_eq_priority_cycleLeader G σ τ₃ v).symm
  have habove : ∀ q : ℕ, max p₃ p_star < q → ∀ x ∈ R₃,
      count G (m (step G σ τ₃ x)).path q =
        count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path q := by
    intro q hq x hx
    let M := Finset.univ.sup G.priority + max p₃ p_star + 1
    have hMM : M - M ≤ q := by simp
    exact (count_minVal_eq_above_max G σ τ₁ τ₂ v M q hMM hq x hx).1
  have hcp_eq : ∀ x ∈ R₃,
      (m (step G σ τ₃ x)).cyclePriority =
        (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).cyclePriority := by
    intro x hx
    have h1 : (m (step G σ τ₃ x)).cyclePriority = p_star :=
      minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ (step_mem_recurring hx) hw₃
    have h2 : (m x).cyclePriority = p_star :=
      minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
    rw [h1, chosenStrategy_step_cyclePriority]
    exact h2.symm
  rcases lt_trichotomy p₃ p_star with hlt | heq | hgt
  · rcases Nat.mod_two_eq_zero_or_one p_star with hpar | hpar
    · unfold reward
      split_ifs <;> omega
    · exfalso
      have hseq : ∀ x ∈ R₃, SetEquivalent G
          (m (step G σ τ₃ x)).path
          (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path := by
        intro x hx q
        by_cases hq : p_star < q
        · exact habove q (by omega) x hx
        · have h1 : (m (step G σ τ₃ x)).cyclePriority = p_star :=
            minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ (step_mem_recurring hx) hw₃
          have h2 : (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).cyclePriority = p_star :=
            (hcp_eq x hx).symm.trans h1
          have h1' : (playValue G σ
              (chosenStrategy G σ τ₁ τ₂ (step G σ τ₃ x))
              (step G σ τ₃ x)).cyclePriority = p_star := by
            rw [← minVal_eq_playValue_chosenStrategy]
            exact h1
          change count G (minVal G σ τ₁ τ₂ (step G σ τ₃ x)).path q = _
          rw [minVal_eq_playValue_chosenStrategy,
              count_playValue_eq_zero_of_le_cyclePriority (by omega),
              count_playValue_eq_zero_of_le_cyclePriority (by omega)]
      have hlen_step : ∀ x ∈ R₃,
          (m (step G σ τ₃ x)).length ≤
            (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).length ∧
          (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).length + 1 = (m x).length := by
        intro x hx
        have h1 : (m (step G σ τ₃ x)).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ (step_mem_recurring hx) hw₃
        have h2 : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
        have hlen_le := length_le_of_multiplicity_valueLE_odd
          (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
          (hcp_eq x hx) (hseq x hx) (by rw [h1]; exact hpar)
        have hx_ne : x ≠ cycleLeader G σ (chosenStrategy G σ τ₁ τ₂ x) x := by
          intro hcl
          have hpx : G.priority x = p_star := by
            have hpcl := playValue_cyclePriority_eq_priority_cycleLeader
              G σ (chosenStrategy G σ τ₁ τ₂ x) x
            rw [← minVal_eq_playValue_chosenStrategy] at hpcl
            change (m x).cyclePriority = _ at hpcl
            rw [h2, ← hcl] at hpcl
            exact hpcl.symm
          have hpx_le : G.priority x ≤ p₃ := Finset.le_sup hx
          omega
        have hlen_eq := playValue_length_eq_succ_of_ne_cycleLeader hx_ne
        rw [← minVal_eq_playValue_chosenStrategy,
            ← step_minStrategy_eq_chosenStrategy] at hlen_eq
        exact ⟨hlen_le, hlen_eq.symm⟩
      have hstep_le : ∀ x ∈ R₃, (m (step G σ τ₃ x)).length ≤ (m x).length := by
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
          count G (m (step G σ τ₃ x)).path p₃ ≤
            count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path p₃ ∧
          count G (m x).path p₃ =
            count G (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) (step G σ τ₃ x)).path p₃ +
              (if G.priority x = p₃ then 1 else 0) := by
        intro x hx
        have hle_cnt := (count_le_or_ge_of_multiplicity_valueLE
          (minVal_step_le_chosenStrategy G σ τ₁ τ₂ x)
          (hcp_eq x hx)
          (fun q' hq' => habove q' (by omega) x hx)).1 hpar
        have h2 : (m x).cyclePriority = p_star :=
          minVal_cyclePriority_eq_on_recurring G σ τ₁ τ₂ hx hw₃
        have hp_lt : (playValue G σ (chosenStrategy G σ τ₁ τ₂ x) x).cyclePriority < p₃ := by
          rw [← minVal_eq_playValue_chosenStrategy]
          change (m x).cyclePriority < p₃
          rw [h2]
          exact hgt
        have hcnt := count_playValue_step hp_lt
        rw [← minVal_eq_playValue_chosenStrategy,
            ← step_minStrategy_eq_chosenStrategy] at hcnt
        exact ⟨hle_cnt, hcnt⟩
      have hstep_le : ∀ x ∈ R₃,
          count G (m (step G σ τ₃ x)).path p₃ ≤ count G (m x).path p₃ := by
        intro x hx
        have ⟨h1, h2⟩ := hstep_rel x hx
        omega
      have heq_w3 := eq_of_le_step_on_recurring
        (fun y => count G (m y).path p₃) hstep_le hw₃
      have ⟨h1, h2⟩ := hstep_rel w₃ hw₃
      rw [if_pos hpw₃] at h2
      omega
    · unfold reward
      split_ifs <;> omega

lemma valueLE_playValue_minStrategy {G : Game V} (hinj : Function.Injective G.priority)
    (σ τ₁ τ₂ : V → V) (v : V) :
    FriedmannMultiplicity.ValueLE G
      (playValue G σ (minStrategy G σ τ₁ τ₂) v)
      (minVal G σ τ₁ τ₂ v) := by
  let τ₃ := minStrategy G σ τ₁ τ₂
  let π₃ := play G σ τ₃ v
  let w₃ := cycleLeader G σ τ₃ v
  let p₃ := (playValue G σ τ₃ v).cyclePriority
  let k := (playValue G σ τ₃ v).length
  have hcl_play : ∀ t : ℕ, cycleLeader G σ τ₃ (π₃ t) = w₃ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      dsimp only [π₃] at ih ⊢
      rw [play_succ', cycleLeader_step, ih]
  have hcp_play : ∀ t : ℕ, (playValue G σ τ₃ (π₃ t)).cyclePriority = p₃ := by
    intro t
    rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl_play t,
        ← playValue_cyclePriority_eq_priority_cycleLeader]
  have hbase_w3 : FriedmannMultiplicity.ValueLE G
      (playValue G σ τ₃ w₃) (minVal G σ τ₁ τ₂ w₃) := by
    have hrew : reward p₃ ≤ reward (minVal G σ τ₁ τ₂ w₃).cyclePriority :=
      reward_playValue_minStrategy_le G σ τ₁ τ₂ v
    have hcl_w3 : w₃ = cycleLeader G σ τ₃ w₃ := by
      have h := hcl_play k
      dsimp only [π₃, k] at h
      rw [play_playValue_length] at h
      exact h.symm
    have hcp_w3 : (playValue G σ τ₃ w₃).cyclePriority = p₃ := by
      have h := hcp_play k
      dsimp only [π₃, k] at h
      rw [play_playValue_length] at h
      exact h
    rcases lt_or_eq_of_le hrew with hlt | heq
    · rw [multiplicity_valueLE_iff]
      right; left
      rw [hcp_w3]
      exact hlt
    · have hp_eq : p₃ = (minVal G σ τ₁ τ₂ w₃).cyclePriority := reward_injective heq
      let τ₀ := chosenStrategy G σ τ₁ τ₂ w₃
      have hcp_0 : (playValue G σ τ₃ w₃).cyclePriority =
          (playValue G σ τ₀ w₃).cyclePriority := by
        rw [hcp_w3, ← minVal_eq_playValue_chosenStrategy, hp_eq]
      have hcl_0 : w₃ = cycleLeader G σ τ₀ w₃ :=
        hcl_w3.trans (cycleLeader_eq_of_cyclePriority_eq hinj hcp_0)
      have hval_3 := playValue_eq_of_eq_cycleLeader hcl_w3
      have hval_0 := playValue_eq_of_eq_cycleLeader hcl_0
      rw [minVal_eq_playValue_chosenStrategy]
      change FriedmannMultiplicity.ValueLE G
        (playValue G σ τ₃ w₃) (playValue G σ τ₀ w₃)
      rw [hval_3, hval_0, hcp_0]
      exact multiplicity_valueLE_refl G _
  have hind : ∀ d : ℕ, d ≤ k →
      FriedmannMultiplicity.ValueLE G
        (playValue G σ τ₃ (π₃ (k - d)))
        (minVal G σ τ₁ τ₂ (π₃ (k - d))) := by
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
      let x' := step G σ τ₃ x
      have hx'_eq : x' = π₃ (k - d) := by
        dsimp only [x', x, π₃]
        rw [← play_succ', ht_succ]
      have ih' : FriedmannMultiplicity.ValueLE G
          (playValue G σ τ₃ x') (minVal G σ τ₁ τ₂ x') := by
        rw [hx'_eq]
        exact ih (by omega)
      let τ_i := chosenStrategy G σ τ₁ τ₂ x
      have hm_step : FriedmannMultiplicity.ValueLE G (minVal G σ τ₁ τ₂ x')
          (playValue G σ τ_i (step G σ τ_i x)) := by
        dsimp only [x', τ_i]
        rw [← step_minStrategy_eq_chosenStrategy]
        exact minVal_step_le_chosenStrategy G σ τ₁ τ₂ x
      have hle_step : FriedmannMultiplicity.ValueLE G
          (playValue G σ τ₃ x')
          (playValue G σ τ_i (step G σ τ_i x)) :=
        multiplicity_valueLE_trans ih' hm_step
      have hrew_le : reward (playValue G σ τ₃ x).cyclePriority ≤
          reward (minVal G σ τ₁ τ₂ x).cyclePriority := by
        have h := reward_cyclePriority_le_of_multiplicity_valueLE hle_step
        dsimp only [x', τ_i] at h
        rw [playValue_cyclePriority_step, playValue_cyclePriority_step,
            ← minVal_eq_playValue_chosenStrategy] at h
        exact h
      rcases lt_or_eq_of_le hrew_le with hlt | heq
      · rw [multiplicity_valueLE_iff]
        right; left
        exact hlt
      · have hp_eq : (playValue G σ τ₃ x).cyclePriority =
            (minVal G σ τ₁ τ₂ x).cyclePriority :=
          reward_injective heq
        have hx_ne_w3 : x ≠ cycleLeader G σ τ₃ x := by
          rw [hcl_play t]
          exact play_ne_cycleLeader_of_lt_length ht_lt
        have hx_ne_i : x ≠ cycleLeader G σ τ_i x := by
          intro hcl_i
          have hcp_i : (playValue G σ τ_i x).cyclePriority =
              (playValue G σ τ₃ x).cyclePriority := by
            dsimp only [τ_i]
            rw [← minVal_eq_playValue_chosenStrategy, hp_eq]
          exact hx_ne_w3 (hcl_i.trans (cycleLeader_eq_of_cyclePriority_eq hinj hcp_i))
        have hval_3 := playValue_eq_prepend_of_ne_cycleLeader hx_ne_w3
        have hnot_3 := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_w3
        have hval_i := playValue_eq_prepend_of_ne_cycleLeader hx_ne_i
        have hnot_i := notMem_playValue_step_path_of_ne_cycleLeader hx_ne_i
        change FriedmannMultiplicity.ValueLE G
          (playValue G σ τ₃ x) (minVal G σ τ₁ τ₂ x)
        rw [minVal_eq_playValue_chosenStrategy, hval_3]
        change FriedmannMultiplicity.ValueLE G
          (prepend G x (playValue G σ τ₃ x'))
          (playValue G σ τ_i x)
        rw [hval_i]
        apply multiplicity_valueLE_prepend
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

noncomputable def defaultStrategy (G : Game V) (hG : WellFormed G) (v : V) : V :=
  Classical.choose (hG.1 v)

omit [Fintype V] [DecidableEq V] in
lemma defaultStrategy_legal {G : Game V} (hG : WellFormed G) (player : Bool) :
    Legal G player (defaultStrategy G hG) := by
  intro v _
  exact Classical.choose_spec (hG.1 v)

lemma exists_counterstrategy_list {G : Game V} (hG : WellFormed G)
    (σ : V → V) (L : List (V → V)) :
    ∃ τ : V → V,
      Legal G true τ ∧
      ∀ τ' ∈ L, Legal G true τ' →
        ∀ v, ValueLE G (playValue G σ τ v) (playValue G σ τ' v) := by
  induction L with
  | nil =>
    refine ⟨defaultStrategy G hG, defaultStrategy_legal hG true, ?_⟩
    intro τ' hmem
    nomatch hmem
  | cons τ₁ L ih =>
    rcases ih with ⟨τ₂, hτ₂, hle₂⟩
    by_cases hτ₁ : Legal G true τ₁
    · refine ⟨minStrategy G σ τ₁ τ₂, minStrategy_legal hτ₁ hτ₂, ?_⟩
      intro τ' hmem hleg v
      have hmin : ValueLE G (playValue G σ (minStrategy G σ τ₁ τ₂) v) (minVal G σ τ₁ τ₂ v) :=
        (valueLE_iff_multiplicity_valueLE hG.2 _ _).mpr
          (valueLE_playValue_minStrategy hG.2 σ τ₁ τ₂ v)
      have hleft : ValueLE G (minVal G σ τ₁ τ₂ v) (playValue G σ τ₁ v) :=
        (valueLE_iff_multiplicity_valueLE hG.2 _ _).mpr
          (minVal_le_left G σ τ₁ τ₂ v)
      have hright : ValueLE G (minVal G σ τ₁ τ₂ v) (playValue G σ τ₂ v) :=
        (valueLE_iff_multiplicity_valueLE hG.2 _ _).mpr
          (minVal_le_right G σ τ₁ τ₂ v)
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [heq]
        exact valueLE_trans hG.2 hmin hleft
      · exact valueLE_trans hG.2 hmin
          (valueLE_trans hG.2 hright (hle₂ τ' hmem' hleg v))
    · refine ⟨τ₂, hτ₂, ?_⟩
      intro τ' hmem hleg v
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [heq] at hleg
        exact False.elim (hτ₁ hleg)
      · exact hle₂ τ' hmem' hleg v

lemma exists_optimalCounterstrategy (G : Game V) (hG : WellFormed G) (σ : V → V) :
    ∃ τ, OptimalCounterstrategy G σ τ := by
  rcases exists_counterstrategy_list hG σ (Finset.univ : Finset (V → V)).toList with
    ⟨τ, hτ, hle⟩
  refine ⟨τ, hτ, ?_⟩
  intro v τ' hτ'
  exact hle τ' (Finset.mem_toList.mpr (Finset.mem_univ τ')) hτ' v

lemma isMinimum_playValue_of_optimalCounterstrategy {G : Game V} {σ τ : V → V}
    (hτ : OptimalCounterstrategy G σ τ) (v : V) :
    IsMinimum G σ v (playValue G σ τ v) :=
  ⟨⟨τ, hτ.1, rfl⟩, fun τ' hτ' => hτ.2 v τ' hτ'⟩

lemma isMinimum_unique {G : Game V} (hG : WellFormed G) {σ : V → V} {v : V}
    {a b : Valuation V} (ha : IsMinimum G σ v a) (hb : IsMinimum G σ v b) :
    a = b := by
  rcases ha.1 with ⟨τ₁, hτ₁, rfl⟩
  rcases hb.1 with ⟨τ₂, hτ₂, rfl⟩
  exact valueLE_antisymm hG.2 (ha.2 τ₂ hτ₂) (hb.2 τ₁ hτ₁)

lemma value_eq_of_isMinimum {G : Game V} (hG : WellFormed G) {σ : V → V} {v : V}
    {a : Valuation V} (ha : IsMinimum G σ v a) :
    value G σ v = a := by
  classical
  have hex : ∃ b, IsMinimum G σ v b := ⟨a, ha⟩
  have hval : value G σ v = Classical.choose hex := by
    unfold value
    rw [dif_pos hex]
  rw [hval]
  exact isMinimum_unique hG (Classical.choose_spec hex) ha

lemma value_eq_playValue_of_optimalCounterstrategy {G : Game V} (hG : WellFormed G)
    {σ τ : V → V} (hτ : OptimalCounterstrategy G σ τ) (v : V) :
    value G σ v = playValue G σ τ v :=
  value_eq_of_isMinimum hG (isMinimum_playValue_of_optimalCounterstrategy hτ v)

lemma isMinimum_value {G : Game V} (hG : WellFormed G) (σ : V → V) (v : V) :
    IsMinimum G σ v (value G σ v) := by
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
  rw [value_eq_playValue_of_optimalCounterstrategy hG hτ v]
  exact isMinimum_playValue_of_optimalCounterstrategy hτ v

lemma value_le_playValue {G : Game V} (hG : WellFormed G) (σ : V → V)
    {τ : V → V} (hτ : Legal G true τ) (v : V) :
    ValueLE G (value G σ v) (playValue G σ τ v) :=
  (isMinimum_value hG σ v).2 τ hτ

end Counterstrategy

theorem counterstrategy_exists {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ : V → V) (hσ : Legal G false σ) :
    ∃ τ, OptimalCounterstrategy G σ τ ∧ ∀ v, value G σ v = playValue G σ τ v := by
  let _ := hσ
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ, hτ⟩
  exact ⟨τ, hτ, value_eq_playValue_of_optimalCounterstrategy hG hτ⟩

end FriedmannParity

open FriedmannParity

theorem solution_counterstrategy {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ : V → V) (hσ : Legal G false σ) :
    ∃ τ, OptimalCounterstrategy G σ τ ∧ ∀ v, value G σ v = playValue G σ τ v :=
  counterstrategy_exists G hG σ hσ

end Mod_counterstrategy

section Mod_transport
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FriedmannParity

open scoped BigOperators
open Matrix

section SinkTransport

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Part 0: Discounted Bellman Equation -/

lemma transition_mulVec
    (H : FriedmannDiscounted.Game V) (σ τ : V → V) (x : V → ℚ) (v : V) :
    (FriedmannDiscounted.transition H σ τ *ᵥ x) v = x (step H.arena σ τ v) := by
  classical
  dsimp [FriedmannDiscounted.transition, step, mulVec, dotProduct]
  simp

lemma one_sub_discount_transition_mulVec
    (H : FriedmannDiscounted.Game V) (σ τ : V → V) (x : V → ℚ) (v : V) :
    ((1 - H.discount • FriedmannDiscounted.transition H σ τ) *ᵥ x) v =
      x v - H.discount * x (step H.arena σ τ v) := by
  rw [sub_mulVec, one_mulVec, Pi.sub_apply, ← transition_mulVec H σ τ x v]
  congr 1
  dsimp [mulVec, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma isUnit_det_one_sub_discount_transition
    (H : FriedmannDiscounted.Game V) (hH : FriedmannDiscounted.WellFormed H) (σ τ : V → V) :
    IsUnit (1 - H.discount • FriedmannDiscounted.transition H σ τ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  rcases Matrix.exists_mulVec_eq_zero_iff.mpr hdet with ⟨x, hxne, hx⟩
  have hfp : ∀ v, x v = H.discount * x (step H.arena σ τ v) := by
    intro v
    have hv := congrFun hx v
    rw [Pi.zero_apply, one_sub_discount_transition_mulVec] at hv
    linarith
  have hne : (Finset.univ : Finset V).Nonempty := by
    by_contra hempty
    apply hxne
    ext v
    exact False.elim (hempty ⟨v, Finset.mem_univ v⟩)
  set M := Finset.univ.sup' hne (fun v => |x v|)
  have hM : ∀ v, |x v| ≤ M := fun v => Finset.le_sup' (fun u => |x u|) (Finset.mem_univ v)
  obtain ⟨v₀, _, hv₀⟩ := Finset.exists_mem_eq_sup' hne (fun v => |x v|)
  have hβ0 : 0 < H.discount := hH.2.1
  have hβ1 : H.discount < 1 := hH.2.2
  by_cases hMpos : 0 < M
  · have hstep : |x v₀| = H.discount * |x (step H.arena σ τ v₀)| := by
      rw [hfp v₀, abs_mul, abs_of_pos hβ0]
    have hle : H.discount * |x (step H.arena σ τ v₀)| ≤ H.discount * M :=
      mul_le_mul_of_nonneg_left (hM _) (le_of_lt hβ0)
    have hlt : H.discount * M < 1 * M :=
      mul_lt_mul_of_pos_right hβ1 hMpos
    linarith
  · apply hxne
    ext v
    have h1 : |x v| ≤ 0 := le_trans (hM v) (not_lt.mp hMpos)
    exact abs_nonpos_iff.mp h1

lemma discounted_playValue_step {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ τ : V → V) (u : V) :
    FriedmannDiscounted.playValue H σ τ u =
      H.reward u + H.discount * FriedmannDiscounted.playValue H σ τ (step H.arena σ τ u) := by
  have hunit := isUnit_det_one_sub_discount_transition H hH σ τ
  set A := 1 - H.discount • FriedmannDiscounted.transition H σ τ
  have hmul : A *ᵥ FriedmannDiscounted.playValue H σ τ = H.reward := by
    unfold FriedmannDiscounted.playValue
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, one_mulVec]
  have hu := congrFun hmul u
  rw [one_sub_discount_transition_mulVec] at hu
  linarith

/-! ### Part 1: Basic Properties of `IsSinkGame` and `FriedmannDiscounted.induced` -/

lemma isSinkGame_wellFormed {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) : WellFormed G :=
  hSink.1

lemma isSinkGame_priority_sink {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) : G.priority sink = 1 :=
  hSink.2.2.2.1

lemma isSinkGame_one_lt_priority_of_ne {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {u : V} (hu : u ≠ sink) : 1 < G.priority u :=
  hSink.2.2.2.2.1 u hu

lemma isSinkGame_one_le_priority {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (u : V) : 1 ≤ G.priority u := by
  by_cases hu : u = sink
  · subst hu
    have hp := isSinkGame_priority_sink hSink
    omega
  · have hp := isSinkGame_one_lt_priority_of_ne hSink hu
    omega

lemma isSinkGame_priority_eq_one_iff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (u : V) : G.priority u = 1 ↔ u = sink := by
  constructor
  · intro hp
    by_contra hu
    have := isSinkGame_one_lt_priority_of_ne hSink hu
    omega
  · rintro rfl
    exact isSinkGame_priority_sink hSink

lemma isSinkGame_card_pos {G : Game V} {ι : V → V} {sink : V}
    (_hSink : IsSinkGame G ι sink) : 1 ≤ Fintype.card V :=
  Fintype.card_pos_iff.mpr ⟨sink⟩

lemma two_le_card_of_ne {u v : V} (huv : u ≠ v) : 2 ≤ Fintype.card V := by
  have hsub : ({u, v} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair huv, Finset.card_univ] at hcard
  exact hcard

noncomputable def maxRewardNat (G : Game V) : ℕ :=
  Finset.univ.sup (fun v => (Fintype.card V) ^ G.priority v)

lemma le_maxRewardNat (G : Game V) (u : V) :
    (Fintype.card V) ^ G.priority u ≤ maxRewardNat G :=
  Finset.le_sup (f := fun v => (Fintype.card V) ^ G.priority v) (Finset.mem_univ u)

lemma isSinkGame_card_le_maxRewardNat {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) : Fintype.card V ≤ maxRewardNat G := by
  have h := le_maxRewardNat G sink
  rw [isSinkGame_priority_sink hSink, pow_one] at h
  exact h

lemma isSinkGame_one_le_maxRewardNat {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) : 1 ≤ maxRewardNat G :=
  le_trans (isSinkGame_card_pos hSink) (isSinkGame_card_le_maxRewardNat hSink)

lemma induced_discount_eq (G : Game V) :
    (FriedmannDiscounted.induced G).discount =
      1 - 1 / (4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ)) :=
  rfl

lemma one_sub_induced_discount (G : Game V) :
    1 - (FriedmannDiscounted.induced G).discount =
      1 / (4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ)) := by
  rw [induced_discount_eq]
  ring

lemma isSinkGame_induced_denom_ge_four {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) :
    (4 : ℚ) ≤ 4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ) := by
  have hN : (1 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast isSinkGame_card_pos hSink
  have hM : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have hN3 : (1 : ℚ) ≤ (Fintype.card V : ℚ) ^ 3 := one_le_pow₀ hN
  nlinarith

lemma isSinkGame_wellFormed_induced {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) :
    FriedmannDiscounted.WellFormed (FriedmannDiscounted.induced G) := by
  have hden := isSinkGame_induced_denom_ge_four hSink
  have hden_pos : (0 : ℚ) < 4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ) := by linarith
  have hpos : (0 : ℚ) < 1 / (4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ)) :=
    div_pos one_pos hden_pos
  have hlt1 : 1 / (4 * (Fintype.card V : ℚ) ^ 3 * (maxRewardNat G : ℚ)) < 1 := by
    rw [div_lt_iff₀ hden_pos]
    linarith
  refine ⟨(isSinkGame_wellFormed hSink).1, ?_, ?_⟩
  · rw [induced_discount_eq]; linarith
  · rw [induced_discount_eq]; linarith

lemma card_mul_one_sub_induced_discount_mul_maxReward
    {G : Game V} {ι : V → V} {sink : V} (hSink : IsSinkGame G ι sink) :
    (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) *
      (maxRewardNat G : ℚ) = 1 / (4 * (Fintype.card V : ℚ) ^ 2) := by
  have hN_pos : (0 : ℚ) < (Fintype.card V : ℚ) := by
    exact_mod_cast isSinkGame_card_pos hSink
  have hM_pos : (0 : ℚ) < (maxRewardNat G : ℚ) := by
    exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have hN_ne : (Fintype.card V : ℚ) ≠ 0 := ne_of_gt hN_pos
  have hM_ne : (maxRewardNat G : ℚ) ≠ 0 := ne_of_gt hM_pos
  rw [one_sub_induced_discount]
  field_simp

lemma card_mul_one_sub_induced_discount_mul_maxReward_le_quarter
    {G : Game V} {ι : V → V} {sink : V} (hSink : IsSinkGame G ι sink) :
    (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) *
      (maxRewardNat G : ℚ) ≤ 1 / 4 := by
  rw [card_mul_one_sub_induced_discount_mul_maxReward hSink]
  have hN : (1 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast isSinkGame_card_pos hSink
  have hN2 : (1 : ℚ) ≤ (Fintype.card V : ℚ) ^ 2 := one_le_pow₀ hN
  have hden : (4 : ℚ) ≤ 4 * (Fintype.card V : ℚ) ^ 2 := by linarith
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

lemma card_mul_one_sub_induced_discount_le_quarter
    {G : Game V} {ι : V → V} {sink : V} (hSink : IsSinkGame G ι sink) :
    (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) ≤ 1 / 4 := by
  have h1 := card_mul_one_sub_induced_discount_mul_maxReward_le_quarter hSink
  have hM : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have hH := isSinkGame_wellFormed_induced hSink
  have hnonneg : 0 ≤ (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [hH.2.2])
  nlinarith

lemma one_sub_pow_le {β : ℚ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∀ m : ℕ, 1 - β ^ m ≤ (m : ℚ) * (1 - β)
  | 0 => by simp
  | m + 1 => by
    have ih := one_sub_pow_le hβ0 hβ1 m
    have hpow : β ^ m ≤ 1 := pow_le_one₀ hβ0 hβ1
    have h1 : 1 - β ^ (m + 1) = (1 - β ^ m) + β ^ m * (1 - β) := by ring
    have h2 : β ^ m * (1 - β) ≤ 1 * (1 - β) :=
      mul_le_mul_of_nonneg_right hpow (by linarith)
    push_cast
    linarith

lemma induced_discount_pow_bounds {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {t : ℕ} (ht : t ≤ Fintype.card V) :
    1 - (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) ≤
      (FriedmannDiscounted.induced G).discount ^ t ∧
    (FriedmannDiscounted.induced G).discount ^ t ≤ 1 := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  have hβ0 : 0 ≤ H.discount := le_of_lt hH.2.1
  have hβ1 : H.discount ≤ 1 := le_of_lt hH.2.2
  have hpow1 : H.discount ^ t ≤ 1 := pow_le_one₀ hβ0 hβ1
  have hsub := one_sub_pow_le hβ0 hβ1 t
  have htQ : (t : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast ht
  have hmul : (t : ℚ) * (1 - H.discount) ≤ (Fintype.card V : ℚ) * (1 - H.discount) :=
    mul_le_mul_of_nonneg_right htQ (by linarith)
  exact ⟨by linarith, hpow1⟩

lemma one_half_le_induced_discount_pow {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {t : ℕ} (ht : t ≤ Fintype.card V) :
    (1 / 2 : ℚ) ≤ (FriedmannDiscounted.induced G).discount ^ t := by
  have hb := (induced_discount_pow_bounds hSink ht).1
  have hq := card_mul_one_sub_induced_discount_le_quarter hSink
  linarith

lemma induced_reward_of_even {G : Game V} {u : V} (he : G.priority u % 2 = 0) :
    (FriedmannDiscounted.induced G).reward u = (Fintype.card V : ℚ) ^ G.priority u := by
  change (- (Fintype.card V : ℚ)) ^ G.priority u = _
  exact (Nat.even_iff.mpr he).neg_pow (Fintype.card V : ℚ)

lemma induced_reward_of_odd {G : Game V} {u : V} (ho : G.priority u % 2 = 1) :
    (FriedmannDiscounted.induced G).reward u = - ((Fintype.card V : ℚ) ^ G.priority u) := by
  change (- (Fintype.card V : ℚ)) ^ G.priority u = _
  exact (Nat.odd_iff.mpr ho).neg_pow (Fintype.card V : ℚ)

lemma abs_induced_reward (G : Game V) (u : V) :
    |(FriedmannDiscounted.induced G).reward u| = (Fintype.card V : ℚ) ^ G.priority u := by
  change |(- (Fintype.card V : ℚ)) ^ G.priority u| = _
  rw [abs_pow, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]

lemma abs_induced_reward_le_maxReward (G : Game V) (u : V) :
    |(FriedmannDiscounted.induced G).reward u| ≤ (maxRewardNat G : ℚ) := by
  rw [abs_induced_reward]
  exact_mod_cast le_maxRewardNat G u

lemma abs_induced_reward_add_card_le (G : Game V) (u : V) :
    |(FriedmannDiscounted.induced G).reward u + (Fintype.card V : ℚ)| ≤
      (Fintype.card V : ℚ) ^ G.priority u + (Fintype.card V : ℚ) := by
  calc |(FriedmannDiscounted.induced G).reward u + (Fintype.card V : ℚ)|
      ≤ |(FriedmannDiscounted.induced G).reward u| + |(Fintype.card V : ℚ)| := abs_add_le _ _
    _ = (Fintype.card V : ℚ) ^ G.priority u + (Fintype.card V : ℚ) := by
      rw [abs_induced_reward, abs_of_nonneg (Nat.cast_nonneg _)]

lemma abs_induced_reward_add_card_le_two_maxReward
    {G : Game V} {ι : V → V} {sink : V} (hSink : IsSinkGame G ι sink) (u : V) :
    |(FriedmannDiscounted.induced G).reward u + (Fintype.card V : ℚ)| ≤
      2 * (maxRewardNat G : ℚ) := by
  have h1 := abs_induced_reward_add_card_le G u
  have h2 : (Fintype.card V : ℚ) ^ G.priority u ≤ (maxRewardNat G : ℚ) := by
    exact_mod_cast le_maxRewardNat G u
  have h3 : (Fintype.card V : ℚ) ≤ (maxRewardNat G : ℚ) := by
    exact_mod_cast isSinkGame_card_le_maxRewardNat hSink
  linarith

lemma sum_Ico_pow_le {B : ℚ} (hB : 2 ≤ B) (a : ℕ) :
    ∀ m : ℕ, a ≤ m → ∑ i ∈ Finset.Ico a m, B ^ i ≤ B ^ m - B ^ a
  | 0, ha => by
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | m + 1, ha => by
    rcases eq_or_lt_of_le ha with rfl | hlt
    · simp
    · have ham : a ≤ m := by omega
      rw [Finset.sum_Ico_succ_top ham]
      have ih := sum_Ico_pow_le hB a m ham
      have hpow : 0 ≤ B ^ m := pow_nonneg (by linarith) m
      have hmul : 2 * B ^ m ≤ B * B ^ m :=
        mul_le_mul_of_nonneg_right hB hpow
      have hsucc : B ^ (m + 1) = B * B ^ m := by ring
      linarith

/-! ### Part 2: Finite Bellman Expansion and Optimal Counterstrategy in Discounted Games -/

lemma discounted_playValue_expand {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ τ : V → V) (v : V) :
    ∀ m : ℕ,
      FriedmannDiscounted.playValue H σ τ v =
        (∑ t ∈ Finset.range m, H.discount ^ t * H.reward (play H.arena σ τ v t)) +
          H.discount ^ m * FriedmannDiscounted.playValue H σ τ (play H.arena σ τ v m)
  | 0 => by simp [play_zero]
  | m + 1 => by
    rw [discounted_playValue_expand hH σ τ v m, Finset.sum_range_succ, play_succ',
        discounted_playValue_step hH σ τ (play H.arena σ τ v m)]
    ring

lemma discounted_playValue_sub_const_expand {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ τ : V → V) (v : V) {c r₀ : ℚ}
    (hc : c = r₀ + H.discount * c) :
    ∀ m : ℕ,
      FriedmannDiscounted.playValue H σ τ v - c =
        (∑ t ∈ Finset.range m,
          H.discount ^ t * (H.reward (play H.arena σ τ v t) - r₀)) +
          H.discount ^ m * (FriedmannDiscounted.playValue H σ τ (play H.arena σ τ v m) - c)
  | 0 => by simp [play_zero]
  | m + 1 => by
    have hstep : FriedmannDiscounted.playValue H σ τ (play H.arena σ τ v m) - c =
        (H.reward (play H.arena σ τ v m) - r₀) +
          H.discount * (FriedmannDiscounted.playValue H σ τ (step H.arena σ τ (play H.arena σ τ v m)) - c) := by
      have h1 := discounted_playValue_step hH σ τ (play H.arena σ τ v m)
      linarith
    rw [discounted_playValue_sub_const_expand hH σ τ v hc m, Finset.sum_range_succ, play_succ', hstep]
    ring

noncomputable def minDiscStrategy (H : FriedmannDiscounted.Game V)
    (σ τ₁ τ₂ : V → V) (u : V) : V := by
  classical
  exact if FriedmannDiscounted.playValue H σ τ₁ u ≤ FriedmannDiscounted.playValue H σ τ₂ u
    then τ₁ u else τ₂ u

lemma minDiscStrategy_legal {H : FriedmannDiscounted.Game V} {σ τ₁ τ₂ : V → V}
    (hτ₁ : Legal H.arena true τ₁) (hτ₂ : Legal H.arena true τ₂) :
    Legal H.arena true (minDiscStrategy H σ τ₁ τ₂) := by
  intro u hu
  unfold minDiscStrategy
  split_ifs
  · exact hτ₁ u hu
  · exact hτ₂ u hu

lemma playValue_minDiscStrategy_le {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ τ₁ τ₂ : V → V) (v : V) :
    FriedmannDiscounted.playValue H σ (minDiscStrategy H σ τ₁ τ₂) v ≤
      min (FriedmannDiscounted.playValue H σ τ₁ v) (FriedmannDiscounted.playValue H σ τ₂ v) := by
  let τ₃ := minDiscStrategy H σ τ₁ τ₂
  let m : V → ℚ := fun u =>
    min (FriedmannDiscounted.playValue H σ τ₁ u) (FriedmannDiscounted.playValue H σ τ₂ u)
  have hβ0 : 0 < H.discount := hH.2.1
  have hβ1 : H.discount < 1 := hH.2.2
  have hm_step : ∀ u, H.reward u + H.discount * m (step H.arena σ τ₃ u) ≤ m u := by
    intro u
    dsimp only [m, τ₃, step, minDiscStrategy]
    by_cases hle : FriedmannDiscounted.playValue H σ τ₁ u ≤ FriedmannDiscounted.playValue H σ τ₂ u
    · rw [min_eq_left hle, if_pos hle]
      have h1 := discounted_playValue_step hH σ τ₁ u
      dsimp only [step] at h1
      have hmin : m (if H.arena.owner u = false then σ u else τ₁ u) ≤
          FriedmannDiscounted.playValue H σ τ₁ (if H.arena.owner u = false then σ u else τ₁ u) :=
        min_le_left _ _
      nlinarith
    · rw [min_eq_right (le_of_not_ge hle), if_neg hle]
      have h2 := discounted_playValue_step hH σ τ₂ u
      dsimp only [step] at h2
      have hmin : m (if H.arena.owner u = false then σ u else τ₂ u) ≤
          FriedmannDiscounted.playValue H σ τ₂ (if H.arena.owner u = false then σ u else τ₂ u) :=
        min_le_right _ _
      nlinarith
  have hdiff : ∀ u,
      FriedmannDiscounted.playValue H σ τ₃ u - m u ≤
        H.discount * (FriedmannDiscounted.playValue H σ τ₃ (step H.arena σ τ₃ u) - m (step H.arena σ τ₃ u)) := by
    intro u
    have h3 := discounted_playValue_step hH σ τ₃ u
    have hm := hm_step u
    linarith
  have hne : (Finset.univ : Finset V).Nonempty := ⟨v, Finset.mem_univ v⟩
  set M := Finset.univ.sup' hne (fun u => FriedmannDiscounted.playValue H σ τ₃ u - m u)
  have hle_M : ∀ u, FriedmannDiscounted.playValue H σ τ₃ u - m u ≤ M :=
    fun u => Finset.le_sup' (fun w => FriedmannDiscounted.playValue H σ τ₃ w - m w) (Finset.mem_univ u)
  obtain ⟨u₀, _, hu₀⟩ := Finset.exists_mem_eq_sup' hne
    (fun u => FriedmannDiscounted.playValue H σ τ₃ u - m u)
  have hM_step : M ≤ H.discount * M := by
    calc M = FriedmannDiscounted.playValue H σ τ₃ u₀ - m u₀ := hu₀
      _ ≤ H.discount * (FriedmannDiscounted.playValue H σ τ₃ (step H.arena σ τ₃ u₀) -
            m (step H.arena σ τ₃ u₀)) := hdiff u₀
      _ ≤ H.discount * M := mul_le_mul_of_nonneg_left (hle_M _) (le_of_lt hβ0)
  have hM_nonpos : M ≤ 0 := by nlinarith
  have hv := hle_M v
  linarith

lemma exists_disc_counterstrategy_list {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ : V → V) (L : List (V → V)) :
    ∃ ϱ : V → V,
      Legal H.arena true ϱ ∧
      ∀ τ ∈ L, Legal H.arena true τ →
        ∀ v, FriedmannDiscounted.playValue H σ ϱ v ≤ FriedmannDiscounted.playValue H σ τ v := by
  induction L with
  | nil =>
    have hex : ∀ v, ∃ w, H.arena.edge v w := hH.1
    refine ⟨fun v => Classical.choose (hex v), fun v _ => Classical.choose_spec (hex v), ?_⟩
    intro τ hmem
    nomatch hmem
  | cons τ₁ L ih =>
    rcases ih with ⟨τ₂, hτ₂, hle₂⟩
    by_cases hτ₁ : Legal H.arena true τ₁
    · refine ⟨minDiscStrategy H σ τ₁ τ₂, minDiscStrategy_legal hτ₁ hτ₂, ?_⟩
      intro τ hmem hleg v
      have hmin := playValue_minDiscStrategy_le hH σ τ₁ τ₂ v
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact le_trans hmin (min_le_left _ _)
      · exact le_trans hmin (le_trans (min_le_right _ _) (hle₂ τ hmem' hleg v))
    · refine ⟨τ₂, hτ₂, ?_⟩
      intro τ hmem hleg v
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact False.elim (hτ₁ hleg)
      · exact hle₂ τ hmem' hleg v

lemma exists_disc_optimalCounterstrategy {H : FriedmannDiscounted.Game V}
    (hH : FriedmannDiscounted.WellFormed H) (σ : V → V) :
    ∃ ϱ : V → V,
      Legal H.arena true ϱ ∧
      (∀ v τ, Legal H.arena true τ →
        FriedmannDiscounted.playValue H σ ϱ v ≤ FriedmannDiscounted.playValue H σ τ v) ∧
      ∀ v, FriedmannScalar.value (FriedmannDiscounted.model H) σ v =
        FriedmannDiscounted.playValue H σ ϱ v := by
  rcases exists_disc_counterstrategy_list hH σ (Finset.univ : Finset (V → V)).toList with
    ⟨ϱ, hϱ, hle⟩
  have hmin : ∀ v τ, Legal H.arena true τ →
      FriedmannDiscounted.playValue H σ ϱ v ≤ FriedmannDiscounted.playValue H σ τ v :=
    fun v τ hτ => hle τ (Finset.mem_toList.mpr (Finset.mem_univ τ)) hτ v
  refine ⟨ϱ, hϱ, hmin, ?_⟩
  intro v
  classical
  let M := FriedmannDiscounted.model H
  have hex : ∃ a : ℚ,
      (∃ τ, M.minLegal τ ∧ M.payoff σ τ v = a) ∧
        ∀ τ, M.minLegal τ → a ≤ M.payoff σ τ v :=
    ⟨FriedmannDiscounted.playValue H σ ϱ v, ⟨ϱ, hϱ, rfl⟩, fun τ hτ => hmin v τ hτ⟩
  have hval : FriedmannScalar.value M σ v = Classical.choose hex := by
    unfold FriedmannScalar.value
    rw [dif_pos hex]
  rw [hval]
  rcases Classical.choose_spec hex with ⟨⟨τ₀, hτ₀, hpay₀⟩, hle₀⟩
  apply le_antisymm
  · exact hle₀ ϱ hϱ
  · rw [← hpay₀]
    exact hmin v τ₀ hτ₀

/-! ### Part 3: Plays Reaching the 1-Sink -/

lemma cycleLeader_eq_sink_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    cycleLeader G σ τ v = sink := by
  apply (isSinkGame_wellFormed hSink).2
  rw [← playValue_cyclePriority_eq_priority_cycleLeader, hcp, isSinkGame_priority_sink hSink]

lemma eq_sink_of_mem_recurring_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∈ recurring (play G σ τ v)) :
    u = sink := by
  have hle : G.priority u ≤ (playValue G σ τ v).cyclePriority := Finset.le_sup hu
  have hge : 1 ≤ G.priority u := isSinkGame_one_le_priority hSink u
  exact (isSinkGame_priority_eq_one_iff hSink u).mp (by omega)

lemma step_sink_eq_sink_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    step G σ τ sink = sink := by
  have hcl := cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp
  have hmem : sink ∈ recurring (play G σ τ v) := hcl ▸ cycleLeader_mem_recurring G σ τ v
  exact eq_sink_of_mem_recurring_of_cyclePriority_eq_one hSink hcp (step_mem_recurring hmem)

lemma induced_reward_sink {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) :
    (FriedmannDiscounted.induced G).reward sink = - (Fintype.card V : ℚ) := by
  change (- (Fintype.card V : ℚ)) ^ G.priority sink = - (Fintype.card V : ℚ)
  rw [isSinkGame_priority_sink hSink, pow_one]

lemma discounted_playValue_sink_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ sink =
      - (Fintype.card V : ℚ) / (1 - (FriedmannDiscounted.induced G).discount) := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  have hstep := discounted_playValue_step hH σ τ sink
  have hsink_step : step H.arena σ τ sink = sink :=
    step_sink_eq_sink_of_cyclePriority_eq_one hSink hcp
  rw [hsink_step, induced_reward_sink hSink] at hstep
  have hβ1 : H.discount < 1 := hH.2.2
  rw [eq_div_iff (by linarith)]
  linarith

lemma mem_playValue_path_iff_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    u ∈ (playValue G σ τ v).path ↔
      ∃ t < (playValue G σ τ v).length, play G σ τ v t = u := by
  rw [mem_playValue_path_iff, hcp]
  constructor
  · exact fun h => h.1
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht, rfl⟩, ?_⟩
    have hne := play_ne_cycleLeader_of_lt_length ht
    rw [cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp] at hne
    exact isSinkGame_one_lt_priority_of_ne hSink hne

lemma playValue_path_eq_image_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    (playValue G σ τ v).path =
      (Finset.range (playValue G σ τ v).length).image (play G σ τ v) := by
  ext u
  rw [mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp, Finset.mem_image]
  simp only [Finset.mem_range]

lemma playValue_path_card_eq_length_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    (playValue G σ τ v).path.card = (playValue G σ τ v).length := by
  rw [playValue_path_eq_image_of_cyclePriority_eq_one hSink hcp]
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj heq
  rw [Finset.mem_coe, Finset.mem_range] at hi hj
  exact play_injective_of_le_length G σ τ v (le_of_lt hi) (le_of_lt hj) heq

lemma ne_sink_of_mem_playValue_path_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∈ (playValue G σ τ v).path) :
    u ≠ sink := by
  rw [mem_playValue_path_iff, hcp] at hu
  intro rfl
  have hp := isSinkGame_priority_sink hSink
  omega

lemma two_le_priority_of_mem_playValue_path_of_cyclePriority_eq_one
    {G : Game V} {ι : V → V} {sink : V}
    (_hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∈ (playValue G σ τ v).path) :
    2 ≤ G.priority u := by
  rw [mem_playValue_path_iff, hcp] at hu
  omega

lemma playValue_length_le_card_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    (playValue G σ τ v).length ≤ Fintype.card V := by
  rw [← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp]
  exact Finset.card_le_univ _

lemma valueLT_iff_setLT_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ τ₁ σ₂ τ₂ : V → V} {v₁ v₂ : V}
    (hcp₁ : (playValue G σ₁ τ₁ v₁).cyclePriority = 1)
    (hcp₂ : (playValue G σ₂ τ₂ v₂).cyclePriority = 1) :
    ValueLT G (playValue G σ₁ τ₁ v₁) (playValue G σ₂ τ₂ v₂) ↔
      SetLT G (playValue G σ₁ τ₁ v₁).path (playValue G σ₂ τ₂ v₂).path := by
  unfold ValueLT
  rw [hcp₁, hcp₂]
  constructor
  · rintro (hr | ⟨_, hs⟩ | ⟨_, hpath, hl⟩)
    · omega
    · exact hs
    · have hlen : (playValue G σ₁ τ₁ v₁).length = (playValue G σ₂ τ₂ v₂).length := by
        rw [← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp₁,
            ← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp₂, hpath]
      rcases hl with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega
  · intro hs
    exact Or.inr (Or.inl ⟨rfl, hs⟩)

lemma playValue_eq_iff_path_eq_of_cyclePriority_eq_one {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ τ₁ σ₂ τ₂ : V → V} {v₁ v₂ : V}
    (hcp₁ : (playValue G σ₁ τ₁ v₁).cyclePriority = 1)
    (hcp₂ : (playValue G σ₂ τ₂ v₂).cyclePriority = 1) :
    playValue G σ₁ τ₁ v₁ = playValue G σ₂ τ₂ v₂ ↔
      (playValue G σ₁ τ₁ v₁).path = (playValue G σ₂ τ₂ v₂).path := by
  constructor
  · intro h; rw [h]
  · intro hpath
    have hlen : (playValue G σ₁ τ₁ v₁).length = (playValue G σ₂ τ₂ v₂).length := by
      rw [← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp₁,
          ← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp₂, hpath]
    cases hp₁ : playValue G σ₁ τ₁ v₁
    cases hp₂ : playValue G σ₂ τ₂ v₂
    simp only [hp₁, hp₂] at hcp₁ hcp₂ hpath hlen ⊢
    subst hcp₁ hcp₂ hpath hlen
    rfl

lemma playValue_length_play_le (G : Game V) (σ τ : V → V) (w : V) {t : ℕ}
    (ht : t ≤ (playValue G σ τ w).length) :
    (playValue G σ τ (play G σ τ w t)).length ≤ (playValue G σ τ w).length - t := by
  have hcl : ∀ s : ℕ, cycleLeader G σ τ (play G σ τ w s) = cycleLeader G σ τ w := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [play_succ', cycleLeader_step, ih]
  apply length_le_of_play_eq_cycleLeader
  rw [hcl t, ← play_add]
  have hadd : t + ((playValue G σ τ w).length - t) = (playValue G σ τ w).length := by omega
  rw [hadd]
  exact play_playValue_length G σ τ w

lemma eq_of_playValue_path_eq {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v w : V}
    (hcp_v : (playValue G σ τ v).cyclePriority = 1)
    (hcp_w : (playValue G σ τ w).cyclePriority = 1)
    (hpath : (playValue G σ τ v).path = (playValue G σ τ w).path) :
    v = w := by
  have hlen : (playValue G σ τ v).length = (playValue G σ τ w).length := by
    rw [← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp_v,
        ← playValue_path_card_eq_length_of_cyclePriority_eq_one hSink hcp_w, hpath]
  rcases Nat.eq_zero_or_pos (playValue G σ τ v).length with h0 | hpos
  · have hv : v = sink := by
      have h1 := play_playValue_length G σ τ v
      rw [h0, play_zero, cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp_v] at h1
      exact h1
    have hw : w = sink := by
      have h2 := play_playValue_length G σ τ w
      rw [← hlen, h0, play_zero, cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp_w] at h2
      exact h2
    exact hv.trans hw.symm
  · have hv_mem : v ∈ (playValue G σ τ v).path := by
      rw [mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp_v]
      exact ⟨0, hpos, rfl⟩
    rw [hpath, mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp_w] at hv_mem
    rcases hv_mem with ⟨t, ht, hplay⟩
    have hle := playValue_length_play_le G σ τ w (le_of_lt ht)
    rw [hplay, ← hlen] at hle
    have ht0 : t = 0 := by omega
    rw [ht0, play_zero] at hplay
    exact hplay.symm

/-! ### Part 4: Path Comparison for Plays Reaching the 1-Sink (Lemma 9.7) -/

noncomputable def pathCoeff (G : Game V) (σ τ : V → V) (v u : V) : ℚ := by
  classical
  exact if h : ∃ t < (playValue G σ τ v).length, play G σ τ v t = u then
    (FriedmannDiscounted.induced G).discount ^ (Classical.choose h)
  else 0

lemma pathCoeff_eq_zero_of_notMem {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∉ (playValue G σ τ v).path) :
    pathCoeff G σ τ v u = 0 := by
  rw [mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp] at hu
  unfold pathCoeff
  rw [dif_neg hu]

lemma pathCoeff_play_eq_pow (G : Game V) (σ τ : V → V) (v : V) {t : ℕ}
    (ht : t < (playValue G σ τ v).length) :
    pathCoeff G σ τ v (play G σ τ v t) = (FriedmannDiscounted.induced G).discount ^ t := by
  have hex : ∃ t' < (playValue G σ τ v).length, play G σ τ v t' = play G σ τ v t :=
    ⟨t, ht, rfl⟩
  unfold pathCoeff
  rw [dif_pos hex]
  rcases Classical.choose_spec hex with ⟨ht', heq⟩
  have h_eq := play_injective_of_le_length G σ τ v (le_of_lt ht') (le_of_lt ht) heq
  rw [h_eq]

lemma pathCoeff_bounds_of_mem {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    (hu : u ∈ (playValue G σ τ v).path) :
    1 - (Fintype.card V : ℚ) * (1 - (FriedmannDiscounted.induced G).discount) ≤
      pathCoeff G σ τ v u ∧
    pathCoeff G σ τ v u ≤ 1 := by
  rw [mem_playValue_path_iff_of_cyclePriority_eq_one hSink hcp] at hu
  rcases hu with ⟨t, ht, rfl⟩
  rw [pathCoeff_play_eq_pow G σ τ v ht]
  have hlen := playValue_length_le_card_of_cyclePriority_eq_one hSink hcp
  exact induced_discount_pow_bounds hSink (le_trans (le_of_lt ht) hlen)

lemma pathCoeff_bounds {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v u : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    0 ≤ pathCoeff G σ τ v u ∧ pathCoeff G σ τ v u ≤ 1 := by
  by_cases hu : u ∈ (playValue G σ τ v).path
  · have hb := pathCoeff_bounds_of_mem hSink hcp hu
    have hq := card_mul_one_sub_induced_discount_le_quarter hSink
    exact ⟨by linarith, hb.2⟩
  · rw [pathCoeff_eq_zero_of_notMem hSink hcp hu]
    exact ⟨le_rfl, zero_le_one⟩

lemma sum_pathCoeff_mul_eq {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    {S : Finset V} (hsub : (playValue G σ τ v).path ⊆ S) (f : V → ℚ) :
    ∑ u ∈ S, pathCoeff G σ τ v u * f u =
      ∑ t ∈ Finset.range (playValue G σ τ v).length,
        (FriedmannDiscounted.induced G).discount ^ t * f (play G σ τ v t) := by
  have h1 : ∑ u ∈ S, pathCoeff G σ τ v u * f u =
      ∑ u ∈ (playValue G σ τ v).path, pathCoeff G σ τ v u * f u := by
    symm
    apply Finset.sum_subset hsub
    intro u _ hu_not
    rw [pathCoeff_eq_zero_of_notMem hSink hcp hu_not, zero_mul]
  rw [h1, playValue_path_eq_image_of_cyclePriority_eq_one hSink hcp]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    rw [pathCoeff_play_eq_pow G σ τ v ht]
  · intro i hi j hj heq
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    exact play_injective_of_le_length G σ τ v (le_of_lt hi) (le_of_lt hj) heq

lemma discounted_playValue_sub_sink_eq_sum_pathCoeff {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1)
    {S : Finset V} (hsub : (playValue G σ τ v).path ⊆ S) :
    FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ v -
      (- (Fintype.card V : ℚ) / (1 - (FriedmannDiscounted.induced G).discount)) =
      ∑ u ∈ S, pathCoeff G σ τ v u *
        ((FriedmannDiscounted.induced G).reward u + (Fintype.card V : ℚ)) := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  let c : ℚ := - (Fintype.card V : ℚ) / (1 - H.discount)
  have hc : c = - (Fintype.card V : ℚ) + H.discount * c := by
    dsimp only [c]
    have hβ1 : H.discount < 1 := hH.2.2
    have hne : 1 - H.discount ≠ 0 := by linarith
    field_simp
    ring
  have hexp := discounted_playValue_sub_const_expand hH σ τ v hc (playValue G σ τ v).length
  change FriedmannDiscounted.playValue H σ τ v - c =
    (∑ t ∈ Finset.range (playValue G σ τ v).length,
      H.discount ^ t * (H.reward (play G σ τ v t) - - (Fintype.card V : ℚ))) +
      H.discount ^ (playValue G σ τ v).length *
        (FriedmannDiscounted.playValue H σ τ (play G σ τ v (playValue G σ τ v).length) - c) at hexp
  rw [play_playValue_length, cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp,
      discounted_playValue_sink_of_cyclePriority_eq_one hSink hcp] at hexp
  change FriedmannDiscounted.playValue H σ τ v - c = _
  rw [hexp, sub_self, mul_zero, add_zero, sum_pathCoeff_mul_eq hSink hcp hsub]
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma discounted_playValue_lt_of_setLT {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ₁ τ₁ σ₂ τ₂ : V → V} {v₁ v₂ : V}
    (hcp₁ : (playValue G σ₁ τ₁ v₁).cyclePriority = 1)
    (hcp₂ : (playValue G σ₂ τ₂ v₂).cyclePriority = 1)
    (hset : SetLT G (playValue G σ₁ τ₁ v₁).path (playValue G σ₂ τ₂ v₂).path) :
    FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ₁ τ₁ v₁ <
      FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ₂ τ₂ v₂ := by
  let H := FriedmannDiscounted.induced G
  let U := (playValue G σ₁ τ₁ v₁).path
  let W := (playValue G σ₂ τ₂ v₂).path
  let N : ℚ := (Fintype.card V : ℚ)
  let c : ℚ := - N / (1 - H.discount)
  let g : V → ℚ := fun u =>
    (pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u) * (H.reward u + N)
  have hsub₁ := discounted_playValue_sub_sink_eq_sum_pathCoeff hSink hcp₁
    (Finset.subset_union_left : U ⊆ U ∪ W)
  have hsub₂ := discounted_playValue_sub_sink_eq_sum_pathCoeff hSink hcp₂
    (Finset.subset_union_right : W ⊆ U ∪ W)
  have hdiff : FriedmannDiscounted.playValue H σ₂ τ₂ v₂ -
      FriedmannDiscounted.playValue H σ₁ τ₁ v₁ = ∑ u ∈ U ∪ W, g u := by
    calc FriedmannDiscounted.playValue H σ₂ τ₂ v₂ - FriedmannDiscounted.playValue H σ₁ τ₁ v₁
        = (FriedmannDiscounted.playValue H σ₂ τ₂ v₂ - c) -
            (FriedmannDiscounted.playValue H σ₁ τ₁ v₁ - c) := by ring
      _ = (∑ u ∈ U ∪ W, pathCoeff G σ₂ τ₂ v₂ u * (H.reward u + N)) -
            (∑ u ∈ U ∪ W, pathCoeff G σ₁ τ₁ v₁ u * (H.reward u + N)) := by rw [hsub₂, hsub₁]
      _ = ∑ u ∈ U ∪ W, g u := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by dsimp [g]; ring)
  rcases hset with ⟨u_m, hu_mem, hu_max, hu_par⟩
  let p_m := G.priority u_m
  have hu_union : u_m ∈ U ∪ W := by
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hu_mem
    rw [Finset.mem_union]
    rcases hu_mem with ⟨hU, _⟩ | ⟨hW, _⟩
    · exact Or.inl hU
    · exact Or.inr hW
  have hne_sink_union : ∀ u ∈ U ∪ W, u ≠ sink := by
    intro u hu
    rcases Finset.mem_union.mp hu with hU | hW
    · exact ne_sink_of_mem_playValue_path_of_cyclePriority_eq_one hSink hcp₁ hU
    · exact ne_sink_of_mem_playValue_path_of_cyclePriority_eq_one hSink hcp₂ hW
  have hprio_ge_two_union : ∀ u ∈ U ∪ W, 2 ≤ G.priority u := by
    intro u hu
    rcases Finset.mem_union.mp hu with hU | hW
    · exact two_le_priority_of_mem_playValue_path_of_cyclePriority_eq_one hSink hcp₁ hU
    · exact two_le_priority_of_mem_playValue_path_of_cyclePriority_eq_one hSink hcp₂ hW
  have hu_m_ne_sink : u_m ≠ sink := hne_sink_union u_m hu_union
  have hp_m_ge_two : 2 ≤ p_m := hprio_ge_two_union u_m hu_union
  have hN_ge_two_nat : 2 ≤ Fintype.card V := two_le_card_of_ne hu_m_ne_sink
  have hN_ge_two : (2 : ℚ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hN_ge_two_nat
  let S_gt := ((U ∪ W).erase u_m).filter (fun u => p_m < G.priority u)
  let S_lt := ((U ∪ W).erase u_m).filter (fun u => ¬ p_m < G.priority u)
  have hsplit : ∑ u ∈ U ∪ W, g u = g u_m + ((∑ u ∈ S_gt, g u) + (∑ u ∈ S_lt, g u)) := by
    rw [← Finset.add_sum_erase _ _ hu_union,
        ← Finset.sum_filter_add_sum_filter_not ((U ∪ W).erase u_m) (fun u => p_m < G.priority u)]
  -- Bound 1: g u_m ≥ N ^ p_m - N - 1 / 2
  have hpow_ge_N : N ≤ N ^ p_m := by
    have h1 : N ^ 1 ≤ N ^ p_m := pow_le_pow_right₀ (by linarith) (by omega)
    simpa using h1
  have hpow_le_M : N ^ p_m ≤ (maxRewardNat G : ℚ) := by
    dsimp only [N, p_m]
    exact_mod_cast le_maxRewardNat G u_m
  have hg_um_1 : (1 - N * (1 - H.discount)) * (N ^ p_m - N) ≤ g u_m := by
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hu_mem
    rcases hu_par with ⟨he, huW⟩ | ⟨ho, huU⟩
    · have hu_notU : u_m ∉ U := by
        rcases hu_mem with ⟨_, hnW⟩ | ⟨_, hnU⟩
        · exact False.elim (hnW huW)
        · exact hnU
      have hc1 := pathCoeff_eq_zero_of_notMem hSink hcp₁ hu_notU
      have hc2 := pathCoeff_bounds_of_mem hSink hcp₂ huW
      have hc2_nonneg := (pathCoeff_bounds hSink hcp₂ (u := u_m)).1
      have hrew := induced_reward_of_even (G := G) he
      dsimp only [g]
      rw [hc1, sub_zero, hrew]
      have h1 : pathCoeff G σ₂ τ₂ v₂ u_m * (N ^ p_m - N) ≤
          pathCoeff G σ₂ τ₂ v₂ u_m * (N ^ p_m + N) :=
        mul_le_mul_of_nonneg_left (by linarith) hc2_nonneg
      have h2 : (1 - N * (1 - H.discount)) * (N ^ p_m - N) ≤
          pathCoeff G σ₂ τ₂ v₂ u_m * (N ^ p_m - N) :=
        mul_le_mul_of_nonneg_right hc2.1 (by linarith)
      linarith
    · have hu_notW : u_m ∉ W := by
        rcases hu_mem with ⟨_, hnW⟩ | ⟨_, hnU⟩
        · exact hnW
        · exact False.elim (hnU huU)
      have hc2 := pathCoeff_eq_zero_of_notMem hSink hcp₂ hu_notW
      have hc1 := pathCoeff_bounds_of_mem hSink hcp₁ huU
      have hrew := induced_reward_of_odd (G := G) ho
      dsimp only [g]
      rw [hc2, zero_sub, hrew]
      have heq : - pathCoeff G σ₁ τ₁ v₁ u_m * (- N ^ p_m + N) =
          pathCoeff G σ₁ τ₁ v₁ u_m * (N ^ p_m - N) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hc1.1 (by linarith)
  have hg_um : N ^ p_m - N - 1 / 2 ≤ g u_m := by
    have hq := card_mul_one_sub_induced_discount_mul_maxReward_le_quarter hSink
    have hH := isSinkGame_wellFormed_induced hSink
    have hnonneg : 0 ≤ N * (1 - H.discount) :=
      mul_nonneg (by linarith) (by linarith [hH.2.2])
    have hle : N * (1 - H.discount) * (N ^ p_m - N) ≤
        N * (1 - H.discount) * (maxRewardNat G : ℚ) :=
      mul_le_mul_of_nonneg_left (by linarith) hnonneg
    linarith
  -- Bound 2: -(1 / 2) ≤ ∑ u ∈ S_gt, g u
  have hS_gt_term : ∀ u ∈ S_gt, |g u| ≤ 1 / (2 * N) := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_erase] at hu
    rcases hu with ⟨⟨_, hu_UW⟩, hpu⟩
    have hu_UW' : u ∈ U ∧ u ∈ W := by
      rcases Finset.mem_union.mp hu_UW with hU | hW
      · refine ⟨hU, ?_⟩
        by_contra hnW
        have hsd : u ∈ (U \ W) ∪ (W \ U) :=
          Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hU, hnW⟩))
        have := hu_max u hsd
        omega
      · refine ⟨?_, hW⟩
        by_contra hnU
        have hsd : u ∈ (U \ W) ∪ (W \ U) :=
          Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hW, hnU⟩))
        have := hu_max u hsd
        omega
    have hb1 := pathCoeff_bounds_of_mem hSink hcp₁ hu_UW'.1
    have hb2 := pathCoeff_bounds_of_mem hSink hcp₂ hu_UW'.2
    have habs_c : |pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u| ≤ N * (1 - H.discount) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have habs_r := abs_induced_reward_add_card_le_two_maxReward hSink u
    dsimp only [g]
    rw [abs_mul]
    have hmul : |pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u| * |H.reward u + N| ≤
        (N * (1 - H.discount)) * (2 * (maxRewardNat G : ℚ)) :=
      mul_le_mul habs_c habs_r (abs_nonneg _) (by linarith [hb1.1, hb1.2])
    have heq : (N * (1 - H.discount)) * (2 * (maxRewardNat G : ℚ)) =
        2 * (N * (1 - H.discount) * (maxRewardNat G : ℚ)) := by ring
    rw [heq, card_mul_one_sub_induced_discount_mul_maxReward hSink] at hmul
    have hle_div : 2 * (1 / (4 * N ^ 2)) ≤ 1 / (2 * N) := by
      have hN2 : 2 * N ≤ 2 * N ^ 2 := by nlinarith
      have h1 : 2 * (1 / (4 * N ^ 2)) = 1 / (2 * N ^ 2) := by ring
      rw [h1, div_le_div_iff₀ (by nlinarith) (by linarith)]
      linarith
    linarith
  have hS_gt : - (1 / 2 : ℚ) ≤ ∑ u ∈ S_gt, g u := by
    have habs : |∑ u ∈ S_gt, g u| ≤ 1 / 2 := by
      have hcard_S_gt : (S_gt.card : ℚ) ≤ N := by
        dsimp only [N]
        exact_mod_cast Finset.card_le_univ S_gt
      have hdiv_nonneg : (0 : ℚ) ≤ 1 / (2 * N) :=
        div_nonneg zero_le_one (by linarith)
      calc |∑ u ∈ S_gt, g u|
          ≤ ∑ u ∈ S_gt, |g u| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u ∈ S_gt, (1 / (2 * N)) := Finset.sum_le_sum hS_gt_term
        _ = (S_gt.card : ℚ) * (1 / (2 * N)) := by simp
        _ ≤ N * (1 / (2 * N)) := mul_le_mul_of_nonneg_right hcard_S_gt hdiv_nonneg
        _ = 1 / 2 := by
          have hN_ne : N ≠ 0 := by linarith
          field_simp
    exact (abs_le.mp habs).1
  -- Bound 3: -(N ^ p_m - 2 * N) ≤ ∑ u ∈ S_lt, g u
  have hS_lt_term : ∀ u ∈ S_lt, |g u| ≤ N ^ G.priority u + N := by
    intro u _
    have hb1 := pathCoeff_bounds hSink hcp₁ (u := u)
    have hb2 := pathCoeff_bounds hSink hcp₂ (u := u)
    have habs_c : |pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have habs_r := abs_induced_reward_add_card_le G u
    dsimp only [g]
    rw [abs_mul]
    calc |pathCoeff G σ₂ τ₂ v₂ u - pathCoeff G σ₁ τ₁ v₁ u| * |H.reward u + N|
        ≤ 1 * (N ^ G.priority u + N) :=
          mul_le_mul habs_c habs_r (abs_nonneg _) zero_le_one
      _ = N ^ G.priority u + N := one_mul _
  have hS_lt_pow : ∑ u ∈ S_lt, N ^ G.priority u ≤ N ^ p_m - N ^ 2 := by
    have hsub_Ico : S_lt.image G.priority ⊆ Finset.Ico 2 p_m := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨u, hu, rfl⟩
      rw [Finset.mem_filter, Finset.mem_erase] at hu
      rcases hu with ⟨⟨hu_ne, hu_UW⟩, hnot_gt⟩
      have hge2 := hprio_ge_two_union u hu_UW
      have hne_pm : G.priority u ≠ p_m := fun heq => hu_ne ((isSinkGame_wellFormed hSink).2 heq)
      rw [Finset.mem_Ico]
      exact ⟨hge2, by omega⟩
    have hinj_on : Set.InjOn G.priority S_lt := by
      intro x _ y _ hxy
      exact (isSinkGame_wellFormed hSink).2 hxy
    calc ∑ u ∈ S_lt, N ^ G.priority u
        = ∑ p ∈ S_lt.image G.priority, N ^ p :=
          (Finset.sum_image (f := fun p => N ^ p) hinj_on).symm
      _ ≤ ∑ p ∈ Finset.Ico 2 p_m, N ^ p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_Ico (fun _ _ _ => pow_nonneg (by linarith) _)
      _ ≤ N ^ p_m - N ^ 2 := sum_Ico_pow_le hN_ge_two 2 p_m hp_m_ge_two
  have hS_lt_card : (S_lt.card : ℚ) ≤ N - 2 := by
    have hsub_erase : S_lt ⊆ (Finset.univ.erase sink).erase u_m := by
      intro u hu
      rw [Finset.mem_filter, Finset.mem_erase] at hu
      rcases hu with ⟨⟨hu_ne_um, hu_UW⟩, _⟩
      have hu_ne_sink := hne_sink_union u hu_UW
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨hu_ne_um, hu_ne_sink, Finset.mem_univ u⟩
    have hcard_le := Finset.card_le_card hsub_erase
    have hum_mem_erase : u_m ∈ (Finset.univ : Finset V).erase sink :=
      Finset.mem_erase.mpr ⟨hu_m_ne_sink, Finset.mem_univ u_m⟩
    rw [Finset.card_erase_of_mem hum_mem_erase,
        Finset.card_erase_of_mem (Finset.mem_univ sink), Finset.card_univ] at hcard_le
    have hcard_nat : S_lt.card + 2 ≤ Fintype.card V := by omega
    have hcard_Q : ((S_lt.card + 2 : ℕ) : ℚ) ≤ N := by
      dsimp only [N]
      exact_mod_cast hcard_nat
    push_cast at hcard_Q
    linarith
  have hS_lt : - (N ^ p_m - 2 * N) ≤ ∑ u ∈ S_lt, g u := by
    have habs : |∑ u ∈ S_lt, g u| ≤ N ^ p_m - 2 * N := by
      calc |∑ u ∈ S_lt, g u|
          ≤ ∑ u ∈ S_lt, |g u| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ u ∈ S_lt, (N ^ G.priority u + N) := Finset.sum_le_sum hS_lt_term
        _ = (∑ u ∈ S_lt, N ^ G.priority u) + (∑ _u ∈ S_lt, N) := Finset.sum_add_distrib
        _ = (∑ u ∈ S_lt, N ^ G.priority u) + (S_lt.card : ℚ) * N := by simp
        _ ≤ (N ^ p_m - N ^ 2) + (N - 2) * N :=
          add_le_add hS_lt_pow (mul_le_mul_of_nonneg_right hS_lt_card (by linarith))
        _ = N ^ p_m - 2 * N := by ring
    exact (abs_le.mp habs).1
  linarith

/-! ### Part 5: Excluding Non-Sink Cycles (Lemma 9.6) and Main Theorem -/

lemma abs_sum_range_reward_le {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) (σ τ : V → V) (v : V) {k : ℕ}
    (hk : k ≤ Fintype.card V) :
    |∑ t ∈ Finset.range k,
      (FriedmannDiscounted.induced G).discount ^ t *
        (FriedmannDiscounted.induced G).reward (play G σ τ v t)| ≤
      (Fintype.card V : ℚ) * (maxRewardNat G : ℚ) := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  have hβ0 : 0 ≤ H.discount := le_of_lt hH.2.1
  have hβ1 : H.discount ≤ 1 := le_of_lt hH.2.2
  calc |∑ t ∈ Finset.range k, H.discount ^ t * H.reward (play G σ τ v t)|
      ≤ ∑ t ∈ Finset.range k, |H.discount ^ t * H.reward (play G σ τ v t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range k, (maxRewardNat G : ℚ) := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      calc H.discount ^ t * |H.reward (play G σ τ v t)|
          ≤ 1 * (maxRewardNat G : ℚ) :=
            mul_le_mul (pow_le_one₀ hβ0 hβ1) (abs_induced_reward_le_maxReward G _)
              (abs_nonneg _) zero_le_one
        _ = (maxRewardNat G : ℚ) := one_mul _
    _ = (k : ℚ) * (maxRewardNat G : ℚ) := by simp
    _ ≤ (Fintype.card V : ℚ) * (maxRewardNat G : ℚ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hk
      · exact Nat.cast_nonneg _

lemma discounted_playValue_lt_zero_of_cyclePriority_eq_one
    {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hcp : (playValue G σ τ v).cyclePriority = 1) :
    FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ v < 0 := by
  have hH := isSinkGame_wellFormed_induced hSink
  have hk : (playValue G σ τ v).length ≤ Fintype.card V :=
    playValue_length_le_card_of_cyclePriority_eq_one hSink hcp
  have hexp := discounted_playValue_expand hH σ τ v (playValue G σ τ v).length
  change FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ v =
    (∑ t ∈ Finset.range (playValue G σ τ v).length,
      (FriedmannDiscounted.induced G).discount ^ t *
        (FriedmannDiscounted.induced G).reward (play G σ τ v t)) +
      (FriedmannDiscounted.induced G).discount ^ (playValue G σ τ v).length *
        FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ
          (play G σ τ v (playValue G σ τ v).length) at hexp
  rw [play_playValue_length, cycleLeader_eq_sink_of_cyclePriority_eq_one hSink hcp,
      discounted_playValue_sink_of_cyclePriority_eq_one hSink hcp] at hexp
  have hsum_le := (abs_le.mp (abs_sum_range_reward_le hSink σ τ v hk)).2
  have hpow_half := one_half_le_induced_discount_pow hSink hk
  have hN1 : (1 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast isSinkGame_card_pos hSink
  have hM1 : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have hN4 : (Fintype.card V : ℚ) ≤ (Fintype.card V : ℚ) ^ 4 := le_self_pow₀ hN1 (by omega)
  have hsink_val : - (Fintype.card V : ℚ) / (1 - (FriedmannDiscounted.induced G).discount) =
      - (4 * (Fintype.card V : ℚ) ^ 4 * (maxRewardNat G : ℚ)) := by
    rw [one_sub_induced_discount]
    have hN_ne : (Fintype.card V : ℚ) ≠ 0 := by linarith
    have hM_ne : (maxRewardNat G : ℚ) ≠ 0 := by linarith
    field_simp
  rw [hsink_val] at hexp
  have hsink_ge : 4 * (Fintype.card V : ℚ) * (maxRewardNat G : ℚ) ≤
      4 * (Fintype.card V : ℚ) ^ 4 * (maxRewardNat G : ℚ) := by nlinarith
  have htail_ge : (1 / 2) * (4 * (Fintype.card V : ℚ) * (maxRewardNat G : ℚ)) ≤
      (FriedmannDiscounted.induced G).discount ^ (playValue G σ τ v).length *
        (4 * (Fintype.card V : ℚ) ^ 4 * (maxRewardNat G : ℚ)) :=
    mul_le_mul hpow_half hsink_ge (by nlinarith) (by linarith)
  nlinarith

lemma zero_lt_discounted_playValue_of_cycleLeader_ne_sink
    {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) {σ τ : V → V} {v : V}
    (hrew_ge : reward 1 ≤ reward (playValue G σ τ v).cyclePriority)
    (hw_ne : cycleLeader G σ τ v ≠ sink) :
    0 < FriedmannDiscounted.playValue (FriedmannDiscounted.induced G) σ τ v := by
  let H := FriedmannDiscounted.induced G
  have hH := isSinkGame_wellFormed_induced hSink
  let w := cycleLeader G σ τ v
  let p_w := G.priority w
  let N : ℚ := (Fintype.card V : ℚ)
  have hcp_eq : (playValue G σ τ v).cyclePriority = p_w :=
    playValue_cyclePriority_eq_priority_cycleLeader G σ τ v
  have hp_w_gt_one : 1 < p_w := isSinkGame_one_lt_priority_of_ne hSink hw_ne
  have hp_w_even : p_w % 2 = 0 := by
    rw [hcp_eq] at hrew_ge
    unfold reward at hrew_ge
    rcases Nat.mod_two_eq_zero_or_one p_w with he | ho
    · exact he
    · rw [if_neg (by omega), if_neg (by omega)] at hrew_ge
      omega
  have hN_ge_two : (2 : ℚ) ≤ N := by
    dsimp only [N]
    exact_mod_cast two_le_card_of_ne hw_ne
  -- Simple cycle from w to w of length L = d + 1
  have hw_rec : w ∈ recurring (play G σ τ v) := cycleLeader_mem_recurring G σ τ v
  have hcp_w : (playValue G σ τ w).cyclePriority = (playValue G σ τ v).cyclePriority := by
    simp only [playValue_cyclePriority, recurring_eq_of_mem_recurring hw_rec]
  have hcl_w : cycleLeader G σ τ w = w :=
    cycleLeader_eq_of_cyclePriority_eq (isSinkGame_wellFormed hSink).2 hcp_w
  let w' := step G σ τ w
  have hcl_w' : cycleLeader G σ τ w' = w := (cycleLeader_step G σ τ w).trans hcl_w
  let d := (playValue G σ τ w').length
  let L := d + 1
  have hplay_L : play G σ τ w L = w := by
    dsimp only [L, d, w']
    rw [play_succ]
    exact (play_playValue_length G σ τ w').trans hcl_w'
  have hinj_L : Set.InjOn (play G σ τ w) (Finset.range L) := by
    intro i hi j hj heq
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases i with _ | i' <;> rcases j with _ | j'
    · rfl
    · exfalso
      rw [play_zero, play_succ] at heq
      have hne := play_ne_cycleLeader_of_lt_length (G := G) (σ := σ) (τ := τ) (v := w') (t := j')
        (by omega)
      rw [hcl_w'] at hne
      exact hne heq.symm
    · exfalso
      rw [play_succ, play_zero] at heq
      have hne := play_ne_cycleLeader_of_lt_length (G := G) (σ := σ) (τ := τ) (v := w') (t := i')
        (by omega)
      rw [hcl_w'] at hne
      exact hne heq
    · rw [play_succ, play_succ] at heq
      have h_eq := play_injective_of_le_length G σ τ w' (by omega) (by omega) heq
      omega
  have hL_le_N : L ≤ Fintype.card V := by
    have hcard := Finset.card_image_of_injOn hinj_L
    rw [Finset.card_range] at hcard
    rw [← hcard]
    exact Finset.card_le_univ _
  -- Expand playValue H σ τ w over L steps
  have hexp_w := discounted_playValue_expand hH σ τ w L
  change FriedmannDiscounted.playValue H σ τ w =
    (∑ t ∈ Finset.range L, H.discount ^ t * H.reward (play G σ τ w t)) +
      H.discount ^ L * FriedmannDiscounted.playValue H σ τ (play G σ τ w L) at hexp_w
  rw [hplay_L] at hexp_w
  have hsum_split : ∑ t ∈ Finset.range L, H.discount ^ t * H.reward (play G σ τ w t) =
      N ^ p_w + ∑ t ∈ Finset.Ico 1 L, H.discount ^ t * H.reward (play G σ τ w t) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < L)]
    simp only [pow_zero, one_mul, play_zero]
    rw [induced_reward_of_even hp_w_even]
  have hIco_bound : -(N ^ p_w - N) ≤
      ∑ t ∈ Finset.Ico 1 L, H.discount ^ t * H.reward (play G σ τ w t) := by
    have habs : |∑ t ∈ Finset.Ico 1 L, H.discount ^ t * H.reward (play G σ τ w t)| ≤
        N ^ p_w - N := by
      have hβ0 : 0 ≤ H.discount := le_of_lt hH.2.1
      have hβ1 : H.discount ≤ 1 := le_of_lt hH.2.2
      have hsub_Ico : (Finset.Ico 1 L).image (fun t => G.priority (play G σ τ w t)) ⊆
          Finset.Ico 1 p_w := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
        rw [Finset.mem_Ico] at ht ⊢
        have hmem_t : play G σ τ w t ∈ recurring (play G σ τ v) :=
          play_mem_recurring hw_rec t
        have hle_pw : G.priority (play G σ τ w t) ≤ p_w := by
          rw [← hcp_eq]
          exact Finset.le_sup hmem_t
        have hne_w : play G σ τ w t ≠ w := by
          intro heq
          have h0 : play G σ τ w t = play G σ τ w 0 := heq
          have ht0 := hinj_L (Finset.mem_coe.mpr (Finset.mem_range.mpr ht.2))
            (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) h0
          omega
        have hne_pw : G.priority (play G σ τ w t) ≠ p_w :=
          fun heq => hne_w ((isSinkGame_wellFormed hSink).2 heq)
        exact ⟨isSinkGame_one_le_priority hSink _, by omega⟩
      have hinj_prio : Set.InjOn (fun t => G.priority (play G σ τ w t)) (Finset.Ico 1 L) := by
        intro i hi j hj heq
        rw [Finset.mem_coe, Finset.mem_Ico] at hi hj
        have hplay_eq := (isSinkGame_wellFormed hSink).2 heq
        exact hinj_L (Finset.mem_coe.mpr (Finset.mem_range.mpr hi.2))
          (Finset.mem_coe.mpr (Finset.mem_range.mpr hj.2)) hplay_eq
      calc |∑ t ∈ Finset.Ico 1 L, H.discount ^ t * H.reward (play G σ τ w t)|
          ≤ ∑ t ∈ Finset.Ico 1 L, |H.discount ^ t * H.reward (play G σ τ w t)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ Finset.Ico 1 L, N ^ G.priority (play G σ τ w t) := by
          apply Finset.sum_le_sum
          intro t _
          rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), abs_induced_reward]
          calc H.discount ^ t * N ^ G.priority (play G σ τ w t)
              ≤ 1 * N ^ G.priority (play G σ τ w t) :=
                mul_le_mul_of_nonneg_right (pow_le_one₀ hβ0 hβ1) (pow_nonneg (by linarith) _)
            _ = N ^ G.priority (play G σ τ w t) := one_mul _
        _ = ∑ p ∈ (Finset.Ico 1 L).image (fun t => G.priority (play G σ τ w t)), N ^ p :=
          (Finset.sum_image (f := fun p => N ^ p) hinj_prio).symm
        _ ≤ ∑ p ∈ Finset.Ico 1 p_w, N ^ p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_Ico (fun _ _ _ => pow_nonneg (by linarith) _)
        _ ≤ N ^ p_w - N ^ 1 := sum_Ico_pow_le hN_ge_two 1 p_w (by omega)
        _ = N ^ p_w - N := by rw [pow_one]
    exact (abs_le.mp habs).1
  have hcycle_ge : N ≤ (1 - H.discount ^ L) * FriedmannDiscounted.playValue H σ τ w := by
    linarith
  have h1_sub_pow_pos : 0 < 1 - H.discount ^ L := by
    have hlt : H.discount ^ L < 1 := pow_lt_one₀ (le_of_lt hH.2.1) hH.2.2 (by omega)
    linarith
  have hx_w_pos : 0 < FriedmannDiscounted.playValue H σ τ w := by
    by_contra hle
    have : (1 - H.discount ^ L) * FriedmannDiscounted.playValue H σ τ w ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h1_sub_pow_pos) (not_lt.mp hle)
    linarith
  have h1_sub_pow_le : 1 - H.discount ^ L ≤ N * (1 - H.discount) := by
    have hb := (induced_discount_pow_bounds hSink hL_le_N).1
    linarith
  have hN_le_mul : N ≤ N * (1 - H.discount) * FriedmannDiscounted.playValue H σ τ w := by
    calc N ≤ (1 - H.discount ^ L) * FriedmannDiscounted.playValue H σ τ w := hcycle_ge
      _ ≤ (N * (1 - H.discount)) * FriedmannDiscounted.playValue H σ τ w :=
        mul_le_mul_of_nonneg_right h1_sub_pow_le (le_of_lt hx_w_pos)
  have hx_w_ge : 4 * N * (maxRewardNat G : ℚ) ≤ FriedmannDiscounted.playValue H σ τ w := by
    have hq := card_mul_one_sub_induced_discount_mul_maxReward hSink
    have hN2 : 1 ≤ N ^ 2 := by nlinarith
    have hmul : (N * (1 - H.discount) * (maxRewardNat G : ℚ)) * (4 * N ^ 2) = 1 := by
      dsimp only [N, H]
      rw [hq]
      have hN_ne : (Fintype.card V : ℚ) ≠ 0 := by linarith
      field_simp
    have h1 : 4 * N ^ 3 * (maxRewardNat G : ℚ) ≤ FriedmannDiscounted.playValue H σ τ w := by
      nlinarith
    have hM1 : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
    have hN_le_N3 : N ≤ N ^ 3 := by nlinarith
    nlinarith
  -- Now expand playValue H σ τ v to w in k ≤ Fintype.card V steps
  let k := (playValue G σ τ v).length
  have hk : k ≤ Fintype.card V := by
    have hinj_k : Set.InjOn (play G σ τ v) (Finset.range k) := by
      intro i hi j hj heq
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      exact play_injective_of_le_length G σ τ v (le_of_lt hi) (le_of_lt hj) heq
    have hcard := Finset.card_image_of_injOn hinj_k
    rw [Finset.card_range] at hcard
    rw [← hcard]
    exact Finset.card_le_univ _
  have hexp_v := discounted_playValue_expand hH σ τ v k
  change FriedmannDiscounted.playValue H σ τ v =
    (∑ t ∈ Finset.range k, H.discount ^ t * H.reward (play G σ τ v t)) +
      H.discount ^ k * FriedmannDiscounted.playValue H σ τ (play G σ τ v (playValue G σ τ v).length) at hexp_v
  rw [play_playValue_length] at hexp_v
  have hsum_ge := (abs_le.mp (abs_sum_range_reward_le hSink σ τ v hk)).1
  have hpow_half := one_half_le_induced_discount_pow hSink hk
  have hM1 : (1 : ℚ) ≤ (maxRewardNat G : ℚ) := by exact_mod_cast isSinkGame_one_le_maxRewardNat hSink
  have htail_ge : (1 / 2) * (4 * N * (maxRewardNat G : ℚ)) ≤
      H.discount ^ k * FriedmannDiscounted.playValue H σ τ w :=
    mul_le_mul hpow_half hx_w_ge (by nlinarith) (by linarith)
  nlinarith

end SinkTransport

theorem sink_discounted_order {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (ι : V → V) (sink : V) (hSink : IsSinkGame G ι sink)
    (σ : V → V) (hσ : Legal G false σ)
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) (v w : V) :
    ValueLT G (value G σ v) (value G σ w) ↔
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v <
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ w := by
  let H := FriedmannDiscounted.induced G
  have hG := isSinkGame_wellFormed hSink
  have hH := isSinkGame_wellFormed_induced hSink
  have hcp_val : ∀ u, (value G σ u).cyclePriority = 1 :=
    hSink.2.2.2.2.2.2 σ hσ hAbove
  rcases exists_optimalCounterstrategy G hG σ with ⟨τ_star, hτ_star⟩
  have hval_eq : ∀ u, value G σ u = playValue G σ τ_star u :=
    value_eq_playValue_of_optimalCounterstrategy hG hτ_star
  have hcp_star : ∀ u, (playValue G σ τ_star u).cyclePriority = 1 := by
    intro u
    rw [← hval_eq u]
    exact hcp_val u
  rcases exists_disc_optimalCounterstrategy hH σ with ⟨ϱ, hϱ_leg, hϱ_min, hϱ_val⟩
  have hcp_ϱ : ∀ u, (playValue G σ ϱ u).cyclePriority = 1 := by
    intro u
    have hle_u : ValueLE G (playValue G σ τ_star u) (playValue G σ ϱ u) :=
      hτ_star.2 u ϱ hϱ_leg
    have hrew_ge : reward 1 ≤ reward (playValue G σ ϱ u).cyclePriority := by
      have h := reward_cyclePriority_le_of_valueLE hle_u
      rwa [hcp_star u] at h
    by_contra hne_one
    have hcl_ne : cycleLeader G σ ϱ u ≠ sink := by
      intro hcl
      apply hne_one
      rw [playValue_cyclePriority_eq_priority_cycleLeader, hcl, isSinkGame_priority_sink hSink]
    have hneg := discounted_playValue_lt_zero_of_cyclePriority_eq_one hSink (hcp_star u)
    have hpos := zero_lt_discounted_playValue_of_cycleLeader_ne_sink hSink hrew_ge hcl_ne
    have hmin_u := hϱ_min u τ_star hτ_star.1
    linarith
  have hpath_eq : ∀ u, (playValue G σ τ_star u).path = (playValue G σ ϱ u).path := by
    intro u
    have hle_u : ValueLE G (playValue G σ τ_star u) (playValue G σ ϱ u) :=
      hτ_star.2 u ϱ hϱ_leg
    rcases hle_u with heq | hlt
    · rw [heq]
    · exfalso
      rw [valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_star u) (hcp_ϱ u)] at hlt
      have hlt_disc := discounted_playValue_lt_of_setLT hSink (hcp_star u) (hcp_ϱ u) hlt
      have hmin_u := hϱ_min u τ_star hτ_star.1
      linarith
  rw [hval_eq v, hval_eq w, hϱ_val v, hϱ_val w]
  rw [valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_star v) (hcp_star w)]
  rw [hpath_eq v, hpath_eq w]
  constructor
  · intro hset
    exact discounted_playValue_lt_of_setLT hSink (hcp_ϱ v) (hcp_ϱ w) hset
  · intro hlt_disc
    rcases valueLT_trichotomy hG.2 (playValue G σ ϱ v) (playValue G σ ϱ w) with heq | hlt | hgt
    · exfalso
      have hpath : (playValue G σ ϱ v).path = (playValue G σ ϱ w).path := by rw [heq]
      have hvw := eq_of_playValue_path_eq hSink (hcp_ϱ v) (hcp_ϱ w) hpath
      subst hvw
      exact lt_irrefl _ hlt_disc
    · exact (valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_ϱ v) (hcp_ϱ w)).mp hlt
    · exfalso
      have hset_gt := (valueLT_iff_setLT_of_cyclePriority_eq_one hSink (hcp_ϱ w) (hcp_ϱ v)).mp hgt
      have hgt_disc := discounted_playValue_lt_of_setLT hSink (hcp_ϱ w) (hcp_ϱ v) hset_gt
      linarith

end FriedmannParity

namespace FriedmannDiscounted

open FriedmannParity

theorem solution_transport {V : Type} [Fintype V] [DecidableEq V]
    (G : FriedmannParity.Game V) (ι : V → V) (sink : V) (hSink : IsSinkGame G ι sink)
    (σ : V → V) (hσ : Legal G false σ)
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) (v w : V) :
    ValueLT G (value G σ v) (value G σ w) ↔
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v <
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ w :=
  sink_discounted_order G ι sink hSink σ hσ hAbove v w

end FriedmannDiscounted

end Mod_transport

open FriedmannParity in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (ι : V → V) (sink : V) (hSink : IsSinkGame G ι sink)
    (σ : V → V) (hσ : Legal G false σ)
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) (v w : V) :
    ValueLT G (value G σ v) (value G σ w) ↔
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v <
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ w := by
  first
    | exact FriedmannParity.sink_discounted_order
    | (apply FriedmannParity.sink_discounted_order <;> assumption)
