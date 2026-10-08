-- Prove2me | solution 1 for EdmondsMatching65.Polyhedron.theorem_P_vertices_eq_matching_vectors
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T17:24:57.378654+00:00
-- url     : https://prove2.me/submissions/16da7006-b492-4cae-bdc3-38c3593e0ec0

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron
import Theorems.Thm_EdmondsMatching65_Polyhedron_matchingVectors_subset_extremePoints

universe u v

namespace EdmondsPM

open Finset

noncomputable section
open scoped Classical

/-- A finite multigraph on fixed ambient types: active nodes `U`, active edges `F`. -/
structure MG (V E : Type*) where
  ends : E → Sym2 V
  U : Finset V
  F : Finset E
  sub : ∀ e ∈ F, ∀ a ∈ ends e, a ∈ U
  loopless : ∀ e ∈ F, ¬ (ends e).IsDiag


variable {V : Type u} {E : Type v}

namespace MG
variable (G : MG V E)

/-- edges at a node -/
def at_ (v : V) : Finset E := G.F.filter (fun e => v ∈ G.ends e)
/-- edges inside a node set -/
def ins (S : Finset V) : Finset E := G.F.filter (fun e => ∀ a ∈ G.ends e, a ∈ S)
/-- edges crossing a node set -/
def cut (S : Finset V) : Finset E :=
  G.F.filter (fun e => (∃ a ∈ G.ends e, a ∈ S) ∧ ∃ a ∈ G.ends e, a ∉ S)

end MG

/-- the perfect matching polytope -/
def InQ (G : MG V E) (x : E → ℝ) : Prop :=
  (∀ e ∈ G.F, 0 ≤ x e) ∧ (∀ v ∈ G.U, ∑ e ∈ G.at_ v, x e = 1) ∧
    ∀ S ⊆ G.U, Odd S.card → 1 ≤ ∑ e ∈ G.cut S, x e

def IsPM (G : MG V E) (M : Finset E) : Prop :=
  M ⊆ G.F ∧ ∀ v ∈ G.U, (M.filter (fun e => v ∈ G.ends e)).card = 1

def ind (M : Finset E) (e : E) : ℝ := if e ∈ M then 1 else 0

/-- `x` is a convex combination of perfect matchings (on the active edges). -/
def ConvPM (G : MG V E) (x : E → ℝ) : Prop :=
  ∃ (ι : Type v) (_ : Fintype ι) (w : ι → ℝ) (M : ι → Finset E),
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, 0 < w i → IsPM G (M i)) ∧
      ∀ e ∈ G.F, x e = ∑ i, w i * ind (M i) e

lemma mem_at {G : MG V E} {v : V} {e : E} : e ∈ G.at_ v ↔ e ∈ G.F ∧ v ∈ G.ends e := mem_filter

lemma mem_ins {G : MG V E} {S : Finset V} {e : E} :
    e ∈ G.ins S ↔ e ∈ G.F ∧ ∀ a ∈ G.ends e, a ∈ S := mem_filter

lemma mem_cut {G : MG V E} {S : Finset V} {e : E} :
    e ∈ G.cut S ↔ e ∈ G.F ∧ (∃ a ∈ G.ends e, a ∈ S) ∧ ∃ a ∈ G.ends e, a ∉ S := mem_filter

lemma ind_pos {M : Finset E} {e : E} (h : e ∈ M) : ind M e = 1 := if_pos h

lemma ind_neg {M : Finset E} {e : E} (h : e ∉ M) : ind M e = 0 := if_neg h

lemma IsPM.eq {G : MG V E} {M : Finset E} (h : IsPM G M) {v : V} (hv : v ∈ G.U) {e f : E}
    (he : e ∈ M) (hf : f ∈ M) (hve : v ∈ G.ends e) (hvf : v ∈ G.ends f) : e = f := by
  obtain ⟨c, hc⟩ := card_eq_one.1 (h.2 v hv)
  have h1 : e ∈ M.filter (fun e => v ∈ G.ends e) := mem_filter.2 ⟨he, hve⟩
  have h2 : f ∈ M.filter (fun e => v ∈ G.ends e) := mem_filter.2 ⟨hf, hvf⟩
  rw [hc, mem_singleton] at h1 h2
  rw [h1, h2]

lemma card_filter_mem (z : Sym2 V) (hz : ¬ z.IsDiag) (S : Finset V) :
    ((S.filter (fun a => a ∈ z)).card : ℝ) =
      2 * (if ∀ a ∈ z, a ∈ S then 1 else 0) +
        (if (∃ a ∈ z, a ∈ S) ∧ ∃ a ∈ z, a ∉ S then 1 else 0) := by
  induction z using Sym2.ind with
  | h a b =>
    rw [Sym2.mk_isDiag_iff] at hz
    have hf : S.filter (fun c => c ∈ s(a, b)) =
        (if a ∈ S then {a} else ∅) ∪ (if b ∈ S then {b} else ∅) := by
      ext c; by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
        simp [ha, hb, Sym2.mem_iff] <;> aesop
    rw [hf]
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
      simp [ha, hb, Sym2.mem_iff, Finset.card_pair hz]

lemma handshake (G : MG V E) (S : Finset V) (x : E → ℝ) :
    ∑ a ∈ S, ∑ e ∈ G.at_ a, x e = 2 * ∑ e ∈ G.ins S, x e + ∑ e ∈ G.cut S, x e := by
  simp only [MG.at_, MG.ins, MG.cut, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    card_filter_mem _ (G.loopless e he) S]
  split_ifs <;> ring

/-! ### Deletion of an edge -/

def MG.erase (G : MG V E) (e0 : E) : MG V E where
  ends := G.ends
  U := G.U
  F := G.F.erase e0
  sub e he := G.sub e (mem_of_mem_erase he)
  loopless e he := G.loopless e (mem_of_mem_erase he)

lemma inQ_erase {G : MG V E} {x : E → ℝ} (hx : InQ G x) {e0 : E} (h0 : x e0 = 0) :
    InQ (G.erase e0) x := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨fun e he => h1 e (mem_of_mem_erase he), fun v hv => ?_, fun S hS hodd => ?_⟩
  · rw [show (G.erase e0).at_ v = (G.at_ v).erase e0 by
      ext e; simp only [MG.at_, mem_filter, mem_erase]; exact ⟨fun ⟨h1, h2⟩ => ⟨(mem_erase.1 h1).1, (mem_erase.1 h1).2, h2⟩, fun ⟨h1, h2, h3⟩ => ⟨mem_erase.2 ⟨h1, h2⟩, h3⟩⟩, Finset.sum_erase _ h0]
    exact h2 v hv
  · rw [show (G.erase e0).cut S = (G.cut S).erase e0 by
      ext e; simp only [MG.cut, mem_filter, mem_erase]; exact ⟨fun ⟨h1, h2⟩ => ⟨(mem_erase.1 h1).1, (mem_erase.1 h1).2, h2⟩, fun ⟨h1, h2, h3⟩ => ⟨mem_erase.2 ⟨h1, h2⟩, h3⟩⟩, Finset.sum_erase _ h0]
    exact h3 S hS hodd

lemma convPM_of_erase {G : MG V E} {x : E → ℝ} {e0 : E} (h0 : x e0 = 0)
    (h : ConvPM (G.erase e0) x) : ConvPM G x := by
  obtain ⟨ι, _, w, M, hw, hs, hpm, hm⟩ := h
  refine ⟨ι, inferInstance, w, M, hw, hs, fun i hi => ?_, fun e he => ?_⟩
  · obtain ⟨h1, h2⟩ := hpm i hi
    exact ⟨h1.trans (erase_subset _ _), h2⟩
  · by_cases he0 : e = e0
    · subst he0
      rw [h0]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rcases (hw i).lt_or_eq with hi | hi
      · have := (hpm i hi).1
        have : e ∉ M i := fun h => by
          have h' : e ∈ G.F.erase e := this h
          simp at h'
        simp [ind, this]
      · simp [← hi]
    · exact hm e (mem_erase.2 ⟨he0, he⟩)

/-! ### Convex combinations -/

lemma convPM_combo {G : MG V E} {x y z : E → ℝ} (hy : ConvPM G y) (hz : ConvPM G z)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : ∀ e ∈ G.F, x e = a * y e + b * z e) : ConvPM G x := by
  obtain ⟨ι, _, w, M, hw, hs, hpm, hm⟩ := hy
  obtain ⟨κ, _, u, N, hu, hs', hpm', hm'⟩ := hz
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim (fun i => a * w i) (fun j => b * u j),
    Sum.elim M N, ?_, ?_, ?_, ?_⟩
  · rintro (i | j)
    · exact mul_nonneg ha (hw i)
    · exact mul_nonneg hb (hu j)
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum, hs, hs', hab, mul_one]
  · rintro (i | j) h
    · exact hpm i (pos_of_mul_pos_right h ha)
    · exact hpm' j (pos_of_mul_pos_right h hb)
  · intro e he
    rw [Fintype.sum_sum_type, hx e he, hm e he, hm' e he]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.mul_sum, mul_assoc]

/-! ### Contraction of a node set -/

def coll (S : Finset V) (s0 : V) (a : V) : V := if a ∈ S then s0 else a

def MG.contract (G : MG V E) (S : Finset V) (s0 : V) (hs0 : s0 ∈ S) : MG V E where
  ends e := (G.ends e).map (coll S s0)
  U := insert s0 (G.U \ S)
  F := G.F.filter (fun e => ¬ ∀ a ∈ G.ends e, a ∈ S)
  sub := by
    intro e he a ha
    rw [Sym2.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    simp only [coll]
    split_ifs with h
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_sdiff.2 ⟨G.sub e (mem_filter.1 he).1 b hb, h⟩)
  loopless := by
    intro e he
    obtain ⟨-, hn⟩ := mem_filter.1 he
    have hl := G.loopless e (mem_filter.1 he).1
    revert hn hl
    induction G.ends e using Sym2.ind with
    | h a b =>
      intro hn hl
      rw [Sym2.mk_isDiag_iff] at hl
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
      simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, not_and_or] at hn
      unfold coll
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp only [ha, hb, if_true, if_false]
      · tauto
      · exact fun h => hb (h ▸ hs0)
      · exact fun h => ha (h ▸ hs0)
      · exact hl

section contract
variable (G : MG V E) {S : Finset V} {s0 : V} (hs0 : s0 ∈ S)

lemma mem_contract_ends {e : E} {a : V} (ha : a ∉ S) :
    a ∈ (G.contract S s0 hs0).ends e ↔ a ∈ G.ends e := by
  simp only [MG.contract, Sym2.mem_map, coll]
  constructor
  · rintro ⟨b, hb, h⟩
    split_ifs at h with h'
    · exact absurd (h ▸ hs0) ha
    · exact h ▸ hb
  · intro h
    exact ⟨a, h, by simp [ha]⟩

lemma s0_mem_contract_ends {e : E} :
    s0 ∈ (G.contract S s0 hs0).ends e ↔ ∃ b ∈ G.ends e, b ∈ S := by
  simp only [MG.contract, Sym2.mem_map, coll]
  constructor
  · rintro ⟨b, hb, h⟩
    split_ifs at h with h'
    · exact ⟨b, hb, h'⟩
    · exact ⟨b, hb, h ▸ hs0⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, by simp [h]⟩

lemma mem_contract_ends_iff {e : E} {T : Finset V} (he : e ∈ G.F) :
    (∃ a ∈ (G.contract S s0 hs0).ends e, a ∈ T) ↔
      ∃ b ∈ G.ends e, b ∈ G.U.filter (fun a => coll S s0 a ∈ T) := by
  simp only [MG.contract, Sym2.mem_map, mem_filter]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, h⟩
    exact ⟨b, hb, G.sub e he b hb, h⟩
  · rintro ⟨b, hb, -, h⟩
    exact ⟨_, ⟨b, hb, rfl⟩, h⟩

lemma not_mem_contract_ends_iff {e : E} {T : Finset V} (he : e ∈ G.F) :
    (∃ a ∈ (G.contract S s0 hs0).ends e, a ∉ T) ↔
      ∃ b ∈ G.ends e, b ∉ G.U.filter (fun a => coll S s0 a ∈ T) := by
  simp only [MG.contract, Sym2.mem_map, mem_filter, not_and]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, h⟩
    exact ⟨b, hb, fun _ => h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨_, ⟨b, hb, rfl⟩, h (G.sub e he b hb)⟩

lemma contract_at_s0 : (G.contract S s0 hs0).at_ s0 = G.cut S := by
  ext e
  simp only [MG.at_, MG.cut, mem_filter, s0_mem_contract_ends]
  simp only [MG.contract, mem_filter, not_forall, exists_prop]
  tauto

lemma contract_at {v : V} (hv : v ∉ S) : (G.contract S s0 hs0).at_ v = G.at_ v := by
  ext e
  simp only [MG.at_, mem_filter, mem_contract_ends G hs0 hv]
  simp only [MG.contract, mem_filter]
  constructor
  · tauto
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun h => hv (h v h2)⟩, h2⟩

lemma contract_cut (T : Finset V) :
    (G.contract S s0 hs0).cut T = G.cut (G.U.filter (fun a => coll S s0 a ∈ T)) := by
  ext e
  simp only [MG.cut]
  constructor
  · intro h
    obtain ⟨hF, h1, h2⟩ := mem_filter.1 h
    have heF : e ∈ G.F := (mem_filter.1 hF).1
    exact mem_filter.2 ⟨heF, (mem_contract_ends_iff G hs0 heF).1 h1,
      (not_mem_contract_ends_iff G hs0 heF).1 h2⟩
  · intro h
    obtain ⟨heF, h1, h2⟩ := mem_filter.1 h
    refine mem_filter.2 ⟨mem_filter.2 ⟨heF, ?_⟩, (mem_contract_ends_iff G hs0 heF).2 h1,
      (not_mem_contract_ends_iff G hs0 heF).2 h2⟩
    intro hin
    obtain ⟨b, hb, hbT⟩ := h1
    obtain ⟨c, hc, hcT⟩ := h2
    apply hcT
    simp only [mem_filter] at hbT ⊢
    refine ⟨G.sub e heF c hc, ?_⟩
    have := hbT.2
    simpa [coll, hin b hb, hin c hc] using this

include hs0 in
lemma card_preimage_odd {T : Finset V} (hT : T ⊆ insert s0 (G.U \ S)) (hTo : Odd T.card)
    (hSo : Odd S.card) (hSU : S ⊆ G.U) :
    Odd (G.U.filter (fun a => coll S s0 a ∈ T)).card := by
  have h1 : G.U.filter (fun a => coll S s0 a ∈ T) \ S = T.erase s0 := by
    ext a
    simp only [mem_sdiff, mem_filter, mem_erase]
    unfold coll
    constructor
    · rintro ⟨⟨-, h⟩, ha⟩
      rw [if_neg ha] at h
      exact ⟨fun h' => ha (h' ▸ hs0), h⟩
    · rintro ⟨hne, h⟩
      have := hT h
      rw [mem_insert, mem_sdiff] at this
      rcases this with h' | ⟨hU, hS⟩
      · exact absurd h' hne
      · exact ⟨⟨hU, by rwa [if_neg hS]⟩, hS⟩
  have h2 : G.U.filter (fun a => coll S s0 a ∈ T) ∩ S = if s0 ∈ T then S else ∅ := by
    ext a
    simp only [mem_inter, mem_filter]
    by_cases h : s0 ∈ T
    · rw [if_pos h]
      exact ⟨fun hh => hh.2, fun ha => ⟨⟨hSU ha, by simp [coll, ha, h]⟩, ha⟩⟩
    · rw [if_neg h]
      simp only [Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, h'⟩, ha⟩
      simp [coll, ha] at h'
      exact h h'
  have := Finset.card_inter_add_card_sdiff (G.U.filter (fun a => coll S s0 a ∈ T)) S
  rw [h1, h2] at this
  rw [← this]
  split_ifs with h
  · rw [card_erase_of_mem h]
    obtain ⟨k, hk⟩ := hTo
    obtain ⟨m, hm⟩ := hSo
    rw [hk, hm]
    exact ⟨m + k, by omega⟩
  · simpa [Finset.erase_eq_of_notMem h] using hTo

lemma inQ_contract {x : E → ℝ} (hx : InQ G x) (hSU : S ⊆ G.U) (hSo : Odd S.card)
    (ht : ∑ e ∈ G.cut S, x e = 1) : InQ (G.contract S s0 hs0) x := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨fun e he => h1 e (mem_filter.1 he).1, fun v hv => ?_, fun T hT hTo => ?_⟩
  · rcases mem_insert.1 hv with rfl | hv
    · rw [contract_at_s0]; exact ht
    · rw [contract_at G hs0 (mem_sdiff.1 hv).2]
      exact h2 v (mem_sdiff.1 hv).1
  · rw [contract_cut]
    exact h3 _ (filter_subset _ _) (card_preimage_odd G hs0 hT hTo hSo hSU)

end contract


/-! ### Gluing two contractions along a tight odd cut -/

lemma sum_ind_eq_card (C M : Finset E) : ∑ g ∈ C, ind M g = (M.filter (· ∈ C)).card := by
  simp only [ind, Finset.sum_boole, Nat.cast_inj]
  congr 1
  ext g; simp [and_comm]

lemma cut_eq_of_compl (G : MG V E) {A B : Finset V} (hAB : ∀ a ∈ G.U, a ∈ B ↔ a ∉ A) :
    G.cut B = G.cut A := by
  ext e
  simp only [MG.cut, mem_filter]
  constructor
  · rintro ⟨he, ⟨a, ha, haB⟩, ⟨b, hb, hbB⟩⟩
    refine ⟨he, ⟨b, hb, ?_⟩, ⟨a, ha, (hAB a (G.sub e he a ha)).1 haB⟩⟩
    by_contra h
    exact hbB ((hAB b (G.sub e he b hb)).2 h)
  · rintro ⟨he, ⟨a, ha, haA⟩, ⟨b, hb, hbA⟩⟩
    refine ⟨he, ⟨b, hb, (hAB b (G.sub e he b hb)).2 hbA⟩, ⟨a, ha, ?_⟩⟩
    rw [hAB a (G.sub e he a ha)]
    exact not_not.2 haA

section pm
variable (G : MG V E) {A : Finset V} {a0 : V} (ha0 : a0 ∈ A)

lemma pm_contract_sub {M : Finset E} (h : IsPM (G.contract A a0 ha0) M) : M ⊆ G.F :=
  fun _ he => (mem_filter.1 (h.1 he)).1

lemma pm_contract_not_ins {M : Finset E} (h : IsPM (G.contract A a0 ha0) M) {e : E}
    (he : e ∈ M) : ¬ ∀ a ∈ G.ends e, a ∈ A :=
  (mem_filter.1 (h.1 he)).2

lemma pm_contract_at {M : Finset E} (h : IsPM (G.contract A a0 ha0) M) {v : V}
    (hv : v ∈ G.U) (hvA : v ∉ A) : (M.filter (fun e => v ∈ G.ends e)).card = 1 := by
  have := h.2 v (mem_insert_of_mem (mem_sdiff.2 ⟨hv, hvA⟩))
  rwa [Finset.filter_congr (fun e _ => mem_contract_ends G ha0 hvA)] at this

lemma pm_contract_cross {M : Finset E} (h : IsPM (G.contract A a0 ha0) M) :
    (M.filter (· ∈ G.cut A)).card = 1 := by
  have := h.2 a0 (mem_insert_self _ _)
  rwa [Finset.filter_congr (q := (· ∈ G.cut A)) (fun e he => by
    rw [s0_mem_contract_ends]
    simp only [MG.cut, mem_filter]
    have := pm_contract_not_ins G ha0 h he
    push Not at this
    exact ⟨fun h' => ⟨pm_contract_sub G ha0 h he, h', this⟩, fun h' => h'.2.1⟩)] at this

lemma pm_contract_sum_cross {M : Finset E} (h : IsPM (G.contract A a0 ha0) M) :
    ∑ g ∈ G.cut A, ind M g = 1 := by
  rw [sum_ind_eq_card, pm_contract_cross G ha0 h, Nat.cast_one]

end pm

lemma union_filter_at (G : MG V E) {A B : Finset V} (hAB : ∀ a ∈ G.U, a ∈ B ↔ a ∉ A)
    {a0 b0 : V} (ha0 : a0 ∈ A) (hb0 : b0 ∈ B) {M1 M2 : Finset E}
    (_h1 : IsPM (G.contract A a0 ha0) M1) (h2 : IsPM (G.contract B b0 hb0) M2) {g : E}
    (hg1 : g ∈ M1) (hg2 : g ∈ M2) (hgc : g ∈ G.cut A) {v : V} (hvB : v ∈ B) :
    (M1 ∪ M2).filter (fun e => v ∈ G.ends e) = M1.filter (fun e => v ∈ G.ends e) := by
  ext e
  simp only [mem_filter, mem_union]
  refine ⟨?_, fun ⟨h, h'⟩ => ⟨Or.inl h, h'⟩⟩
  rintro ⟨h | h, hv⟩
  · exact ⟨h, hv⟩
  · have heF := pm_contract_sub G hb0 h2 h
    have hni := pm_contract_not_ins G hb0 h2 h
    push Not at hni
    have hec : e ∈ G.cut B := mem_filter.2 ⟨heF, ⟨v, hv, hvB⟩, hni⟩
    have hgc' : g ∈ G.cut B := by rwa [cut_eq_of_compl G hAB]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.1 (pm_contract_cross G hb0 h2)
    have h1' : e ∈ M2.filter (· ∈ G.cut B) := mem_filter.2 ⟨h, hec⟩
    have h2' : g ∈ M2.filter (· ∈ G.cut B) := mem_filter.2 ⟨hg2, hgc'⟩
    rw [hc, mem_singleton] at h1' h2'
    exact ⟨h1' ▸ h2' ▸ hg1, hv⟩

lemma sum_W {ι κ : Type*} [Fintype ι] [Fintype κ] (C : Finset E) (x : E → ℝ)
    (hx : ∀ g ∈ C, x g ≠ 0) (p : ι → E → ℝ) (q : κ → E → ℝ) (w : ι → ℝ)
    (hq : ∀ g ∈ C, ∑ j, q j g = x g) (hp : ∀ i, ∑ g ∈ C, p i g = w i) (φ : ι → ℝ) :
    ∑ i, ∑ j, (∑ g ∈ C, p i g * q j g / x g) * φ i = ∑ i, w i * φ i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ j, (∑ g ∈ C, p i g * q j g / x g) * φ i
      = (∑ g ∈ C, p i g * (∑ j, q j g) / x g) * φ i := by
        rw [← Finset.sum_mul, Finset.sum_comm]
        congr 1
        refine sum_congr rfl fun g _ => ?_
        rw [Finset.mul_sum, Finset.sum_div]
    _ = (∑ g ∈ C, p i g) * φ i := by
        congr 1
        refine sum_congr rfl fun g hg => ?_
        rw [hq g hg, mul_div_assoc, div_self (hx g hg), mul_one]
    _ = w i * φ i := by rw [hp i]

lemma glue {G : MG V E} {x : E → ℝ} (hpos : ∀ e ∈ G.F, 0 < x e)
    {A B : Finset V} (hAB : ∀ a ∈ G.U, a ∈ B ↔ a ∉ A)
    {a0 b0 : V} (ha0 : a0 ∈ A) (hb0 : b0 ∈ B)
    (h1 : ConvPM (G.contract A a0 ha0) x) (h2 : ConvPM (G.contract B b0 hb0) x) :
    ConvPM G x := by
  obtain ⟨ι, _, w1, M1, hw1, hs1, hpm1, hm1⟩ := h1
  obtain ⟨κ, _, w2, M2, hw2, hs2, hpm2, hm2⟩ := h2
  have hBA : ∀ a ∈ G.U, a ∈ A ↔ a ∉ B := fun a ha => by rw [hAB a ha]; tauto
  have hcut : G.cut B = G.cut A := cut_eq_of_compl G hAB
  have hCF : G.cut A ⊆ G.F := filter_subset _ _
  have hC1 : ∀ g ∈ G.cut A, g ∈ (G.contract A a0 ha0).F := fun g hg => by
    obtain ⟨hgF, -, b, hb, hbA⟩ := mem_filter.1 hg
    exact mem_filter.2 ⟨hgF, fun h => hbA (h b hb)⟩
  have hC2 : ∀ g ∈ G.cut A, g ∈ (G.contract B b0 hb0).F := fun g hg => by
    rw [← hcut] at hg
    obtain ⟨hgF, -, b, hb, hbA⟩ := mem_filter.1 hg
    exact mem_filter.2 ⟨hgF, fun h => hbA (h b hb)⟩
  have hp1 : ∀ i, ∑ g ∈ G.cut A, w1 i * ind (M1 i) g = w1 i := fun i => by
    rcases (hw1 i).lt_or_eq with h | h
    · rw [← Finset.mul_sum, pm_contract_sum_cross G ha0 (hpm1 i h), mul_one]
    · simp [← h]
  have hp2 : ∀ j, ∑ g ∈ G.cut A, w2 j * ind (M2 j) g = w2 j := fun j => by
    rcases (hw2 j).lt_or_eq with h | h
    · rw [← Finset.mul_sum, ← hcut, pm_contract_sum_cross G hb0 (hpm2 j h), mul_one]
    · simp [← h]
  have hxne : ∀ g ∈ G.cut A, x g ≠ 0 := fun g hg => (hpos g (hCF hg)).ne'
  let W : ι × κ → ℝ := fun ij =>
    ∑ g ∈ G.cut A, w1 ij.1 * ind (M1 ij.1) g * (w2 ij.2 * ind (M2 ij.2) g) / x g
  have hL : ∀ φ : ι → ℝ, ∑ ij, W ij * φ ij.1 = ∑ i, w1 i * φ i := fun φ => by
    rw [Fintype.sum_prod_type]
    exact sum_W (G.cut A) x hxne (fun i g => w1 i * ind (M1 i) g)
      (fun j g => w2 j * ind (M2 j) g) w1 (fun g hg => (hm2 g (hC2 g hg)).symm) hp1 φ
  have hR : ∀ ψ : κ → ℝ, ∑ ij, W ij * ψ ij.2 = ∑ j, w2 j * ψ j := fun ψ => by
    rw [Fintype.sum_prod_type_right]
    have := sum_W (G.cut A) x hxne (fun j g => w2 j * ind (M2 j) g)
      (fun i g => w1 i * ind (M1 i) g) w2 (fun g hg => (hm1 g (hC1 g hg)).symm) hp2 ψ
    rw [← this]
    refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
    simp only [W]
    congr 1
    refine sum_congr rfl fun g _ => ?_
    ring
  have hW : ∀ ij, W ij ≠ 0 → ∃ g ∈ G.cut A,
      0 < w1 ij.1 ∧ 0 < w2 ij.2 ∧ g ∈ M1 ij.1 ∧ g ∈ M2 ij.2 := fun ij h => by
    obtain ⟨g, hg, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    refine ⟨g, hg, ?_, ?_, ?_, ?_⟩
    · rcases (hw1 ij.1).lt_or_eq with h' | h'
      · exact h'
      · simp [← h'] at hne
    · rcases (hw2 ij.2).lt_or_eq with h' | h'
      · exact h'
      · simp [← h'] at hne
    · by_contra h'; simp [ind, h'] at hne
    · by_contra h'; simp [ind, h'] at hne
  have hWnn : ∀ ij, 0 ≤ W ij := fun ij => sum_nonneg fun g hg =>
    div_nonneg (mul_nonneg (mul_nonneg (hw1 _) (by unfold ind; split_ifs <;> norm_num))
      (mul_nonneg (hw2 _) (by unfold ind; split_ifs <;> norm_num))) (hpos g (hCF hg)).le
  refine ⟨ι × κ, inferInstance, W, fun ij => M1 ij.1 ∪ M2 ij.2, hWnn, ?_, ?_, ?_⟩
  · have := hL (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hs1]
  · intro ij hij
    obtain ⟨g, hg, hw1p, hw2p, hg1, hg2⟩ := hW ij hij.ne'
    have P1 := hpm1 _ hw1p
    have P2 := hpm2 _ hw2p
    refine ⟨union_subset (pm_contract_sub G ha0 P1) (pm_contract_sub G hb0 P2),
      fun v hv => ?_⟩
    show ((M1 ij.1 ∪ M2 ij.2).filter (fun e => v ∈ G.ends e)).card = 1
    by_cases hvB : v ∈ B
    · rw [union_filter_at G hAB ha0 hb0 P1 P2 hg1 hg2 hg hvB]
      exact pm_contract_at G ha0 P1 hv ((hAB v hv).1 hvB)
    · have hvA : v ∈ A := (hBA v hv).2 hvB
      rw [union_comm, union_filter_at G hBA hb0 ha0 P2 P1 hg2 hg1 (hcut ▸ hg) hvA]
      exact pm_contract_at G hb0 P2 hv hvB
  · intro e he
    by_cases hin : ∀ a ∈ G.ends e, a ∈ A
    · -- `e` lies inside `A`
      have heB : e ∈ (G.contract B b0 hb0).F := by
        refine mem_filter.2 ⟨he, fun h => ?_⟩
        obtain ⟨a, ha⟩ : ∃ a, a ∈ G.ends e := ⟨_, Sym2.out_fst_mem _⟩
        exact (hAB a (G.sub e he a ha)).1 (h a ha) (hin a ha)
      rw [hm2 e heB, ← hR (fun j => ind (M2 j) e)]
      refine sum_congr rfl fun ij _ => ?_
      by_cases h0 : W ij = 0
      · simp [h0]
      obtain ⟨g, hg, hw1p, hw2p, hg1, hg2⟩ := hW ij h0
      have : e ∉ M1 ij.1 := fun h => pm_contract_not_ins G ha0 (hpm1 _ hw1p) h hin
      simp [ind, this]
    · have heA : e ∈ (G.contract A a0 ha0).F := mem_filter.2 ⟨he, hin⟩
      rw [hm1 e heA, ← hL (fun i => ind (M1 i) e)]
      refine sum_congr rfl fun ij _ => ?_
      by_cases h0 : W ij = 0
      · simp [h0]
      obtain ⟨g, hg, hw1p, hw2p, hg1, hg2⟩ := hW ij h0
      have P2 := hpm2 _ hw2p
      have key : e ∈ M2 ij.2 → e ∈ M1 ij.1 := fun h => by
        have hni := pm_contract_not_ins G hb0 P2 h
        push Not at hin hni
        have hec : e ∈ G.cut A := by
          refine mem_filter.2 ⟨he, ?_, hin⟩
          by_contra hno
          push Not at hno
          obtain ⟨b, hb, hbB⟩ := hni
          exact hbB ((hAB b (G.sub e he b hb)).2 (hno b hb))
        obtain ⟨c, hc⟩ := Finset.card_eq_one.1 (pm_contract_cross G hb0 P2)
        have h1' : e ∈ (M2 ij.2).filter (· ∈ G.cut B) := mem_filter.2 ⟨h, hcut ▸ hec⟩
        have h2' : g ∈ (M2 ij.2).filter (· ∈ G.cut B) := mem_filter.2 ⟨hg2, hcut ▸ hg⟩
        rw [hc, mem_singleton] at h1' h2'
        exact h1' ▸ h2' ▸ hg1
      unfold ind
      by_cases h1 : e ∈ M1 ij.1
      · simp [h1]
      · have h2 : e ∉ M2 ij.2 := fun h => h1 (key h)
        simp [h1, h2]

/-! ### Splitting off a two-node component -/

def MG.delPair (G : MG V E) (u v : V) : MG V E where
  ends := G.ends
  U := (G.U.erase u).erase v
  F := G.F.filter (fun e => u ∉ G.ends e ∧ v ∉ G.ends e)
  sub e he a ha := by
    obtain ⟨he, hu, hv⟩ := mem_filter.1 he
    exact mem_erase.2 ⟨fun h => hv (h ▸ ha), mem_erase.2 ⟨fun h => hu (h ▸ ha), G.sub e he a ha⟩⟩
  loopless e he := G.loopless e (mem_filter.1 he).1

lemma delPair_F (G : MG V E) (u v : V) :
    (G.delPair u v).F = G.F.filter (fun e => u ∉ G.ends e ∧ v ∉ G.ends e) := rfl

section pair
variable {G : MG V E} {u v : V}
  (hc : ∀ e ∈ G.F, u ∈ G.ends e ∨ v ∈ G.ends e → G.ends e = s(u, v))
include hc

lemma not_mem_of_pair {e : E} (he : e ∈ G.F) {a : V} (ha : a ∈ G.ends e) (hau : a ≠ u)
    (hav : a ≠ v) : u ∉ G.ends e ∧ v ∉ G.ends e := by
  by_contra h
  rw [not_and_or, not_not, not_not] at h
  rw [hc e he h, Sym2.mem_iff] at ha
  tauto

lemma delPair_at {a : V} (hau : a ≠ u) (hav : a ≠ v) : (G.delPair u v).at_ a = G.at_ a := by
  ext e
  simp only [MG.at_, mem_filter]
  rw [delPair_F, mem_filter]
  exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ =>
    ⟨⟨h1, not_mem_of_pair hc h1 h3 hau hav⟩, h3⟩⟩

lemma delPair_cut {S : Finset V} (hS : S ⊆ (G.delPair u v).U) :
    (G.delPair u v).cut S = G.cut S := by
  ext e
  simp only [MG.cut, mem_filter]
  rw [delPair_F, mem_filter]
  refine ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨⟨h1, ?_⟩, h3⟩⟩
  obtain ⟨a, ha, haS⟩ := h3.1
  have := hS haS
  simp only [MG.delPair, mem_erase] at this
  exact not_mem_of_pair hc h1 ha this.2.1 this.1

lemma inQ_delPair {x : E → ℝ} (hx : InQ G x) : InQ (G.delPair u v) x := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨fun e he => h1 e (mem_filter.1 he).1, fun a ha => ?_, fun S hS hSo => ?_⟩
  · simp only [MG.delPair, mem_erase] at ha
    rw [delPair_at hc ha.2.1 ha.1]
    exact h2 a ha.2.2
  · rw [delPair_cut hc hS]
    exact h3 S (fun a ha => (mem_erase.1 (mem_erase.1 (hS ha)).2).2) hSo

lemma convPM_of_delPair {x : E → ℝ} (hx : InQ G x) (hu : u ∈ G.U) (hv : v ∈ G.U)
    (huv : u ≠ v) (h : ConvPM (G.delPair u v) x) : ConvPM G x := by
  obtain ⟨ι, _, w, M, hw, hs, hpm, hm⟩ := h
  have hdeg : ∑ g ∈ G.at_ u, x g = 1 := hx.2.1 u hu
  have hgF : ∀ g ∈ G.at_ u, g ∈ G.F := fun g hg => (mem_filter.1 hg).1
  have hge : ∀ g ∈ G.at_ u, G.ends g = s(u, v) := fun g hg =>
    hc g (hgF g hg) (Or.inl (mem_filter.1 hg).2)
  -- edges of a perfect matching of the smaller graph avoid `u` and `v`
  have hMuv : ∀ i, 0 < w i → ∀ e ∈ M i, u ∉ G.ends e ∧ v ∉ G.ends e := fun i hi e he =>
    (mem_filter.1 ((hpm i hi).1 he)).2
  refine ⟨ι × (G.at_ u), inferInstance, fun ig => w ig.1 * x ig.2,
    fun ig => insert (ig.2 : E) (M ig.1), fun ig => mul_nonneg (hw _) (hx.1 _ (hgF _ ig.2.2)),
    ?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_coe_sort (G.at_ u) x, hdeg]
    simpa using hs
  · rintro ⟨i, g, hg⟩ hpos
    have hi : 0 < w i := pos_of_mul_pos_left hpos (hx.1 _ (hgF _ hg))
    obtain ⟨hsub, hcard⟩ := hpm i hi
    refine ⟨insert_subset (hgF g hg) (hsub.trans (filter_subset _ _)), fun a ha => ?_⟩
    simp only
    by_cases hau : a = u
    · subst hau
      rw [Finset.filter_insert, if_pos (by rw [hge g hg]; exact Sym2.mem_mk_left _ _)]
      rw [Finset.filter_eq_empty_iff.2 fun e he => (hMuv i hi e he).1]
      rfl
    by_cases hav : a = v
    · subst hav
      rw [Finset.filter_insert, if_pos (by rw [hge g hg]; exact Sym2.mem_mk_right _ _)]
      rw [Finset.filter_eq_empty_iff.2 fun e he => (hMuv i hi e he).2]
      rfl
    · rw [Finset.filter_insert, if_neg (by rw [hge g hg, Sym2.mem_iff]; tauto)]
      exact hcard a (by simp only [MG.delPair, mem_erase]; exact ⟨hav, hau, ha⟩)
  · intro e he
    by_cases heuv : u ∈ G.ends e ∨ v ∈ G.ends e
    · have heu : e ∈ G.at_ u := by
        refine mem_filter.2 ⟨he, ?_⟩
        rw [hc e he heuv]; exact Sym2.mem_mk_left _ _
      rw [Fintype.sum_prod_type]
      have : ∀ i, ∑ g : G.at_ u, w i * x g * ind (insert (g : E) (M i)) e = w i * x e := by
        intro i
        rcases (hw i).lt_or_eq with hi | hi
        · have hne : e ∉ M i := fun h => by
            have := hMuv i hi e h
            tauto
          rw [Finset.sum_eq_single_of_mem (⟨e, heu⟩ : G.at_ u) (mem_univ _)]
          · simp [ind]
          · rintro ⟨g, hg⟩ _ hge'
            have : e ≠ g := fun h => hge' (Subtype.ext h.symm)
            simp [ind, this, hne]
        · simp [← hi]
      simp only [this, ← Finset.sum_mul, hs, one_mul]
    · push Not at heuv
      have heF : e ∈ (G.delPair u v).F := mem_filter.2 ⟨he, heuv.1, heuv.2⟩
      rw [hm e heF, Fintype.sum_prod_type]
      refine sum_congr rfl fun i _ => ?_
      have : ∀ g : G.at_ u, ind (insert (g : E) (M i)) e = ind (M i) e := by
        rintro ⟨g, hg⟩
        have : e ≠ g := fun h => heuv.1 (h ▸ (mem_filter.1 hg).2)
        simp [ind, this]
      simp only [this, mul_comm (w i) (x _), mul_assoc, ← Finset.sum_mul]
      rw [Finset.sum_coe_sort (G.at_ u) x, hdeg, one_mul]

end pair

/-! ### A node of degree two with distinct neighbours -/

section path
variable {G : MG V E} {x : E → ℝ} (hx : InQ G x) (hpos : ∀ e ∈ G.F, 0 < x e)
  {u v w : V} {e f : E} (hv : v ∈ G.U) (hat : G.at_ v = {e, f}) (hef : e ≠ f)
  (he : G.ends e = s(v, u)) (hf : G.ends f = s(v, w)) (huw : u ≠ w)
include hx hpos hv hat hef he hf huw

omit hx hpos hef in
lemma path_aux :
    e ∈ G.F ∧ f ∈ G.F ∧ u ≠ v ∧ w ≠ v ∧ u ∈ G.U ∧ w ∈ G.U ∧ ({u, v, w} : Finset V) ⊆ G.U ∧
      ({u, v, w} : Finset V).card = 3 := by
  have heF : e ∈ G.F := (mem_filter.1 (hat ▸ mem_insert_self e {f} : e ∈ G.at_ v)).1
  have hfF : f ∈ G.F := (mem_filter.1 (hat ▸ (by simp : f ∈ ({e, f} : Finset E)) :
    f ∈ G.at_ v)).1
  have huv : u ≠ v := by
    have := G.loopless e heF
    rw [he, Sym2.mk_isDiag_iff] at this
    exact Ne.symm this
  have hwv : w ≠ v := by
    have := G.loopless f hfF
    rw [hf, Sym2.mk_isDiag_iff] at this
    exact Ne.symm this
  have hu : u ∈ G.U := G.sub e heF u (by rw [he]; exact Sym2.mem_mk_right _ _)
  have hw : w ∈ G.U := G.sub f hfF w (by rw [hf]; exact Sym2.mem_mk_right _ _)
  refine ⟨heF, hfF, huv, hwv, hu, hw, ?_, ?_⟩
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  · rw [card_insert_of_notMem (by simp [huv, huw]), card_pair hwv.symm]

lemma path_tight :
    ∑ g ∈ G.cut {u, v, w}, x g = 1 ∧ G.ins {u, v, w} = {e, f} := by
  obtain ⟨heF, hfF, huv, hwv, hu, hw, hSU, hS3⟩ := path_aux hv hat he hf huw
  have hhs := handshake G {u, v, w} x
  have hdeg : ∑ a ∈ ({u, v, w} : Finset V), ∑ g ∈ G.at_ a, x g = 3 := by
    rw [Finset.sum_congr rfl fun a ha => hx.2.1 a (hSU ha)]
    simp [hS3]
  have hcut := hx.2.2 {u, v, w} hSU (by rw [hS3]; decide)
  have hef_ins : ({e, f} : Finset E) ⊆ G.ins {u, v, w} := by
    intro g hg
    simp only [mem_insert, mem_singleton] at hg
    rcases hg with rfl | rfl
    · refine mem_filter.2 ⟨heF, fun a ha => ?_⟩
      rw [he, Sym2.mem_iff] at ha
      rcases ha with rfl | rfl <;> simp
    · refine mem_filter.2 ⟨hfF, fun a ha => ?_⟩
      rw [hf, Sym2.mem_iff] at ha
      rcases ha with rfl | rfl <;> simp
  have hvdeg : x e + x f = 1 := by
    have := hx.2.1 v hv
    rwa [hat, sum_pair hef] at this
  have hins : ∑ g ∈ G.ins {u, v, w}, x g =
      x e + x f + ∑ g ∈ G.ins {u, v, w} \ {e, f}, x g := by
    rw [← sum_pair hef, add_comm, sum_sdiff hef_ins]
  have hrest : 0 ≤ ∑ g ∈ G.ins {u, v, w} \ {e, f}, x g :=
    sum_nonneg fun g hg => (hpos g (mem_filter.1 (mem_sdiff.1 hg).1).1).le
  have hzero : ∑ g ∈ G.ins {u, v, w} \ {e, f}, x g = 0 := by linarith
  refine ⟨by linarith, ?_⟩
  refine Subset.antisymm (fun g hg => ?_) hef_ins
  by_contra hgef
  have := (sum_eq_zero_iff_of_nonneg fun g hg =>
    (hpos g (mem_filter.1 (mem_sdiff.1 hg).1).1).le).1 hzero g (mem_sdiff.2 ⟨hg, hgef⟩)
  exact (hpos g (mem_filter.1 hg).1).ne' this

lemma path_convPM (hvS : v ∈ ({u, v, w} : Finset V))
    (h : ConvPM (G.contract {u, v, w} v hvS) x) : ConvPM G x := by
  obtain ⟨heF, hfF, huv, hwv, hu, hw, hSU, hS3⟩ := path_aux hv hat he hf huw
  obtain ⟨-, hins⟩ := path_tight hx hpos hv hat hef he hf huw
  obtain ⟨ι, _, ω, M1, hω, hs, hpm, hm⟩ := h
  set S : Finset V := {u, v, w} with hSdef
  have huS : u ∈ S := by simp [S]
  have hwS : w ∈ S := by simp [S]
  -- basic facts on the edges `e` and `f`
  have hve : v ∈ G.ends e := by rw [he]; exact Sym2.mem_mk_left _ _
  have hue : u ∈ G.ends e := by rw [he]; exact Sym2.mem_mk_right _ _
  have hwe : w ∉ G.ends e := by rw [he, Sym2.mem_iff]; tauto
  have hwf : w ∈ G.ends f := by rw [hf]; exact Sym2.mem_mk_right _ _
  have huf : u ∉ G.ends f := by rw [hf, Sym2.mem_iff]; tauto
  have heS : ∀ a ∈ G.ends e, a ∈ S := fun a ha => by
    rw [he, Sym2.mem_iff] at ha; rcases ha with rfl | rfl <;> simp [S]
  have hfS : ∀ a ∈ G.ends f, a ∈ S := fun a ha => by
    rw [hf, Sym2.mem_iff] at ha; rcases ha with rfl | rfl <;> simp [S]
  -- facts on perfect matchings of the contraction
  have hv0 : ∀ i, 0 < ω i → ∀ g ∈ M1 i, v ∉ G.ends g := fun i hi g hg hvg => by
    have hgF := pm_contract_sub G hvS (hpm i hi) hg
    have : g ∈ G.at_ v := mem_filter.2 ⟨hgF, hvg⟩
    rw [hat] at this
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl
    · exact pm_contract_not_ins G hvS (hpm i hi) hg heS
    · exact pm_contract_not_ins G hvS (hpm i hi) hg hfS
  have hcr : ∀ i, 0 < ω i → ∀ g ∈ M1 i, ∀ a ∈ S, a ∈ G.ends g → g ∈ G.cut S :=
    fun i hi g hg a haS ha => by
      have hni := pm_contract_not_ins G hvS (hpm i hi) hg
      push Not at hni
      exact mem_filter.2 ⟨pm_contract_sub G hvS (hpm i hi) hg, ⟨a, ha, haS⟩, hni⟩
  have huniq : ∀ i, 0 < ω i → ∀ g ∈ M1 i, ∀ g' ∈ M1 i, g ∈ G.cut S → g' ∈ G.cut S →
      g = g' := fun i hi g hg g' hg' hc hc' => by
    obtain ⟨c, hc1⟩ := Finset.card_eq_one.1 (pm_contract_cross G hvS (hpm i hi))
    have h1 : g ∈ (M1 i).filter (· ∈ G.cut S) := mem_filter.2 ⟨hg, hc⟩
    have h2 : g' ∈ (M1 i).filter (· ∈ G.cut S) := mem_filter.2 ⟨hg', hc'⟩
    rw [hc1, mem_singleton] at h1 h2
    rw [h1, h2]
  have hex : ∀ i, 0 < ω i → ∃ g ∈ M1 i, g ∈ G.cut S := fun i hi => by
    obtain ⟨c, hc1⟩ := Finset.card_eq_one.1 (pm_contract_cross G hvS (hpm i hi))
    have : c ∈ (M1 i).filter (· ∈ G.cut S) := by rw [hc1]; exact mem_singleton_self c
    exact ⟨c, (mem_filter.1 this).1, (mem_filter.1 this).2⟩
  have hnuw : ∀ g ∈ G.cut S, ¬ (u ∈ G.ends g ∧ w ∈ G.ends g) := fun g hg ⟨h1, h2⟩ => by
    obtain ⟨hgF, -, b, hb, hbS⟩ := mem_filter.1 hg
    have hl := G.loopless g hgF
    have : G.ends g = s(u, w) := by
      rw [Sym2.mem_and_mem_iff huw] at *
      exact (Sym2.mem_and_mem_iff huw).1 ⟨h1, h2⟩
    rw [this, Sym2.mem_iff] at hb
    rcases hb with rfl | rfl <;> exact hbS (by simp [S])
  have hcrS : ∀ g ∈ G.cut S, u ∈ G.ends g ∨ v ∈ G.ends g ∨ w ∈ G.ends g := fun g hg => by
    obtain ⟨-, ⟨a, ha, haS⟩, -⟩ := mem_filter.1 hg
    simp only [S, mem_insert, mem_singleton] at haS
    rcases haS with rfl | rfl | rfl <;> tauto
  -- the matchings of `G`
  let P : ι → Prop := fun i => ∃ g ∈ M1 i, w ∈ G.ends g
  let M : ι → Finset E := fun i => if P i then insert e (M1 i) else insert f (M1 i)
  have heM1 : ∀ i, 0 < ω i → e ∉ M1 i := fun i hi h =>
    pm_contract_not_ins G hvS (hpm i hi) h heS
  have hfM1 : ∀ i, 0 < ω i → f ∉ M1 i := fun i hi h =>
    pm_contract_not_ins G hvS (hpm i hi) h hfS
  -- `D` : crossing edges at `w`
  set D := (G.cut S).filter (fun g => w ∈ G.ends g) with hD
  have hDF : ∀ g ∈ D, g ∈ (G.contract S v hvS).F := fun g hg => by
    obtain ⟨hgc, -⟩ := mem_filter.1 hg
    obtain ⟨hgF, -, b, hb, hbS⟩ := mem_filter.1 hgc
    exact mem_filter.2 ⟨hgF, fun h => hbS (h b hb)⟩
  have hPind : ∀ i, 0 < ω i → (if P i then (1 : ℝ) else 0) = ∑ g ∈ D, ind (M1 i) g :=
    fun i hi => by
      rw [sum_ind_eq_card]
      split_ifs with hP
      · obtain ⟨g, hg, hwg⟩ := hP
        have hgD : g ∈ D := mem_filter.2 ⟨hcr i hi g hg w hwS hwg, hwg⟩
        have : (M1 i).filter (· ∈ D) = {g} := by
          ext g'
          simp only [mem_filter, mem_singleton]
          constructor
          · rintro ⟨hg', hg'D⟩
            exact huniq i hi g' hg' g hg (mem_filter.1 hg'D).1 (mem_filter.1 hgD).1
          · rintro rfl; exact ⟨hg, hgD⟩
        rw [this, card_singleton, Nat.cast_one]
      · have : (M1 i).filter (· ∈ D) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun g hg hgD => hP ⟨g, hg, (mem_filter.1 hgD).2⟩
        rw [this, card_empty, Nat.cast_zero]
  have hatw : G.at_ w = insert f D := by
    ext g
    simp only [MG.at_, mem_filter, mem_insert, hD]
    constructor
    · rintro ⟨hgF, hwg⟩
      by_cases hgi : ∀ a ∈ G.ends g, a ∈ S
      · have : g ∈ G.ins S := mem_filter.2 ⟨hgF, hgi⟩
        rw [hins] at this
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl
        · exact absurd hwg hwe
        · exact Or.inl rfl
      · push Not at hgi
        exact Or.inr ⟨mem_filter.2 ⟨hgF, ⟨w, hwg, hwS⟩, hgi⟩, hwg⟩
    · rintro (rfl | ⟨hgc, hwg⟩)
      · exact ⟨hfF, hwf⟩
      · exact ⟨(mem_filter.1 hgc).1, hwg⟩
  have hfD : f ∉ D := fun h => by
    obtain ⟨-, -, b, hb, hbS⟩ := mem_filter.1 (mem_filter.1 h).1
    exact hbS (hfS b hb)
  have hvdeg : x e + x f = 1 := by
    have := hx.2.1 v hv
    rwa [hat, sum_pair hef] at this
  have hDsum : ∑ g ∈ D, x g = x e := by
    have := hx.2.1 w hw
    rw [hatw, sum_insert hfD] at this
    linarith
  have hPsum : ∑ i, ω i * (if P i then (1 : ℝ) else 0) = x e := by
    rw [← hDsum]
    calc ∑ i, ω i * (if P i then (1 : ℝ) else 0) = ∑ i, ∑ g ∈ D, ω i * ind (M1 i) g := by
          refine sum_congr rfl fun i _ => ?_
          rcases (hω i).lt_or_eq with hi | hi
          · rw [hPind i hi, Finset.mul_sum]
          · simp [← hi]
      _ = ∑ g ∈ D, x g := by
          rw [Finset.sum_comm]
          exact sum_congr rfl fun g hg => (hm g (hDF g hg)).symm
  refine ⟨ι, inferInstance, ω, M, hω, hs, fun i hi => ?_, fun g hg => ?_⟩
  · -- perfect matching
    have P1 := hpm i hi
    have hsub := pm_contract_sub G hvS P1
    obtain ⟨g, hg, hgc⟩ := hex i hi
    refine ⟨?_, fun a ha => ?_⟩
    · simp only [M]; split_ifs
      · exact insert_subset heF hsub
      · exact insert_subset hfF hsub
    by_cases haS : a ∈ S
    · simp only [S, mem_insert, mem_singleton] at haS
      by_cases hP : P i
      · obtain ⟨g', hg', hwg'⟩ := hP
        have hg'c := hcr i hi g' hg' w hwS hwg'
        simp only [M, if_pos (show P i from ⟨g', hg', hwg'⟩)]
        rcases haS with rfl | rfl | rfl
        · -- node `u`
          rw [Finset.card_eq_one]
          refine ⟨e, ?_⟩
          ext h
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | hh, hah⟩
            · rfl
            · have := huniq i hi h hh g' hg' (hcr i hi h hh a huS hah) hg'c
              subst this
              exact absurd ⟨hah, hwg'⟩ (hnuw h hg'c)
          · rintro rfl; exact ⟨Or.inl rfl, hue⟩
        · -- node `v`
          rw [Finset.card_eq_one]
          refine ⟨e, ?_⟩
          ext h
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | hh, hah⟩
            · rfl
            · exact absurd hah (hv0 i hi h hh)
          · rintro rfl; exact ⟨Or.inl rfl, hve⟩
        · -- node `w`
          rw [Finset.card_eq_one]
          refine ⟨g', ?_⟩
          ext h
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | hh, hah⟩
            · exact absurd hah hwe
            · exact huniq i hi h hh g' hg' (hcr i hi h hh a hwS hah) hg'c
          · rintro rfl; exact ⟨Or.inr hg', hwg'⟩
      · simp only [M, if_neg hP]
        have hgu : u ∈ G.ends g := by
          rcases hcrS g hgc with h | h | h
          · exact h
          · exact absurd h (hv0 i hi g hg)
          · exact absurd ⟨g, hg, h⟩ hP
        rcases haS with rfl | rfl | rfl
        · rw [Finset.card_eq_one]
          refine ⟨g, ?_⟩
          ext h
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | hh, hah⟩
            · exact absurd hah huf
            · exact huniq i hi h hh g hg (hcr i hi h hh a huS hah) hgc
          · rintro rfl; exact ⟨Or.inr hg, hgu⟩
        · rw [Finset.card_eq_one]
          refine ⟨f, ?_⟩
          ext h
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | hh, hah⟩
            · rfl
            · exact absurd hah (hv0 i hi h hh)
          · rintro rfl; exact ⟨Or.inl rfl, by rw [hf]; exact Sym2.mem_mk_left _ _⟩
        · rw [Finset.card_eq_one]
          refine ⟨f, ?_⟩
          ext h
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | hh, hah⟩
            · rfl
            · exact absurd ⟨h, hh, hah⟩ hP
          · rintro rfl; exact ⟨Or.inl rfl, hwf⟩
    · have hea : a ∉ G.ends e := fun h => haS (heS a h)
      have hfa : a ∉ G.ends f := fun h => haS (hfS a h)
      have := pm_contract_at G hvS P1 ha haS
      simp only [M]
      split_ifs
      · rwa [filter_insert, if_neg hea]
      · rwa [filter_insert, if_neg hfa]
  · -- marginals
    by_cases hgi : ∀ a ∈ G.ends g, a ∈ S
    · have : g ∈ G.ins S := mem_filter.2 ⟨hg, hgi⟩
      rw [hins] at this
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h <;> rw [h]
      · rw [← hPsum]
        refine sum_congr rfl fun i _ => ?_
        rcases (hω i).lt_or_eq with hi | hi
        · congr 1
          by_cases hP : P i
          · simp only [M, hP, if_true, ind, mem_insert, true_or]
          · simp only [M, hP, if_false, ind]
            rw [if_neg]
            rw [mem_insert]
            rintro (h' | h')
            · exact hef h'
            · exact heM1 i hi h'
        · simp [← hi]
      · have : x f = ∑ i, ω i * (1 - if P i then (1 : ℝ) else 0) := by
          simp only [mul_sub, mul_one, sum_sub_distrib, hs, hPsum]
          linarith
        rw [this]
        refine sum_congr rfl fun i _ => ?_
        rcases (hω i).lt_or_eq with hi | hi
        · congr 1
          by_cases hP : P i
          · simp only [M, hP, if_true, ind, sub_self]
            rw [if_neg]
            rw [mem_insert]
            rintro (h' | h')
            · exact hef h'.symm
            · exact hfM1 i hi h'
          · simp [M, hP, ind]
        · simp [← hi]
    · have hgF' : g ∈ (G.contract S v hvS).F := mem_filter.2 ⟨hg, hgi⟩
      rw [hm g hgF']
      refine sum_congr rfl fun i _ => ?_
      have hge : g ≠ e := fun h => hgi (h ▸ heS)
      have hgf : g ≠ f := fun h => hgi (h ▸ hfS)
      congr 1
      by_cases hP : P i
      · simp only [M, hP, if_true, ind, mem_insert, hge, false_or]
      · simp only [M, hP, if_false, ind, mem_insert, hgf, false_or]

end path

/-! ### Small facts -/

lemma cut_singleton (G : MG V E) (a : V) : G.cut {a} = G.at_ a := by
  ext e
  simp only [MG.cut, MG.at_, mem_filter, mem_singleton]
  constructor
  · rintro ⟨he, ⟨b, hb, rfl⟩, -⟩
    exact ⟨he, hb⟩
  · rintro ⟨he, ha⟩
    refine ⟨he, ⟨a, ha, rfl⟩, ⟨Sym2.Mem.other ha, Sym2.other_mem ha, ?_⟩⟩
    exact Sym2.other_ne (G.loopless e he) ha

lemma cut_univ (G : MG V E) : G.cut G.U = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun e he ⟨_, b, hb, hbU⟩ => hbU (G.sub e he b hb)

lemma even_card_U {G : MG V E} {x : E → ℝ} (hx : InQ G x) : Even G.U.card := by
  by_contra h
  have := hx.2.2 G.U subset_rfl (Nat.not_even_iff_odd.1 h)
  rw [cut_univ, sum_empty] at this
  norm_num at this

lemma ins_univ (G : MG V E) : G.ins G.U = G.F :=
  Finset.filter_true_of_mem fun e he => G.sub e he

lemma card_contract_lt (G : MG V E) {S : Finset V} {s0 : V} (hs0 : s0 ∈ S) (hSU : S ⊆ G.U)
    (h2 : 2 ≤ S.card) :
    (G.contract S s0 hs0).U.card + (G.contract S s0 hs0).F.card < G.U.card + G.F.card := by
  have h1 : (G.contract S s0 hs0).U.card ≤ (G.U \ S).card + 1 := card_insert_le _ _
  have h3 : (G.contract S s0 hs0).F.card ≤ G.F.card := card_filter_le _ _
  have h4 := card_sdiff_add_card_inter G.U S
  have h5 : G.U ∩ S = S := inter_eq_right.2 hSU
  rw [h5] at h4
  omega

/-! ### A direction preserving all degrees -/

lemma exists_ker (G : MG V E) (h : G.U.card < G.F.card) :
    ∃ d : E → ℝ, (∃ e ∈ G.F, d e ≠ 0) ∧ ∀ v ∈ G.U, ∑ e ∈ G.at_ v, d e = 0 := by
  let ext : (G.F → ℝ) → E → ℝ := fun d e => if he : e ∈ G.F then d ⟨e, he⟩ else 0
  let L : (G.F → ℝ) →ₗ[ℝ] (G.U → ℝ) :=
    { toFun := fun d v => ∑ e ∈ G.at_ v, ext d e
      map_add' := by
        intro d d'
        ext v
        simp only [Pi.add_apply, ← sum_add_distrib]
        refine sum_congr rfl fun e _ => ?_
        simp only [ext]
        split_ifs <;> simp
      map_smul' := by
        intro r d
        ext v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        refine sum_congr rfl fun e _ => ?_
        simp only [ext]
        split_ifs <;> simp }
  have hk : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
  obtain ⟨d, hd, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨ext d, ?_, fun v hv => congrFun (LinearMap.mem_ker.1 hd) ⟨v, hv⟩⟩
  by_contra hc
  push Not at hc
  apply hne
  ext ⟨e, he⟩
  have := hc e he
  simp only [ext, dif_pos he] at this
  simpa using this

/-! ### Moving along a degree-preserving direction -/

lemma isClosed_inQ (G : MG V E) : IsClosed {y : E → ℝ | InQ G y} := by
  simp only [InQ, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_biInter fun e _ => (isClosed_le continuous_const
    (continuous_apply e : Continuous fun y : E → ℝ => y e))).inter
    ((isClosed_biInter fun v _ => isClosed_eq (continuous_finsetSum _ fun e _ =>
      (continuous_apply e : Continuous fun y : E → ℝ => y e)) continuous_const).inter
    (isClosed_iInter fun S => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_finsetSum _ fun e _ =>
        (continuous_apply e : Continuous fun y : E → ℝ => y e))))

lemma ev_lt {a b c : ℝ} (h : c < a) : ∀ᶠ ε in nhds (0 : ℝ), c < a + ε * b := by
  have : Filter.Tendsto (fun ε : ℝ => a + ε * b) (nhds 0) (nhds (a + 0 * b)) :=
    ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at this
  exact this.eventually (lt_mem_nhds h)

def Strict (G : MG V E) (y : E → ℝ) : Prop :=
  (∀ e ∈ G.F, 0 < y e) ∧
    ∀ S ⊆ G.U, Odd S.card → 2 ≤ S.card → 2 ≤ (G.U \ S).card → 1 < ∑ e ∈ G.cut S, y e

lemma perturb {G : MG V E} {y d : E → ℝ} (hy : InQ G y) (hs : Strict G y)
    (hd : ∀ v ∈ G.U, ∑ e ∈ G.at_ v, d e = 0) :
    ∃ ε > 0, InQ G (fun e => y e + ε * d e) := by
  obtain ⟨hpos, hstrict⟩ := hs
  set T := G.U.powerset.filter
    (fun S => Odd S.card ∧ 2 ≤ S.card ∧ 2 ≤ (G.U \ S).card)
  have hev : ∀ᶠ ε in nhds (0 : ℝ), (∀ e ∈ G.F, 0 < y e + ε * d e) ∧
      ∀ S ∈ T, 1 < ∑ e ∈ G.cut S, y e + ε * ∑ e ∈ G.cut S, d e := by
    refine Filter.Eventually.and ((Filter.eventually_all_finset _).2 fun e he => ev_lt (hpos e he))
      ((Filter.eventually_all_finset _).2 fun S hS => ?_)
    obtain ⟨hSU, ho, h2, h2'⟩ := mem_filter.1 hS
    exact ev_lt (hstrict S (mem_powerset.1 hSU) ho h2 h2')
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  obtain ⟨h1, h2⟩ := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
  have hsum : ∀ s : Finset E, ∑ e ∈ s, (y e + δ / 2 * d e) =
      ∑ e ∈ s, y e + δ / 2 * ∑ e ∈ s, d e := fun s => by
    rw [sum_add_distrib, mul_sum]
  refine ⟨fun e he => (h1 e he).le, fun v hv => ?_, fun S hS ho => ?_⟩
  · rw [hsum, hy.2.1 v hv, hd v hv, mul_zero, add_zero]
  · rw [hsum]
    by_cases hS2 : 2 ≤ S.card
    · by_cases hS2' : 2 ≤ (G.U \ S).card
      · exact (h2 S (mem_filter.2 ⟨mem_powerset.2 hS, ho, hS2, hS2'⟩)).le
      · -- the complement is a single node
        have hc := card_sdiff_add_card_inter G.U S
        rw [inter_eq_right.2 hS] at hc
        have hev := even_card_U hy
        have h1' : (G.U \ S).card = 1 := by
          obtain ⟨k, hk⟩ := ho
          obtain ⟨r, hr⟩ := hev
          omega
        obtain ⟨z, hz⟩ := card_eq_one.1 h1'
        have hzU : z ∈ G.U := (mem_sdiff.1 (hz ▸ mem_singleton_self z : z ∈ G.U \ S)).1
        have : G.cut S = G.cut {z} := by
          rw [← hz]
          exact (cut_eq_of_compl G (fun a ha => by simp [ha])).symm
        rw [this, cut_singleton, hy.2.1 z hzU, hd z hzU, mul_zero, add_zero]
    · have h1' : S.card = 1 := by
        obtain ⟨k, hk⟩ := ho
        omega
      obtain ⟨a, rfl⟩ := card_eq_one.1 h1'
      have haU : a ∈ G.U := hS (mem_singleton_self a)
      rw [cut_singleton, hy.2.1 a haU, hd a haU, mul_zero, add_zero]

lemma exists_far {G : MG V E} {x d : E → ℝ} (hx : InQ G x) (hs : Strict G x)
    (hdF : ∃ e ∈ G.F, d e ≠ 0) (hd : ∀ v ∈ G.U, ∑ e ∈ G.at_ v, d e = 0) :
    ∃ t > 0, InQ G (fun e => x e + t * d e) ∧ ¬ Strict G (fun e => x e + t * d e) := by
  -- some coordinate of `d` is negative
  obtain ⟨e1, he1, hneg⟩ : ∃ e ∈ G.F, d e < 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨e0, he0, hne⟩ := hdF
    obtain ⟨a, ha⟩ : ∃ a, a ∈ G.ends e0 := ⟨_, Sym2.out_fst_mem _⟩
    have haU := G.sub e0 he0 a ha
    have := (sum_eq_zero_iff_of_nonneg fun e he => hc e (mem_filter.1 he).1).1 (hd a haU) e0
      (mem_filter.2 ⟨he0, ha⟩)
    exact hne this
  set A : Set ℝ := {t | 0 ≤ t} ∩ (fun t => fun e => x e + t * d e) ⁻¹' {y | InQ G y}
  have hcl : IsClosed A := (isClosed_le continuous_const continuous_id).inter
    ((isClosed_inQ G).preimage (continuous_pi fun e =>
      continuous_const.add (continuous_id.mul continuous_const)))
  have h0 : (0 : ℝ) ∈ A := ⟨by simp, by
    show InQ G (fun e => x e + 0 * d e)
    simpa using hx⟩
  have hbdd : BddAbove A := ⟨x e1 / (-d e1), fun t ht => by
    have := ht.2.1 e1 he1
    rw [le_div_iff₀ (by linarith)]
    nlinarith⟩
  have hmem := hcl.csSup_mem ⟨0, h0⟩ hbdd
  obtain ⟨ε, hε, hεQ⟩ := perturb hx hs hd
  have hεA : ε ∈ A := ⟨hε.le, hεQ⟩
  have hpos : 0 < sSup A := lt_of_lt_of_le hε (le_csSup hbdd hεA)
  refine ⟨sSup A, hpos, hmem.2, fun hs' => ?_⟩
  obtain ⟨ε', hε', hQ'⟩ := perturb hmem.2 hs' hd
  have : sSup A + ε' ∈ A := ⟨by show 0 ≤ sSup A + ε'; linarith, by
    show InQ G (fun e => x e + (sSup A + ε') * d e)
    simpa only [add_mul, add_assoc] using hQ'⟩
  have := le_csSup hbdd this
  linarith

/-! ### The perfect matching polytope theorem -/

lemma card_sdiff_odd {G : MG V E} {x : E → ℝ} (hx : InQ G x) {S : Finset V} (hSU : S ⊆ G.U)
    (ho : Odd S.card) : Odd (G.U \ S).card := by
  have hc := card_sdiff_add_card_inter G.U S
  rw [inter_eq_right.2 hSU] at hc
  obtain ⟨k, hk⟩ := ho
  obtain ⟨r, hr⟩ := even_card_U hx
  exact ⟨r - k - 1, by omega⟩

theorem convPM_of_inQ : ∀ (n : ℕ) (G : MG V E), G.U.card + G.F.card = n →
    ∀ x, InQ G x → ConvPM G x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn x hx
  have IH : ∀ G' : MG V E, G'.U.card + G'.F.card < G.U.card + G.F.card →
      ∀ y, InQ G' y → ConvPM G' y := fun G' h => ih _ (hn ▸ h) G' rfl
  -- the reducible cases
  have easy : ∀ y, InQ G y → ¬ Strict G y → ConvPM G y := by
    intro y hy hns
    by_cases hp : ∀ e ∈ G.F, 0 < y e
    · obtain ⟨S, hS, ho, h2, h2', ht⟩ : ∃ S ⊆ G.U, Odd S.card ∧ 2 ≤ S.card ∧
          2 ≤ (G.U \ S).card ∧ ∑ e ∈ G.cut S, y e = 1 := by
        by_contra hc
        refine hns ⟨hp, fun S hS ho h2 h2' => lt_of_le_of_ne (hy.2.2 S hS ho) fun h => ?_⟩
        exact hc ⟨S, hS, ho, h2, h2', h.symm⟩
      obtain ⟨a0, ha0⟩ : S.Nonempty := card_pos.1 (by omega)
      obtain ⟨b0, hb0⟩ : (G.U \ S).Nonempty := card_pos.1 (by omega)
      have hAB : ∀ a ∈ G.U, a ∈ G.U \ S ↔ a ∉ S := fun a ha => by simp [ha]
      have ht' : ∑ e ∈ G.cut (G.U \ S), y e = 1 := by rwa [cut_eq_of_compl G hAB]
      exact glue hp hAB ha0 hb0
        (IH _ (card_contract_lt G ha0 hS h2) _ (inQ_contract G ha0 hy hS ho ht))
        (IH _ (card_contract_lt G hb0 sdiff_subset h2') _
          (inQ_contract G hb0 hy sdiff_subset (card_sdiff_odd hy hS ho) ht'))
    · push Not at hp
      obtain ⟨e, he, hle⟩ := hp
      have h0 : y e = 0 := le_antisymm hle (hy.1 e he)
      refine convPM_of_erase h0 (IH _ ?_ _ (inQ_erase hy h0))
      show G.U.card + (G.F.erase e).card < _
      rw [card_erase_of_mem he]
      have := card_pos.2 ⟨e, he⟩
      omega
  by_cases hs : Strict G x
  swap
  · exact easy x hx hs
  have hpos := hs.1
  -- a node of degree at most two
  by_cases hsmall : ∃ v ∈ G.U, (G.at_ v).card ≤ 2
  · obtain ⟨v, hv, hcard⟩ := hsmall
    have hdeg := hx.2.1 v hv
    have hatF : ∀ g ∈ G.at_ v, g ∈ G.F := fun g hg => (mem_filter.1 hg).1
    have hatv : ∀ g ∈ G.at_ v, v ∈ G.ends g := fun g hg => (mem_filter.1 hg).2
    -- the edges at a neighbour, when they carry total weight one already
    have hsat : ∀ (u : V), u ∈ G.U → ∀ s : Finset E, s ⊆ G.at_ u → ∑ g ∈ s, x g = 1 →
        G.at_ u = s := fun u hu s hsu hs1 => by
      have h1 := hx.2.1 u hu
      rw [← sum_sdiff hsu, hs1] at h1
      have h0 : ∑ g ∈ G.at_ u \ s, x g = 0 := by linarith
      refine (Subset.antisymm hsu fun g hg => ?_).symm
      by_contra hgs
      have := (sum_eq_zero_iff_of_nonneg fun g hg =>
        (hpos g (mem_filter.1 (mem_sdiff.1 hg).1).1).le).1 h0 g (mem_sdiff.2 ⟨hg, hgs⟩)
      exact (hpos g (mem_filter.1 hg).1).ne' this
    have hmeas : ∀ u, u ∈ G.U → u ≠ v →
        (G.delPair u v).U.card + (G.delPair u v).F.card < G.U.card + G.F.card := by
      intro u hu huv
      have h1 : (G.delPair u v).U.card = G.U.card - 2 := by
        show ((G.U.erase u).erase v).card = _
        rw [card_erase_of_mem (mem_erase.2 ⟨huv.symm, hv⟩), card_erase_of_mem hu]
        omega
      have h2 : (G.delPair u v).F.card ≤ G.F.card := card_filter_le _ _
      have h3 : 2 ≤ G.U.card := by
        have : ({u, v} : Finset V) ⊆ G.U := by
          intro a ha; simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl <;> assumption
        have := card_le_card this
        rwa [card_pair huv] at this
      omega
    interval_cases h : (G.at_ v).card
    · rw [card_eq_zero.1 h, sum_empty] at hdeg
      norm_num at hdeg
    · obtain ⟨e, he⟩ := card_eq_one.1 h
      have heF : e ∈ G.F := hatF e (he ▸ mem_singleton_self e)
      have hve : v ∈ G.ends e := hatv e (he ▸ mem_singleton_self e)
      set u := Sym2.Mem.other hve
      have hends : G.ends e = s(u, v) := by rw [Sym2.eq_swap]; exact (Sym2.other_spec hve).symm
      have huv : u ≠ v := Sym2.other_ne (G.loopless e heF) hve
      have hu : u ∈ G.U := G.sub e heF u (Sym2.other_mem hve)
      have hxe : x e = 1 := by rwa [he, sum_singleton] at hdeg
      have hatu : G.at_ u = {e} := hsat u hu {e}
        (singleton_subset_iff.2 (mem_filter.2 ⟨heF, Sym2.other_mem hve⟩)) (by simpa using hxe)
      have hc : ∀ g ∈ G.F, u ∈ G.ends g ∨ v ∈ G.ends g → G.ends g = s(u, v) := by
        rintro g hg (hg' | hg')
        · have : g ∈ G.at_ u := mem_filter.2 ⟨hg, hg'⟩
          rw [hatu, mem_singleton] at this
          rw [this, hends]
        · have : g ∈ G.at_ v := mem_filter.2 ⟨hg, hg'⟩
          rw [he, mem_singleton] at this
          rw [this, hends]
      exact convPM_of_delPair hc hx hu hv huv
        (IH _ (hmeas u hu huv) _ (inQ_delPair hc hx))
    · obtain ⟨e, f, hef, hat⟩ := card_eq_two.1 h
      have heF : e ∈ G.F := hatF e (hat ▸ mem_insert_self e {f})
      have hfF : f ∈ G.F := hatF f (hat ▸ by simp)
      have hve : v ∈ G.ends e := hatv e (hat ▸ mem_insert_self e {f})
      have hvf : v ∈ G.ends f := hatv f (hat ▸ by simp)
      set u := Sym2.Mem.other hve
      set w := Sym2.Mem.other hvf
      have he : G.ends e = s(v, u) := (Sym2.other_spec hve).symm
      have hf : G.ends f = s(v, w) := (Sym2.other_spec hvf).symm
      have huv : u ≠ v := Sym2.other_ne (G.loopless e heF) hve
      have hu : u ∈ G.U := G.sub e heF u (Sym2.other_mem hve)
      have hxef : x e + x f = 1 := by rwa [hat, sum_pair hef] at hdeg
      by_cases huw : u = w
      · -- two parallel edges: a two-node component
        have hatu : G.at_ u = {e, f} := hsat u hu {e, f} (by
          intro g hg
          simp only [mem_insert, mem_singleton] at hg
          rcases hg with rfl | rfl
          · exact mem_filter.2 ⟨heF, Sym2.other_mem hve⟩
          · exact mem_filter.2 ⟨hfF, huw ▸ Sym2.other_mem hvf⟩) (by rwa [sum_pair hef])
        have hc : ∀ g ∈ G.F, u ∈ G.ends g ∨ v ∈ G.ends g → G.ends g = s(u, v) := by
          rintro g hg (hg' | hg')
          · have : g ∈ G.at_ u := mem_filter.2 ⟨hg, hg'⟩
            rw [hatu] at this
            simp only [mem_insert, mem_singleton] at this
            rcases this with rfl | rfl
            · rw [he, Sym2.eq_swap]
            · rw [hf, ← huw, Sym2.eq_swap]
          · have : g ∈ G.at_ v := mem_filter.2 ⟨hg, hg'⟩
            rw [hat] at this
            simp only [mem_insert, mem_singleton] at this
            rcases this with rfl | rfl
            · rw [he, Sym2.eq_swap]
            · rw [hf, ← huw, Sym2.eq_swap]
        exact convPM_of_delPair hc hx hu hv huv
          (IH _ (hmeas u hu huv) _ (inQ_delPair hc hx))
      · -- a path `u - v - w`: contract `{u, v, w}`
        obtain ⟨-, -, -, -, -, -, hSU, hS3⟩ := path_aux hv hat he hf huw
        obtain ⟨ht, -⟩ := path_tight hx hpos hv hat hef he hf huw
        have hvS : v ∈ ({u, v, w} : Finset V) := by simp
        exact path_convPM hx hpos hv hat hef he hf huw hvS
          (IH _ (card_contract_lt G hvS hSU (by omega)) _
            (inQ_contract G hvS hx hSU (by rw [hS3]; decide) ht))
  -- all degrees are at least three
  push Not at hsmall
  by_cases hU : G.U = ∅
  · have hF : G.F = ∅ := by
      refine eq_empty_of_forall_notMem fun e he => ?_
      have := G.sub e he _ (Sym2.out_fst_mem _)
      rw [hU] at this
      exact notMem_empty _ this
    refine ⟨PUnit, inferInstance, fun _ => 1, fun _ => ∅, fun _ => zero_le_one, by simp,
      fun _ _ => ⟨empty_subset _, fun v hv => by rw [hU] at hv; exact absurd hv (notMem_empty v)⟩,
      fun e he => by rw [hF] at he; exact absurd he (notMem_empty e)⟩
  have hlt : G.U.card < G.F.card := by
    have hh := handshake G G.U (fun _ => 1)
    rw [ins_univ, cut_univ] at hh
    simp only [sum_const, nsmul_eq_mul, mul_one, card_empty, Nat.cast_zero, add_zero] at hh
    have h3 : ∑ a ∈ G.U, ((G.at_ a).card : ℝ) ≥ ∑ a ∈ G.U, (3 : ℝ) :=
      sum_le_sum fun a ha => by exact_mod_cast hsmall a ha
    rw [sum_const, nsmul_eq_mul] at h3
    have hpos' : (0 : ℝ) < G.U.card := by
      exact_mod_cast card_pos.2 (nonempty_iff_ne_empty.2 hU)
    have : (G.U.card : ℝ) < G.F.card := by linarith
    exact_mod_cast this
  obtain ⟨d, hdF, hd⟩ := exists_ker G hlt
  obtain ⟨t1, ht1, hQ1, hn1⟩ := exists_far hx hs hdF hd
  obtain ⟨t2, ht2, hQ2, hn2⟩ := exists_far (d := fun e => -d e) hx hs
    (by obtain ⟨e, he, hne⟩ := hdF; exact ⟨e, he, neg_ne_zero.2 hne⟩)
    (fun v hv => by rw [sum_neg_distrib, hd v hv, neg_zero])
  refine convPM_combo (easy _ hQ1 hn1) (easy _ hQ2 hn2) (a := t2 / (t1 + t2))
    (b := t1 / (t1 + t2)) (by positivity) (by positivity) (by field_simp; ring) fun e _ => ?_
  field_simp
  ring

end

/-! ### Back to Edmonds' polyhedron `C`: doubling the graph -/

section final

open EdmondsMatching65.Polyhedron

variable {V : Type u} {E : Type v} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- the graph `G` itself, all nodes and edges active -/
def G0 (G : EdmondsMatching65.Polyhedron.Graph V E) : MG V E where
  ends := G.ends
  U := univ
  F := univ
  sub _ _ _ _ := mem_univ _
  loopless e _ := G.loopless e

omit [DecidableEq E] in
lemma degSum_eq (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) (v : V) :
    degSum G x v = ∑ e ∈ (G0 G).at_ v, x e := by
  unfold degSum
  congr 1
  ext e
  rw [mem_at, mem_filter]
  simp [G0]

omit [DecidableEq E] in
lemma insideSum_eq (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) (S : Finset V) :
    insideSum G x S = ∑ e ∈ (G0 G).ins S, x e := by
  unfold insideSum
  congr 1
  ext e
  rw [mem_ins, mem_filter, Finset.mem_sym2_iff]
  simp [G0]

/-- two copies of `G`, with a spoke joining the copies of each node -/
def dbl (G : EdmondsMatching65.Polyhedron.Graph V E) : MG (V ⊕ V) (E ⊕ E ⊕ V) where
  ends a := match a with
    | Sum.inl e => (G.ends e).map Sum.inl
    | Sum.inr (Sum.inl e) => (G.ends e).map Sum.inr
    | Sum.inr (Sum.inr v) => s(Sum.inl v, Sum.inr v)
  U := univ
  F := univ
  sub _ _ _ _ := mem_univ _
  loopless := by
    rintro (e | e | v) -
    · exact (Sym2.isDiag_map Sum.inl_injective).not.2 (G.loopless e)
    · exact (Sym2.isDiag_map Sum.inr_injective).not.2 (G.loopless e)
    · simp

/-- the doubled vector -/
def xd (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) : E ⊕ E ⊕ V → ℝ
  | Sum.inl e => x e
  | Sum.inr (Sum.inl e) => x e
  | Sum.inr (Sum.inr v) => 1 - degSum G x v

lemma sum_dbl (s : Finset (E ⊕ E ⊕ V)) (y : E ⊕ E ⊕ V → ℝ) :
    ∑ a ∈ s, y a =
      ∑ e, (if Sum.inl e ∈ s then y (Sum.inl e) else 0) +
      (∑ e, (if Sum.inr (Sum.inl e) ∈ s then y (Sum.inr (Sum.inl e)) else 0) +
       ∑ w, (if Sum.inr (Sum.inr w) ∈ s then y (Sum.inr (Sum.inr w)) else 0)) := by
  have : ∑ a ∈ s, y a = ∑ a, if a ∈ s then y a else 0 := by
    rw [Finset.sum_ite_mem, univ_inter]
  rw [this, Fintype.sum_sum_type, Fintype.sum_sum_type]

lemma dbl_deg (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) (p : V ⊕ V) :
    ∑ a ∈ (dbl G).at_ p, xd G x a = 1 := by
  rw [sum_dbl]
  have hF : ∀ a, a ∈ (dbl G).F := fun a => mem_univ a
  have hdeg : ∀ v, ∑ e, (if v ∈ G.ends e then x e else 0) = degSum G x v := fun v => by
    rw [degSum, sum_filter]
  rcases p with v | v
  · have h1 : ∀ e, Sum.inl e ∈ (dbl G).at_ (Sum.inl v) ↔ v ∈ G.ends e := fun e => by
      rw [mem_at]; simp [dbl]
    have h2 : ∀ e, Sum.inr (Sum.inl e) ∉ (dbl G).at_ (Sum.inl v) := fun e => by
      rw [mem_at]; simp [dbl]
    have h3 : ∀ w, Sum.inr (Sum.inr w) ∈ (dbl G).at_ (Sum.inl v) ↔ w = v := fun w => by
      rw [mem_at]; simp [dbl, eq_comm]
    simp only [h1, h2, h3, if_false, sum_const_zero, zero_add, xd, sum_ite_eq', mem_univ,
      if_true, hdeg]
    ring
  · have h1 : ∀ e, Sum.inl e ∉ (dbl G).at_ (Sum.inr v) := fun e => by
      rw [mem_at]; simp [dbl]
    have h2 : ∀ e, Sum.inr (Sum.inl e) ∈ (dbl G).at_ (Sum.inr v) ↔ v ∈ G.ends e := fun e => by
      rw [mem_at]; simp [dbl]
    have h3 : ∀ w, Sum.inr (Sum.inr w) ∈ (dbl G).at_ (Sum.inr v) ↔ w = v := fun w => by
      rw [mem_at]; simp [dbl, eq_comm]
    simp only [h1, h2, h3, if_false, sum_const_zero, zero_add, xd, sum_ite_eq', mem_univ,
      if_true, hdeg]
    ring

omit [DecidableEq V] [DecidableEq E] in
lemma ins_singleton (G : EdmondsMatching65.Polyhedron.Graph V E) (a : V) :
    (G0 G).ins {a} = ∅ := by
  refine eq_empty_of_forall_notMem fun e he => ?_
  have h := (mem_ins.1 he).2
  have ha : a ∈ G.ends e := by
    obtain ⟨b, hb⟩ : ∃ b, b ∈ G.ends e := ⟨_, Sym2.out_fst_mem _⟩
    have := h b hb
    rw [mem_singleton] at this
    exact this ▸ hb
  exact Sym2.other_ne (G.loopless e) ha (mem_singleton.1 (h _ (Sym2.other_mem ha)))

lemma cut_lb (G : EdmondsMatching65.Polyhedron.Graph V E) {x : E → ℝ}
    (hx : x ∈ matchingPolyhedron G)
    (S : Finset (V ⊕ V)) (T : Finset V) (hT : Odd T.card)
    (h1 : ∀ e, e ∈ (G0 G).cut T →
      Sum.inl e ∈ (dbl G).cut S ∨ Sum.inr (Sum.inl e) ∈ (dbl G).cut S)
    (h2 : ∀ w ∈ T, Sum.inr (Sum.inr w) ∈ (dbl G).cut S) :
    1 ≤ ∑ a ∈ (dbl G).cut S, xd G x a := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  have hcutT : ∑ e ∈ (G0 G).cut T, x e = ∑ e, if e ∈ (G0 G).cut T then x e else 0 := by
    rw [Finset.sum_ite_mem, univ_inter]
  have hlow : ∑ e ∈ (G0 G).cut T, x e + ∑ w ∈ T, (1 - degSum G x w) ≤
      ∑ a ∈ (dbl G).cut S, xd G x a := by
    rw [sum_dbl, ← add_assoc]
    have hA : ∑ e ∈ (G0 G).cut T, x e ≤
        ∑ e, (if Sum.inl e ∈ (dbl G).cut S then xd G x (Sum.inl e) else 0) +
          ∑ e, (if Sum.inr (Sum.inl e) ∈ (dbl G).cut S then
            xd G x (Sum.inr (Sum.inl e)) else 0) := by
      rw [hcutT, ← sum_add_distrib]
      refine sum_le_sum fun e _ => ?_
      simp only [xd]
      have hn1 : 0 ≤ (if Sum.inl e ∈ (dbl G).cut S then x e else 0) := by
        split_ifs <;> simp [hx0 e]
      have hn2 : 0 ≤ (if Sum.inr (Sum.inl e) ∈ (dbl G).cut S then x e else 0) := by
        split_ifs <;> simp [hx0 e]
      by_cases he : e ∈ (G0 G).cut T
      · rw [if_pos he]
        rcases h1 e he with h | h
        · rw [if_pos h]; linarith
        · rw [if_pos h]; linarith
      · rw [if_neg he]
        exact add_nonneg hn1 hn2
    have hB : ∑ w ∈ T, (1 - degSum G x w) ≤
        ∑ w, (if Sum.inr (Sum.inr w) ∈ (dbl G).cut S then
          xd G x (Sum.inr (Sum.inr w)) else 0) := by
      simp only [xd]
      rw [← sum_filter]
      refine sum_le_sum_of_subset_of_nonneg (fun w hw => mem_filter.2 ⟨mem_univ _, h2 w hw⟩)
        fun w _ _ => by linarith [hx1 w]
    exact add_le_add hA hB
  -- the handshake identity in `G`
  have hh := handshake (G0 G) T x
  simp only [← degSum_eq] at hh
  have hins : ∑ e ∈ (G0 G).ins T, x e ≤ (T.card - 1 : ℝ) / 2 := by
    obtain ⟨r, hr⟩ := hT
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · obtain ⟨a, rfl⟩ := card_eq_one.1 (by omega : T.card = 1)
      rw [ins_singleton, sum_empty, card_singleton]
      norm_num
    · have := hx2 T r hr0 (by omega)
      rw [insideSum_eq] at this
      rw [hr]
      push_cast
      linarith
  have : ∑ w ∈ T, (1 - degSum G x w) = T.card - ∑ w ∈ T, degSum G x w := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
  linarith

lemma inQ_dbl (G : EdmondsMatching65.Polyhedron.Graph V E) {x : E → ℝ}
    (hx : x ∈ matchingPolyhedron G) : InQ (dbl G) (xd G x) := by
  refine ⟨?_, fun p _ => dbl_deg G x p, fun S _ hSo => ?_⟩
  · rintro (e | e | v) -
    · exact hx.1 e
    · exact hx.1 e
    · show 0 ≤ 1 - degSum G x v
      linarith [hx.2.1 v]
  -- split `S` into its two layers
  set A := univ.filter (fun v => Sum.inl v ∈ S)
  set B := univ.filter (fun v => Sum.inr v ∈ S)
  have hS : S.card = A.card + B.card := by
    have : S = A.disjSum B := by
      ext p
      rcases p with v | v <;> simp [A, B]
    rw [this, card_disjSum]
  have hA := card_sdiff_add_card_inter A B
  have hB := card_sdiff_add_card_inter B A
  rw [inter_comm] at hB
  have hodd : Odd (A \ B).card ∨ Odd (B \ A).card := by
    rcases Nat.even_or_odd (A \ B).card with h | h
    · right
      obtain ⟨k, hk⟩ := hSo
      obtain ⟨m, hm⟩ := h
      exact ⟨k - m - (A ∩ B).card, by omega⟩
    · exact Or.inl h
  have hcr : ∀ p q : V ⊕ V, ∀ a, p ∈ (dbl G).ends a → q ∈ (dbl G).ends a →
      p ∈ S → q ∉ S → a ∈ (dbl G).cut S := fun p q a hp hq hpS hqS =>
    mem_cut.2 ⟨mem_univ _, ⟨p, hp, hpS⟩, ⟨q, hq, hqS⟩⟩
  have hmem_l : ∀ e b, b ∈ G.ends e → Sum.inl b ∈ (dbl G).ends (Sum.inl e) := fun e b hb =>
    Sym2.mem_map.2 ⟨b, hb, rfl⟩
  have hmem_r : ∀ e b, b ∈ G.ends e → Sum.inr b ∈ (dbl G).ends (Sum.inr (Sum.inl e)) :=
    fun e b hb => Sym2.mem_map.2 ⟨b, hb, rfl⟩
  have hsp_l : ∀ w, Sum.inl w ∈ (dbl G).ends (Sum.inr (Sum.inr w)) := fun w =>
    Sym2.mem_mk_left _ _
  have hsp_r : ∀ w, Sum.inr w ∈ (dbl G).ends (Sum.inr (Sum.inr w)) := fun w =>
    Sym2.mem_mk_right _ _
  rcases hodd with h | h
  · refine cut_lb G hx S (A \ B) h (fun e he => ?_) (fun w hw => ?_)
    · obtain ⟨-, ⟨a, ha, haT⟩, ⟨b, hb, hbT⟩⟩ := mem_cut.1 he
      simp only [A, B, mem_sdiff, mem_filter, mem_univ, true_and] at haT hbT
      by_cases hbA : Sum.inl b ∈ S
      · right
        exact hcr _ _ _ (hmem_r e b hb) (hmem_r e a ha) (by tauto) haT.2
      · left
        exact hcr _ _ _ (hmem_l e a ha) (hmem_l e b hb) haT.1 hbA
    · simp only [A, B, mem_sdiff, mem_filter, mem_univ, true_and] at hw
      exact hcr _ _ _ (hsp_l w) (hsp_r w) hw.1 hw.2
  · refine cut_lb G hx S (B \ A) h (fun e he => ?_) (fun w hw => ?_)
    · obtain ⟨-, ⟨a, ha, haT⟩, ⟨b, hb, hbT⟩⟩ := mem_cut.1 he
      simp only [A, B, mem_sdiff, mem_filter, mem_univ, true_and] at haT hbT
      by_cases hbB : Sum.inr b ∈ S
      · left
        exact hcr _ _ _ (hmem_l e b hb) (hmem_l e a ha) (by tauto) haT.2
      · right
        exact hcr _ _ _ (hmem_r e a ha) (hmem_r e b hb) haT.1 hbB
    · simp only [A, B, mem_sdiff, mem_filter, mem_univ, true_and] at hw
      exact hcr _ _ _ (hsp_r w) (hsp_l w) hw.1 hw.2

omit [Fintype V] in
lemma incidence_mem (G : EdmondsMatching65.Polyhedron.Graph V E) {M : Finset E}
    (hM : IsMatching G M) : incidence M ∈ matchingVectors G := by
  refine ⟨fun e => by unfold incidence; split_ifs <;> simp, fun v => ?_⟩
  unfold degSum incidence
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_filter]
  have : (univ.filter (fun e => v ∈ G.ends e ∧ e ∈ M)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun e he f hf => ?_
    simp only [mem_filter, mem_univ, true_and] at he hf
    by_contra hne
    exact hM e he.2 f hf.2 hne v he.1 hf.1
  exact_mod_cast this

lemma mem_convexHull (G : EdmondsMatching65.Polyhedron.Graph V E) {x : E → ℝ}
    (hx : x ∈ matchingPolyhedron G) : x ∈ convexHull ℝ (matchingVectors G) := by
  obtain ⟨ι, _, ω, M', hω, hs, hpm, hm⟩ :=
    convPM_of_inQ _ (dbl G) rfl (xd G x) (inQ_dbl G hx)
  let M : ι → Finset E := fun i => univ.filter (fun e => Sum.inl e ∈ M' i)
  let t := univ.filter (fun i => 0 < ω i)
  have hsum : ∑ i ∈ t, ω i = 1 := by
    rw [← hs, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · exact (le_antisymm (not_lt.1 h) (hω i)).symm
  have hx' : x = ∑ i ∈ t, ω i • incidence (M i) := by
    ext e
    rw [Finset.sum_apply]
    have := hm (Sum.inl e) (mem_univ _)
    simp only [xd] at this
    rw [this, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    split_ifs with h
    · by_cases he : Sum.inl e ∈ M' i
      · rw [ind_pos he]; simp [M, incidence, he]
      · rw [ind_neg he]; simp [M, incidence, he]
    · simp [le_antisymm (not_lt.1 h) (hω i)]
  rw [hx']
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => hω i) hsum fun i hi => ?_
  refine subset_convexHull ℝ _ (incidence_mem G fun e he f hf hef v hve hvf => ?_)
  have hP := hpm i (mem_filter.1 hi).2
  simp only [M, mem_filter, mem_univ, true_and] at he hf
  exact hef (Sum.inl_injective (hP.eq (mem_univ (Sum.inl v)) he hf
    (Sym2.mem_map.2 ⟨v, hve, rfl⟩) (Sym2.mem_map.2 ⟨v, hvf, rfl⟩)))

omit [Fintype V] [DecidableEq E] in
lemma convex_C (G : EdmondsMatching65.Polyhedron.Graph V E) :
    Convex ℝ (matchingPolyhedron G) := by
  intro y hy z hz a b ha hb hab
  obtain ⟨hy0, hy1, hy2⟩ := hy
  obtain ⟨hz0, hz1, hz2⟩ := hz
  have hlin : ∀ s : Finset E, ∑ e ∈ s, (a • y + b • z) e =
      a * ∑ e ∈ s, y e + b * ∑ e ∈ s, z e := fun s => by
    simp [sum_add_distrib, mul_sum]
  refine ⟨fun e => ?_, fun v => ?_, fun S r hr hS => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hy0 e)) (mul_nonneg hb (hz0 e))
  · unfold degSum at *
    rw [hlin]
    nlinarith [hy1 v, hz1 v]
  · unfold insideSum at *
    rw [hlin]
    nlinarith [hy2 S r hr hS, hz2 S r hr hS]

end final

end EdmondsPM

open EdmondsMatching65.Polyhedron in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) :
    Set.extremePoints ℝ (matchingPolyhedron G) = matchingVectors G := by
  refine Set.Subset.antisymm (fun x hx => ?_) (matchingVectors_subset_extremePoints G)
  have hP : matchingVectors G ⊆ matchingPolyhedron G :=
    (matchingVectors_subset_extremePoints G).trans (extremePoints_subset)
  have hsub : convexHull ℝ (matchingVectors G) ⊆ matchingPolyhedron G :=
    convexHull_min hP (EdmondsPM.convex_C G)
  have hxC : x ∈ convexHull ℝ (matchingVectors G) := EdmondsPM.mem_convexHull G hx.1
  exact extremePoints_convexHull_subset
    (inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hxC, hx⟩)
