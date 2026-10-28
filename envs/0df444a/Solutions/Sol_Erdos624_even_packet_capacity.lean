-- Prove2me | solution 1 for Erdos624.even_packet_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:36:43.321236+00:00
-- url     : https://prove2.me/submissions/f3d5bd07-a5e6-4f10-a60c-aa160175f61e

import Mathlib
open Finset

namespace E624R13
open Finset Module

variable {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

omit [Fintype U] [DecidableEq U] [DecidableEq C] in
lemma exists_min_witness (L : Finset U → Finset C) (u : C) (A : Finset U) (hA : u ∈ L A) :
    ∃ H ⊆ A, u ∈ L H ∧ ∀ H' ⊂ H, u ∉ L H' := by
  classical
  have hne : (A.powerset.filter (fun B => u ∈ L B)).Nonempty :=
    ⟨A, mem_filter.2 ⟨mem_powerset_self _, hA⟩⟩
  obtain ⟨H, hH, hmin⟩ := exists_min_image _ card hne
  rw [mem_filter, mem_powerset] at hH
  refine ⟨H, hH.1, hH.2, fun H' hH' huH' => ?_⟩
  have := hmin H' (mem_filter.2 ⟨mem_powerset.2 (hH'.1.trans hH.1), huH'⟩)
  have := card_lt_card hH'
  omega

omit [Fintype U] [DecidableEq C] in
lemma finrank_span_finset_le (p : U → W) (B : Finset U) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (B : Set U))) ≤ #B := by
  classical
  have := finrank_span_finset_le_card (R := ZMod 2) (B.image p)
  rw [coe_image] at this
  exact this.trans card_image_le

/-- Exact-`k` extension / witness localization. -/
theorem localize (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (p : U → W)
    (hvalid : ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p x = 0)
    (T : Finset U) (hT : #T ≤ k)
    (hrank : finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (T : Set U))) + k ≤
      #T + finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p))) :
    ∃ F ⊆ T, 0 < #F ∧ u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ ∑ x ∈ F, p x = 0 := by
  classical
  obtain ⟨s, hsT, -, hTs, hsind⟩ := exists_linearIndepOn_extension (K := ZMod 2) (v := p)
    (s := ∅) (t := (T : Set U)) (linearIndepOn_empty _ _) (Set.empty_subset _)
  obtain ⟨b, -, hsb, hbspan, hbind⟩ := exists_linearIndepOn_extension (K := ZMod 2) (v := p)
    (s := s) (t := Set.univ) hsind (Set.subset_univ _)
  have hspanT : Submodule.span (ZMod 2) (p '' s) = Submodule.span (ZMod 2) (p '' (T : Set U)) := by
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hsT)
    · rw [Submodule.span_le]; exact hTs
  have hspanU : Submodule.span (ZMod 2) (p '' b) = Submodule.span (ZMod 2) (Set.range p) := by
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · rw [Submodule.span_le]; rintro _ ⟨x, rfl⟩; exact hbspan ⟨x, Set.mem_univ _, rfl⟩
  have hcs := linearIndependent_iff_card_eq_finrank_span.1 hsind
  have hcb := linearIndependent_iff_card_eq_finrank_span.1 hbind
  rw [Set.finrank, ← Set.image_eq_range, hspanT] at hcs
  rw [Set.finrank, ← Set.image_eq_range, hspanU] at hcb
  set rT := finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (T : Set U)))
  set rU := finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p))
  -- b ∩ T ⊆ s
  have hbT : ∀ x ∈ b, x ∈ (T : Set U) → x ∈ s := by
    intro x hxb hxT
    by_contra hxs
    have h1 : p x ∈ Submodule.span (ZMod 2) (p '' (b \ {x})) := by
      apply Submodule.span_mono (Set.image_mono (s := s) _)
      · rw [hspanT]; exact Submodule.subset_span ⟨x, hxT, rfl⟩
      · intro y hy; exact ⟨hsb hy, fun h => hxs (by rw [Set.mem_singleton_iff.1 h] at hy; exact hy)⟩
    exact hbind.notMem_span hxb h1
  set X := (b.toFinset) \ T with hX
  have hXcard : rU - rT ≤ #X := by
    have h1 : #(b.toFinset) = rU := by rw [Set.toFinset_card]; omega
    have h2 : #(b.toFinset ∩ T) ≤ rT := by
      rw [← hcs, ← Set.toFinset_card]
      apply card_le_card
      intro x hx
      rw [mem_inter, Set.mem_toFinset] at hx
      rw [Set.mem_toFinset]; exact hbT x hx.1 (by exact_mod_cast hx.2)
    have h3 := card_sdiff_add_card_inter (b.toFinset) T
    rw [hX]
    omega
  obtain ⟨X', hX'X, hX'card⟩ := exists_subset_card_eq (show k - #T ≤ #X by omega)
  have hdisj : Disjoint T X' := by
    rw [disjoint_left]; intro x hxT hxX'
    have := hX'X hxX'; rw [hX, mem_sdiff] at this; exact this.2 hxT
  obtain ⟨A, hAY, huA⟩ := hcov (T ∪ X') (by rw [card_union_of_disjoint hdisj]; omega)
  obtain ⟨F, hFA, huF, hmin⟩ := exists_min_witness L u A huA
  have hFk : #F ≤ k := by
    have := card_le_card (hFA.trans hAY); rw [card_union_of_disjoint hdisj] at this; omega
  have hFpos : 0 < #F := by
    rw [card_pos, nonempty_iff_ne_empty]; rintro rfl; exact hu huF
  have hsum := hvalid F hFpos hFk huF hmin
  refine ⟨F, ?_, hFpos, huF, hmin, hsum⟩
  intro y hyF
  by_contra hyT
  have hyX' : y ∈ X' := by
    have := hFA.trans hAY hyF
    rcases mem_union.1 this with h | h
    · exact absurd h hyT
    · exact h
  have hyb : y ∈ b := by
    have := hX'X hyX'; rw [hX, mem_sdiff, Set.mem_toFinset] at this; exact this.1
  -- p y ∈ span (p '' (b \ {y}))
  have hrest : ∑ x ∈ F.erase y, p x ∈ Submodule.span (ZMod 2) (p '' (b \ {y})) := by
    apply Submodule.sum_mem
    intro x hx
    rw [mem_erase] at hx
    by_cases hxT : x ∈ T
    · apply Submodule.span_mono (Set.image_mono (s := s) _)
      · rw [hspanT]; exact Submodule.subset_span ⟨x, hxT, rfl⟩
      · intro z hz
        refine ⟨hsb hz, fun h => ?_⟩
        rw [Set.mem_singleton_iff.1 h] at hz
        exact hyT (by exact_mod_cast hsT hz)
    · apply Submodule.subset_span
      refine ⟨x, ⟨?_, by simpa using hx.1⟩, rfl⟩
      have := hFA.trans hAY hx.2
      rcases mem_union.1 this with h | h
      · exact absurd h hxT
      · have := hX'X h; rw [hX, mem_sdiff, Set.mem_toFinset] at this; exact this.1
  have hpy : p y = -(∑ x ∈ F.erase y, p x) := by
    rw [← add_sum_erase F p hyF] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  exact hbind.notMem_span hyb (hpy ▸ Submodule.neg_mem _ hrest)

omit [Fintype U] [DecidableEq U] in
/-- colours witnessed by a nonempty subset of a fixed set have bounded count. -/
lemma card_le_of_witness_in (L : Finset U → Finset C) (b : ℕ) (hb : ∀ A, #(L A) ≤ b)
    (S : Finset C) (A : Finset U) (h : ∀ u ∈ S, ∃ F ⊆ A, 0 < #F ∧ u ∈ L F) :
    #S ≤ b * (2 ^ #A - 1) := by
  classical
  have hsub : S ⊆ (A.powerset.erase ∅).biUnion L := by
    intro u hu
    obtain ⟨F, hFA, hF, huF⟩ := h u hu
    rw [mem_biUnion]
    refine ⟨F, mem_erase.2 ⟨?_, mem_powerset.2 hFA⟩, huF⟩
    rintro rfl; simp at hF
  calc #S ≤ #((A.powerset.erase ∅).biUnion L) := card_le_card hsub
    _ ≤ ∑ B ∈ A.powerset.erase ∅, #(L B) := card_biUnion_le
    _ ≤ ∑ _B ∈ A.powerset.erase ∅, b := sum_le_sum fun B _ => hb B
    _ = b * (2 ^ #A - 1) := by
      rw [sum_const, smul_eq_mul, card_erase_of_mem (empty_mem_powerset A), card_powerset,
        mul_comm]

theorem common_pool (L : Finset U → Finset C) (b k d R : ℕ) (hb : ∀ A, #(L A) ≤ b)
    (S : Finset C) (p : C → U → W) (hu : ∀ u ∈ S, u ∉ L ∅)
    (hcov : ∀ u ∈ S, ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (hvalid : ∀ u ∈ S, ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p u x = 0)
    (hglob : ∀ u ∈ S, k ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (p u))) + d)
    (P : Finset U)
    (hpool : ∀ u ∈ S, finrank (ZMod 2) (Submodule.span (ZMod 2) (p u '' (P : Set U))) ≤ R)
    (hRk : R + d ≤ k) (hRP : R + d ≤ #P) :
    #S ≤ b * (2 ^ (R + d) - 1) := by
  obtain ⟨A, hAP, hA⟩ := exists_subset_card_eq hRP
  rw [← hA]
  apply card_le_of_witness_in L b hb S A
  intro u huS
  haveI : Module.Finite (ZMod 2) (Submodule.span (ZMod 2) (p u '' (P : Set U))) :=
    FiniteDimensional.span_of_finite _ ((P.finite_toSet).image _)
  have hrA : finrank (ZMod 2) (Submodule.span (ZMod 2) (p u '' (A : Set U))) ≤ R :=
    (Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (by exact_mod_cast hAP)))).trans
      (hpool u huS)
  obtain ⟨F, hFA, hF, huF, -, -⟩ := localize L k u (hu u huS) (hcov u huS) (p u) (hvalid u huS) A
    (by omega) (by have := hglob u huS; omega)
  exact ⟨F, hFA, hF, huF⟩

end E624R13

namespace E624R13R
open Finset

variable {ι : Type*} [DecidableEq ι]

lemma fin3_key : ∀ a b c c0 : Fin 3, a ≠ c0 → a ≠ c → b ≠ c0 → b ≠ c → c ≠ c0 → a = b := by
  decide

/-- `R(3,3) ≤ 6` inside a set whose edges avoid colour `c0`. -/
lemma two_colour (g : ι → ι → Fin 3) (hg : ∀ x y, g x y = g y x) (c0 : Fin 3) (S : Finset ι)
    (hS : 6 ≤ #S) (havoid : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → g x y ≠ c0) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ g x y = g x z ∧ g x y = g y z := by
  obtain ⟨v, hv⟩ : S.Nonempty := card_pos.1 (by omega)
  set S' := S.erase v
  have hS' : 5 ≤ #S' := by rw [card_erase_of_mem hv]; omega
  have hmaps : ∀ x ∈ S', g v x ∈ (univ.erase c0 : Finset (Fin 3)) := by
    intro x hx; rw [mem_erase] at hx ⊢
    exact ⟨havoid v hv x hx.2 (Ne.symm hx.1), mem_univ _⟩
  obtain ⟨c, hc, hcard⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
    (n := 2) (by rw [card_erase_of_mem (mem_univ _)]; simp; omega)
  set N := S'.filter (fun x => g v x = c)
  have hNS : N ⊆ S := (filter_subset _ _).trans (erase_subset _ _)
  have hvN : v ∉ N := fun h => by simp [N, S'] at h
  by_cases hin : ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ g x y = c
  · obtain ⟨x, hx, y, hy, hxy, hc'⟩ := hin
    have hgx : g v x = c := (mem_filter.1 hx).2
    have hgy : g v y = c := (mem_filter.1 hy).2
    refine ⟨v, hv, x, hNS hx, y, hNS hy, fun h => hvN (h ▸ hx), fun h => hvN (h ▸ hy), hxy,
      by rw [hgx, hgy], by rw [hgx, hc']⟩
  · push Not at hin
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.1 hcard
    have hc0 : c ≠ c0 := (mem_erase.1 hc).1
    have key : ∀ a b : Fin 3, a ≠ c0 → a ≠ c → b ≠ c0 → b ≠ c → a = b :=
      fun a b h1 h2 h3 h4 => fin3_key a b c c0 h1 h2 h3 h4 hc0
    refine ⟨x, hNS hx, y, hNS hy, z, hNS hz, hxy, hxz, hyz, ?_, ?_⟩
    · exact key _ _ (havoid x (hNS hx) y (hNS hy) hxy) (hin x hx y hy hxy)
        (havoid x (hNS hx) z (hNS hz) hxz) (hin x hx z hz hxz)
    · exact key _ _ (havoid x (hNS hx) y (hNS hy) hxy) (hin x hx y hy hxy)
        (havoid y (hNS hy) z (hNS hz) hyz) (hin y hy z hz hyz)

lemma three_colour (g : ι → ι → Fin 3) (hg : ∀ x y, g x y = g y x) (S : Finset ι)
    (hS : 17 ≤ #S) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ g x y = g x z ∧ g x y = g y z := by
  obtain ⟨v, hv⟩ : S.Nonempty := card_pos.1 (by omega)
  set S' := S.erase v
  have hS' : 16 ≤ #S' := by rw [card_erase_of_mem hv]; omega
  have hmaps : ∀ x ∈ S', g v x ∈ (univ : Finset (Fin 3)) := fun _ _ => mem_univ _
  obtain ⟨c, -, hcard⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
    (n := 5) (by simp; omega)
  set N := S'.filter (fun x => g v x = c)
  have hNS : N ⊆ S := (filter_subset _ _).trans (erase_subset _ _)
  have hvN : v ∉ N := fun h => by simp [N, S'] at h
  by_cases hin : ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ g x y = c
  · obtain ⟨x, hx, y, hy, hxy, hc'⟩ := hin
    have hgx : g v x = c := (mem_filter.1 hx).2
    have hgy : g v y = c := (mem_filter.1 hy).2
    refine ⟨v, hv, x, hNS hx, y, hNS hy, fun h => hvN (h ▸ hx), fun h => hvN (h ▸ hy), hxy,
      by rw [hgx, hgy], by rw [hgx, hc']⟩
  · push Not at hin
    obtain ⟨x, hx, y, hy, z, hz, h1, h2, h3, h4, h5⟩ :=
      two_colour g hg c N (by omega) (fun x hx y hy hxy => hin x hx y hy hxy)
    exact ⟨x, hNS hx, y, hNS hy, z, hNS hz, h1, h2, h3, h4, h5⟩

end E624R13R

namespace E624R13
open Finset Module

variable {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

omit [Fintype U] in
lemma mem_span_of_sum_zero (p : U → W) (G S : Finset U) (y : U) (hG : ∑ x ∈ G, p x = 0)
    (hy : y ∈ G) (hsub : G.erase y ⊆ S) : p y ∈ Submodule.span (ZMod 2) (p '' (S : Set U)) := by
  have hpy : p y = -(∑ x ∈ G.erase y, p x) := by
    rw [← add_sum_erase G p hy] at hG
    exact eq_neg_of_add_eq_zero_left hG
  rw [hpy]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro x hx
  exact Submodule.subset_span ⟨x, by exact_mod_cast hsub hx, rfl⟩

omit [Fintype U] in
lemma rank_add_le (p : U → W) (S R : Finset U) (hRS : R ⊆ S)
    (h : ∀ x ∈ R, p x ∈ Submodule.span (ZMod 2) (p '' ((S \ R : Finset U) : Set U))) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (S : Set U))) + #R ≤ #S := by
  classical
  have hle : Submodule.span (ZMod 2) (p '' (S : Set U)) ≤
      Submodule.span (ZMod 2) (p '' ((S \ R : Finset U) : Set U)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxR : x ∈ R
    · exact h x hxR
    · exact Submodule.subset_span ⟨x, by rw [coe_sdiff]; exact ⟨hx, hxR⟩, rfl⟩
  haveI : Module.Finite (ZMod 2) (Submodule.span (ZMod 2) (p '' ((S \ R : Finset U) : Set U))) :=
    FiniteDimensional.span_of_finite _ (((S \ R).finite_toSet).image _)
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_finset_le p (S \ R)
  have h3 := card_sdiff_add_card_eq_card hRS
  omega

theorem skew_union (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (p : U → W)
    (hvalid : ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p x = 0)
    (hglob : k ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p)) + 2)
    (A B : Finset U) (hAB : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hA0 : ∑ x ∈ A, p x = 0) (hB0 : ∑ x ∈ B, p x = 0)
    (hzs : ∀ G ⊆ A ∪ B, ∑ x ∈ G, p x = 0 → G = ∅ ∨ G = A ∨ G = B ∨ G = A ∪ B)
    (huA : u ∉ L A) (huB : u ∉ L B) (hk : #(A ∪ B) ≤ k) :
    u ∈ L (A ∪ B) ∧ ∀ F' ⊂ A ∪ B, u ∉ L F' := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hab : a ≠ b := fun h => disjoint_left.1 hAB ha (h ▸ hb)
  have hR : ({a, b} : Finset U) ⊆ A ∪ B := by
    intro x hx; rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_union_left _ ha
    · exact mem_union_right _ hb
  have hrank := rank_add_le p (A ∪ B) {a, b} hR (by
    intro x hx; rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · apply mem_span_of_sum_zero p A _ x hA0 ha
      intro y hy; rw [mem_erase] at hy
      rw [mem_sdiff, mem_insert, mem_singleton]
      exact ⟨mem_union_left _ hy.2, by
        rintro (h | h)
        · exact hy.1 h
        · exact disjoint_left.1 hAB hy.2 (h ▸ hb)⟩
    · apply mem_span_of_sum_zero p B _ x hB0 hb
      intro y hy; rw [mem_erase] at hy
      rw [mem_sdiff, mem_insert, mem_singleton]
      exact ⟨mem_union_right _ hy.2, by
        rintro (h | h)
        · exact disjoint_left.1 hAB (h ▸ ha) hy.2
        · exact hy.1 h⟩)
  rw [card_pair hab] at hrank
  obtain ⟨F, hFT, hF0, huF, hmin, hsum⟩ :=
    localize L k u hu hcov p hvalid (A ∪ B) hk (by omega)
  rcases hzs F hFT hsum with rfl | rfl | rfl | rfl
  · simp at hF0
  · exact absurd huF huA
  · exact absurd huF huB
  · exact ⟨huF, hmin⟩

theorem seventeen (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (k : ℕ)
    (c : Fin 3 → C) (hc : Function.Injective c) (hu : ∀ i, c i ∉ L ∅)
    (hcov : ∀ i, ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, c i ∈ L A)
    (p : Fin 3 → U → W)
    (hvalid : ∀ i, ∀ F : Finset U, 0 < #F → #F ≤ k → c i ∈ L F → (∀ F' ⊂ F, c i ∉ L F') →
      ∑ x ∈ F, p i x = 0)
    (hglob : ∀ i, k ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (p i))) + 2)
    (P : Fin 17 → Finset U) (hdisj : ∀ j l, j ≠ l → Disjoint (P j) (P l))
    (hne : ∀ j, (P j).Nonempty)
    (hsize : ∀ j l m, j ≠ l → j ≠ m → l ≠ m → #(P j ∪ P l ∪ P m) ≤ k)
    (hpair : ∀ i j l, j ≠ l → ∑ x ∈ P j ∪ P l, p i x = 0)
    (hker : ∀ i j l m, j ≠ l → j ≠ m → l ≠ m → ∀ G ⊆ P j ∪ P l ∪ P m,
      ∑ x ∈ G, p i x = 0 → G = ∅ ∨ G = P j ∪ P l ∨ G = P j ∪ P m ∨ G = P l ∪ P m) :
    False := by
  classical
  have hmiss : ∀ A : Finset U, ∃ i, c i ∉ L A := by
    intro A
    by_contra hcon
    push Not at hcon
    have hsub : univ.image c ⊆ L A := by
      intro x hx; obtain ⟨i, -, rfl⟩ := mem_image.1 hx; exact hcon i
    have := card_le_card hsub
    rw [card_image_of_injective _ hc, card_univ, Fintype.card_fin] at this
    have := hb A; omega
  choose h hh using hmiss
  set g : Fin 17 → Fin 17 → Fin 3 := fun j l => h (P j ∪ P l) with hg
  have hgs : ∀ x y, g x y = g y x := fun x y => by simp only [hg, union_comm]
  obtain ⟨x, -, y, -, z, -, hxy, hxz, hyz, h1, h2⟩ :=
    E624R13R.three_colour g hgs univ (by simp)
  set i := g x y with hi
  have nxy : c i ∉ L (P x ∪ P y) := hh _
  have nxz : c i ∉ L (P x ∪ P z) := by rw [h1]; exact hh _
  have nyz : c i ∉ L (P y ∪ P z) := by rw [h2]; exact hh _
  obtain ⟨a, ha⟩ := hne x
  obtain ⟨b, hb'⟩ := hne y
  have hab : a ≠ b := fun e => disjoint_left.1 (hdisj x y hxy) ha (e ▸ hb')
  set T := P x ∪ P y ∪ P z with hT
  have hR : ({a, b} : Finset U) ⊆ T := by
    intro w hw; rw [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [hT, ha]
    · simp [hT, hb']
  have hrank := rank_add_le (p i) T {a, b} hR (by
    intro w hw; rw [mem_insert, mem_singleton] at hw
    rcases hw with e | e <;> rw [e]
    · apply mem_span_of_sum_zero (p i) (P x ∪ P z) _ a (hpair i x z hxz) (mem_union_left _ ha)
      intro t ht; rw [mem_erase] at ht
      rw [mem_sdiff, mem_insert, mem_singleton]
      refine ⟨by rw [hT]; rcases mem_union.1 ht.2 with h' | h' <;> simp [h'], ?_⟩
      rintro (e' | e')
      · exact ht.1 e'
      · rw [e'] at ht
        rcases mem_union.1 ht.2 with h' | h'
        · exact disjoint_left.1 (hdisj x y hxy) h' hb'
        · exact disjoint_left.1 (hdisj y z hyz) hb' h'
    · apply mem_span_of_sum_zero (p i) (P y ∪ P z) _ b (hpair i y z hyz) (mem_union_left _ hb')
      intro t ht; rw [mem_erase] at ht
      rw [mem_sdiff, mem_insert, mem_singleton]
      refine ⟨by rw [hT]; rcases mem_union.1 ht.2 with h' | h' <;> simp [h'], ?_⟩
      rintro (e' | e')
      · rw [e'] at ht
        rcases mem_union.1 ht.2 with h' | h'
        · exact disjoint_left.1 (hdisj x y hxy) ha h'
        · exact disjoint_left.1 (hdisj x z hxz) ha h'
      · exact ht.1 e')
  rw [card_pair hab] at hrank
  have hTk := hsize x y z hxy hxz hyz
  obtain ⟨F, hFT, hF0, huF, -, hsum⟩ :=
    localize L k (c i) (hu i) (hcov i) (p i) (hvalid i) T hTk
      (by have := hglob i; omega)
  rcases hker i x y z hxy hxz hyz F hFT hsum with rfl | rfl | rfl | rfl
  · simp at hF0
  · exact nxy huF
  · exact nxz huF
  · exact nyz huF

end E624R13

namespace E624R13
open Finset Module

variable {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

lemma even_count (d : ℕ) :
    #((univ : Finset (Finset (Fin (d + 1)))).filter (fun I => Even #I ∧ I.Nonempty)) ≤
      2 ^ d - 1 := by
  classical
  set E := (univ : Finset (Finset (Fin (d + 1)))).filter (fun I => Even #I ∧ I.Nonempty)
  have hpar : ∀ I : Finset (Fin (d + 1)), Even #I → (0 ∈ I ↔ ¬ Even #(I.erase 0)) := by
    intro I hI
    constructor
    · intro h0 hE
      have := card_erase_add_one h0
      rw [← this] at hI
      exact (Nat.even_add_one.1 hI) hE
    · intro hE
      by_contra h0
      exact hE (by rw [erase_eq_of_notMem h0]; exact hI)
  have hmaps : ∀ I ∈ E, I.erase 0 ∈ ((univ : Finset (Fin (d + 1))).erase 0).powerset.erase ∅ := by
    intro I hI
    rw [mem_filter] at hI
    rw [mem_erase, mem_powerset]
    refine ⟨?_, erase_subset_erase _ (subset_univ _)⟩
    intro h
    have h2 : 2 ≤ #I := by
      obtain ⟨m, hm⟩ := hI.2.1
      have := card_pos.2 hI.2.2
      omega
    have := pred_card_le_card_erase (s := I) (a := 0)
    rw [h, card_empty] at this; omega
  have hinj : Set.InjOn (fun I : Finset (Fin (d + 1)) => I.erase 0) E := by
    intro I1 h1 I2 h2 heq
    simp only at heq
    have e1 := (mem_filter.1 h1).2.1
    have e2 := (mem_filter.1 h2).2.1
    have h0 : 0 ∈ I1 ↔ 0 ∈ I2 := by rw [hpar I1 e1, hpar I2 e2, heq]
    ext x
    by_cases hx : x = 0
    · subst hx; exact h0
    · have := congrArg (x ∈ ·) heq
      simpa [mem_erase, hx] using this
  have := card_le_card_of_injOn _ hmaps hinj
  rw [card_erase_of_mem (empty_mem_powerset _), card_powerset,
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
  simpa using this

theorem even_packets (L : Finset U → Finset C) (b k d : ℕ) (hb : ∀ A, #(L A) ≤ b)
    (S : Finset C) (p : C → U → W) (hu : ∀ u ∈ S, u ∉ L ∅)
    (hcov : ∀ u ∈ S, ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (hvalid : ∀ u ∈ S, ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p u x = 0)
    (hglob : ∀ u ∈ S,
      k ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (p u))) + d)
    (P : Fin (d + 1) → Finset U) (hdisj : ∀ j l, j ≠ l → Disjoint (P j) (P l))
    (hne : ∀ j, (P j).Nonempty) (hk : #(univ.biUnion P) ≤ k)
    (hpair : ∀ u ∈ S, ∀ j, j ≠ 0 → ∑ x ∈ P 0 ∪ P j, p u x = 0)
    (hzs : ∀ u ∈ S, ∀ G ⊆ univ.biUnion P, ∑ x ∈ G, p u x = 0 →
      ∃ I : Finset (Fin (d + 1)), Even #I ∧ G = I.biUnion P) :
    #S ≤ b * (2 ^ d - 1) := by
  classical
  set T := univ.biUnion P with hT
  set E := (univ : Finset (Finset (Fin (d + 1)))).filter (fun I => Even #I ∧ I.Nonempty)
  choose a ha using hne
  have hainj : ∀ j l, a j = a l → j = l := by
    intro j l h
    by_contra hjl
    exact disjoint_left.1 (hdisj j l hjl) (ha j) (h ▸ ha l)
  set R := (univ.erase (0 : Fin (d + 1))).image a with hR
  have hRcard : #R = d := by
    rw [hR, card_image_of_injective _ (fun j l h => hainj j l h), card_erase_of_mem (mem_univ _),
      card_univ, Fintype.card_fin]; rfl
  have hRT : R ⊆ T := by
    intro x hx; rw [hR, mem_image] at hx; obtain ⟨j, -, rfl⟩ := hx
    rw [hT, mem_biUnion]; exact ⟨j, mem_univ _, ha j⟩
  have hsub : S ⊆ E.biUnion (fun I => L (I.biUnion P)) := by
    intro u huS
    have hrank := rank_add_le (p u) T R hRT (by
      intro x hx
      rw [hR, mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      have hj0 : j ≠ 0 := (mem_erase.1 hj).1
      apply mem_span_of_sum_zero (p u) (P 0 ∪ P j) _ (a j) (hpair u huS j hj0)
        (mem_union_right _ (ha j))
      intro t ht
      rw [mem_erase] at ht
      rw [mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [hT, mem_biUnion]
        rcases mem_union.1 ht.2 with h | h
        · exact ⟨0, mem_univ _, h⟩
        · exact ⟨j, mem_univ _, h⟩
      · intro htR
        rw [hR, mem_image] at htR
        obtain ⟨l, hl, rfl⟩ := htR
        have hl0 : l ≠ 0 := (mem_erase.1 hl).1
        rcases mem_union.1 ht.2 with h | h
        · exact disjoint_left.1 (hdisj l 0 hl0) (ha l) h
        · by_cases hlj : l = j
          · exact ht.1 (hlj ▸ rfl)
          · exact disjoint_left.1 (hdisj l j hlj) (ha l) h)
    rw [hRcard] at hrank
    obtain ⟨F, hFT, hF0, huF, -, hsum⟩ := localize L k u (hu u huS) (hcov u huS) (p u)
      (hvalid u huS) T hk (by have := hglob u huS; omega)
    obtain ⟨I, hIe, rfl⟩ := hzs u huS F hFT hsum
    rw [mem_biUnion]
    refine ⟨I, mem_filter.2 ⟨mem_univ _, hIe, ?_⟩, huF⟩
    rw [nonempty_iff_ne_empty]; rintro rfl; simp at hF0
  calc #S ≤ #(E.biUnion (fun I => L (I.biUnion P))) := card_le_card hsub
    _ ≤ ∑ I ∈ E, #(L (I.biUnion P)) := card_biUnion_le
    _ ≤ ∑ _I ∈ E, b := sum_le_sum fun I _ => hb _
    _ = #E * b := by rw [sum_const, smul_eq_mul]
    _ ≤ (2 ^ d - 1) * b := Nat.mul_le_mul_right _ (even_count d)
    _ = b * (2 ^ d - 1) := mul_comm _ _

end E624R13

namespace Erdos624

theorem even_packet_capacity {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (b k d : ℕ) (hb : ∀ A, #(L A) ≤ b)
    (S : Finset C) (p : C → U → W) (hu : ∀ u ∈ S, u ∉ L ∅)
    (hcov : ∀ u ∈ S, ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (hvalid : ∀ u ∈ S, ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p u x = 0)
    (hglob : ∀ u ∈ S,
      k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (p u))) + d)
    (P : Fin (d + 1) → Finset U) (hdisj : ∀ j l, j ≠ l → Disjoint (P j) (P l))
    (hne : ∀ j, (P j).Nonempty) (hk : #(Finset.univ.biUnion P) ≤ k)
    (hpair : ∀ u ∈ S, ∀ j, j ≠ 0 → ∑ x ∈ P 0 ∪ P j, p u x = 0)
    (hzs : ∀ u ∈ S, ∀ G ⊆ Finset.univ.biUnion P, ∑ x ∈ G, p u x = 0 →
      ∃ I : Finset (Fin (d + 1)), Even #I ∧ G = I.biUnion P) :
    #S ≤ b * (2 ^ d - 1) := by
  exact E624R13.even_packets L b k d hb S p hu hcov hvalid hglob P hdisj hne hk hpair hzs

end Erdos624

open Finset

theorem solution {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (b k d : ℕ) (hb : ∀ A, #(L A) ≤ b)
    (S : Finset C) (p : C → U → W) (hu : ∀ u ∈ S, u ∉ L ∅)
    (hcov : ∀ u ∈ S, ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (hvalid : ∀ u ∈ S, ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p u x = 0)
    (hglob : ∀ u ∈ S,
      k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (p u))) + d)
    (P : Fin (d + 1) → Finset U) (hdisj : ∀ j l, j ≠ l → Disjoint (P j) (P l))
    (hne : ∀ j, (P j).Nonempty) (hk : #(Finset.univ.biUnion P) ≤ k)
    (hpair : ∀ u ∈ S, ∀ j, j ≠ 0 → ∑ x ∈ P 0 ∪ P j, p u x = 0)
    (hzs : ∀ u ∈ S, ∀ G ⊆ Finset.univ.biUnion P, ∑ x ∈ G, p u x = 0 →
      ∃ I : Finset (Fin (d + 1)), Even #I ∧ G = I.biUnion P) :
    #S ≤ b * (2 ^ d - 1) :=
  Erdos624.even_packet_capacity L b k d hb S p hu hcov hvalid hglob P hdisj hne hk hpair hzs
