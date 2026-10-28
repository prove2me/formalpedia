-- Prove2me | solution 1 for Erdos624.actual_generation_gap
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:29:37.341527+00:00
-- url     : https://prove2.me/submissions/5c64e451-7237-4bc7-8a41-0258646e8384

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

namespace E624R13
open Finset Module

variable {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem hole_bound (L : Finset U → Finset C) (k d : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (p : U → W)
    (hvalid : ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p x = 0)
    (hglob : k ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p)) + d)
    (H : Finset U) (hH : #H ≤ k) (hhole : ∀ A ⊆ H, u ∉ L A) :
    #H < finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (H : Set U))) + d := by
  by_contra hc
  obtain ⟨F, hFH, -, huF, -, -⟩ := localize L k u hu hcov p hvalid H hH (by omega)
  exact hhole F hFH huF

omit [Fintype U] [DecidableEq U] [DecidableEq C] in
lemma indep_sum_ne {ι M : Type*} [DecidableEq ι] [AddCommGroup M] [Module (ZMod 2) M]
    (v : ι → M) (s : Set ι) (hv : LinearIndepOn (ZMod 2) v s) (F : Finset ι)
    (hF : (F : Set ι) ⊆ s) (hne : F.Nonempty) : ∑ x ∈ F, v x ≠ 0 := by
  intro hsum
  obtain ⟨y, hy⟩ := hne
  have hrest : ∑ x ∈ F.erase y, v x ∈ Submodule.span (ZMod 2) (v '' (s \ {y})) := by
    apply Submodule.sum_mem
    intro x hx
    rw [mem_erase] at hx
    exact Submodule.subset_span ⟨x, ⟨hF hx.2, by simpa using hx.1⟩, rfl⟩
  have hpy : v y = -(∑ x ∈ F.erase y, v x) := by
    rw [← add_sum_erase F v hy] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  exact hv.notMem_span (hF hy) (hpy ▸ Submodule.neg_mem _ hrest)

omit [Fintype U] in
lemma indicator_eq_sum (T : Finset U) (s : Finset T) :
    (fun y : T => if y ∈ s then (1 : ZMod 2) else 0) = ∑ x ∈ s, Pi.single x 1 := by
  ext y
  simp [Finset.sum_apply, Pi.single_apply]

theorem gen_gap (L : Finset U → Finset C) (k d : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (p : U → W)
    (hvalid : ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p x = 0)
    (hglob : k ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p)) + d)
    (T : Finset U) :
    Submodule.span (ZMod 2) {f : T → ZMod 2 | ∃ F : Finset U, F ⊆ T ∧ 0 < #F ∧ #F ≤ k ∧
        u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0} ≤
      LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun x : T => p x)) ∧
    finrank (ZMod 2) (LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun x : T => p x))) + 1 ≤
      finrank (ZMod 2) (Submodule.span (ZMod 2) {f : T → ZMod 2 | ∃ F : Finset U, F ⊆ T ∧
        0 < #F ∧ #F ≤ k ∧ u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧
        f = fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0}) + d := by
  classical
  set Z := Submodule.span (ZMod 2) {f : T → ZMod 2 | ∃ F : Finset U, F ⊆ T ∧ 0 < #F ∧ #F ≤ k ∧
        u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0} with hZ
  set f := Fintype.linearCombination (ZMod 2) (fun x : T => p x) with hf
  have hZK : Z ≤ LinearMap.ker f := by
    rw [hZ, Submodule.span_le]
    rintro g ⟨F, hFT, hF0, hFk, huF, hmin, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hf, Fintype.linearCombination_apply]
    have h1 : ∑ x : T, (if x.1 ∈ F then (1 : ZMod 2) else 0) • p x = ∑ x ∈ F, p x := by
      rw [Finset.sum_coe_sort T (fun x : U => (if x ∈ F then (1 : ZMod 2) else 0) • p x)]
      simp_rw [ite_smul, one_smul, zero_smul]
      rw [sum_ite_mem, inter_eq_right.2 hFT]
    rw [h1]; exact hvalid F hF0 hFk huF hmin
  refine ⟨hZK, ?_⟩
  -- quotient and coordinate cosets
  set v : T → (T → ZMod 2) ⧸ Z := fun x => Z.mkQ (Pi.single x 1) with hv
  have hspan : Submodule.span (ZMod 2) (Set.range v) = ⊤ := by
    have : Set.range v = Z.mkQ '' Set.range (fun x : T => (Pi.single x (1 : ZMod 2))) := by
      rw [← Set.range_comp]; rfl
    have h2 : Set.range (fun x : T => (Pi.single x (1 : ZMod 2))) =
        Set.range (Pi.basisFun (ZMod 2) T) := by
      ext; simp [Pi.basisFun_apply]
    rw [this, Submodule.span_image, h2, Module.Basis.span_eq, Submodule.map_top,
      Submodule.range_mkQ]
  obtain ⟨H, -, -, hHspan, hHind⟩ := exists_linearIndepOn_extension (K := ZMod 2) (v := v)
    (s := ∅) (t := Set.univ) (linearIndepOn_empty _ _) (Set.empty_subset _)
  have hHtop : Submodule.span (ZMod 2) (v '' H) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩; exact hHspan ⟨x, Set.mem_univ _, rfl⟩
  have hcardH := linearIndependent_iff_card_eq_finrank_span.1 hHind
  rw [Set.finrank, ← Set.image_eq_range, hHtop, finrank_top] at hcardH
  have hquot := Submodule.finrank_quotient_add_finrank Z
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hquot
  set H' : Finset U := H.toFinset.map (Function.Embedding.subtype _) with hH'
  have hH'card : #H' = Fintype.card H := by rw [hH', card_map, Set.toFinset_card]
  have hH'T : H' ⊆ T := by
    intro x hx; rw [hH', mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact y.2
  have noW : ∀ F : Finset U, F ⊆ H' → 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      False := by
    intro F hFH hF0 hFk huF hmin
    have hFT := hFH.trans hH'T
    have hmem : (fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0) ∈ Z :=
      Submodule.subset_span ⟨F, hFT, hF0, hFk, huF, hmin, rfl⟩
    set F' : Finset T := F.subtype (· ∈ T) with hF'
    have hind : (fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0) =
        (fun y : T => if y ∈ F' then (1 : ZMod 2) else 0) := by
      ext y; simp [hF']
    rw [hind, indicator_eq_sum] at hmem
    have hsum : ∑ x ∈ F', v x = 0 := by
      rw [hv]; simp only
      rw [← map_sum, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hmem
    refine indep_sum_ne v H hHind F' ?_ ?_ hsum
    · intro x hx
      rw [mem_coe, hF', mem_subtype] at hx
      have := hFH hx
      rw [hH', mem_map] at this
      obtain ⟨y, hy, hyx⟩ := this
      rw [Set.mem_toFinset] at hy
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    · obtain ⟨x, hx⟩ := card_pos.1 hF0
      exact ⟨⟨x, hFT hx⟩, by rw [hF', mem_subtype]; exact hx⟩
  have hHk : #H' < k := by
    by_contra hc
    obtain ⟨Y, hYH, hY⟩ := exists_subset_card_eq (show k ≤ #H' by omega)
    obtain ⟨A, hAY, huA⟩ := hcov Y hY
    obtain ⟨F, hFA, huF, hmin⟩ := exists_min_witness L u A huA
    have hF0 : 0 < #F := by
      rw [card_pos, nonempty_iff_ne_empty]; rintro rfl; exact hu huF
    exact noW F ((hFA.trans hAY).trans hYH) hF0 (hY ▸ card_le_card (hFA.trans hAY)) huF hmin
  have hhole : ∀ A ⊆ H', u ∉ L A := by
    intro A hAH huA
    obtain ⟨F, hFA, huF, hmin⟩ := exists_min_witness L u A huA
    have hF0 : 0 < #F := by
      rw [card_pos, nonempty_iff_ne_empty]; rintro rfl; exact hu huF
    have := card_le_card (hFA.trans hAH)
    exact noW F (hFA.trans hAH) hF0 (by omega) huF hmin
  have hb := hole_bound L k d u hu hcov p hvalid hglob H' hHk.le hhole
  haveI : Module.Finite (ZMod 2) (Submodule.span (ZMod 2) (p '' (T : Set U))) :=
    FiniteDimensional.span_of_finite _ ((T.finite_toSet).image _)
  have hrHT : finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (H' : Set U))) ≤
      finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (T : Set U))) :=
    Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (by exact_mod_cast hH'T)))
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have himg : Set.range (fun x : T => p x) = p '' (T : Set U) := by ext; simp
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hf, Fintype.range_linearCombination,
    himg] at hrn
  rw [← hf] at hrn
  omega

end E624R13

namespace Erdos624

theorem actual_generation_gap {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (k d : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (p : U → W)
    (hvalid : ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p x = 0)
    (hglob : k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p)) + d)
    (T : Finset U) :
    Submodule.span (ZMod 2) {f : T → ZMod 2 | ∃ F : Finset U, F ⊆ T ∧ 0 < #F ∧ #F ≤ k ∧
        u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0} ≤
      LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun x : T => p x)) ∧
    Module.finrank (ZMod 2) (LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun x : T => p x))) + 1 ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {f : T → ZMod 2 | ∃ F : Finset U, F ⊆ T ∧ 0 < #F ∧ #F ≤ k ∧
        u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0}) + d := by
  exact E624R13.gen_gap L k d u hu hcov p hvalid hglob T

end Erdos624

open Finset

theorem solution {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (k d : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (p : U → W)
    (hvalid : ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p x = 0)
    (hglob : k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p)) + d)
    (T : Finset U) :
    Submodule.span (ZMod 2) {f : T → ZMod 2 | ∃ F : Finset U, F ⊆ T ∧ 0 < #F ∧ #F ≤ k ∧
        u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0} ≤
      LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun x : T => p x)) ∧
    Module.finrank (ZMod 2) (LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun x : T => p x))) + 1 ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {f : T → ZMod 2 | ∃ F : Finset U, F ⊆ T ∧ 0 < #F ∧ #F ≤ k ∧
        u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0}) + d :=
  Erdos624.actual_generation_gap L k d u hu hcov p hvalid hglob T
