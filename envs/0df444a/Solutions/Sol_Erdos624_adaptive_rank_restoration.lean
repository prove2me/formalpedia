-- Prove2me | solution 1 for Erdos624.adaptive_rank_restoration
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T02:12:05.444196+00:00
-- url     : https://prove2.me/submissions/e04fd986-1731-44e8-91fb-1b2317c7bca9

import Mathlib
open Finset
namespace E624R18
open Finset Module

/-- Indicator second coordinate used to restore lost pool rank. -/
def restoredLabel {U : Type*} [DecidableEq U] {W : Type*}
    (p : U → W) (S : Finset U) : U → W × (U → ZMod 2) :=
  fun x => (p x, fun y => if y = x ∧ x ∈ S then (1 : ZMod 2) else 0)

lemma eq_of_add_eq_zero_char_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {a b : M} (h : a + b = 0) : a = b := by
  have haa : a + a = 0 := by
    have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    rw [← two_smul (ZMod 2) a, h2, zero_smul]
  exact (add_left_cancel (h.trans haa.symm)).symm

lemma k_pos_of_covering {U : Type*}
    (P : Finset U) (G : Finset (Finset U)) (k : ℕ)
    (hGne : ∀ A ∈ G, A.Nonempty)
    (hcov : ∀ Y : Finset U, Y ⊆ P → #Y = k → ∃ A ∈ G, A ⊆ Y) :
    0 < k := by
  by_contra hk
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
  obtain ⟨A, hAG, hA⟩ := hcov (∅ : Finset U) (empty_subset P) (by simp [hk0])
  exact Finset.not_nonempty_empty ((subset_empty.1 hA) ▸ hGne A hAG)

/-- A linear combination witnessing membership in the span of an image. -/
lemma exists_lincomb_of_mem_span_image {U : Type*} [DecidableEq U]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (s : Finset U) (v : U → W) {x : W}
    (hx : x ∈ Submodule.span (ZMod 2) (v '' (s : Set U))) :
    ∃ g : U → ZMod 2, ∑ i ∈ s, g i • v i = x := by
  have hx' : x ∈ Submodule.span (ZMod 2) (v '' (s : Set U)) := hx
  simpa [coe_image] using
    (Submodule.mem_span_image_finset_iff_exists_fun' (R := ZMod 2) (s := s) (v := v)).1
      (by simpa [coe_image] using hx')

/-- An annihilated covering family on `P` cannot have label-rank `≥ k`. -/
lemma covering_annihilator_rank_lt {U : Type*} [DecidableEq U]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (P : Finset U) (G : Finset (Finset U)) (k : ℕ) (p : U → W)
    (hGne : ∀ A ∈ G, A.Nonempty)
    (hcov : ∀ Y : Finset U, Y ⊆ P → #Y = k → ∃ A ∈ G, A ⊆ Y)
    (hann : ∀ A ∈ G, ∑ x ∈ A, p x = 0) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) < k := by
  classical
  haveI : Module.Finite (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) :=
    FiniteDimensional.span_of_finite _ (P.finite_toSet.image _)
  have hkpos := k_pos_of_covering P G k hGne hcov
  by_contra hge
  have hrk : k ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) :=
    Nat.le_of_not_lt hge
  obtain ⟨b, hbP, -, hbspan, hbind⟩ :=
    exists_linearIndepOn_extension (K := ZMod 2) (v := p)
      (s := (∅ : Set U)) (t := (P : Set U)) (linearIndepOn_empty _ _) (Set.empty_subset _)
  have hbfin : b.Finite := (P.finite_toSet).subset hbP
  letI := hbfin.fintype
  have hspanb :
      Submodule.span (ZMod 2) (p '' b) =
        Submodule.span (ZMod 2) (p '' (P : Set U)) := by
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hbP)
    · rw [Submodule.span_le]; exact hbspan
  have hbr : Fintype.card ↥b =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) := by
    have hcard := finrank_span_eq_card (R := ZMod 2) (M := W) hbind
    rw [← Set.image_eq_range, hspanb] at hcard
    exact hcard.symm
  obtain ⟨Y0, hY0b, hY0card⟩ :=
    exists_subset_card_eq (s := b.toFinset) (n := k)
      (by rw [Set.toFinset_card]; omega)
  have hY0P : Y0 ⊆ P := by
    intro x hx
    exact hbP (Set.mem_toFinset.mp (hY0b hx))
  obtain ⟨A, hAG, hAY⟩ := hcov Y0 hY0P hY0card
  obtain ⟨y, hyA⟩ := hGne A hAG
  have hyb : y ∈ b := Set.mem_toFinset.mp (hY0b (hAY hyA))
  have hAb : ∀ x ∈ A, x ∈ b := fun x hx => Set.mem_toFinset.mp (hY0b (hAY hx))
  have hrest :
      ∑ x ∈ A.erase y, p x ∈ Submodule.span (ZMod 2) (p '' (b \ {y})) := by
    apply Submodule.sum_mem
    intro x hx
    apply Submodule.subset_span
    refine ⟨x, ?_, rfl⟩
    exact ⟨hAb x (mem_erase.mp hx).2, by simp [Set.mem_diff, (mem_erase.mp hx).1]⟩
  have hpy : p y = ∑ x ∈ A.erase y, p x :=
    eq_of_add_eq_zero_char_two (by
      have h := (sum_erase_add A p hyA).trans (hann A hAG)
      simpa [add_comm] using h)
  exact hbind.notMem_span hyb (hpy ▸ hrest)

/-- The restored labels on `T ∪ S` are linearly independent when `p` is independent on `T`. -/
lemma restoredLabel_independent_on_union {U : Type*} [DecidableEq U]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (T S : Finset U) (p : U → W)
    (hdisj : Disjoint T S)
    (hTind : LinearIndepOn (ZMod 2) p (T : Set U)) :
    LinearIndepOn (ZMod 2) (restoredLabel p S) ((T ∪ S : Finset U) : Set U) := by
  classical
  rw [linearIndepOn_iff']
  intro t g hts hg i hi
  have hsnd : (∑ x ∈ t, g x • restoredLabel p S x).2 = 0 :=
    congrArg Prod.snd hg
  have hcoord : ∀ j ∈ S, (∑ x ∈ t, g x • restoredLabel p S x).2 j =
      if j ∈ t then g j else 0 := by
    intro j hj
    have : (∑ x ∈ t, g x • restoredLabel p S x).2 j =
        ∑ x ∈ t, g x * (if j = x ∧ x ∈ S then (1 : ZMod 2) else 0) := by
      simp [restoredLabel, Prod.snd_sum, Pi.smul_apply, smul_eq_mul]
    rw [this]
    have hterm : ∀ x ∈ t,
        g x * (if j = x ∧ x ∈ S then (1 : ZMod 2) else 0) =
          if x = j then g j else 0 := by
      intro x hx
      by_cases hxy : x = j
      · subst hxy; simp [hj]
      · simp [hxy, Ne.symm hxy]
    simp_rw [sum_congr rfl hterm, sum_ite_eq']
  have hgS : ∀ j ∈ t, j ∈ S → g j = 0 := by
    intro j hj hjS
    have := congrFun hsnd j
    have hcj := hcoord j hjS
    rw [if_pos hj] at hcj
    exact hcj.symm.trans this
  by_cases hiS : i ∈ S
  · exact hgS i hi hiS
  · have hiT : i ∈ T := by
      have : i ∈ T ∪ S := by simpa using hts hi
      exact (mem_union.1 this).resolve_right hiS
    have hfst : ∑ x ∈ t, g x • p x = 0 := by
      have := congrArg Prod.fst hg
      simpa [restoredLabel, Prod.fst_sum] using this
    have ht_split : t = (t ∩ T) ∪ (t ∩ S) := by
      ext x
      simp only [mem_union, mem_inter]
      constructor
      · intro hx
        have hxUS : x ∈ T ∪ S := by simpa using hts hx
        rcases mem_union.1 hxUS with hT | hS
        · exact Or.inl ⟨hx, hT⟩
        · exact Or.inr ⟨hx, hS⟩
      · rintro (h | h) <;> exact h.1
    have hdis : Disjoint (t ∩ T) (t ∩ S) :=
      disjoint_left.2 fun x hxT hxS =>
        disjoint_left.1 hdisj (mem_inter.1 hxT).2 (mem_inter.1 hxS).2
    have hS0 : ∑ x ∈ t ∩ S, g x • p x = 0 := by
      apply sum_eq_zero
      intro x hx
      simp [hgS x (mem_inter.1 hx).1 (mem_inter.1 hx).2]
    have hsumT : ∑ x ∈ t ∩ T, g x • p x = 0 := by
      rw [ht_split, sum_union hdis] at hfst
      simpa [hS0] using hfst
    exact (linearIndepOn_iff'.1 hTind) (t ∩ T) g
      (fun x hx => (mem_inter.1 hx).2) hsumT i (mem_inter.2 ⟨hi, hiT⟩)

/-- Restored labels on `Q` are spanned by those on `T ∪ S` when `T` spans `p '' Q`. -/
lemma restoredLabel_span_eq {U : Type*} [DecidableEq U]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (Q S T : Finset U) (p : U → W)
    (hT : T ⊆ Q \ S) (hS : S ⊆ Q)
    (hspanT : Submodule.span (ZMod 2) (p '' (T : Set U)) =
              Submodule.span (ZMod 2) (p '' (Q : Set U))) :
    Submodule.span (ZMod 2) (restoredLabel p S '' (Q : Set U)) =
      Submodule.span (ZMod 2) (restoredLabel p S '' ((T ∪ S : Finset U) : Set U)) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    intro w hw
    obtain ⟨x, hxQ, rfl⟩ := hw
    by_cases hxS : x ∈ S
    · exact Submodule.subset_span ⟨x, by simp [hxS], rfl⟩
    · let ι : W →ₗ[ZMod 2] W × (U → ZMod 2) :=
        { toFun := fun w => (w, 0)
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      have hιT : ∀ t ∈ T, restoredLabel p S t = ι (p t) := by
        intro t ht
        have htS : t ∉ S := (mem_sdiff.1 (hT ht)).2
        apply Prod.ext
        · rfl
        · ext y
          change (if y = t ∧ t ∈ S then (1 : ZMod 2) else 0) = 0
          simp [htS]
      have hxι : restoredLabel p S x = ι (p x) := by
        apply Prod.ext
        · rfl
        · ext y
          change (if y = x ∧ x ∈ S then (1 : ZMod 2) else 0) = 0
          simp [hxS]
      have hpx : p x ∈ Submodule.span (ZMod 2) (p '' (T : Set U)) := by
        rw [hspanT]; exact Submodule.subset_span ⟨x, hxQ, rfl⟩
      have him : ι '' (p '' (T : Set U)) = restoredLabel p S '' (T : Set U) := by
        ext v
        constructor
        · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t, ht, hιT t ht⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨p t, ⟨t, ht, rfl⟩, (hιT t ht).symm⟩
      have : ι (p x) ∈ Submodule.span (ZMod 2) (restoredLabel p S '' (T : Set U)) := by
        rw [← him, ← LinearMap.map_span]
        exact ⟨p x, hpx, rfl⟩
      have hTsub : (T : Set U) ⊆ ((T ∪ S : Finset U) : Set U) := by
        intro t ht; simp [ht]
      exact hxι ▸ Submodule.span_mono (Set.image_mono hTsub) this
  · exact Submodule.span_mono (Set.image_mono (by
      intro x hx
      rw [mem_coe, mem_union] at hx
      rcases hx with hT' | hS'
      · exact (mem_sdiff.1 (hT hT')).1
      · exact hS hS'))

/-- Guard-free restoration: a feasible annihilator of a covering family on `P`
can be restored, after pruning the family, to the same rank on any `Q ⊆ P`
that still has at least `k` coordinates. -/
theorem adaptive_rank_restoration {U : Type*} [DecidableEq U]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (P Q : Finset U) (G : Finset (Finset U)) (k : ℕ) (p : U → W)
    (hQP : Q ⊆ P) (hQk : k ≤ #Q)
    (hGne : ∀ A ∈ G, A.Nonempty)
    (hcov : ∀ Y : Finset U, Y ⊆ P → #Y = k → ∃ A ∈ G, A ⊆ Y)
    (hann : ∀ A ∈ G, ∑ x ∈ A, p x = 0) :
    ∃ (H : Finset (Finset U)) (p' : U → W × (U → ZMod 2)),
      H ⊆ G ∧
      (∀ A ∈ H, A ⊆ Q) ∧
      (∀ Y : Finset U, Y ⊆ Q → #Y = k → ∃ A ∈ H, A ⊆ Y) ∧
      (∀ A ∈ H, ∑ x ∈ A, p' x = 0) ∧
      finrank (ZMod 2) (Submodule.span (ZMod 2) (p' '' (Q : Set U))) =
        finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) := by
  classical
  haveI : Module.Finite (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) :=
    FiniteDimensional.span_of_finite _ (P.finite_toSet.image _)
  haveI : Module.Finite (ZMod 2) (Submodule.span (ZMod 2) (p '' (Q : Set U))) :=
    FiniteDimensional.span_of_finite _ (Q.finite_toSet.image _)
  set r := finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) with hr
  set rQ := finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (Q : Set U))) with hrQ
  have hrQ_le : rQ ≤ r :=
    Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (by exact_mod_cast hQP)))
  have hkpos := k_pos_of_covering P G k hGne hcov
  have hrlt := covering_annihilator_rank_lt P G k p hGne hcov hann
  set ℓ := r - rQ with hℓdef
  have hℓ : rQ + ℓ = r := Nat.add_sub_of_le hrQ_le
  have hℓk : ℓ < k := by omega
  -- A basis of columns of `Q`.
  obtain ⟨t, htQ, -, htspan, htind⟩ :=
    exists_linearIndepOn_extension (K := ZMod 2) (v := p)
      (s := (∅ : Set U)) (t := (Q : Set U)) (linearIndepOn_empty _ _) (Set.empty_subset _)
  have htfin : t.Finite := (Q.finite_toSet).subset htQ
  letI := htfin.fintype
  have hspanTQ :
      Submodule.span (ZMod 2) (p '' t) =
        Submodule.span (ZMod 2) (p '' (Q : Set U)) := by
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono htQ)
    · rw [Submodule.span_le]; exact htspan
  have hTcard_type : Fintype.card ↥t = rQ := by
    have hcard := finrank_span_eq_card (R := ZMod 2) (M := W) htind
    rw [← Set.image_eq_range, hspanTQ] at hcard
    exact hcard.symm
  set T : Finset U := t.toFinset with hTdef
  have hTcard : #T = rQ := by rw [hTdef, Set.toFinset_card]; exact hTcard_type
  have hTQ : T ⊆ Q := by
    intro x hx
    exact htQ (Set.mem_toFinset.mp (hTdef ▸ hx))
  have hTset : (T : Set U) = t := by
    rw [hTdef]; exact Set.coe_toFinset t
  have hTind : LinearIndepOn (ZMod 2) p (T : Set U) := by
    rw [hTset]; exact htind
  -- Extend the `Q`-basis to a basis of columns of `P`.
  obtain ⟨b, hbP, htb, hbspan, hbind⟩ :=
    exists_linearIndepOn_extension (K := ZMod 2) (v := p)
      (s := t) (t := (P : Set U)) htind (htQ.trans (by exact_mod_cast hQP))
  have hbfin : b.Finite := (P.finite_toSet).subset hbP
  letI := hbfin.fintype
  have hspanb :
      Submodule.span (ZMod 2) (p '' b) =
        Submodule.span (ZMod 2) (p '' (P : Set U)) := by
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hbP)
    · rw [Submodule.span_le]; exact hbspan
  have hbcard : Fintype.card ↥b = r := by
    have hcard := finrank_span_eq_card (R := ZMod 2) (M := W) hbind
    rw [← Set.image_eq_range, hspanb] at hcard
    exact hcard.symm
  have hbT : ∀ x ∈ b, x ∈ (Q : Set U) → x ∈ t := by
    intro x hxb hxQ
    by_contra hxt
    have : p x ∈ Submodule.span (ZMod 2) (p '' (b \ {x})) := by
      apply Submodule.span_mono (Set.image_mono (s := t) ?_)
      · rw [hspanTQ]; exact Submodule.subset_span ⟨x, hxQ, rfl⟩
      · intro y hy
        refine ⟨htb hy, fun h => ?_⟩
        rw [Set.mem_singleton_iff.1 h] at hy
        exact hxt hy
    exact hbind.notMem_span hxb this
  set B : Finset U := b.toFinset \ T with hBdef
  have hTb : T ⊆ b.toFinset := by
    intro x hx
    exact Set.mem_toFinset.mpr (htb (by rw [← hTset]; exact hx))
  have hBcard : #B = ℓ := by
    rw [hBdef, card_sdiff_of_subset hTb, Set.toFinset_card, hbcard, hTcard, hℓdef]
  have hBQ : B ⊆ P \ Q := by
    intro x hx
    rw [hBdef, mem_sdiff] at hx
    rw [mem_sdiff]
    have hxb : x ∈ b := Set.mem_toFinset.mp hx.1
    have hxt : x ∉ t := by
      intro ht'
      have : x ∈ T := by
        rw [hTdef]
        exact Set.mem_toFinset.mpr ht'
      exact hx.2 this
    exact ⟨hbP hxb, fun hxQ => hxt (hbT x hxb hxQ)⟩
  -- Padding: `G` members inside `Q` cover every `(k-ℓ)`-face of `Q`.
  have hshort : ∀ F : Finset U, F ⊆ Q → #F = k - ℓ → ∃ A ∈ G, A ⊆ F := by
    intro F hFQ hFcard
    have hdisjFB : Disjoint F B :=
      disjoint_left.2 fun x hxF hxB => (mem_sdiff.1 (hBQ hxB)).2 (hFQ hxF)
    have hℓle : ℓ ≤ k := Nat.le_of_lt hℓk
    have hcardFB : #(F ∪ B) = k := by
      rw [card_union_of_disjoint hdisjFB, hBcard, hFcard, Nat.sub_add_cancel hℓle]
    have hFBP : F ∪ B ⊆ P :=
      union_subset (hFQ.trans hQP) ((hBQ.trans sdiff_subset))
    obtain ⟨A, hAG, hA⟩ := hcov (F ∪ B) hFBP hcardFB
    have hsum0 := hann A hAG
    have hAsplit : A = (A \ B) ∪ (A ∩ B) := by
      ext x; simp only [mem_union, mem_sdiff, mem_inter]; tauto
    have hdisjAB : Disjoint (A \ B) (A ∩ B) :=
      disjoint_left.2 fun x hx1 hx2 => (mem_sdiff.1 hx1).2 (mem_inter.1 hx2).2
    have hsumsplit : ∑ x ∈ A \ B, p x + ∑ x ∈ A ∩ B, p x = 0 := by
      rw [← sum_union hdisjAB, ← hAsplit, hsum0]
    have hAminus : (A \ B : Finset U) ⊆ Q := by
      intro x hx
      have hxFB := hA (mem_sdiff.1 hx).1
      rcases mem_union.1 hxFB with hF | hB'
      · exact hFQ hF
      · exact ((mem_sdiff.1 hx).2 hB').elim
    have hmemQ :
        ∑ x ∈ A \ B, p x ∈ Submodule.span (ZMod 2) (p '' (T : Set U)) := by
      rw [hTset, hspanTQ]
      exact Submodule.sum_mem _ fun x hx => Submodule.subset_span ⟨x, hAminus hx, rfl⟩
    obtain ⟨g, hg⟩ := exists_lincomb_of_mem_span_image T p hmemQ
    -- Independence on `b = T ∪ B` forces `A ∩ B = ∅`.
    have hTB : (T ∪ B : Finset U) = b.toFinset := by
      rw [hBdef, union_sdiff_of_subset hTb]
    have hbind' : LinearIndepOn (ZMod 2) p (b : Set U) := hbind
    have hbindT : LinearIndepOn (ZMod 2) p ((T ∪ B : Finset U) : Set U) := by
      rw [hTB, Set.coe_toFinset]; exact hbind'
    let g' : U → ZMod 2 := fun x => if x ∈ A ∩ B then 1 else if x ∈ T then g x else 0
    have hcomb : ∑ x ∈ T ∪ B, g' x • p x = 0 := by
      have hdisjTB : Disjoint T B :=
        disjoint_left.2 fun x hxT hxB => (mem_sdiff.1 (hBQ hxB)).2 (hTQ hxT)
      rw [sum_union hdisjTB]
      have hTpart : ∑ x ∈ T, g' x • p x = ∑ x ∈ T, g x • p x := by
        apply sum_congr rfl
        intro x hxT
        have hxAB : x ∉ A ∩ B := by
          intro hx
          exact (mem_sdiff.1 (hBQ (mem_inter.1 hx).2)).2 (hTQ hxT)
        change (if x ∈ A ∩ B then (1 : ZMod 2) else if x ∈ T then g x else 0) • p x =
          g x • p x
        rw [if_neg hxAB, if_pos hxT]
      have hBpart : ∑ x ∈ B, g' x • p x = ∑ x ∈ A ∩ B, p x := by
        have hAB : A ∩ B ⊆ B := inter_subset_right
        rw [← sum_sdiff hAB]
        have hrest0 : ∑ x ∈ B \ (A ∩ B), g' x • p x = 0 := by
          apply sum_eq_zero
          intro x hx
          have hxAB' : x ∉ A ∩ B := (mem_sdiff.1 hx).2
          have hxT' : x ∉ T := by
            intro hxT
            exact (mem_sdiff.1 (hBQ (mem_sdiff.1 hx).1)).2 (hTQ hxT)
          change (if x ∈ A ∩ B then (1 : ZMod 2) else if x ∈ T then g x else 0) • p x = 0
          rw [if_neg hxAB', if_neg hxT', zero_smul]
        have hAB1 : ∑ x ∈ A ∩ B, g' x • p x = ∑ x ∈ A ∩ B, p x := by
          apply sum_congr rfl
          intro x hx
          change (if x ∈ A ∩ B then (1 : ZMod 2) else if x ∈ T then g x else 0) • p x = p x
          rw [if_pos hx, one_smul]
        rw [hrest0, zero_add, hAB1]
      rw [hTpart, hBpart, hg, hsumsplit]
    have hg'all : ∀ i ∈ T ∪ B, g' i = 0 :=
      (linearIndepOn_iff'.1 hbindT) (T ∪ B) g' (fun _ hx => hx) hcomb
    have hg'B : ∀ x ∈ A ∩ B, g' x = 0 := fun x hx =>
      hg'all x (mem_union.2 (Or.inr (mem_inter.1 hx).2))
    have hABempty : A ∩ B = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hx0 := hg'B x hx
      have hx1 : g' x = 1 := by
        change (if x ∈ A ∩ B then (1 : ZMod 2) else if x ∈ T then g x else 0) = 1
        rw [if_pos hx]
      exact one_ne_zero (hx1.symm.trans hx0)
    have hAF : A ⊆ F := by
      intro x hxA
      have hxFB := hA hxA
      rcases mem_union.1 hxFB with hF | hB'
      · exact hF
      · have hxAB : x ∈ A ∩ B := mem_inter.2 ⟨hxA, hB'⟩
        rw [hABempty] at hxAB
        exact absurd hxAB (notMem_empty x)
    exact ⟨A, hAG, hAF⟩
  -- Choose a restoring support `S ⊆ Q \ T` of size `ℓ`.
  have hroom : ℓ ≤ #(Q \ T) := by
    rw [card_sdiff_of_subset hTQ, hTcard]
    omega
  obtain ⟨S, hSQT, hScard⟩ := exists_subset_card_eq (s := Q \ T) (n := ℓ) hroom
  have hS : S ⊆ Q := hSQT.trans (sdiff_subset)
  have hST : Disjoint T S :=
    disjoint_left.2 fun x hxT hxS => (mem_sdiff.1 (hSQT hxS)).2 hxT
  have hTQS : T ⊆ Q \ S := by
    intro x hxT
    exact mem_sdiff.2 ⟨hTQ hxT, fun hxS => disjoint_left.1 hST hxT hxS⟩
  set H : Finset (Finset U) := G.filter (fun A => A ⊆ Q \ S) with hHdef
  refine ⟨H, restoredLabel p S, ?hHG, ?hHQ, ?hHcov, ?hann', ?hrank⟩
  · exact filter_subset _ _
  · intro A hA
    have hA' : A ∈ G.filter (fun A => A ⊆ Q \ S) := hHdef ▸ hA
    exact (mem_filter.1 hA').2.trans sdiff_subset
  · intro Y hYQ hYk
    have hℓle : ℓ ≤ k := Nat.le_of_lt hℓk
    have hYS : k - ℓ ≤ #(Y \ S) := by
      have hinter : #(Y ∩ S) ≤ #S := card_le_card inter_subset_right
      have hid : #(Y \ S) = #Y - #(Y ∩ S) := by
        have hsub : Y ∩ S ⊆ Y := inter_subset_left
        have hss : Y \ (Y ∩ S) = Y \ S := by
          ext z; simp only [mem_sdiff, mem_inter]; tauto
        rw [← hss, card_sdiff_of_subset hsub]
      have hinterℓ : #(Y ∩ S) ≤ ℓ := hinter.trans (hScard ▸ le_rfl)
      rw [hid, hYk]
      exact Nat.sub_le_sub_left hinterℓ k
    obtain ⟨F, hFYS, hFcard⟩ := exists_subset_card_eq hYS
    have hFQ : F ⊆ Q := hFYS.trans (sdiff_subset.trans hYQ)
    obtain ⟨A, hAG, hAF⟩ := hshort F hFQ hFcard
    have hYSsub : Y \ S ⊆ Q \ S := by
      intro x hx
      exact mem_sdiff.2 ⟨hYQ (mem_sdiff.1 hx).1, (mem_sdiff.1 hx).2⟩
    have hAQS : A ⊆ Q \ S := hAF.trans (hFYS.trans hYSsub)
    refine ⟨A, ?_, hAF.trans (hFYS.trans sdiff_subset)⟩
    exact mem_filter.2 ⟨hAG, hAQS⟩
  · intro A hA
    have hA' : A ∈ G.filter (fun A => A ⊆ Q \ S) := hHdef ▸ hA
    have hAQS : A ⊆ Q \ S := (mem_filter.1 hA').2
    have hAG : A ∈ G := (mem_filter.1 hA').1
    have hfst : (∑ x ∈ A, restoredLabel p S x).1 = 0 := by
      simpa [restoredLabel, Prod.fst_sum] using hann A hAG
    have hsnd : (∑ x ∈ A, restoredLabel p S x).2 = 0 := by
      ext y
      have : (∑ x ∈ A, restoredLabel p S x).2 y =
          ∑ x ∈ A, (if y = x ∧ x ∈ S then (1 : ZMod 2) else 0) := by
        simp [restoredLabel, Prod.snd_sum]
      rw [this]
      apply sum_eq_zero
      intro x hx
      have hxS : x ∉ S := (mem_sdiff.1 (hAQS hx)).2
      simp [hxS]
    ext <;> simp [hfst, hsnd]
  · -- Rank equality.
    have hspanT :
        Submodule.span (ZMod 2) (p '' (T : Set U)) =
          Submodule.span (ZMod 2) (p '' (Q : Set U)) := by
      rw [hTset, hspanTQ]
    have hspan' := restoredLabel_span_eq Q S T p hTQS hS hspanT
    have hdisjTS : Disjoint T S := hST
    have hind := restoredLabel_independent_on_union T S p hdisjTS hTind
    have hTSfin : ((T ∪ S : Finset U) : Set U).Finite := (T ∪ S).finite_toSet
    letI := hTSfin.fintype
    haveI : Module.Finite (ZMod 2)
        (Submodule.span (ZMod 2) (restoredLabel p S '' ((T ∪ S : Finset U) : Set U))) :=
      FiniteDimensional.span_of_finite _ ((T ∪ S).finite_toSet.image _)
    have hcardTS : #(T ∪ S) = r := by
      rw [card_union_of_disjoint hST, hTcard, hScard, hℓ]
    have hfr :
        finrank (ZMod 2)
          (Submodule.span (ZMod 2) (restoredLabel p S '' ((T ∪ S : Finset U) : Set U))) = r := by
      have hcard := finrank_span_eq_card (R := ZMod 2) (M := W × (U → ZMod 2)) hind
      have hrng : Set.range (fun x : ((T ∪ S : Finset U) : Set U) => restoredLabel p S x) =
          restoredLabel p S '' ((T ∪ S : Finset U) : Set U) := (Set.image_eq_range _ _).symm
      have hct : Fintype.card ↥((T ∪ S : Finset U) : Set U) = #(T ∪ S) :=
        Fintype.card_coe (T ∪ S)
      rw [hrng, hct, hcardTS] at hcard
      exact hcard
    haveI : Module.Finite (ZMod 2)
        (Submodule.span (ZMod 2) (restoredLabel p S '' (Q : Set U))) :=
      FiniteDimensional.span_of_finite _ (Q.finite_toSet.image _)
    rw [hspan']
    exact hfr

end E624R18

namespace Erdos624

theorem adaptive_rank_restoration {U : Type*} [DecidableEq U]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (P Q : Finset U) (G : Finset (Finset U)) (k : ℕ) (p : U → W)
    (hQP : Q ⊆ P) (hQk : k ≤ #Q)
    (hGne : ∀ A ∈ G, A.Nonempty)
    (hcov : ∀ Y : Finset U, Y ⊆ P → #Y = k → ∃ A ∈ G, A ⊆ Y)
    (hann : ∀ A ∈ G, ∑ x ∈ A, p x = 0) :
    ∃ (H : Finset (Finset U)) (p' : U → W × (U → ZMod 2)),
      H ⊆ G ∧
      (∀ A ∈ H, A ⊆ Q) ∧
      (∀ Y : Finset U, Y ⊆ Q → #Y = k → ∃ A ∈ H, A ⊆ Y) ∧
      (∀ A ∈ H, ∑ x ∈ A, p' x = 0) ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (p' '' (Q : Set U))) =
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) :=
  E624R18.adaptive_rank_restoration P Q G k p hQP hQk hGne hcov hann

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (P Q : Finset U) (G : Finset (Finset U)) (k : ℕ) (p : U → W)
    (hQP : Q ⊆ P) (hQk : k ≤ #Q)
    (hGne : ∀ A ∈ G, A.Nonempty)
    (hcov : ∀ Y : Finset U, Y ⊆ P → #Y = k → ∃ A ∈ G, A ⊆ Y)
    (hann : ∀ A ∈ G, ∑ x ∈ A, p x = 0) :
    ∃ (H : Finset (Finset U)) (p' : U → W × (U → ZMod 2)),
      H ⊆ G ∧
      (∀ A ∈ H, A ⊆ Q) ∧
      (∀ Y : Finset U, Y ⊆ Q → #Y = k → ∃ A ∈ H, A ⊆ Y) ∧
      (∀ A ∈ H, ∑ x ∈ A, p' x = 0) ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (p' '' (Q : Set U))) =
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) :=
  Erdos624.adaptive_rank_restoration P Q G k p hQP hQk hGne hcov hann
