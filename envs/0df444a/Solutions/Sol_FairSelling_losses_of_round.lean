-- Prove2me | solution 1 for FairSelling.losses_of_round
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:10:29.522272+00:00
-- url     : https://prove2.me/submissions/d4fbd77d-6c7b-4ac5-8d66-d6545192f26f

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Theorems.Thm_FairSelling_losses_extend_set
import Theorems.Thm_FairSelling_Canonical_cash_nonneg
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hInv : Inv v p T R D) {i : Fin n}
    (hmax : ∀ a ∈ T, MMS n (v a) p ≤ MMS n (v i) p)
    {k : ℕ} [NeZero k] (C : Canonical (v i) p (MMS n (v i) p) (thr v p i) k R D)
    (Kset : Finset (Fin n)) (part : Fin n → Fin k) (hKT : Kset ⊆ T)
    (hinj : Set.InjOn part Kset)
    (hloss : ∀ a ∈ T, a ∉ Kset → ∀ b ∈ Kset,
      vbarSum (v a) p (C.goods (part b)) + C.cash (part b) < thr v p a)
    (hspecial : ∀ a ∈ Kset, a ≠ i → part a ≠ 0) (hzero : Kset = T ∨ part i ≠ 0) :
    Losses v p (T \ Kset)
      (R \ ((Kset.image part).biUnion C.goods ∪ C.sold (Kset.image part)))
      (D + (∑ g ∈ C.sold (Kset.image part), p g) - ∑ j ∈ Kset.image part, C.cash j) := by
  classical
  obtain ⟨hD, hL, hsmall⟩ := hInv
  set J : Finset (Fin k) := Kset.image part with hJ
  -- The good sold to fund a part is charged to the first served agent that uses it.
  set Fa : Fin n → Finset G := fun b =>
    (C.src (part b)).toFinset \
      (Kset.filter (fun b' => b' < b)).biUnion (fun b' => (C.src (part b')).toFinset) with hFadef
  have hFasub : ∀ b, Fa b ⊆ (C.src (part b)).toFinset := fun b => Finset.sdiff_subset
  have hsrc_of_mem : ∀ b, ∀ g ∈ Fa b, C.src (part b) = some g := by
    intro b g hg
    have := hFasub b hg
    rwa [Option.mem_toFinset, Option.mem_def] at this
  have hFasell : ∀ b, Fa b ⊆ C.sell := fun b g hg => C.src_mem _ _ (hsrc_of_mem b g hg)
  -- disjointness of the events
  have hpair : ∀ b ∈ Kset, ∀ b' ∈ Kset, b ≠ b' →
      Disjoint (C.goods (part b) ∪ Fa b) (C.goods (part b') ∪ Fa b') := by
    intro b hb b' hb' hbb
    rw [Finset.disjoint_left]
    intro g hg hg'
    have hpp : part b ≠ part b' := fun h => hbb (hinj hb hb' h)
    rcases Finset.mem_union.mp hg with hg1 | hg1 <;> rcases Finset.mem_union.mp hg' with hg2 | hg2
    · exact Finset.disjoint_left.mp (C.goods_disj _ _ hpp) hg1 hg2
    · exact Finset.disjoint_left.mp (C.sell_disj (part b)) (hFasell b' hg2) hg1
    · exact Finset.disjoint_left.mp (C.sell_disj (part b')) (hFasell b hg1) hg2
    · rcases lt_or_gt_of_ne hbb with hlt | hlt
      · have : g ∈ (Kset.filter (fun x => x < b')).biUnion
            (fun b'' => (C.src (part b'')).toFinset) :=
          Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hlt⟩, hFasub b hg1⟩
        exact (Finset.mem_sdiff.mp hg2).2 this
      · have : g ∈ (Kset.filter (fun x => x < b)).biUnion
            (fun b'' => (C.src (part b'')).toFinset) :=
          Finset.mem_biUnion.mpr ⟨b', Finset.mem_filter.mpr ⟨hb', hlt⟩, hFasub b' hg2⟩
        exact (Finset.mem_sdiff.mp hg1).2 this
  -- the union of the charged goods is exactly the set of goods sold in this round
  have hunionF : Kset.biUnion Fa = C.sold J := by
    ext g
    simp only [Finset.mem_biUnion, Canonical.sold, hJ, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, hgb⟩
      exact ⟨part b, ⟨b, hb, rfl⟩, hFasub b hgb⟩
    · rintro ⟨j, ⟨b, hb, rfl⟩, hgj⟩
      set W : Finset (Fin n) := Kset.filter (fun x => g ∈ (C.src (part x)).toFinset) with hW
      have hWne : W.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hgj⟩⟩
      refine ⟨W.min' hWne, (Finset.mem_filter.mp (W.min'_mem hWne)).1, ?_⟩
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp (W.min'_mem hWne)).2, ?_⟩
      intro hcon
      obtain ⟨b', hb', hgb'⟩ := Finset.mem_biUnion.mp hcon
      obtain ⟨hb'K, hb'lt⟩ := Finset.mem_filter.mp hb'
      exact absurd (W.min'_le b' (Finset.mem_filter.mpr ⟨hb'K, hgb'⟩)) (not_le.mpr hb'lt)
  have hgoodsU : Kset.biUnion (fun b => C.goods (part b)) = J.biUnion C.goods := by
    ext g
    simp only [Finset.mem_biUnion, hJ, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, hg⟩; exact ⟨part b, ⟨b, hb, rfl⟩, hg⟩
    · rintro ⟨j, ⟨b, hb, rfl⟩, hg⟩; exact ⟨b, hb, hg⟩
  have hunion : Kset.biUnion (fun b => C.goods (part b) ∪ Fa b) = J.biUnion C.goods ∪ C.sold J := by
    rw [← hgoodsU, ← hunionF]
    ext g
    simp only [Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨a, ha, h | h⟩
      · exact Or.inl ⟨a, ha, h⟩
      · exact Or.inr ⟨a, ha, h⟩
    · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
      · exact ⟨a, ha, Or.inl h⟩
      · exact ⟨a, ha, Or.inr h⟩
  have hcashsum : ∑ b ∈ Kset, C.cash (part b) = ∑ j ∈ J, C.cash j :=
    (Finset.sum_image (fun x hx y hy h => hinj hx hy h)).symm
  have hFsum : ∑ b ∈ Kset, ∑ g ∈ Fa b, p g = ∑ g ∈ C.sold J, p g := by
    rw [← hunionF, Finset.sum_biUnion]
    intro b hb b' hb' hbb
    exact Finset.disjoint_of_subset_left Finset.subset_union_right
      (Finset.disjoint_of_subset_right Finset.subset_union_right (hpair b hb b' hb' hbb))
  have key := losses_extend_set v p hL hKT (fun b => C.goods (part b)) Fa
    (fun b => C.cash (part b)) (fun b _ => C.goods_subset _)
    (fun b _ => (hFasell b).trans C.sell_subset)
    (fun b _ => (Finset.disjoint_of_subset_left (hFasell b) (C.sell_disj (part b))).symm)
    hpair (fun b _ => C.cash_nonneg _) ?_
  · rw [hunion, hFsum, hcashsum] at key
    exact key
  · intro a ha Ei b hb
    obtain ⟨haT, haK⟩ := Finset.mem_sdiff.mp ha
    have hlt := hloss a haT haK b hb
    rcases Finset.eq_empty_or_nonempty (Fa b) with hFe | ⟨f, hf⟩
    · exact Or.inr (Or.inl ⟨le_of_lt hlt, by rw [hFe]; simp⟩)
    · have hsrc : C.src (part b) = some f := hsrc_of_mem b f hf
      have hFb : Fa b = {f} := by
        have hsub : Fa b ⊆ {f} := by
          intro g hg
          have : C.src (part b) = some g := hsrc_of_mem b g hg
          rw [hsrc] at this
          simp [Option.some_inj.mp this]
        rcases Finset.subset_singleton_iff.mp hsub with h | h
        · exact absurd (h ▸ hf) (by simp)
        · exact h
      have hfsell : f ∈ C.sell := C.src_mem _ _ hsrc
      by_cases hfS : f ∈ Ei.sell
      · refine Or.inr (Or.inl ⟨le_of_lt hlt, ?_⟩)
        intro g hg
        rw [hFb, Finset.mem_singleton] at hg
        exact Or.inr (hg ▸ hfS)
      · -- the part is a singleton funded by the sale of `f`
        have hbne0 : part b ≠ 0 := by
          by_cases hbi : b = i
          · subst hbi
            rcases hzero with hKT' | h
            · exact absurd (hKT' ▸ haT) haK
            · exact h
          · exact hspecial b hb hbi
        have hsrcne : C.src (part b) ≠ none := by rw [hsrc]; simp
        obtain ⟨e, he⟩ := (C.pure_or_singleton (part b) hbne0).resolve_left hsrcne
        have hdc : C.dcash (part b) = 0 := C.singleton_dcash (part b) hbne0 hsrcne
        have hcf : C.cash (part b) ≤ p f := by
          have h1 : C.scash (part b) ≤ p f := by
            refine le_trans (Finset.single_le_sum
              (f := C.scash) (fun j _ => C.scash_nonneg j) ?_) (C.scash_sum f hfsell)
            simp [hsrc]
          simp only [Canonical.cash, hdc, zero_add]
          exact h1
        have hc0 : 0 ≤ C.cash (part b) := C.cash_nonneg _
        have heR : e ∈ R := C.goods_subset (part b) (by rw [he]; simp)
        have hfR : f ∈ R := C.sell_subset hfsell
        have hve : vbar (v a) p e ≤ thr v p a := le_of_lt (hsmall a haT e heR)
        have hvf : vbar (v a) p f ≤ thr v p a := le_of_lt (hsmall a haT f hfR)
        -- the price of a good the *proposing* agent sells is at least `(1-ρ)` of its maximin
        -- share, which — the proposing agent having the largest maximin share — is at least
        -- `(1-ρ)` of the maximin share of the still-active agent `a`
        have hprice : MMS n (v a) p - thr v p a ≤ p f := by
          refine le_trans ?_ (C.price_large f hfsell)
          have hle : MMS n (v a) p ≤ MMS n (v i) p := hmax a haT
          simp only [thr, rho]
          linarith
        by_cases heS : e ∈ Ei.sell
        · exact Or.inr (Or.inr (Or.inr
            ⟨⟨e, he, heS, hve⟩, ⟨f, hFb, hfS, hvf, hcf, hprice⟩, hc0, le_of_lt hlt⟩))
        · exact Or.inr (Or.inr (Or.inl
            ⟨⟨e, he, heS, hve⟩, ⟨f, hFb, hfS, hvf, hcf, hprice⟩, hc0, le_of_lt hlt⟩))
end FairSelling
