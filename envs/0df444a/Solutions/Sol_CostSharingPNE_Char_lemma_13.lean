-- Prove2me | solution 1 for CostSharingPNE.Char.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @Albert
-- created : 2026-11-13T14:58:45.188078+00:00
-- url     : https://prove2.me/submissions/472f4212-08af-479f-b4df-20f7cf5aed37

import Definitions.Def_CostSharingPNE_Char_Basis
import Theorems.Thm_CostSharingPNE_Char_lemma_9
import Theorems.Thm_CostSharingPNE_Char_lemma_10

open CostSharingPNE.Char
open Finset

namespace ShapleyPriority

variable {n : ℕ}

noncomputable def predecessors (r : Fin n → Fin n → Prop) (i : Fin n) : Finset (Fin n) := by
  classical
  exact univ.filter fun j => Relation.TransGen r j i

lemma mem_predecessors {r : Fin n → Fin n → Prop} {i j : Fin n} :
    j ∈ predecessors r i ↔ Relation.TransGen r j i := by
  classical
  simp [predecessors]

noncomputable def priority (r : Fin n → Fin n → Prop) (i : Fin n) : Fin (n+1) :=
  ⟨(predecessors r i).card, Nat.lt_succ_of_le (by
    simpa using card_le_univ (predecessors r i))⟩

lemma priority_le {r : Fin n → Fin n → Prop} {i j : Fin n}
    (h : Relation.TransGen r i j) : priority r i ≤ priority r j := by
  exact card_le_card fun k hk => mem_predecessors.mpr ((mem_predecessors.mp hk).trans h)

lemma priority_lt {r : Fin n → Fin n → Prop} {i j : Fin n}
    (hrefl : ∀ x, r x x) (h : Relation.TransGen r i j) (hn : ¬ Relation.TransGen r j i) :
    priority r i < priority r j := by
  change (predecessors r i).card < (predecessors r j).card
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · exact fun k hk => mem_predecessors.mpr ((mem_predecessors.mp hk).trans h)
  · intro he
    exact hn (mem_predecessors.mp (he.symm ▸ mem_predecessors.mpr (Relation.TransGen.single (hrefl j))))

lemma localBlock (ω : WeightSystem n) {T : Finset (Fin n)} {i j : Fin n}
    (hi : i ∈ tbar ω T) (hj : j ∈ T) :
    ω.block i ≤ ω.block j := by
  unfold tbar at hi
  split at hi
  · rw [(mem_filter.mp hi).2]
    exact inf'_le _ hj
  · simp at hi

lemma localStrict (ω : WeightSystem n) {T : Finset (Fin n)} {i j : Fin n}
    (hi : i ∈ tbar ω T) (hj : j ∈ T) (hn : j ∉ tbar ω T) :
    ω.block i < ω.block j := by
  refine lt_of_le_of_ne (localBlock ω hi hj) ?_
  intro he
  apply hn
  have ht : T.Nonempty := ⟨j,hj⟩
  rw [tbar,dif_pos ht] at hi ⊢
  exact mem_filter.mpr ⟨hj, he.symm.trans (mem_filter.mp hi).2⟩

lemma tbarNonempty (ω : WeightSystem n) {T : Finset (Fin n)} (hT : T.Nonempty) :
    (tbar ω T).Nonempty := by
  rw [tbar, dif_pos hT]
  obtain ⟨i,hi,he⟩ := exists_mem_eq_inf' hT ω.block
  exact ⟨i,mem_filter.mpr ⟨hi,he.symm⟩⟩

lemma tbar_subset (ω : WeightSystem n) (T : Finset (Fin n)) : tbar ω T ⊆ T := by
  unfold tbar
  split <;> simp

theorem commonPriority (V : Set (Welfare n))
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hstrict : ∀ W ∈ V, ∀ T ∈ coalitions W, ∀ i ∈ tbar (Ω W T) T,
      ∀ j ∈ T, j ∉ tbar (Ω W T) T → ¬ Relation.TransGen (succeq V Ω) j i)
    (weights : Fin n → ℝ) (hweights : ∀ i, 0 < weights i) :
    ∃ ω : WeightSystem n, ω.lam = weights ∧
      ∀ W ∈ V, ∀ T ∈ coalitions W, tbar ω T = tbar (Ω W T) T := by
  let ω : WeightSystem n := ⟨n+1, priority (succeq V Ω), weights,hweights⟩
  refine ⟨ω,rfl,?_⟩
  intro W hW T hT
  have ht : T.Nonempty := (mem_filter.mp hT).2.1
  have edge (i j : Fin n) (hi : i ∈ tbar (Ω W T) T) (hj : j ∈ T) :
      Relation.TransGen (succeq V Ω) i j :=
    Relation.TransGen.single (Or.inl ⟨W,hW,T,
      mem_filter.mpr ⟨hT,tbar_subset _ _ hi,hj⟩,Or.inl hi,hi⟩)
  have keep (i : Fin n) (hi : i ∈ tbar (Ω W T) T) : i ∈ tbar ω T := by
    rw [tbar,dif_pos ht]
    refine mem_filter.mpr ⟨tbar_subset _ _ hi, le_antisymm ?_ (inf'_le _ (tbar_subset _ _ hi))⟩
    exact le_inf' _ _ fun j hj => priority_le (edge i j hi hj)
  ext j
  constructor
  · intro hj
    by_contra hn
    obtain ⟨i,hi⟩ := tbarNonempty (Ω W T) ht
    have hlt : ω.block i < ω.block j :=
      priority_lt (fun x => Or.inr rfl) (edge i j hi (tbar_subset _ _ hj))
        (hstrict W hW T hT i hi j (tbar_subset _ _ hj) hn)
    exact (not_lt_of_ge (localBlock ω hj (tbar_subset _ _ hi))) hlt
  · exact keep j

end ShapleyPriority

namespace ShapleyPriority

theorem basis_eq_of_ratios {n : ℕ} (u v : WeightSystem n) (T : Finset (Fin n))
    (hblocks : tbar u T = tbar v T)
    (hratio : ∀ i ∈ tbar u T, ∀ j ∈ tbar u T, u.lam i * v.lam j = v.lam i * u.lam j)
    (i : Fin n) (S : Finset (Fin n)) :
    gwsvBasis u T i S = gwsvBasis v T i S := by
  unfold gwsvBasis
  rw [← hblocks]
  split
  · rename_i h
    have hsu : 0 < ∑ j ∈ tbar u T, u.lam j :=
      sum_pos (fun j _ => u.lam_pos j) ⟨i,h.1⟩
    have hsv : 0 < ∑ j ∈ tbar u T, v.lam j :=
      sum_pos (fun j _ => v.lam_pos j) ⟨i,h.1⟩
    apply (div_eq_div_iff hsu.ne' hsv.ne').2
    rw [mul_sum,mul_sum]
    exact sum_congr rfl (fun j hj => hratio i h.1 j hj)
  · rfl

end ShapleyPriority

namespace ShapleyPriority

inductive RatioPath {V : Type*} (edge : V → V → ℝ → Prop) : V → V → ℝ → Prop
  | nil (i) : RatioPath edge i i 1
  | step {i j k a b} : RatioPath edge i j a → edge j k b → RatioPath edge i k (a*b)

namespace RatioPath

variable {V : Type*} {edge : V → V → ℝ → Prop}

lemma trans {i j k : V} {a b : ℝ} (h : RatioPath edge i j a)
    (g : RatioPath edge j k b) : RatioPath edge i k (a*b) := by
  induction g with
  | nil => simpa using h
  | step g e ih => simpa only [mul_assoc] using RatioPath.step ih e

lemma reverse (hs : ∀ i j a, edge i j a → edge j i a⁻¹) {i j : V} {a : ℝ}
    (h : RatioPath edge i j a) : RatioPath edge j i a⁻¹ := by
  induction h with
  | nil => simpa using RatioPath.nil _
  | step h e ih =>
    simpa only [mul_inv_rev, one_mul] using ((RatioPath.nil _).step (hs _ _ _ e)).trans ih

lemma positive (hp : ∀ i j a, edge i j a → 0 < a) {i j : V} {a : ℝ}
    (h : RatioPath edge i j a) : 0 < a := by
  induction h with
  | nil => exact zero_lt_one
  | step h e ih => exact mul_pos ih (hp _ _ _ e)

theorem commonWeights (hp : ∀ i j a, edge i j a → 0 < a)
    (hs : ∀ i j a, edge i j a → edge j i a⁻¹)
    (hc : ∀ i a, RatioPath edge i i a → a = 1) :
    ∃ w : V → ℝ, (∀ i, 0 < w i) ∧ ∀ i j a, edge i j a → w j = w i * a := by
  classical
  let rel : V → V → Prop := fun i j => ∃ a, RatioPath edge i j a
  let st : Setoid V := ⟨rel, ⟨fun i => ⟨1,.nil i⟩,
    fun ⟨a,h⟩ => ⟨a⁻¹,h.reverse hs⟩,
    fun ⟨a,h⟩ ⟨b,g⟩ => ⟨a*b,h.trans g⟩⟩⟩
  let root := fun i : V => Quotient.out (Quotient.mk st i)
  have path (i : V) : ∃ a, RatioPath edge (root i) i a :=
    Quotient.exact (Quotient.out_eq (Quotient.mk st i))
  let w := fun i => Classical.choose (path i)
  have hw (i : V) : RatioPath edge (root i) i (w i) := Classical.choose_spec (path i)
  refine ⟨w,fun i => (hw i).positive hp,?_⟩
  intro i j a he
  have hh : root i = root j := congrArg Quotient.out
    (Quotient.sound (s := st) ⟨a,by simpa using (RatioPath.nil i).step he⟩)
  have hpath := (hw i).step he
  rw [hh] at hpath
  have hone := hc _ _ (hpath.trans ((hw j).reverse hs))
  have hne := ((hw j).positive hp).ne'
  have h := (div_eq_iff hne).mp
    (show (w i * a) / w j = 1 by simpa [div_eq_mul_inv] using hone)
  simpa using h.symm

end RatioPath
end ShapleyPriority

open CostSharingPNE.Char

namespace ShapleyPriority

def weightEdge {n : ℕ} (V : Set (Welfare n))
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n) (i j : Fin n) (a : ℝ) : Prop :=
  ∃ W ∈ V, ∃ T ∈ coalitions W, i ∈ tbar (Ω W T) T ∧ j ∈ tbar (Ω W T) T ∧
    a = (Ω W T).lam j / (Ω W T).lam i

theorem commonWeightSystem {n : ℕ} (V : Set (Welfare n))
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hstrict : ∀ W ∈ V, ∀ T ∈ coalitions W, ∀ i ∈ tbar (Ω W T) T,
      ∀ j ∈ T, j ∉ tbar (Ω W T) T → ¬ Relation.TransGen (succeq V Ω) j i)
    (hcycle : ∀ i a, RatioPath (weightEdge V Ω) i i a → a = 1) :
    ∃ ω : WeightSystem n, ∀ W ∈ V, ∀ T ∈ coalitions W,
      ∀ i S, gwsvBasis (Ω W T) T i S = gwsvBasis ω T i S := by
  have hp : ∀ i j a, weightEdge V Ω i j a → 0 < a := by
    intro i j a h
    obtain ⟨W,hW,T,hT,hi,hj,heq⟩ := h
    rw [heq]
    exact div_pos ((Ω W T).lam_pos j) ((Ω W T).lam_pos i)
  have hs : ∀ i j a, weightEdge V Ω i j a → weightEdge V Ω j i a⁻¹ := by
    intro i j a h
    obtain ⟨W,hW,T,hT,hi,hj,heq⟩ := h
    rw [heq]
    exact ⟨W,hW,T,hT,hj,hi,inv_div _ _⟩
  obtain ⟨w,hw,he⟩ := RatioPath.commonWeights hp hs hcycle
  obtain ⟨ω,hω,hbar⟩ := commonPriority V Ω hstrict w hw
  refine ⟨ω,?_⟩
  intro W hW T hT i S
  apply basis_eq_of_ratios (Ω W T) ω T (hbar W hW T hT).symm
  intro p hp' q hq'
  have h := he p q ((Ω W T).lam q / (Ω W T).lam p) ⟨W,hW,T,hT,hp',hq',rfl⟩
  rw [hω,h]
  have hne := ((Ω W T).lam_pos p).ne'
  field_simp
  <;> ring

end ShapleyPriority

open CostSharingPNE.Char Finset

namespace ShapleyPriority

private lemma basis_zero_outside {n : ℕ} (W : Welfare n) (g : Rule n)
    (h0 : ∀ i S, i ∉ S → g i S = 0)
    (T S : Finset (Fin n)) (i : Fin n) (hi : i ∉ T) :
    basisRule g W T i S = 0 := by
  induction T using Finset.strongInduction with
  | _ T ih =>
    rw [basisRule]
    split
    · rw [h0 i T hi]
      have hz : (∑ U ∈ ((coalitionsIn W T).erase T).attach,
          mobius W U.1 * basisRule g W U.1 i S) = 0 := by
        apply sum_eq_zero
        intro U _
        obtain ⟨hne,hU⟩ := mem_erase.mp U.2
        have hs := (mem_filter.mp hU).2
        rw [ih U.1 (Finset.ssubset_iff_subset_ne.mpr ⟨hs,hne⟩) (fun h => hi (hs h)),mul_zero]
      rw [hz,sub_zero,mul_zero]
    · rfl

theorem basis_identification {n : ℕ} (W : Welfare n) (g : Rule n)
    (Ω : Finset (Fin n) → WeightSystem n)
    (h0 : ∀ i S, i ∉ S → g i S = 0)
    (hg : ∀ S, ∀ i ∈ S, g i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω T) T i S)
    (T : Finset (Fin n)) (hT : T ∈ coalitions W) (i : Fin n) (hi : i ∈ T)
    (S : Finset (Fin n)) :
    basisRule g W T i S = gwsvBasis (Ω T) T i S := by
  classical
  induction T using Finset.strongInduction generalizing S with
  | _ T ih =>
    rw [basisRule]
    split
    · rename_i hTS
      have hmem : T ∈ coalitionsIn W T := mem_filter.mpr ⟨hT,Subset.refl _⟩
      have hq : mobius W T ≠ 0 := (mem_filter.mp hT).2.2
      have hg' := hg T i hi
      have hsum :
          (∑ U ∈ coalitionsIn W T, mobius W U * gwsvBasis (Ω U) U i T) =
            ∑ U ∈ coalitions W, mobius W U * gwsvBasis (Ω U) U i T := by
        apply sum_subset (filter_subset _ _)
        intro U hU hn
        have hnot : ¬ U ⊆ T := fun h => hn (mem_filter.mpr ⟨hU,h⟩)
        simp [gwsvBasis,hnot]
      rw [← hsum, ← sum_erase_add _ _ hmem] at hg'
      rw [hg', sum_attach (f := fun U => mobius W U * basisRule g W U i S)]
      have he :
          (∑ U ∈ (coalitionsIn W T).erase T, mobius W U * basisRule g W U i S) =
            ∑ U ∈ (coalitionsIn W T).erase T, mobius W U * gwsvBasis (Ω U) U i T := by
        apply sum_congr rfl
        intro U hU
        obtain ⟨hne,hU⟩ := mem_erase.mp hU
        obtain ⟨hc,hs⟩ := mem_filter.mp hU
        by_cases hI : i ∈ U
        · rw [ih U (Finset.ssubset_iff_subset_ne.mpr ⟨hs,hne⟩) hc hI]
          simp [gwsvBasis,hs,hs.trans hTS]
        · have hz : basisRule g W U i S = 0 := basis_zero_outside W g h0 U S i hI
          rw [hz]
          simp [gwsvBasis, show i ∉ tbar (Ω U) U from fun h => hI (tbar_subset _ _ h)]
      rw [he]
      simp only [add_sub_cancel_left]
      have hh : gwsvBasis (Ω T) T i T = gwsvBasis (Ω T) T i S := by
        simp [gwsvBasis,hTS]
      rw [hh]
      field_simp
    · rename_i hn
      simp [gwsvBasis,hn]

end ShapleyPriority

namespace ShapleyPriority

theorem pairwiseShares {n : ℕ} (hn : 1 < n) (V : Set (Welfare n))
    (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0)
    (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S, ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S)
    {W Z : Welfare n} (hW : W ∈ V) (hZ : Z ∈ V) {i j : Fin n}
    {T U : Finset (Fin n)} (hT : T ∈ coalitionsPair W i j)
    (hU : U ∈ coalitionsPair Z i j) :
    gwsvBasis (Ω W T) T i T * gwsvBasis (Ω Z U) U j U =
      gwsvBasis (Ω Z U) U i U * gwsvBasis (Ω W T) T j T := by
  have hp' : GuaranteesPNE {W,Z} f := by
    intro m hm L hL A hA
    apply hp m hm L _ A hA
    intro r
    rcases Set.mem_insert_iff.mp (hL r) with h | h
    · exact h ▸ hW
    · exact (Set.mem_singleton_iff.mp h) ▸ hZ
  have he := lemma_9 n hn W Z f (hbb W hW) (hbb Z hZ) (h0 W) (h0 Z) hp' i j T hT U hU
  obtain ⟨hTc,hi,hj⟩ := mem_filter.mp hT
  obtain ⟨hUc,hi',hj'⟩ := mem_filter.mp hU
  simpa only [basis_identification W (f W) (Ω W) (h0 W) (hΩ W hW) T hTc i hi T,
    basis_identification W (f W) (Ω W) (h0 W) (hΩ W hW) T hTc j hj T,
    basis_identification Z (f Z) (Ω Z) (h0 Z) (hΩ Z hZ) U hUc i hi' U,
    basis_identification Z (f Z) (Ω Z) (h0 Z) (hΩ Z hZ) U hUc j hj' U] using he

end ShapleyPriority

namespace ShapleyPriority

theorem pairwiseRatios {n : ℕ} (hn : 1 < n) (V : Set (Welfare n)) (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0) (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S, ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S)
    {i j : Fin n} {a b : ℝ} (ha : weightEdge V Ω i j a) (hb : weightEdge V Ω i j b) :
    a = b := by
  obtain ⟨W,hW,T,hT,hi,hj,ha⟩ := ha
  obtain ⟨Z,hZ,U,hU,hi',hj',hb⟩ := hb
  have hc := pairwiseShares hn V f hbb h0 hp Ω hΩ hW hZ
    (mem_filter.mpr ⟨hT,tbar_subset _ _ hi,tbar_subset _ _ hj⟩)
    (mem_filter.mpr ⟨hU,tbar_subset _ _ hi',tbar_subset _ _ hj'⟩)
  have htpos : 0 < ∑ k ∈ tbar (Ω W T) T, (Ω W T).lam k :=
    sum_pos (fun k _ => (Ω W T).lam_pos k) ⟨i,hi⟩
  have hupos : 0 < ∑ k ∈ tbar (Ω Z U) U, (Ω Z U).lam k :=
    sum_pos (fun k _ => (Ω Z U).lam_pos k) ⟨i,hi'⟩
  simp only [gwsvBasis,hi,hj,hi',hj',true_and,Finset.Subset.refl,if_true] at hc
  field_simp [htpos.ne',hupos.ne'] at hc
  rw [ha,hb]
  apply (div_eq_div_iff ((Ω W T).lam_pos i).ne' ((Ω Z U).lam_pos i).ne').2
  linear_combination -hc

end ShapleyPriority

namespace ShapleyPriority

theorem noReverseEdge {n : ℕ} (hn : 1 < n) (V : Set (Welfare n)) (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0) (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S, ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S)
    {W : Welfare n} (hW : W ∈ V) {T : Finset (Fin n)} (hT : T ∈ coalitions W)
    {i j : Fin n} (hi : i ∈ tbar (Ω W T) T) (hj : j ∈ T)
    (hj0 : j ∉ tbar (Ω W T) T) : ¬ succeq V Ω j i := by
  intro he
  rcases he with ⟨Z,hZ,U,hU,_,hj'⟩ | he
  · have hU' : U ∈ coalitionsPair Z i j := by
      obtain ⟨hc,hjU,hiU⟩ := mem_filter.mp hU
      exact mem_filter.mpr ⟨hc,hiU,hjU⟩
    have hc := pairwiseShares hn V f hbb h0 hp Ω hΩ hW hZ
      (mem_filter.mpr ⟨hT,tbar_subset _ _ hi,hj⟩) hU'
    have ht : 0 < ∑ k ∈ tbar (Ω W T) T, (Ω W T).lam k :=
      sum_pos (fun k _ => (Ω W T).lam_pos k) ⟨i,hi⟩
    have hu : 0 < ∑ k ∈ tbar (Ω Z U) U, (Ω Z U).lam k :=
      sum_pos (fun k _ => (Ω Z U).lam_pos k) ⟨j,hj'⟩
    have hpos := mul_pos (div_pos ((Ω W T).lam_pos i) ht)
      (div_pos ((Ω Z U).lam_pos j) hu)
    simp only [gwsvBasis,hi,hj0,hj',true_and,false_and,Finset.Subset.refl,if_true,if_false,mul_zero] at hc
    exact hpos.ne' hc
  · exact hj0 (he.symm ▸ hi)

end ShapleyPriority

open CostSharingPNE.Char Finset
namespace ShapleyPriority

private lemma exists_minimal_coalition {n : ℕ} (B : Finset (Finset (Fin n)))
    (hB : B.Nonempty) : ∃ T ∈ minimals B, T ∈ B := by
  classical
  obtain ⟨T,hT,hmin⟩ := Finset.exists_min_image B Finset.card hB
  have hm : T ∈ minimals B := by
    apply Finset.mem_filter.mpr
    refine ⟨hT,?_⟩
    intro U hU hsub
    exact (not_lt_of_ge (hmin U hU)) (Finset.card_lt_card hsub)
  exact ⟨T,hm,hT⟩

private lemma share_pos_iff {n : ℕ} (ω : WeightSystem n) (T : Finset (Fin n)) (i : Fin n) :
    0 < gwsvBasis ω T i T ↔ i ∈ tbar ω T := by
  by_cases hi : i ∈ tbar ω T
  · simp only [hi, iff_true, gwsvBasis, Subset.refl, and_self, if_true]
    exact div_pos (ω.lam_pos i) (sum_pos (fun j _ => ω.lam_pos j) ⟨i,hi⟩)
  · simp [gwsvBasis,hi]

theorem cycleShares {n : ℕ} (hn : 1 < n) (V : Set (Welfare n))
    (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0) (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S, ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S)
    (k : ℕ) (hk : 3 ≤ k) (p : Fin k → Fin n) (W : Fin k → Welfare n)
    (T : Fin k → Finset (Fin n)) (hW : ∀ l, W l ∈ V)
    (hT : ∀ l, T l ∈ coalitionsPair (W l) (p l) (p (finRotate k l)))
    (hleft : ∀ l, p l ∈ tbar (Ω (W l) (T l)) (T l)) :
    (∏ l, gwsvBasis (Ω (W l) (T l)) (T l) (p l) (T l)) =
      ∏ l, gwsvBasis (Ω (W l) (T l)) (T l) (p (finRotate k l)) (T l) := by
  classical
  let q := fun l : Fin k => p (finRotate k l)
  have identify (l : Fin k) (U : Finset (Fin n)) (hU : U ∈ coalitionsPair (W l) (p l) (q l)) :
      basisRule (f (W l)) (W l) U (p l) U = gwsvBasis (Ω (W l) U) U (p l) U ∧
      basisRule (f (W l)) (W l) U (q l) U = gwsvBasis (Ω (W l) U) U (q l) U := by
    obtain ⟨hc,hi,hj⟩ := mem_filter.mp hU
    exact ⟨basis_identification _ _ _ (h0 _) (hΩ _ (hW l)) _ hc _ hi _,
      basis_identification _ _ _ (h0 _) (hΩ _ (hW l)) _ hc _ hj _⟩
  have hnon (l : Fin k) : (plusPair (f (W l)) (W l) (p l) (q l)).Nonempty := by
    refine ⟨T l,mem_filter.mpr ⟨hT l,Or.inl ?_⟩⟩
    rw [(identify l _ (hT l)).1]
    exact (share_pos_iff _ _ _).2 (hleft l)
  choose U hmin hU using fun l => exists_minimal_coalition _ (hnon l)
  have huPair (l : Fin k) : U l ∈ coalitionsPair (W l) (p l) (q l) :=
    (mem_filter.mp (hU l)).1
  have hrel (l : Fin k) :=
    pairwiseShares hn V f hbb h0 hp Ω hΩ (hW l) (hW l) (hT l) (huPair l)
  have hpos (l : Fin k) : 0 < gwsvBasis (Ω (W l) (U l)) (U l) (p l) (U l) := by
    obtain hp' | hq' := (mem_filter.mp (hU l)).2
    · rwa [(identify l _ (huPair l)).1] at hp'
    · rw [(identify l _ (huPair l)).2] at hq'
      by_contra! hbad
      have hzero : gwsvBasis (Ω (W l) (U l)) (U l) (p l) (U l) = 0 := by
        have hn' : p l ∉ tbar (Ω (W l) (U l)) (U l) :=
          fun hh => (not_lt_of_ge hbad) ((share_pos_iff _ _ _).2 hh)
        simp [gwsvBasis,hn']
      have he := hrel l
      rw [hzero,zero_mul] at he
      exact (mul_pos ((share_pos_iff _ _ _).2 (hleft l)) hq').ne' he
  have hp' : GuaranteesPNE (Set.range W) f := by
    intro m hm L hL A hA
    exact hp m hm L (fun r => by obtain ⟨l,hl⟩ := hL r; exact hl ▸ hW l) A hA
  have he := lemma_10 n hn k hk W f (fun l => hbb _ (hW l)) (fun l => h0 _) hp' p U hmin
  simp only [show ∀ l, basisRule (f (W l)) (W l) (U l) (p l) (U l) =
    gwsvBasis (Ω (W l) (U l)) (U l) (p l) (U l) from fun l => (identify l _ (huPair l)).1,
    show ∀ l, basisRule (f (W l)) (W l) (U l) (p (finRotate k l)) (U l) =
    gwsvBasis (Ω (W l) (U l)) (U l) (p (finRotate k l)) (U l) from fun l => (identify l _ (huPair l)).2] at he
  have hprod := congrArg (fun g : Fin k → ℝ => ∏ l, g l) (funext hrel)
  simp only [Finset.prod_mul_distrib] at hprod
  rw [← he] at hprod
  rw [mul_comm (∏ l, gwsvBasis (Ω (W l) (U l)) (U l) (p l) (U l))] at hprod
  exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun l _ => (hpos l).ne')) hprod

end ShapleyPriority

namespace ShapleyPriority

theorem cyclePriority {n : ℕ} (hn : 1 < n) (V : Set (Welfare n))
    (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0) (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S, ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S)
    (k : ℕ) (hk : 3 ≤ k) (p : Fin k → Fin n) (W : Fin k → Welfare n)
    (T : Fin k → Finset (Fin n)) (hW : ∀ l, W l ∈ V)
    (hT : ∀ l, T l ∈ coalitionsPair (W l) (p l) (p (finRotate k l)))
    (hleft : ∀ l, p l ∈ tbar (Ω (W l) (T l)) (T l)) :
    ∀ l, p (finRotate k l) ∈ tbar (Ω (W l) (T l)) (T l) := by
  have he := cycleShares hn V f hbb h0 hp Ω hΩ k hk p W T hW hT hleft
  have hpos : 0 < ∏ l, gwsvBasis (Ω (W l) (T l)) (T l) (p l) (T l) :=
    Finset.prod_pos (fun l _ => (share_pos_iff _ _ _).2 (hleft l))
  rw [he] at hpos
  intro l
  by_contra hn'
  have hz : gwsvBasis (Ω (W l) (T l)) (T l) (p (finRotate k l)) (T l) = 0 := by
    simp only [gwsvBasis,hn',false_and,if_false]
  exact hpos.ne' (Finset.prod_eq_zero (Finset.mem_univ l) hz)

end ShapleyPriority

namespace ShapleyPriority

theorem cycleRatioProduct {n : ℕ} (hn : 1 < n) (V : Set (Welfare n))
    (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0) (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S, ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S)
    (k : ℕ) (hk : 3 ≤ k) (p : Fin k → Fin n) (W : Fin k → Welfare n)
    (T : Fin k → Finset (Fin n)) (hW : ∀ l, W l ∈ V)
    (hT : ∀ l, T l ∈ coalitionsPair (W l) (p l) (p (finRotate k l)))
    (hleft : ∀ l, p l ∈ tbar (Ω (W l) (T l)) (T l)) :
    (∏ l, (Ω (W l) (T l)).lam (p (finRotate k l)) /
      (Ω (W l) (T l)).lam (p l)) = 1 := by
  have hr := cyclePriority hn V f hbb h0 hp Ω hΩ k hk p W T hW hT hleft
  let A := fun l => gwsvBasis (Ω (W l) (T l)) (T l) (p l) (T l)
  let B := fun l => gwsvBasis (Ω (W l) (T l)) (T l) (p (finRotate k l)) (T l)
  have hA (l : Fin k) : 0 < A l := (share_pos_iff _ _ _).2 (hleft l)
  have he : (∏ l, A l) = ∏ l, B l :=
    cycleShares hn V f hbb h0 hp Ω hΩ k hk p W T hW hT hleft
  calc
    _ = ∏ l, B l / A l := by
      apply Finset.prod_congr rfl
      intro l _
      have hd : 0 < ∑ i ∈ tbar (Ω (W l) (T l)) (T l), (Ω (W l) (T l)).lam i :=
        sum_pos (fun i _ => (Ω (W l) (T l)).lam_pos i) ⟨p l,hleft l⟩
      simp only [A,B,gwsvBasis,hleft l,hr l,Subset.refl,and_self,if_true]
      field_simp [hd.ne', ((Ω (W l) (T l)).lam_pos (p l)).ne']
    _ = 1 := by
      rw [Finset.prod_div_distrib, ← he, div_self]
      exact Finset.prod_ne_zero_iff.mpr (fun l _ => (hA l).ne')

end ShapleyPriority

namespace ShapleyPriority

theorem strictPriorityNotOnCycle {n : ℕ} (hn : 1 < n) (V : Set (Welfare n))
    (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0) (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S, ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S)
    (k : ℕ) (hk : 3 ≤ k) (p : Fin k → Fin n)
    (he : ∀ l, succeq V Ω (p l) (p (finRotate k l)))
    (hne : ∀ l, p l ≠ p (finRotate k l)) :
    ∀ l, succeq V Ω (p (finRotate k l)) (p l) := by
  classical
  have hw (l : Fin k) : ∃ W ∈ V, ∃ T ∈ coalitionsPair W (p l) (p (finRotate k l)),
      p l ∈ tbar (Ω W T) T := by
    rcases he l with ⟨W,hW,T,hT,_,hi⟩ | heq
    · exact ⟨W,hW,T,hT,hi⟩
    · exact False.elim (hne l heq)
  choose W hW T hT hleft using hw
  have hr := cyclePriority hn V f hbb h0 hp Ω hΩ k hk p W T hW hT hleft
  intro l
  obtain ⟨hc,hi,hj⟩ := mem_filter.mp (hT l)
  exact Or.inl ⟨W l,hW l,T l,mem_filter.mpr ⟨hc,hj,hi⟩,Or.inl (hr l),hr l⟩

end ShapleyPriority

open CostSharingPNE.Char

namespace ShapleyPriority

private theorem indexedPath {V : Type*} {r : V → V → Prop} {a b : V}
    (hne : a ≠ b) (h : Relation.TransGen r a b) :
    ∃ (k : ℕ) (p : Fin (k+1) → V), 0 < k ∧ p 0 = a ∧ p (Fin.last k) = b ∧
      ∀ l : Fin k, r (p l.castSucc) (p l.succ) ∧ p l.castSucc ≠ p l.succ := by
  induction h with
  | @single y he =>
    exact ⟨1,![a,y],by decide,by simp,by simp [Fin.last],fun l => by fin_cases l; simpa using And.intro he hne⟩
  | @tail x y hxy hy ih =>
    by_cases hx : a = x
    · exact ⟨1,![a,y],by decide,by simp,by simp [Fin.last],fun l => by
        fin_cases l
        have h : r a y := hx.symm ▸ hy
        simpa using And.intro h hne⟩
    · obtain ⟨k,p,hk,hfirst,hlast,hs⟩ := ih hx
      by_cases hxy' : x = y
      · exact ⟨k,p,hk,hfirst,hlast.trans hxy',hs⟩
      refine ⟨k+1,Fin.snoc p y,by omega,?_,by simp,?_⟩
      · change @Fin.snoc (k+1) (fun _ => V) p y (Fin.castSucc (0 : Fin (k+1))) = a
        simpa using hfirst
      · intro l
        refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa [hlast] using And.intro hy hxy'
        · have he : (i.castSucc.succ : Fin (k+2)) = i.succ.castSucc := Fin.ext rfl
          simp only [he, Fin.snoc_castSucc]
          exact hs i

end ShapleyPriority

namespace ShapleyPriority

lemma rotate_castSucc {k : ℕ} (i : Fin k) :
    finRotate (k+1) i.castSucc = i.succ := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last]
  · rfl
  · intro h
    have h' := congrArg Fin.val h
    simp at h'
    omega

lemma rotate_last (k : ℕ) : finRotate (k+1) (Fin.last k) = 0 := by
  apply Fin.ext
  simp only [coe_finRotate,if_true,Fin.val_zero]

theorem strictPriorityNoPath {n : ℕ} (hn : 1 < n) (V : Set (Welfare n))
    (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0) (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S, ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S)
    {W : Welfare n} (hW : W ∈ V) {T : Finset (Fin n)} (hT : T ∈ coalitions W)
    {i j : Fin n} (hi : i ∈ tbar (Ω W T) T) (hj : j ∈ T)
    (hj0 : j ∉ tbar (Ω W T) T) : ¬ Relation.TransGen (succeq V Ω) j i := by
  have hne : j ≠ i := fun he => hj0 (he.symm ▸ hi)
  have hf : succeq V Ω i j := Or.inl ⟨W,hW,T,
    Finset.mem_filter.mpr ⟨hT,tbar_subset _ _ hi,hj⟩,Or.inl hi,hi⟩
  have hb := noReverseEdge hn V f hbb h0 hp Ω hΩ hW hT hi hj hj0
  intro hpath
  obtain ⟨k,p,hk,hfirst,hlast,hs⟩ := indexedPath hne hpath
  have hk' : 3 ≤ k+1 := by
    by_contra! hh
    have he : k = 1 := by omega
    subst k
    apply hb
    have h := (hs (0 : Fin 1)).1
    change succeq V Ω (p 0) (p (Fin.last 1)) at h
    rwa [hfirst,hlast] at h
  have he : ∀ l, succeq V Ω (p l) (p (finRotate (k+1) l)) := by
    intro l
    refine Fin.lastCases ?_ (fun t => ?_) l
    · rw [rotate_last,hlast,hfirst]; exact hf
    · rw [rotate_castSucc]; exact (hs t).1
  have hn' : ∀ l, p l ≠ p (finRotate (k+1) l) := by
    intro l
    refine Fin.lastCases ?_ (fun t => ?_) l
    · rw [rotate_last,hlast,hfirst]; exact Ne.symm hne
    · rw [rotate_castSucc]; exact (hs t).2
  have hrev := strictPriorityNotOnCycle hn V f hbb h0 hp Ω hΩ (k+1) hk' p he hn' (Fin.last k)
  rw [rotate_last,hfirst,hlast] at hrev
  exact hb hrev

end ShapleyPriority

open CostSharingPNE.Char
namespace ShapleyPriority

private theorem indexedRatioPath {V : Type*} {r : V → V → ℝ → Prop} {a b : V} {v : ℝ}
    (h : RatioPath r a b v) :
    ∃ (k : ℕ) (p : Fin (k+1) → V) (u : Fin k → ℝ), p 0 = a ∧ p (Fin.last k) = b ∧
      (∀ l : Fin k, r (p l.castSucc) (p l.succ) (u l)) ∧ (∏ l, u l) = v := by
  induction h with
  | nil =>
    refine ⟨0, fun _ => a, Fin.elim0, rfl, rfl, fun l => l.elim0, by simp⟩
  | @step j k x y hp he ih =>
    obtain ⟨m,p,u,hp0,hplast,hs,hu⟩ := ih
    refine ⟨m+1,Fin.snoc p k,Fin.snoc u y,?_,by simp,?_,?_⟩
    · change @Fin.snoc (m+1) (fun _ => V) p k (Fin.castSucc (0 : Fin (m+1))) = a
      simpa using hp0
    · intro l
      refine Fin.lastCases ?_ (fun t => ?_) l
      · simpa [hplast] using he
      · have he : (t.castSucc.succ : Fin (m+2)) = t.succ.castSucc := Fin.ext rfl
        simp only [he, Fin.snoc_castSucc]
        exact hs t
    · rw [Fin.prod_univ_castSucc]
      simpa [hu]

theorem allRatioCycles {n : ℕ} (hn : 1 < n) (V : Set (Welfare n))
    (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0) (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S, ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S)
    (i : Fin n) (a : ℝ) (h : RatioPath (weightEdge V Ω) i i a) : a = 1 := by
  classical
  obtain ⟨k,p,u,hp0,hplast,hs,hu⟩ := indexedRatioPath h
  have hloop : p (Fin.last k) = p 0 := hplast.trans hp0.symm
  rw [← hu]
  by_cases hk : 3 ≤ k
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    let q := fun l : Fin (m+1) => p l.castSucc
    have hnext (l : Fin (m+1)) : q (finRotate (m+1) l) = p l.succ := by
      refine Fin.lastCases ?_ (fun t => ?_) l
      · rw [rotate_last]
        change p 0 = p (Fin.last (m+1))
        exact hloop.symm
      · rw [rotate_castSucc]
        change p t.succ.castSucc = p t.castSucc.succ
        rw [Fin.castSucc_succ]
    have hdata (l : Fin (m+1)) : ∃ W ∈ V, ∃ T ∈ coalitions W,
      q l ∈ tbar (Ω W T) T ∧ q (finRotate (m+1) l) ∈ tbar (Ω W T) T ∧
      u l = (Ω W T).lam (q (finRotate (m+1) l)) / (Ω W T).lam (q l) := by
      rw [hnext]
      exact hs l
    choose W hW T hT hleft hright heq using hdata
    have hpair l : T l ∈ coalitionsPair (W l) (q l) (q (finRotate (m+1) l)) :=
      Finset.mem_filter.mpr ⟨hT l,tbar_subset _ _ (hleft l),tbar_subset _ _ (hright l)⟩
    simpa only [heq] using cycleRatioProduct hn V f hbb h0 hp Ω hΩ (m+1) hk q W T hW hpair hleft
  · have hks : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hks with rfl | rfl | rfl
    · simp
    · rw [Fin.prod_univ_one]
      obtain ⟨W,_,T,_,_,_,heq⟩ := hs (0 : Fin 1)
      change u 0 = (Ω W T).lam (p (Fin.last 1)) / (Ω W T).lam (p 0) at heq
      rw [heq,hloop,div_self ((Ω W T).lam_pos _).ne']
    · rw [Fin.prod_univ_two]
      have ha : weightEdge V Ω (p 0) (p 1) (u 0) := hs (0 : Fin 2)
      have hb : weightEdge V Ω (p 1) (p 0) (u 1) := by
        have hh := hs (1 : Fin 2)
        change weightEdge V Ω (p 1) (p (Fin.last 2)) (u 1) at hh
        rwa [hloop] at hh
      obtain ⟨W,hW,T,hT,h1,h2,heq⟩ := ha
      have hrev : weightEdge V Ω (p 1) (p 0) (u 0)⁻¹ := by
        rw [heq]
        exact ⟨W,hW,T,hT,h2,h1,inv_div _ _⟩
      rw [pairwiseRatios hn V f hbb h0 hp Ω hΩ hb hrev, mul_inv_cancel₀]
      rw [heq]
      exact div_ne_zero ((Ω W T).lam_pos _).ne' ((Ω W T).lam_pos _).ne'

end ShapleyPriority

open CostSharingPNE.Char ShapleyPriority

theorem solution (n : ℕ) (hn : 1 < n) (V : Set (Welfare n)) (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W) (hp : GuaranteesPNE V f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ V, ∀ S : Finset (Fin n), ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S) :
    ∃ ω : WeightSystem n, ∀ W ∈ V, ∀ T ∈ coalitions W,
      ∀ i S, gwsvBasis (Ω W T) T i S = gwsvBasis ω T i S := by
  classical
  let g : Welfare n → Rule n := fun W i S => if i ∈ S then f W i S else 0
  have hg0 (W : Welfare n) (i : Fin n) (S : Finset (Fin n)) (hi : i ∉ S) :
      g W i S = 0 := if_neg hi
  have hgb : ∀ W ∈ V, IsBudgetBalanced (g W) W := by
    intro W hW S
    calc
      _ = ∑ i ∈ S, f W i S := Finset.sum_congr rfl fun i hi => if_pos hi
      _ = W S := hbb W hW S
  have hgp : GuaranteesPNE V g := by
    intro m hm L hL A hA
    obtain ⟨a,ha,hbest⟩ := hp m hm L hL A hA
    have hu (x : Fin n → Finset (Fin m)) (i : Fin n) :
        utility L g x i = utility L f x i := by
      apply Finset.sum_congr rfl
      intro r hr
      exact if_pos (by simp [players,hr])
    refine ⟨a,ha,?_⟩
    intro i b hb
    rw [hu,hu]
    exact hbest i b hb
  have hgΩ : ∀ W ∈ V, ∀ S : Finset (Fin n), ∀ i ∈ S,
      g W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S := by
    intro W hW S i hi
    exact (if_pos hi).trans (hΩ W hW S i hi)
  exact commonWeightSystem V Ω
    (fun W hW T hT i hi j hj hn' => strictPriorityNoPath hn V g hgb hg0 hgp Ω hgΩ hW hT hi hj hn')
    (allRatioCycles hn V g hgb hg0 hgp Ω hgΩ)
