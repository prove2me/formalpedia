-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.observation_4_8
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T05:48:27.480125+00:00
-- url     : https://prove2.me/submissions/69dc1862-6024-4b59-a459-2cb1b7197a5e

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Theorems.Thm_BinaryExtForm_HypercubeRank_lemma_4_3

set_option autoImplicit false

open Disjunctive.HigherDim

namespace BinaryExtForm.HypercubeRank.BalasProof

lemma convexHull_binary_subset {n : ℕ} (S : Set (Fin n → ℝ)) (i : Fin n)
    (hbox : ∀ x ∈ S, 0 ≤ x i ∧ x i ≤ 1) :
    convexHull ℝ S ∩ ZeroOneSet i ⊆ convexHull ℝ (S ∩ ZeroOneSet i) := by
  let C := convexHull ℝ (S ∩ ZeroOneSet i)
  let T : Set (Fin n → ℝ) := {x | 0 ≤ x i ∧ x i ≤ 1 ∧
    (x i = 0 ∨ x i = 1 → x ∈ C)}
  have hST : S ⊆ T := by
    intro x hx
    exact ⟨(hbox x hx).1, (hbox x hx).2,
      fun hb => subset_convexHull ℝ (S ∩ ZeroOneSet i) ⟨hx,hb⟩⟩
  have hT : Convex ℝ T := by
    intro x hx y hy a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0,hb1] using hy
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0,ha1] using hx
    change 0 ≤ x i ∧ x i ≤ 1 ∧ (x i = 0 ∨ x i = 1 → x ∈ C) at hx
    change 0 ≤ y i ∧ y i ≤ 1 ∧ (y i = 0 ∨ y i = 1 → y ∈ C) at hy
    change 0 ≤ a*x i+b*y i ∧ a*x i+b*y i ≤ 1 ∧
      (a*x i+b*y i = 0 ∨ a*x i+b*y i = 1 → a • x+b • y ∈ C)
    have hlow : 0 ≤ a*x i+b*y i := add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
    have hupp : a*x i+b*y i ≤ 1 := by
      have hax := mul_le_mul_of_nonneg_left hx.2.1 ha
      have hby := mul_le_mul_of_nonneg_left hy.2.1 hb
      nlinarith
    refine ⟨hlow,hupp,?_⟩
    intro he
    rcases he with he | he
    · have hz := (add_eq_zero_iff_of_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)).mp he
      have hxi : x i = 0 := (mul_eq_zero.mp hz.1).resolve_left ha0
      have hyi : y i = 0 := (mul_eq_zero.mp hz.2).resolve_left hb0
      exact (convex_convexHull ℝ (S ∩ ZeroOneSet i))
        (hx.2.2 (Or.inl hxi)) (hy.2.2 (Or.inl hyi)) ha hb hab
    · have hdef : a*(1-x i)+b*(1-y i) = 0 := by nlinarith
      have hz := (add_eq_zero_iff_of_nonneg (mul_nonneg ha (sub_nonneg.mpr hx.2.1))
        (mul_nonneg hb (sub_nonneg.mpr hy.2.1))).mp hdef
      have hxi : x i = 1 := by have := (mul_eq_zero.mp hz.1).resolve_left ha0; linarith
      have hyi : y i = 1 := by have := (mul_eq_zero.mp hz.2).resolve_left hb0; linarith
      exact (convex_convexHull ℝ (S ∩ ZeroOneSet i))
        (hx.2.2 (Or.inr hxi)) (hy.2.2 (Or.inr hyi)) ha hb hab
  intro x hx
  exact (convexHull_min hST hT hx.1).2.2 hx.2

lemma split_convexHull_eq {n : ℕ} (S : Set (Fin n → ℝ)) (i : Fin n)
    (hbox : ∀ x ∈ S, 0 ≤ x i ∧ x i ≤ 1) :
    SplitConvexify (convexHull ℝ S) i = convexHull ℝ (S ∩ ZeroOneSet i) := by
  unfold SplitConvexify
  apply Set.Subset.antisymm
  · exact convexHull_min (convexHull_binary_subset S i hbox) (convex_convexHull ℝ _)
  · exact convexHull_mono (fun x hx => ⟨subset_convexHull ℝ S hx.1, hx.2⟩)

lemma iteratedSplit_convexHull {n : ℕ} (S : Set (Fin n → ℝ)) (l : List (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1) :
    IteratedSplit (convexHull ℝ S) l =
      convexHull ℝ (S ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}) := by
  induction l generalizing S with
  | nil => simp [IteratedSplit]
  | cons i l ih =>
    change IteratedSplit (SplitConvexify (convexHull ℝ S) i) l = _
    rw [split_convexHull_eq S i (fun x hx => hbox x hx i (by simp))]
    rw [ih (S ∩ ZeroOneSet i) (fun x hx k hk => hbox x hx.1 k (by simp [hk]))]
    congr 1
    ext x
    simp [List.mem_cons, and_assoc]

lemma convexHull_binary_restriction {n : ℕ} (S : Set (Fin n → ℝ)) (l : List (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1)
    {x : Fin n → ℝ} (hx : x ∈ convexHull ℝ S) (hbin : ∀ i ∈ l, x ∈ ZeroOneSet i) :
    x ∈ convexHull ℝ (S ∩ {z | ∀ i ∈ l, z ∈ ZeroOneSet i}) := by
  induction l generalizing S with
  | nil => simpa using hx
  | cons i l ih =>
    have hx' : x ∈ convexHull ℝ (S ∩ ZeroOneSet i) :=
      convexHull_binary_subset S i (fun z hz => hbox z hz i (by simp))
        ⟨hx,hbin i (by simp)⟩
    have hr := ih (S ∩ ZeroOneSet i) (fun z hz k hk => hbox z hz.1 k (by simp [hk]))
      hx' (fun k hk => hbin k (by simp [hk]))
    have heq : (S ∩ ZeroOneSet i) ∩ {z | ∀ k ∈ l, z ∈ ZeroOneSet k} =
        S ∩ {z | ∀ k ∈ i::l, z ∈ ZeroOneSet k} := by
      ext z
      simp [List.mem_cons,and_assoc]
    rwa [heq] at hr

lemma binary_restriction_nonempty_iff {n : ℕ} (S : Set (Fin n → ℝ)) (l : List (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1) :
    (convexHull ℝ S ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}).Nonempty ↔
      (S ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}).Nonempty := by
  constructor
  · rintro ⟨x,hx,hbin⟩
    exact convexHull_nonempty_iff.mp ⟨x,convexHull_binary_restriction S l hbox hx hbin⟩
  · rintro ⟨x,hx,hbin⟩
    exact ⟨x,subset_convexHull ℝ S hx,hbin⟩

lemma binary_restriction_finset_nonempty_iff {n : ℕ} (S : Set (Fin n → ℝ))
    (H : Finset (Fin n)) (hbox : ∀ x ∈ S, ∀ i ∈ H, 0 ≤ x i ∧ x i ≤ 1) :
    (convexHull ℝ S ∩ ⋂ i ∈ H, ZeroOneSet i).Nonempty ↔
      (S ∩ ⋂ i ∈ H, ZeroOneSet i).Nonempty := by
  classical
  have heq : {x : Fin n → ℝ | ∀ i ∈ H.toList, x ∈ ZeroOneSet i} =
      ⋂ i ∈ H, ZeroOneSet i := by
    ext x
    simp
  rw [← heq]
  exact binary_restriction_nonempty_iff S H.toList (by simpa using hbox)

end BinaryExtForm.HypercubeRank.BalasProof

namespace BinaryExtForm.HypercubeRank.CoverProof

lemma segment_left_extreme {n : ℕ} (u v : Fin n → ℝ) :
    u ∈ Set.extremePoints ℝ (segment ℝ u v) := by
  by_cases huv : u=v
  · subst v
    simp
  have hi : ∃ i, u i ≠ v i := Function.ne_iff.mp huv
  obtain ⟨i,hi⟩ := hi
  refine ⟨left_mem_segment ℝ u v,?_⟩
  intro p hp q hq hu
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hp
  obtain ⟨c,d,hc,hd,hcd,rfl⟩ := hq
  obtain ⟨e,f,he,hf,hef,hvec⟩ := hu
  have heq := congrFun hvec i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at heq
  have hm : (e*b+f*d)*(v i-u i)=0 := by
    calc
      _ = (e*(a*u i+b*v i)+f*(c*u i+d*v i))-u i := by
        have ha' : a=1-b := by linarith
        have hc' : c=1-d := by linarith
        have he' : e=1-f := by linarith
        rw [ha',hc',he']
        ring
      _ = 0 := by rw [heq]; ring
  have hzero : e*b+f*d=0 := (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hi.symm)
  have hbd : b=0 := by nlinarith [mul_nonneg hf.le hd]
  have ha' : a=1 := by linarith
  simp [ha',hbd]

lemma adj_endpoints {n : ℕ} {B : Set (Fin n → ℝ)} {u v : Fin n → ℝ}
    (h : Hirsch.Adj B u v) :
    u ∈ Set.extremePoints ℝ B ∧ v ∈ Set.extremePoints ℝ B := by
  refine ⟨h.2.extremePoints_subset_extremePoints (segment_left_extreme u v),?_⟩
  apply h.2.extremePoints_subset_extremePoints
  rw [segment_symm]
  exact segment_left_extreme v u

end BinaryExtForm.HypercubeRank.CoverProof

namespace BinaryExtForm.HypercubeRank.CoverProof

lemma binary_combo_endpoints (x y a b : ℝ) (hx : 0≤x ∧ x≤1) (hy : 0≤y ∧ y≤1)
    (ha : 0<a) (hb : 0<b) (hab : a+b=1) (h : a*x+b*y=0 ∨ a*x+b*y=1) :
    (x=0 ∧ y=0) ∨ (x=1 ∧ y=1) := by
  rcases h with h|h
  · left
    constructor
    · nlinarith [mul_nonneg hb.le hy.1]
    · nlinarith [mul_nonneg ha.le hx.1]
  · right
    have hax := mul_nonneg ha.le (sub_nonneg.mpr hx.2)
    have hby := mul_nonneg hb.le (sub_nonneg.mpr hy.2)
    constructor <;> nlinarith

lemma fractional_iff_indicator {d k : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) {u v p : Fin (d+1) → ℝ}
    (hadj : Hirsch.Adj B u v) (hp : p∈openSegment ℝ u v) (i : Fin d) :
    (p i.succ≠0 ∧ p i.succ≠1) ↔ indicator u v i := by
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hp
  have hu := hB.2.2.1 u (adj_endpoints hadj).1.1 i
  have hv := hB.2.2.1 v (adj_endpoints hadj).2.1 i
  change (a*u i.succ+b*v i.succ≠0 ∧ a*u i.succ+b*v i.succ≠1) ↔ _
  constructor
  · intro h hi
    rcases hi with ⟨hu,hv⟩|⟨hu,hv⟩
    · exact h.1 (by rw [hu,hv]; ring)
    · exact h.2 (by rw [hu,hv]; nlinarith)
  · intro hi
    constructor
    · intro h
      exact hi (binary_combo_endpoints _ _ a b hu hv ha hb hab (Or.inl h))
    · intro h
      exact hi (binary_combo_endpoints _ _ a b hu hv ha hb hab (Or.inr h))

lemma compact_binarization {d k : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) : IsCompact B := by
  obtain ⟨S,hS⟩ := hB.1
  rw [hS]
  exact S.finite_toSet.isCompact_convexHull ℝ

lemma compact_slice {d k : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) (f : ℝ) : IsCompact (slice B f) :=
  (compact_binarization hB).inter_right (isClosed_eq (continuous_apply 0) continuous_const)

lemma exists_binary_extreme_slice {d k : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) (f : ℝ) (Z : Finset (Fin d))
    (p : Fin (d+1) → ℝ) (hp : p∈slice B f)
    (hbin : ∀ i∈Z,p i.succ=0 ∨ p i.succ=1) :
    ∃ q∈Set.extremePoints ℝ (slice B f), ∀ i∈Z,q i.succ=0 ∨ q i.succ=1 := by
  let F : Set (Fin (d+1) → ℝ) := {q | q∈slice B f ∧ ∀ i∈Z,q i.succ=p i.succ}
  have hFclosed : IsClosed {q : Fin (d+1) → ℝ | ∀ i∈Z,q i.succ=p i.succ} := by
    convert isClosed_iInter (fun i : Fin d => isClosed_iInter (fun _ : i∈Z =>
      isClosed_eq (continuous_apply i.succ) (continuous_const : Continuous (fun _ : Fin (d+1) → ℝ => p i.succ)))) using 1
    ext q
    simp
  have hFc : IsCompact F := (compact_slice hB f).inter_right hFclosed
  have hFe : IsExtreme ℝ (slice B f) F := by
    refine ⟨fun _ h => h.1,?_⟩
    intro u hu v hv q hq hseg
    refine ⟨hu,?_⟩
    obtain ⟨a,b,ha,hb,hab,rfl⟩ := hseg
    intro i hi
    have hcoord := hq.2 i hi
    change a*u i.succ+b*v i.succ=p i.succ at hcoord
    have hends := binary_combo_endpoints (u i.succ) (v i.succ) a b
      (hB.2.2.1 u hu.1 i) (hB.2.2.1 v hv.1 i) ha hb hab
      (hcoord ▸ hbin i hi)
    rcases hends with ⟨hu0,hv0⟩|⟨hu1,hv1⟩
    · rw [hu0,hv0] at hcoord
      simpa [hu0] using hcoord
    · rw [hu1,hv1] at hcoord
      simpa [hu1,hab] using hcoord
  obtain ⟨q,hq⟩ := hFc.extremePoints_nonempty ⟨p,hp,fun _ _ => rfl⟩
  refine ⟨q,hFe.extremePoints_subset_extremePoints hq,?_⟩
  intro i hi
  rw [hq.1.2 i hi]
  exact hbin i hi

end BinaryExtForm.HypercubeRank.CoverProof

namespace BinaryExtForm.HypercubeRank.CoverProof

open Disjunctive.HigherDim

lemma binary_yCoords_iff {d : ℕ} (p : Fin (d+1) → ℝ) :
    p ∈ ⋂ i∈yCoords d, ZeroOneSet i ↔ IsBinaryY p := by
  constructor
  · intro hp i
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hp i.succ)
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  · intro hp
    apply Set.mem_iInter.mpr
    intro i
    apply Set.mem_iInter.mpr
    intro hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact hp j

lemma no_binary_fractional_slice {d k : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) (α : ℕ) (f : ℝ)
    (hf₁ : (α:ℝ)<f) (hf₂ : f<α+1) {p : Fin (d+1) → ℝ}
    (hp : p∈slice B f) : ¬ IsBinaryY p := by
  intro hbin
  have hm : p 0 ∈ (fun q => q 0) '' {q | q∈B ∧ IsBinaryY q} := ⟨p,⟨hp.1,hbin⟩,rfl⟩
  rw [hB.2.2.2] at hm
  obtain ⟨m,_,hm⟩ := hm
  have hf : f=(m:ℝ) := hp.2.symm.trans hm
  rw [hf] at hf₁ hf₂
  have hm₁ : α < m := by exact_mod_cast hf₁
  have hm₂ : m < α+1 := by exact_mod_cast hf₂
  omega

lemma slice_union_box {d k ℓ : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) (xbar : Fin ℓ → ℝ) :
    ∀ p∈⋃ j, slice B (xbar j), ∀ i∈yCoords d, 0≤p i ∧ p i≤1 := by
  intro p hp i hi
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hp
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
  exact hB.2.2.1 p hj.1 a

lemma slice_union_binary_empty {d k ℓ : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) (α : Fin ℓ → ℕ) (xbar : Fin ℓ → ℝ)
    (hx : ∀ j, (α j:ℝ)<xbar j ∧ xbar j<α j+1) :
    (⋃ j, slice B (xbar j)) ∩ ⋂ i∈yCoords d,ZeroOneSet i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hp.1
  exact no_binary_fractional_slice hB (α j) (xbar j) (hx j).1 (hx j).2 hj
    ((binary_yCoords_iff p).mp hp.2)

lemma alpha_edge_crossing {d k : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) (hN : IsNatural B) (α : ℕ) (hα : α<k)
    (f : ℝ) (hf₁ : (α:ℝ)<f) (hf₂ : f<α+1)
    {u v : Fin (d+1) → ℝ} (he : IsAlphaEdge B α u v) :
    ∃ p∈slice B f, p∈openSegment ℝ u v := by
  rcases he.2 with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · obtain ⟨p,hp,_⟩ := (lemma_4_3 B hB hN α hα f hf₁ hf₂).2 u v he.1 hu hv
    exact ⟨p,⟨he.1.2.subset (openSegment_subset_segment ℝ u v hp.1),hp.2⟩,hp.1⟩
  · have hadj : Hirsch.Adj B v u := ⟨he.1.1.symm,by simpa only [segment_symm] using he.1.2⟩
    obtain ⟨p,hp,_⟩ := (lemma_4_3 B hB hN α hα f hf₁ hf₂).2 v u hadj hv hu
    have hseg : p∈openSegment ℝ u v := by simpa only [openSegment_symm] using hp.1
    exact ⟨p,⟨he.1.2.subset (openSegment_subset_segment ℝ u v hseg),hp.2⟩,hseg⟩

lemma selected_empty_iff_edge_cover {d k ℓ : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) (hN : IsNatural B) (α : Fin ℓ → ℕ)
    (hα : ∀ j,α j<k) (xbar : Fin ℓ → ℝ)
    (hx : ∀ j,(α j:ℝ)<xbar j ∧ xbar j<α j+1) (Z : Finset (Fin d)) :
    (⋃ j, slice B (xbar j)) ∩ {p | ∀ i∈Z,p i.succ=0 ∨ p i.succ=1} = ∅ ↔
      ∀ u v, (∃ j,IsAlphaEdge B (α j) u v) → ∃ i∈Z,indicator u v i := by
  classical
  constructor
  · intro hempty u v he
    obtain ⟨j,he⟩ := he
    by_contra hcover
    push Not at hcover
    obtain ⟨p,hp,hseg⟩ := alpha_edge_crossing hB hN (α j) (hα j) (xbar j) (hx j).1 (hx j).2 he
    have hbin : ∀ i∈Z,p i.succ=0 ∨ p i.succ=1 := by
      intro i hi
      by_contra h
      push Not at h
      exact hcover i hi ((fractional_iff_indicator hB he.1 hseg i).mp h)
    have hmem : p∈(⋃ j,slice B (xbar j)) ∩ {p | ∀ i∈Z,p i.succ=0 ∨ p i.succ=1} :=
      ⟨Set.mem_iUnion.mpr ⟨j,hp⟩,hbin⟩
    simp only [hempty,Set.notMem_empty] at hmem
  · intro hcover
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hp.1
    obtain ⟨q,hq,hbin⟩ := exists_binary_extreme_slice hB (xbar j) Z p hj hp.2
    rw [(lemma_4_3 B hB hN (α j) (hα j) (xbar j) (hx j).1 (hx j).2).1] at hq
    obtain ⟨u,v,hadj,hu,hv,hseg,_⟩ := hq
    obtain ⟨i,hi,hind⟩ := hcover u v ⟨j,hadj,Or.inl ⟨hu,hv⟩⟩
    have hfrac := (fractional_iff_indicator hB hadj hseg i).mpr hind
    exact (hbin i hi).elim hfrac.1 hfrac.2

end BinaryExtForm.HypercubeRank.CoverProof

set_option autoImplicit false

open Disjunctive.HigherDim

namespace BinaryExtForm.HypercubeRank.CoverProof

/-- When the generators have no point binary on all selected coordinates, their
convex hull has empty integer hull on those coordinates. -/
lemma intHull_convexHull_eq_empty {n : ℕ} (S : Set (Fin n → ℝ))
    (H : Finset (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ H, 0 ≤ x i ∧ x i ≤ 1)
    (hempty : S ∩ ⋂ i ∈ H, ZeroOneSet i = ∅) :
    intHull (convexHull ℝ S) H = ∅ := by
  apply convexHull_eq_empty.mpr
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  have := (BalasProof.binary_restriction_finset_nonempty_iff S H hbox).mp hne
  simp [hempty] at this

/-- For an empty integer hull, the original list-based rank is the minimum
cardinality of a set of coordinates whose binary restriction is empty. -/
theorem lpr_empty_hull_eq_cover {n : ℕ} (S : Set (Fin n → ℝ))
    (H : Finset (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ H, 0 ≤ x i ∧ x i ≤ 1)
    (hempty : S ∩ ⋂ i ∈ H, ZeroOneSet i = ∅) :
    lpr (convexHull ℝ S) H =
      sInf {c : ℕ | ∃ Z : Finset (Fin n), Z ⊆ H ∧ Z.card = c ∧
        S ∩ ⋂ i ∈ Z, ZeroOneSet i = ∅} := by
  classical
  have hint : intHull (convexHull ℝ S) H = ∅ :=
    intHull_convexHull_eq_empty S H hbox hempty
  let L : Set ℕ := {k | ∃ l : List (Fin n), (∀ i ∈ l, i ∈ H) ∧ l.length = k ∧
    IteratedSplit (convexHull ℝ S) l = intHull (convexHull ℝ S) H}
  let F : Set ℕ := {c | ∃ Z : Finset (Fin n), Z ⊆ H ∧ Z.card = c ∧
    S ∩ ⋂ i ∈ Z, ZeroOneSet i = ∅}
  change sInf L = sInf F
  have to_list : ∀ Z : Finset (Fin n), Z ⊆ H →
      S ∩ ⋂ i ∈ Z, ZeroOneSet i = ∅ → Z.card ∈ L := by
    intro Z hZH hZ
    refine ⟨Z.toList, ?_, Finset.length_toList Z, ?_⟩
    · intro i hi
      exact hZH (Finset.mem_toList.mp hi)
    · rw [hint, BalasProof.iteratedSplit_convexHull S Z.toList
        (fun x hx i hi => hbox x hx i (hZH (Finset.mem_toList.mp hi)))]
      apply convexHull_eq_empty.mpr
      have hsets : {x : Fin n → ℝ | ∀ i ∈ Z.toList, x ∈ ZeroOneSet i} =
          ⋂ i ∈ Z, ZeroOneSet i := by
        ext x
        simp
      rwa [hsets]
  have hL : L.Nonempty := ⟨H.card, to_list H (fun _ hi => hi) hempty⟩
  have hF : F.Nonempty := ⟨H.card, H, (fun _ hi => hi), rfl, hempty⟩
  apply le_antisymm
  · apply le_csInf hF
    intro c hc
    rcases hc with ⟨Z, hZH, hcard, hZ⟩
    rw [← hcard]
    exact csInf_le (OrderBot.bddBelow L) (to_list Z hZH hZ)
  · apply le_csInf hL
    intro k hk
    rcases hk with ⟨l, hlH, hlen, hsplit⟩
    have hboxl : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1 :=
      fun x hx i hi => hbox x hx i (hlH i hi)
    rw [hint, BalasProof.iteratedSplit_convexHull S l hboxl] at hsplit
    have hZ : S ∩ ⋂ i ∈ l.toFinset, ZeroOneSet i = ∅ := by
      have hsets : {x : Fin n → ℝ | ∀ i ∈ l, x ∈ ZeroOneSet i} =
          ⋂ i ∈ l.toFinset, ZeroOneSet i := by
        ext x
        simp
      rw [← hsets]
      exact convexHull_eq_empty.mp hsplit
    have hmem : l.toFinset.card ∈ F :=
      ⟨l.toFinset, fun i hi => hlH i (List.mem_toFinset.mp hi), rfl, hZ⟩
    exact (csInf_le (OrderBot.bddBelow F) hmem).trans
      (hlen ▸ List.toFinset_card_le l)

end BinaryExtForm.HypercubeRank.CoverProof

namespace BinaryExtForm.HypercubeRank.CoverProof

open Disjunctive.HigherDim

lemma binary_succ_image {d : ℕ} (Z : Finset (Fin d)) :
    (⋂ i∈Z.image Fin.succ, ZeroOneSet i) =
      {p : Fin (d+1) → ℝ | ∀ i∈Z,p i.succ=0 ∨ p i.succ=1} := by
  ext p
  simp only [Set.mem_iInter,Finset.mem_image,forall_exists_index,and_imp,Set.mem_ofPred_eq]
  constructor
  · intro hp i hi
    exact hp i.succ i hi rfl
  · intro hp i j hj hji
    subst i
    exact hp j hj

lemma succ_image_subset_yCoords {d : ℕ} (Z : Finset (Fin d)) :
    Z.image Fin.succ ⊆ yCoords d :=
  Finset.image_subset_image (Finset.subset_univ Z)

lemma exists_succ_preimage {d : ℕ} (H : Finset (Fin (d+1))) (hH : H⊆yCoords d) :
    ∃ Z : Finset (Fin d), Z.image Fin.succ=H ∧ Z.card=H.card := by
  classical
  let Z := Finset.univ.filter (fun i : Fin d => i.succ∈H)
  have heq : Z.image Fin.succ=H := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (hH hi)
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hi⟩,rfl⟩
  refine ⟨Z,heq,?_⟩
  rw [← heq,Finset.card_image_of_injective _ (Fin.succ_injective d)]

lemma selected_cover_cardinality_sets {d k ℓ : ℕ} {B : Set (Fin (d+1) → ℝ)}
    (hB : IsBinarization d k B) (hN : IsNatural B) (α : Fin ℓ → ℕ)
    (hα : ∀ j,α j<k) (xbar : Fin ℓ → ℝ)
    (hx : ∀ j,(α j:ℝ)<xbar j ∧ xbar j<α j+1) :
    {c : ℕ | ∃ H : Finset (Fin (d+1)), H⊆yCoords d ∧ H.card=c ∧
      (⋃ j,slice B (xbar j)) ∩ ⋂ i∈H,ZeroOneSet i = ∅} =
    {c : ℕ | ∃ Z : Finset (Fin d), Z.card=c ∧
      ∀ u v,(∃ j,IsAlphaEdge B (α j) u v) → ∃ i∈Z,indicator u v i} := by
  classical
  ext c
  constructor
  · rintro ⟨H,hH,hcard,hempty⟩
    obtain ⟨Z,hZH,hZcard⟩ := exists_succ_preimage H hH
    refine ⟨Z,hZcard.trans hcard,?_⟩
    apply (selected_empty_iff_edge_cover hB hN α hα xbar hx Z).mp
    rw [← hZH,binary_succ_image] at hempty
    exact hempty
  · rintro ⟨Z,hcard,hcover⟩
    refine ⟨Z.image Fin.succ,succ_image_subset_yCoords Z,?_,?_⟩
    · rw [Finset.card_image_of_injective _ (Fin.succ_injective d),hcard]
    · rw [binary_succ_image]
      exact (selected_empty_iff_edge_cover hB hN α hα xbar hx Z).mpr hcover

end BinaryExtForm.HypercubeRank.CoverProof

open BinaryExtForm.HypercubeRank BinaryExtForm.HypercubeRank.CoverProof

theorem solution {d k ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsBinarization d k B)
    (hN : IsNatural B) (hBk : ∀ p ∈ B, 0 ≤ p 0 ∧ p 0 ≤ k) (α : Fin ℓ → ℕ) (hα : ∀ j, α j < k)
    (xbar : Fin ℓ → ℝ) (hx : ∀ j, (α j : ℝ) < xbar j ∧ xbar j < α j + 1) :
    rk B xbar = sInf {c : ℕ | ∃ Z : Finset (Fin d), Z.card = c ∧
      ∀ u v, (∃ j, IsAlphaEdge B (α j) u v) → ∃ i ∈ Z, indicator u v i}  := by
  have _hBk := hBk
  unfold rk
  rw [lpr_empty_hull_eq_cover _ (yCoords d) (slice_union_box hB xbar)
    (slice_union_binary_empty hB α xbar hx),selected_cover_cardinality_sets hB hN α hα xbar hx]
