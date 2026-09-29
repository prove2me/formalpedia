-- Prove2me | solution 1 for CannonFloydParry.exists_refines_isIntegralSubdivision
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:15:39.01388+00:00
-- url     : https://prove2.me/submissions/148d3bb3-5379-4847-aad4-51223bb03382

import Theorems.Thm_CannonFloydParry_ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff
import Mathlib
import Definitions.Def_CannonFloydParry_PIP

/-!
# Barycentric weights on finite sets of points

Helpers for the stellar subdivision used in the proof of Cannon–Floyd–Parry Theorem 7.1.
-/

namespace CannonFloydParry.S7

open Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `w` is a system of barycentric weights of `x` on the finite set `u`, vanishing off `u`. -/
def Bary (u : Finset E) (w : E → ℝ) (x : E) : Prop :=
  (∀ p, p ∉ u → w p = 0) ∧ (∀ p, 0 ≤ w p) ∧ ∑ p ∈ u, w p = 1 ∧ ∑ p ∈ u, w p • p = x

lemma exists_bary {u : Finset E} {x : E} (hx : x ∈ convexHull ℝ (u : Set E)) :
    ∃ w, Bary u w x := by
  classical
  obtain ⟨w, h0, h1, h2⟩ := Finset.mem_convexHull'.1 hx
  refine ⟨fun p => if p ∈ u then w p else 0, fun p hp => by simp [hp], fun p => ?_, ?_, ?_⟩
  · by_cases hp : p ∈ u
    · simp [hp, h0 p hp]
    · simp [hp]
  · rw [← h1]; exact Finset.sum_congr rfl fun p hp => by simp [hp]
  · rw [← h2]; exact Finset.sum_congr rfl fun p hp => by simp [hp]

namespace Bary

variable {u u' : Finset E} {w w' : E → ℝ} {x : E}

lemma mem (h : Bary u w x) : x ∈ convexHull ℝ (u : Set E) :=
  Finset.mem_convexHull'.2 ⟨w, fun p _ => h.2.1 p, h.2.2.1, h.2.2.2⟩

lemma mono (h : Bary u w x) (hu : u ⊆ u') : Bary u' w x := by
  refine ⟨fun p hp => h.1 p (fun h' => hp (hu h')), h.2.1, ?_, ?_⟩
  · rw [← h.2.2.1]
    exact (Finset.sum_subset hu fun p _ hp => h.1 p hp).symm
  · rw [← h.2.2.2]
    exact (Finset.sum_subset hu fun p _ hp => by rw [h.1 p hp, zero_smul]).symm

lemma unique (hind : AffineIndependent ℝ ((↑) : u → E)) (h1 : Bary u w x) (h2 : Bary u w' x) :
    w = w' := by
  funext p
  by_cases hp : p ∈ u
  · exact hind.eq_of_sum_eq_sum_subtype (h1.2.2.1.trans h2.2.2.1.symm)
      (h1.2.2.2.trans h2.2.2.2.symm) p hp
  · rw [h1.1 p hp, h2.1 p hp]

/-- In a simplicial complex, the barycentric weights of a point do not depend on the face. -/
lemma eq_of_faces (K : Geometry.SimplicialComplex ℝ E) {u₁ u₂ : Finset E} {w₁ w₂ : E → ℝ}
    (hu₁ : u₁ ∈ K.faces) (hu₂ : u₂ ∈ K.faces) (h₁ : Bary u₁ w₁ x) (h₂ : Bary u₂ w₂ x) :
    w₁ = w₂ := by
  classical
  have hx := K.inter_subset_convexHull hu₁ hu₂ ⟨h₁.mem, h₂.mem⟩
  rw [← Finset.coe_inter] at hx
  obtain ⟨w₃, h₃⟩ := exists_bary hx
  rw [h₁.unique (K.indep hu₁) (h₃.mono Finset.inter_subset_left),
    h₂.unique (K.indep hu₂) (h₃.mono Finset.inter_subset_right)]

end Bary

lemma affineIndependent_of_forall {s : Finset E}
    (h : ∀ w : E → ℝ, ∑ p ∈ s, w p = 0 → ∑ p ∈ s, w p • p = 0 → ∀ p ∈ s, w p = 0) :
    AffineIndependent ℝ ((↑) : s → E) := by
  classical
  rw [affineIndependent_iff]
  intro t w hw hwp i hi
  let w' : E → ℝ := fun p => if h : p ∈ s then (if (⟨p, h⟩ : s) ∈ t then w ⟨p, h⟩ else 0) else 0
  have hw' : ∀ j : s, w' j = if j ∈ t then w j else 0 := fun j => by simp [w', j.2]
  have e1 : ∑ p ∈ s, w' p = ∑ j ∈ t, w j := by
    rw [← Finset.sum_attach s, ← Finset.univ_eq_attach]
    simp_rw [hw']
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have e2 : ∑ p ∈ s, w' p • p = ∑ j ∈ t, w j • (j : E) := by
    rw [← Finset.sum_attach s (fun p => w' p • p), ← Finset.univ_eq_attach]
    simp_rw [hw', ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have := h w' (e1.trans hw) (e2.trans hwp) i i.2
  rwa [hw', if_pos hi] at this

end CannonFloydParry.S7

/-!
# Stellar subdivision of a geometric simplicial complex

Starring `K` at a point `v` of the relative interior of a face `τ`: the faces of `K` not
containing `τ`, together with the joins `insert v t` for `t` with `τ ⊄ t` and `t ∪ τ ∈ K`.
-/

namespace CannonFloydParry.S7

open Finset Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- The faces of the stellar subdivision of `K` at `v`, with carrier face `τ`. -/
def starFaces (K : SimplicialComplex ℝ E) (τ : Finset E) (v : E) : Set (Finset E) :=
  {s | s ∈ K.faces ∧ ¬ τ ⊆ s} ∪ {s | ∃ t, ¬ τ ⊆ t ∧ t ∪ τ ∈ K.faces ∧ s = insert v t}

/-- The data of a starring: `v` is a point of the relative interior of the face `τ`. -/
structure StarData (K : SimplicialComplex ℝ E) (τ : Finset E) (v : E) (μ : E → ℝ) : Prop where
  mem : τ ∈ K.faces
  bary : Bary τ μ v
  pos : ∀ p ∈ τ, 0 < μ p
  notMem : v ∉ τ

/-- `x = a v + ∑_{p ∈ t} b p • p`, a convex combination. -/
def Split (v : E) (t : Finset E) (a : ℝ) (b : E → ℝ) (x : E) : Prop :=
  0 ≤ a ∧ (∀ p, p ∉ t → b p = 0) ∧ (∀ p, 0 ≤ b p) ∧ a + ∑ p ∈ t, b p = 1 ∧
    a • v + ∑ p ∈ t, b p • p = x

lemma exists_split {v : E} {t : Finset E} {x : E} (hvt : v ∉ t)
    (hx : x ∈ convexHull ℝ ((insert v t : Finset E) : Set E)) : ∃ a b, Split v t a b x := by
  obtain ⟨β, h0, h1, h2, h3⟩ := exists_bary hx
  have hne : ∀ p ∈ t, p ≠ v := fun p hp => ne_of_mem_of_not_mem hp hvt
  refine ⟨β v, fun p => if p = v then 0 else β p, h1 v, ?_, ?_, ?_, ?_⟩
  · intro p hp
    by_cases hpv : p = v
    · simp [hpv]
    · simp only [hpv, if_false]
      exact h0 p (by simp [hpv, hp])
  · intro p
    dsimp only
    split_ifs
    · exact le_rfl
    · exact h1 p
  · rw [sum_insert hvt] at h2
    rw [← h2]
    congr 1
    exact sum_congr rfl fun p hp => by simp [hne p hp]
  · rw [sum_insert hvt] at h3
    rw [← h3]
    congr 1
    exact sum_congr rfl fun p hp => by simp [hne p hp]

lemma Split.mem {v : E} {t : Finset E} {a : ℝ} {b : E → ℝ} {x : E} (hvt : v ∉ t)
    (h : Split v t a b x) : x ∈ convexHull ℝ ((insert v t : Finset E) : Set E) := by
  have hne : ∀ p ∈ t, p ≠ v := fun p hp => ne_of_mem_of_not_mem hp hvt
  refine Bary.mem (w := fun p => if p = v then a else b p) ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    have hpv : p ≠ v := fun e => hp (e ▸ mem_insert_self v t)
    simp only [hpv, if_false]
    exact h.2.1 p (fun h' => hp (mem_insert_of_mem h'))
  · intro p
    dsimp only
    split_ifs
    · exact h.1
    · exact h.2.2.1 p
  · rw [sum_insert hvt, if_pos rfl, ← h.2.2.2.1]
    congr 1
    exact sum_congr rfl fun p hp => by simp [hne p hp]
  · rw [sum_insert hvt]; beta_reduce; rw [if_pos rfl, ← h.2.2.2.2]
    congr 1
    exact sum_congr rfl fun p hp => by simp [hne p hp]

namespace StarData

variable {K : SimplicialComplex ℝ E} {τ : Finset E} {v : E} {μ : E → ℝ}
  (hd : StarData K τ v μ)
include hd

lemma τ_nonempty : τ.Nonempty := K.nonempty_of_mem_faces hd.mem

lemma v_notMem {s : Finset E} (hs : s ∈ K.faces) : v ∉ s := by
  intro hv
  have h1 : ({v} : Finset E) ∈ K.faces :=
    K.down_closed hs (by simpa using hv) (by simp)
  have := K.inter_subset_convexHull h1 hd.mem
    ⟨by simpa using subset_convexHull ℝ ({v} : Set E) (Set.mem_singleton v), hd.bary.mem⟩
  have he : ((({v} : Finset E) : Set E) ∩ (τ : Set E)) = ∅ := by
    ext p
    simp only [coe_singleton, Set.mem_inter_iff, Set.mem_singleton_iff, mem_coe,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl
    exact hd.notMem
  rw [he, convexHull_empty] at this
  exact this

lemma v_notMem_of_union {t : Finset E} (hu : t ∪ τ ∈ K.faces) : v ∉ t :=
  fun h => hd.v_notMem hu (mem_union_left _ h)

lemma indep_insert {t : Finset E} (ht : ¬ τ ⊆ t) (hu : t ∪ τ ∈ K.faces) :
    AffineIndependent ℝ ((↑) : ↥(insert v t : Finset E) → E) := by
  have hvt := hd.v_notMem_of_union hu
  apply affineIndependent_of_forall
  intro w hw0 hw1
  rw [sum_insert hvt] at hw0 hw1
  set w' : E → ℝ := fun p => (if p ∈ t then w p else 0) + w v * μ p with hw'
  have hB := hd.bary.mono (subset_union_right (s₁ := t))
  have s1 : ∑ p ∈ t ∪ τ, w' p = 0 := by
    simp only [w', sum_add_distrib, ← mul_sum, hB.2.2.1, sum_ite_mem, union_inter_cancel_left]
    linarith
  have s2 : ∑ p ∈ t ∪ τ, w' p • p = 0 := by
    simp only [w', add_smul, sum_add_distrib, mul_smul, ← smul_sum, hB.2.2.2, ite_smul,
      zero_smul, sum_ite_mem, union_inter_cancel_left]
    rw [← hw1, add_comm]
  have hz := (K.indep hu).eq_zero_of_sum_eq_zero_subtype s1 s2
  obtain ⟨j, hjτ, hjt⟩ := not_subset.1 ht
  have hwv : w v = 0 := by
    have := hz j (mem_union_right _ hjτ)
    simp only [w', hjt, if_false, zero_add] at this
    exact (mul_eq_zero.1 this).resolve_right (hd.pos j hjτ).ne'
  intro p hp
  rcases mem_insert.1 hp with rfl | hp
  · exact hwv
  · have := hz p (mem_union_left _ hp)
    simpa [w', hp, hwv] using this

lemma bary_of_split {t : Finset E} {a : ℝ} {b : E → ℝ} {x : E} (h : Split v t a b x) :
    Bary (t ∪ τ) (fun p => a * μ p + b p) x := by
  have hB := hd.bary.mono (subset_union_right (s₁ := t))
  have hbt : ∀ p ∈ t ∪ τ, p ∉ t → b p = 0 := fun p _ hp => h.2.1 p hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    show a * μ p + b p = 0
    rw [hB.1 p hp, h.2.1 p (fun h' => hp (mem_union_left _ h')), mul_zero, add_zero]
  · intro p
    exact add_nonneg (mul_nonneg h.1 (hd.bary.2.1 p)) (h.2.2.1 p)
  · rw [sum_add_distrib, ← mul_sum, hB.2.2.1, mul_one,
      ← sum_subset subset_union_left hbt, h.2.2.2.1]
  · simp only [add_smul, sum_add_distrib, mul_smul, ← smul_sum, hB.2.2.2]
    rw [← sum_subset subset_union_left (fun p hp hp' => by rw [hbt p hp hp', zero_smul]),
      h.2.2.2.2]

lemma inter_BB {t₁ t₂ : Finset E} (h₁ : ¬ τ ⊆ t₁) (hu₁ : t₁ ∪ τ ∈ K.faces) (h₂ : ¬ τ ⊆ t₂)
    (hu₂ : t₂ ∪ τ ∈ K.faces) :
    convexHull ℝ ((insert v t₁ : Finset E) : Set E) ∩
        convexHull ℝ ((insert v t₂ : Finset E) : Set E) ⊆
      convexHull ℝ (((insert v t₁ : Finset E) : Set E) ∩ ((insert v t₂ : Finset E) : Set E)) := by
  rintro x ⟨hx₁, hx₂⟩
  have hv₁ := hd.v_notMem_of_union hu₁
  have hv₂ := hd.v_notMem_of_union hu₂
  obtain ⟨a₁, b₁, hs₁⟩ := exists_split hv₁ hx₁
  obtain ⟨a₂, b₂, hs₂⟩ := exists_split hv₂ hx₂
  have hL := Bary.eq_of_faces K hu₁ hu₂ (hd.bary_of_split hs₁) (hd.bary_of_split hs₂)
  obtain ⟨j₁, hj₁τ, hj₁t⟩ := not_subset.1 h₁
  obtain ⟨j₂, hj₂τ, hj₂t⟩ := not_subset.1 h₂
  have e1 := congrFun hL j₁
  have e2 := congrFun hL j₂
  rw [hs₁.2.1 j₁ hj₁t] at e1
  rw [hs₂.2.1 j₂ hj₂t] at e2
  have ha₁ : a₂ ≤ a₁ := le_of_mul_le_mul_right (by linarith [hs₂.2.2.1 j₁]) (hd.pos j₁ hj₁τ)
  have ha₂ : a₁ ≤ a₂ := le_of_mul_le_mul_right (by linarith [hs₁.2.2.1 j₂]) (hd.pos j₂ hj₂τ)
  have ha : a₁ = a₂ := le_antisymm ha₂ ha₁
  have hb : b₁ = b₂ := by
    funext p
    have := congrFun hL p
    simp only [ha] at this
    linarith
  have hz : ∀ p, p ∉ t₁ ∩ t₂ → b₁ p = 0 := by
    intro p hp
    rw [mem_inter, not_and_or] at hp
    rcases hp with hp | hp
    · exact hs₁.2.1 p hp
    · rw [hb]; exact hs₂.2.1 p hp
  have hvt : v ∉ t₁ ∩ t₂ := fun h => hv₁ (mem_inter.1 h).1
  rw [← coe_inter, ← insert_inter_distrib]
  refine Split.mem hvt ⟨hs₁.1, hz, hs₁.2.2.1, ?_, ?_⟩
  · rw [sum_subset inter_subset_left (fun p _ hp => hz p hp), hs₁.2.2.2.1]
  · rw [sum_subset inter_subset_left (fun p _ hp => by rw [hz p hp, zero_smul]), hs₁.2.2.2.2]

lemma inter_AB {s t : Finset E} (hs : s ∈ K.faces) (hτs : ¬ τ ⊆ s) (hu : t ∪ τ ∈ K.faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ ((insert v t : Finset E) : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ ((insert v t : Finset E) : Set E)) := by
  rintro x ⟨hxs, hxt⟩
  have hvt := hd.v_notMem_of_union hu
  obtain ⟨a, b, hsp⟩ := exists_split hvt hxt
  obtain ⟨l, hl⟩ := exists_bary hxs
  have hL := Bary.eq_of_faces K hs hu hl (hd.bary_of_split hsp)
  have ha : a = 0 := by
    by_contra ha
    have hapos : 0 < a := lt_of_le_of_ne hsp.1 (Ne.symm ha)
    apply hτs
    intro j hj
    by_contra hjs
    have := congrFun hL j
    rw [hl.1 j hjs] at this
    nlinarith [hd.pos j hj, hsp.2.2.1 j, mul_pos hapos (hd.pos j hj)]
  have hbs : ∀ p, p ∉ s → b p = 0 := fun p hp => by
    have := congrFun hL p
    rw [hl.1 p hp, ha] at this
    linarith
  have hz : ∀ p, p ∉ s ∩ t → b p = 0 := by
    intro p hp
    rw [mem_inter, not_and_or] at hp
    rcases hp with hp | hp
    · exact hbs p hp
    · exact hsp.2.1 p hp
  have hmem : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    refine Bary.mem (w := b) ⟨hz, hsp.2.2.1, ?_, ?_⟩
    · rw [sum_subset inter_subset_right (fun p _ hp => hz p hp)]
      linarith [hsp.2.2.2.1]
    · rw [sum_subset inter_subset_right (fun p _ hp => by rw [hz p hp, zero_smul]),
        ← hsp.2.2.2.2, ha, zero_smul, zero_add]
  refine convexHull_mono ?_ hmem
  rw [coe_inter]
  exact Set.inter_subset_inter_right _ (by simp [Set.subset_insert])

end StarData

/-- The stellar subdivision of `K` at `v`, with carrier face `τ`. -/
def star {K : SimplicialComplex ℝ E} {τ : Finset E} {v : E} {μ : E → ℝ}
    (hd : StarData K τ v μ) : SimplicialComplex ℝ E where
  faces := starFaces K τ v
  isRelLowerSet_faces := by
    rintro s (⟨hs, hτs⟩ | ⟨t, ht, hu, rfl⟩)
    · refine ⟨K.nonempty_of_mem_faces hs, fun r hrs hr => Or.inl ⟨K.down_closed hs hrs hr, ?_⟩⟩
      exact fun h => hτs (h.trans hrs)
    · refine ⟨insert_nonempty _ _, fun r hrs hr => ?_⟩
      have hrs' : r.erase v ⊆ t := subset_insert_iff.1 hrs
      by_cases hv : v ∈ r
      · refine Or.inr ⟨r.erase v, fun h => ht (h.trans hrs'), ?_, (insert_erase hv).symm⟩
        exact K.down_closed hu (union_subset_union hrs' subset_rfl)
          (hd.τ_nonempty.mono subset_union_right)
      · rw [erase_eq_of_notMem hv] at hrs'
        exact Or.inl ⟨K.down_closed hu (hrs'.trans subset_union_left) hr,
          fun h => ht (h.trans hrs')⟩
  indep := by
    rintro s (⟨hs, -⟩ | ⟨t, ht, hu, rfl⟩)
    · exact K.indep hs
    · exact hd.indep_insert ht hu
  inter_subset_convexHull := by
    rintro s₁ s₂ (⟨hs₁, hτ₁⟩ | ⟨t₁, ht₁, hu₁, rfl⟩) (⟨hs₂, hτ₂⟩ | ⟨t₂, ht₂, hu₂, rfl⟩)
    · exact K.inter_subset_convexHull hs₁ hs₂
    · exact hd.inter_AB hs₁ hτ₁ hu₂
    · rw [Set.inter_comm, Set.inter_comm ((insert v t₁ : Finset E) : Set E)]
      exact hd.inter_AB hs₂ hτ₂ hu₁
    · exact hd.inter_BB ht₁ hu₁ ht₂ hu₂

namespace StarData

variable {K : SimplicialComplex ℝ E} {τ : Finset E} {v : E} {μ : E → ℝ}
  (hd : StarData K τ v μ)
include hd

lemma refines_faces {s : Finset E} (hs : s ∈ (star hd).faces) :
    ∃ u ∈ K.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (u : Set E) := by
  rcases hs with ⟨hs, -⟩ | ⟨t, -, hu, rfl⟩
  · exact ⟨s, hs, subset_rfl⟩
  · refine ⟨t ∪ τ, hu, convexHull_min ?_ (convex_convexHull ℝ _)⟩
    rw [coe_insert]
    refine Set.insert_subset ?_ ?_
    · exact convexHull_mono (by simp) hd.bary.mem
    · exact (by simp : (t : Set E) ⊆ ↑(t ∪ τ)).trans (subset_convexHull ℝ _)

lemma space_star : (star hd).space = K.space := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [SimplicialComplex.mem_space_iff] at hx ⊢
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨u, hu, hsu⟩ := hd.refines_faces hs
    exact ⟨u, hu, hsu hx⟩
  · intro x hx
    rw [SimplicialComplex.mem_space_iff] at hx ⊢
    obtain ⟨u, hu, hx⟩ := hx
    by_cases hτu : τ ⊆ u
    · obtain ⟨l, hl⟩ := exists_bary hx
      obtain ⟨j, hjτ, hjmin⟩ := exists_min_image τ (fun p => l p / μ p) hd.τ_nonempty
      set α := l j / μ j with hα
      have hμj := hd.pos j hjτ
      set b : E → ℝ := fun p => l p - α * μ p with hb
      have hbj : b j = 0 := by simp only [b, α]; field_simp; ring
      have hμu := hd.bary.mono hτu
      have hvu : v ∉ u := hd.v_notMem hu
      have hvt : v ∉ u.erase j := fun h => hvu (mem_of_mem_erase h)
      have hz : ∀ p, p ∉ u.erase j → b p = 0 := by
        intro p hp
        by_cases hpj : p = j
        · rw [hpj, hbj]
        · have hpu : p ∉ u := fun h => hp (mem_erase.2 ⟨hpj, h⟩)
          simp only [b, hl.1 p hpu, hμu.1 p hpu, mul_zero, sub_zero]
      have hsplit : Split v (u.erase j) α b x := by
        refine ⟨div_nonneg (hl.2.1 j) hμj.le, hz, ?_, ?_, ?_⟩
        · intro p
          simp only [b, sub_nonneg]
          by_cases hpτ : p ∈ τ
          · have h1 := hjmin p hpτ
            have hμp := hd.pos p hpτ
            rw [le_div_iff₀ hμp] at h1
            exact h1
          · rw [hd.bary.1 p hpτ, mul_zero]
            exact hl.2.1 p
        · rw [sum_erase u hbj]
          simp only [b, sum_sub_distrib, ← mul_sum, hl.2.2.1, hμu.2.2.1]
          ring
        · rw [sum_erase u (by rw [hbj, zero_smul])]
          simp only [b, sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, hl.2.2.2, hμu.2.2.2]
          abel
      refine ⟨insert v (u.erase j), Or.inr ⟨u.erase j, fun h => ?_, ?_, rfl⟩, hsplit.mem hvt⟩
      · exact (notMem_erase j u) (h hjτ)
      · have : u.erase j ∪ τ = u := by
          ext p
          simp only [mem_union, mem_erase]
          constructor
          · rintro (⟨-, h⟩ | h)
            · exact h
            · exact hτu h
          · intro h
            by_cases hpj : p = j
            · exact Or.inr (hpj ▸ hjτ)
            · exact Or.inl ⟨hpj, h⟩
        rw [this]; exact hu
    · exact ⟨u, Or.inl ⟨hu, hτu⟩, hx⟩

lemma finite_star (hK : K.faces.Finite) : (star hd).faces.Finite := by
  refine Set.Finite.union (hK.subset fun s hs => hs.1) ?_
  have : {t : Finset E | t ∪ τ ∈ K.faces} ⊆ ⋃ u ∈ K.faces, (u.powerset : Set (Finset E)) := by
    intro t ht
    simp only [Set.mem_iUnion, mem_coe, mem_powerset]
    exact ⟨t ∪ τ, ht, subset_union_left⟩
  have hfin := (hK.biUnion fun u _ => u.powerset.finite_toSet).subset this
  refine (hfin.image (insert v)).subset ?_
  rintro s ⟨t, -, hu, rfl⟩
  exact ⟨t, hu, rfl⟩

end StarData

end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix

variable {n : ℕ}

lemma sum_abs_pos {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) : 0 < ∑ i, |x i| := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact lt_of_lt_of_le (abs_pos.mpr hi)
    (Finset.single_le_sum (f := fun i => |x i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))

lemma rho_smul {c : ℝ} (hc : 0 < c) (y : Fin (n + 1) → ℝ) : rho (c • y) = rho y := by
  unfold rho
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc, ← Finset.mul_sum, smul_smul]
  congr 1
  by_cases hs : ∑ i, |y i| = 0
  · simp [hs]
  · field_simp

lemma rho_of_mem {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) : rho x = x := by
  unfold rho
  have : ∑ i, |x i| = 1 := by
    rw [← hx.2]; exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hx.1 i)
  simp [this]

lemma rho_mem {y : Fin (n + 1) → ℝ} (hy : ∀ i, 0 ≤ y i) (hy0 : y ≠ 0) : rho y ∈ Simplex n := by
  have hs := sum_abs_pos hy0
  refine ⟨fun i => ?_, ?_⟩
  · unfold rho
    exact mul_nonneg (inv_nonneg.mpr hs.le) (hy i)
  · unfold rho
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => (abs_of_nonneg (hy i)).symm]
    exact inv_mul_cancel₀ hs.ne'

lemma rho_eq_smul (y : Fin (n + 1) → ℝ) : rho y = (∑ i, |y i|)⁻¹ • y := rfl


end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

/-! ### Convex hulls of finite families -/

/-! ### Columns -/

lemma exists_pos_of_mem {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) : ∃ j, 0 < x j := by
  by_contra h
  push Not at h
  have : ∑ j, x j ≤ 0 := Finset.sum_nonpos fun j _ => h j
  rw [hx.2] at this
  norm_num at this

/-! ### Primitive lifts -/

lemma sum_abs_intCast {w : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) :
    ∑ i, |(w i : ℝ)| = ((∑ i, w i : ℤ) : ℝ) := by
  push_cast
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (by exact_mod_cast hw i)

lemma gcd_nonneg' (w : Fin (n + 1) → ℤ) : 0 ≤ Finset.univ.gcd w :=
  Int.nonneg_of_normalize_eq_self Finset.normalize_gcd

lemma ne_zero_of_gcd_eq_one {w : Fin (n + 1) → ℤ} (hg : Finset.univ.gcd w = 1) : w ≠ 0 := by
  rintro rfl
  have : Finset.univ.gcd (0 : Fin (n + 1) → ℤ) = 0 :=
    Finset.gcd_eq_zero_iff.2 fun _ _ => rfl
  rw [this] at hg
  exact zero_ne_one hg

lemma sum_pos_of_prim {w : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) (hg : Finset.univ.gcd w = 1) :
    0 < ∑ i, w i := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (ne_zero_of_gcd_eq_one hg)
  exact Finset.sum_pos' (fun k _ => hw k) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hw i) (Ne.symm hi)⟩

lemma rho_intCast {w : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) :
    rho (fun i => (w i : ℝ)) = ((∑ i, w i : ℤ) : ℝ)⁻¹ • (fun i => (w i : ℝ)) := by
  rw [rho_eq_smul, sum_abs_intCast hw]

lemma prim_unique {w w' : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) (hw' : ∀ i, 0 ≤ w' i)
    (hg : Finset.univ.gcd w = 1) (hg' : Finset.univ.gcd w' = 1)
    (h : rho (fun i => (w i : ℝ)) = rho (fun i => (w' i : ℝ))) : w = w' := by
  rw [rho_intCast hw, rho_intCast hw'] at h
  set s := ∑ i, w i
  set s' := ∑ i, w' i
  have hs : 0 < s := sum_pos_of_prim hw hg
  have hs' : 0 < s' := sum_pos_of_prim hw' hg'
  have key : ∀ i, s' * w i = s * w' i := by
    intro i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    have hs0' : (s' : ℝ) ≠ 0 := by exact_mod_cast hs'.ne'
    field_simp at this
    exact_mod_cast (by linarith : (s' : ℝ) * w i = s * w' i)
  have d1 : s' ∣ s := by
    have : s' ∣ Finset.univ.gcd (fun i => s * w' i) :=
      Finset.dvd_gcd fun i _ => ⟨w i, (key i).symm⟩
    rwa [Finset.gcd_mul_left, hg', mul_one, Int.normalize_of_nonneg hs.le] at this
  have d2 : s ∣ s' := by
    have : s ∣ Finset.univ.gcd (fun i => s' * w i) :=
      Finset.dvd_gcd fun i _ => ⟨w' i, key i⟩
    rwa [Finset.gcd_mul_left, hg, mul_one, Int.normalize_of_nonneg hs'.le] at this
  have hss : s = s' := Int.dvd_antisymm hs.le hs'.le d2 d1
  funext i
  have := key i
  rw [hss] at this
  exact mul_left_cancel₀ hs'.ne' this

lemma lift_eq {w : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) (hg : Finset.univ.gcd w = 1) :
    lift (rho (fun i => (w i : ℝ))) = w := by
  have hex : ∃ w' : Fin (n + 1) → ℤ, (∀ i, 0 ≤ w' i) ∧
      rho (fun i => (w' i : ℝ)) = rho (fun i => (w i : ℝ)) ∧ Finset.univ.gcd w' = 1 :=
    ⟨w, hw, rfl, hg⟩
  unfold lift
  rw [dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  exact prim_unique h1 hw h3 hg h2

lemma exists_prim {x : Fin (n + 1) → ℝ} (hx : IsRationalPoint x) :
    ∃ w : Fin (n + 1) → ℤ, (∀ i, 0 ≤ w i) ∧ rho (fun i => (w i : ℝ)) = x ∧
      Finset.univ.gcd w = 1 := by
  choose q hq using hx.2
  set D : ℕ := ∏ i, (q i).den with hD
  have hDpos : (0 : ℝ) < D := by
    rw [hD]; push_cast
    exact Finset.prod_pos fun i _ => by exact_mod_cast (q i).den_pos
  set w0 : Fin (n + 1) → ℤ := fun i => (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ)
    with hw0
  have hw0x : ∀ i, (w0 i : ℝ) = D * x i := by
    intro i
    rw [hq i, hw0, hD]
    have hden : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ i)]
    push_cast
    rw [Rat.cast_def]
    field_simp
  obtain ⟨g, hg, hgcd⟩ := Finset.extract_gcd w0 Finset.univ_nonempty
  set G := Finset.univ.gcd w0 with hG
  have hw0nn : ∀ i, 0 ≤ w0 i := fun i => by
    have : (0 : ℝ) ≤ w0 i := by rw [hw0x]; exact mul_nonneg hDpos.le (hx.1.1 i)
    exact_mod_cast this
  have hGpos : 0 < G := by
    refine lt_of_le_of_ne (gcd_nonneg' w0) (Ne.symm fun h0 => ?_)
    have hall := Finset.gcd_eq_zero_iff.1 h0
    obtain ⟨j, hj⟩ := exists_pos_of_mem hx.1
    have := hw0x j
    rw [hall j (Finset.mem_univ _)] at this
    push_cast at this
    nlinarith
  have hgnn : ∀ i, 0 ≤ g i := fun i => by
    have := hw0nn i
    rw [hg i (Finset.mem_univ _)] at this
    exact (mul_nonneg_iff_of_pos_left hGpos).mp this
  refine ⟨g, hgnn, ?_, hgcd⟩
  have hvec : (fun i => ((g i : ℤ) : ℝ)) = ((G : ℝ))⁻¹ • ((D : ℝ) • x) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hw0x, hg i (Finset.mem_univ _)]
    have : (G : ℝ) ≠ 0 := by exact_mod_cast hGpos.ne'
    push_cast
    field_simp
  rw [hvec, rho_smul (inv_pos.mpr (by exact_mod_cast hGpos)), rho_smul hDpos, rho_of_mem hx.1]

lemma lift_spec {x : Fin (n + 1) → ℝ} (hx : IsRationalPoint x) :
    (∀ i, 0 ≤ lift x i) ∧ rho (fun i => (lift x i : ℝ)) = x ∧ Finset.univ.gcd (lift x) = 1 := by
  obtain ⟨w, hw, hrho, hg⟩ := exists_prim hx
  rw [← hrho, lift_eq hw hg]
  exact ⟨hw, rfl, hg⟩

end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix Set Module

variable {n : ℕ}

lemma lift_col_real {x : Fin (n + 1) → ℝ} (hx : IsRationalPoint x) :
    (fun i => (lift x i : ℝ)) = (∑ i, |(lift x i : ℝ)|) • x := by
  obtain ⟨hnn, hrho, hg⟩ := lift_spec hx
  have hne : (fun i => (lift x i : ℝ)) ≠ 0 := by
    intro h0
    apply ne_zero_of_gcd_eq_one hg
    funext i
    have := congrFun h0 i
    simpa using this
  have hs := sum_abs_pos hne
  have h := hrho
  rw [rho_eq_smul] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  rw [← hi]
  field_simp

lemma det_lift_ne_zero {v : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hv : ∀ j, IsRationalPoint (v j)) (hind : AffineIndependent ℝ v) :
    (Matrix.of fun i j => lift (v j) i).det ≠ 0 := by
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j => lift (v j) i
  intro h0
  have hR : (W.map (Int.cast : ℤ → ℝ)).det = 0 := by
    have := (Int.castRingHom ℝ).map_det W
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hR
  set s : Fin (n + 1) → ℝ := fun j => ∑ i, |(lift (v j) i : ℝ)|
  have hvec : ∑ j, (c j * s j) • v j = 0 := by
    rw [← hc]
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.map_apply, W, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrFun (lift_col_real (hv j)) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    ring
  have hsum : ∑ j, c j * s j = 0 := by
    have := congrArg (fun z : Fin (n + 1) → ℝ => ∑ i, z i) hvec
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Finset.sum_const_zero] at this
    rw [Finset.sum_comm] at this
    simpa [← Finset.mul_sum, (hv _).1.2] using this
  have hall := affineIndependent_iff.1 hind Finset.univ _ hsum hvec
  apply hc0
  funext j
  have hsj : 0 < s j := by
    obtain ⟨_, _, hg⟩ := lift_spec (hv j)
    apply sum_abs_pos
    intro h0
    apply ne_zero_of_gcd_eq_one hg
    funext i
    have := congrFun h0 i
    simpa using this
  have := hall j (Finset.mem_univ j)
  simpa [hsj.ne'] using this

lemma ind_eq_natAbs_det {v : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hv : ∀ j, IsRationalPoint (v j)) (hind : AffineIndependent ℝ v) :
    ind v = (Matrix.of fun i j => lift (v j) i).det.natAbs := by
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j => lift (v j) i with hW
  have hli : LinearIndependent ℤ (fun j => lift (v j)) :=
    Matrix.linearIndependent_cols_of_det_ne_zero (det_lift_ne_zero hv hind)
  set w := fun j => lift (v j)
  have hS : Submodule.span ℤ (range w) =
      (AddSubgroup.closure (range w)).toIntSubmodule := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.toAddSubgroup_toIntSubmodule]
  let bN := (Basis.span hli).map (LinearEquiv.ofEq _ _ hS)
  have := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin (n + 1)))
    (AddSubgroup.closure (range w)) bN
  unfold ind
  rw [this, Basis.det_apply]
  congr 2
  ext i j
  simp only [Basis.toMatrix_apply, Pi.basisFun_repr, W, Matrix.of_apply]
  show ((bN j : _) : Fin (n + 1) → ℤ) i = _
  simp only [bN, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply, w]

theorem ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff' {n : ℕ}
    {v : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hv : ∀ j, IsRationalPoint (v j)) (hind : AffineIndependent ℝ v) :
    ind v ≠ 0 ∧ ind v = (Matrix.of fun i j => lift (v j) i).det.natAbs ∧
      (ind v = 1 ↔ IsIntegralSubsimplex n (convexHull ℝ (Set.range v))) :=
  by
  try haveI := hv; try haveI := hind; first
    | exact CannonFloydParry.ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff hv hind
    | exact CannonFloydParry.ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff
    | exact CannonFloydParry.ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff ..
    | (apply CannonFloydParry.ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff <;> first | assumption | infer_instance)
    | simpa using CannonFloydParry.ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff


end CannonFloydParry.S7

/-!
# The index of a finite set of rational points, and its behaviour under starring
-/

namespace CannonFloydParry.S7

open Finset Geometry Matrix

variable {n : ℕ}

/-- The index of a finite set of points of `Δₙ`: the index of the subgroup generated by the
lifts. -/
noncomputable def indS (s : Finset (Fin (n + 1) → ℝ)) : ℕ :=
  (AddSubgroup.closure (lift '' (s : Set (Fin (n + 1) → ℝ)))).index

lemma ind_eq_indS {f : Fin (n + 1) → Fin (n + 1) → ℝ} {s : Finset (Fin (n + 1) → ℝ)}
    (h : Set.range f = ↑s) : ind f = indS s := by
  unfold ind indS
  rw [← h, ← Set.range_comp]
  rfl

/-- Affinely independent points of `Δₙ` number at most `n + 1`. -/
lemma card_le_of_affInd {s : Finset (Fin (n + 1) → ℝ)}
    (hs : AffineIndependent ℝ ((↑) : s → Fin (n + 1) → ℝ)) (hΔ : ∀ p ∈ s, p ∈ Simplex n) :
    s.card ≤ n + 1 := by
  have h1 := hs.card_le_finrank_succ
  rw [Fintype.card_coe] at h1
  let φ : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ i, x i
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum] }
  have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → Fin (n + 1) → ℝ))) < n + 1 := by
    have hne : vectorSpan ℝ (Set.range ((↑) : s → Fin (n + 1) → ℝ)) ≠ ⊤ := by
      intro htop
      have hle : vectorSpan ℝ (Set.range ((↑) : s → Fin (n + 1) → ℝ)) ≤ LinearMap.ker φ := by
        rw [vectorSpan_def]
        apply Submodule.span_le.2
        rintro _ ⟨p, ⟨a, rfl⟩, q, ⟨b, rfl⟩, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, φ, LinearMap.coe_mk,
          AddHom.coe_mk, Pi.sub_apply, Finset.sum_sub_distrib]
        rw [(hΔ a a.2).2, (hΔ b b.2).2, sub_self]
      have : (Pi.single 0 1 : Fin (n + 1) → ℝ) ∈ LinearMap.ker φ := hle (htop ▸ Submodule.mem_top)
      simp [φ] at this
    have := Submodule.finrank_lt hne
    simpa using this
  omega

lemma exists_enum {s : Finset (Fin (n + 1) → ℝ)} (hs : s.card = n + 1) :
    ∃ f : Fin (n + 1) → Fin (n + 1) → ℝ, Function.Injective f ∧ Set.range f = ↑s := by
  let e := s.equivFinOfCardEq hs
  refine ⟨fun k => (e.symm k : Fin (n + 1) → ℝ), fun a b h => e.symm.injective
    (Subtype.val_injective h), ?_⟩
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact (e.symm k).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp⟩

lemma affInd_of_range {f : Fin (n + 1) → Fin (n + 1) → ℝ} {s : Finset (Fin (n + 1) → ℝ)}
    (hs : AffineIndependent ℝ ((↑) : s → Fin (n + 1) → ℝ)) (hr : Set.range f = ↑s)
    (hinj : Function.Injective f) : AffineIndependent ℝ f := by
  have h : AffineIndependent ℝ (fun x => x : ((s : Set (Fin (n + 1) → ℝ))) → Fin (n + 1) → ℝ) :=
    hs
  rw [← hr] at h
  exact h.of_set_of_injective hinj

lemma sum_enum {f : Fin (n + 1) → Fin (n + 1) → ℝ} {s : Finset (Fin (n + 1) → ℝ)}
    {M : Type*} [AddCommMonoid M] (g : (Fin (n + 1) → ℝ) → M)
    (hr : Set.range f = ↑s) (hinj : Function.Injective f) : ∑ k, g (f k) = ∑ p ∈ s, g p := by
  have : s = Finset.univ.image f := by
    ext x
    have h1 : x ∈ (s : Set (Fin (n + 1) → ℝ)) ↔ x ∈ Set.range f := by rw [hr]
    rw [mem_coe] at h1
    rw [h1]
    simp
  rw [this, Finset.sum_image (fun a _ b _ h => hinj h)]

/-- For a rational `n`-simplex, `indS` is the absolute value of the determinant of the lifts. -/
lemma indS_facts {s : Finset (Fin (n + 1) → ℝ)} (hs : IsRationalSubsimplex s)
    (hcard : s.card = n + 1) :
    indS s ≠ 0 ∧ (indS s = 1 → IsIntegralSubsimplex n (convexHull ℝ (s : Set (Fin (n + 1) → ℝ)))) := by
  obtain ⟨f, hinj, hr⟩ := exists_enum hcard
  have hv : ∀ j, IsRationalPoint (f j) := fun j => hs.1 _ (by
    rw [← mem_coe, ← hr]; exact Set.mem_range_self j)
  have hind := affInd_of_range hs.2 hr hinj
  obtain ⟨h0, -, h1⟩ := ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff' hv hind
  rw [ind_eq_indS hr, hr] at h1
  rw [ind_eq_indS hr] at h0
  exact ⟨h0, h1.1⟩

lemma det_updateCol_mulVec' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) (k : Fin m) :
    (A.updateCol k (A *ᵥ c)).det = c k * A.det := by
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [mul_comm]

/-- The real lift of a point. -/
noncomputable abbrev liftR (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ := fun i => (lift x i : ℝ)

/-- Replacing a vertex `j ∈ τ` of a rational `n`-simplex `σ' ⊇ τ` by `v`, whose lift is
`∑_{p ∈ τ} c p • lift p` with `0 < c < 1`, strictly lowers the index. -/
lemma indS_insert_erase_lt {σ' τ : Finset (Fin (n + 1) → ℝ)} {v j : Fin (n + 1) → ℝ}
    {c : (Fin (n + 1) → ℝ) → ℝ}
    (hσ' : IsRationalSubsimplex σ') (hcard : σ'.card = n + 1) (hτσ : τ ⊆ σ') (hj : j ∈ τ)
    (hv : IsRationalPoint v) (hvσ : v ∉ σ') (hc : ∀ p ∈ τ, 0 < c p ∧ c p < 1)
    (hrel : liftR v = ∑ p ∈ τ, c p • liftR p)
    (hnew : AffineIndependent ℝ ((↑) : ↥(insert v (σ'.erase j)) → Fin (n + 1) → ℝ)) :
    indS (insert v (σ'.erase j)) < indS σ' := by
  classical
  obtain ⟨f, hinj, hr⟩ := exists_enum hcard
  have hjσ : j ∈ σ' := hτσ hj
  obtain ⟨k₀, hk₀⟩ : j ∈ Set.range f := by rw [hr]; exact hjσ
  have hfσ : ∀ k, f k ∈ σ' := fun k => by rw [← mem_coe, ← hr]; exact Set.mem_range_self k
  set f' := Function.update f k₀ v with hf'
  have hr' : Set.range f' = ↑(insert v (σ'.erase j)) := by
    ext x
    simp only [Set.mem_range, coe_insert, coe_erase, Set.mem_insert_iff, Set.mem_sdiff,
      mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩
      by_cases hk : k = k₀
      · left; rw [hk, hf', Function.update_self]
      · right
        rw [hf', Function.update_of_ne hk]
        exact ⟨hfσ k, fun h => hk (hinj (h.trans hk₀.symm))⟩
    · rintro (rfl | ⟨hx, hxj⟩)
      · exact ⟨k₀, by rw [hf', Function.update_self]⟩
      · obtain ⟨k, rfl⟩ : x ∈ Set.range f := by rw [hr]; exact hx
        have hk : k ≠ k₀ := fun h => hxj (h ▸ hk₀)
        exact ⟨k, by rw [hf', Function.update_of_ne hk]⟩
  have hinj' : Function.Injective f' := by
    intro a b h
    by_cases ha : a = k₀ <;> by_cases hb : b = k₀
    · rw [ha, hb]
    · rw [ha, hf', Function.update_self, Function.update_of_ne hb] at h
      exact absurd (h ▸ hfσ b) hvσ
    · rw [hb, hf', Function.update_self, Function.update_of_ne ha] at h
      exact absurd (h ▸ hfσ a) hvσ
    · rw [hf', Function.update_of_ne ha, Function.update_of_ne hb] at h
      exact hinj h
  have hv' : ∀ k, IsRationalPoint (f' k) := by
    intro k
    by_cases hk : k = k₀
    · rw [hk, hf', Function.update_self]; exact hv
    · rw [hf', Function.update_of_ne hk]; exact hσ'.1 _ (hfσ k)
  have hvf : ∀ k, IsRationalPoint (f k) := fun k => hσ'.1 _ (hfσ k)
  have hind := affInd_of_range hσ'.2 hr hinj
  have hind' := affInd_of_range hnew hr' hinj'
  rw [← ind_eq_indS hr, ← ind_eq_indS hr', ind_eq_natAbs_det hvf hind,
    ind_eq_natAbs_det hv' hind']
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i k => lift (f k) i with hW
  have hW' : (Matrix.of fun i k => lift (f' k) i) = W.updateCol k₀ (lift v) := by
    ext i k
    by_cases hk : k = k₀
    · subst hk; simp [hf', W]
    · simp [hf', W, Function.update_of_ne hk, Matrix.updateCol_ne hk]
  rw [hW']
  set c'' : Fin (n + 1) → ℝ := fun k => if f k ∈ τ then c (f k) else 0 with hc''
  have hmv : (fun i => (lift v i : ℝ)) = (W.map (Int.cast : ℤ → ℝ)) *ᵥ c'' := by
    funext i
    have := congrFun hrel i
    simp only [liftR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, W, Matrix.of_apply, c'']
    rw [sum_enum (fun p => (lift p i : ℝ) * if p ∈ τ then c p else 0) hr hinj]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hτσ]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  have hdet : (((W.updateCol k₀ (lift v)).det : ℤ) : ℝ) = c j * ((W.det : ℤ) : ℝ) := by
    have e : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
        ((M.det : ℤ) : ℝ) = (M.map (Int.cast : ℤ → ℝ)).det :=
      fun M => (Int.castRingHom ℝ).map_det M
    rw [e, e]
    have : (W.updateCol k₀ (lift v)).map (Int.cast : ℤ → ℝ) =
        (W.map (Int.cast : ℤ → ℝ)).updateCol k₀ (fun i => (lift v i : ℝ)) := by
      ext i k
      by_cases hk : k = k₀
      · subst hk; simp
      · simp [Matrix.updateCol_ne hk]
    rw [this, hmv, det_updateCol_mulVec']
    have hc0 : c'' k₀ = c j := by simp [c'', hk₀, hj]
    rw [hc0]
  have hWne : W.det ≠ 0 := det_lift_ne_zero hvf hind
  obtain ⟨hcpos, hclt⟩ := hc j hj
  have key : ((W.updateCol k₀ (lift v)).det.natAbs : ℝ) < (W.det.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs, hdet, abs_mul, abs_of_pos hcpos]
    have : (0 : ℝ) < |((W.det : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast hWne)
    nlinarith
  exact_mod_cast key

end CannonFloydParry.S7

/-!
# The point at which to star (Cannon–Floyd–Parry, p. 250)

For a rational `n`-simplex of index `> 1`, a rational point `v` whose lift is
`∑_{k ∈ J} c_k ṽ_k` with `0 < c_k < 1`.
-/

namespace CannonFloydParry.S7

open Finset Matrix

variable {n : ℕ}

lemma exists_key_point {f : Fin (n + 1) → Fin (n + 1) → ℝ} (hv : ∀ j, IsRationalPoint (f j))
    (hind : AffineIndependent ℝ f) (h1 : ind f ≠ 1) :
    ∃ (J : Finset (Fin (n + 1))) (v : Fin (n + 1) → ℝ) (c : Fin (n + 1) → ℝ),
      J.Nonempty ∧ IsRationalPoint v ∧ (∀ k ∈ J, 0 < c k ∧ c k < 1) ∧
        liftR v = ∑ k ∈ J, c k • liftR (f k) := by
  classical
  set H := AddSubgroup.closure (Set.range fun j => lift (f j)) with hH
  have hHtop : H ≠ ⊤ := fun h => h1 (by unfold ind; rw [← hH, h, AddSubgroup.index_top])
  obtain ⟨u, hu⟩ : ∃ u, u ∉ H := by
    by_contra hc
    push Not at hc
    exact hHtop (eq_top_iff.2 fun x _ => hc x)
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i k => lift (f k) i with hW
  set WR := W.map (Int.cast : ℤ → ℝ) with hWR
  have hdet : WR.det ≠ 0 := by
    have e : ((W.det : ℤ) : ℝ) = WR.det := (Int.castRingHom ℝ).map_det W
    rw [← e]
    exact_mod_cast det_lift_ne_zero hv hind
  set a : Fin (n + 1) → ℝ := WR⁻¹ *ᵥ (fun i => (u i : ℝ)) with ha_def
  have ha : ∀ i, (u i : ℝ) = ∑ k, a k * (lift (f k) i : ℝ) := by
    intro i
    have e : WR *ᵥ a = fun i => (u i : ℝ) := by
      rw [ha_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
        Matrix.one_mulVec]
    have := congrFun e i
    rw [← this]
    simp [Matrix.mulVec, dotProduct, WR, W, mul_comm]
  set c : Fin (n + 1) → ℝ := fun k => Int.fract (a k) with hc_def
  set u' : Fin (n + 1) → ℤ := u - ∑ k, ⌊a k⌋ • lift (f k) with hu'_def
  have hmemH : (∑ k, ⌊a k⌋ • lift (f k)) ∈ H :=
    AddSubgroup.sum_mem _ fun k _ =>
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (f := fun j => lift (f j)) k)) _
  have hu' : u' ∉ H := fun h => hu (by simpa [u'] using H.add_mem h hmemH)
  have hu'R : ∀ i, (u' i : ℝ) = ∑ k, c k * (lift (f k) i : ℝ) := by
    intro i
    simp only [u', Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub,
      Int.cast_sum, Int.cast_mul, ha i, c, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Int.self_sub_floor]
    ring
  have hu'0 : u' ≠ 0 := fun h => hu' (h ▸ H.zero_mem)
  have hc0 : ∀ k, 0 ≤ c k := fun k => Int.fract_nonneg _
  have hc1 : ∀ k, c k < 1 := fun k => Int.fract_lt_one _
  have hlnn : ∀ k i, (0 : ℝ) ≤ lift (f k) i := fun k i => by
    exact_mod_cast (lift_spec (hv k)).1 i
  have hu'nn : ∀ i, 0 ≤ u' i := fun i => by
    have : (0 : ℝ) ≤ u' i := by
      rw [hu'R]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (hlnn k i)
    exact_mod_cast this
  obtain ⟨p, hp, hpg⟩ := Finset.extract_gcd u' Finset.univ_nonempty
  set G := Finset.univ.gcd u' with hG
  have hGpos : 0 < G := by
    refine lt_of_le_of_ne (gcd_nonneg' u') (Ne.symm fun h0 => hu'0 ?_)
    funext i
    exact Finset.gcd_eq_zero_iff.1 h0 i (Finset.mem_univ _)
  have hpnn : ∀ i, 0 ≤ p i := fun i => by
    have := hu'nn i
    rw [hp i (Finset.mem_univ _)] at this
    exact (mul_nonneg_iff_of_pos_left hGpos).mp this
  set v := rho (fun i => (p i : ℝ)) with hv_def
  have hlv : lift v = p := lift_eq hpnn hpg
  have hvrat : IsRationalPoint v := by
    have hp0 : (fun i => (p i : ℝ)) ≠ 0 := by
      intro h0
      apply ne_zero_of_gcd_eq_one hpg
      funext i
      have := congrFun h0 i
      simpa using this
    refine ⟨rho_mem (fun i => by exact_mod_cast hpnn i) hp0, fun i => ?_⟩
    refine ⟨((∑ j, p j : ℤ) : ℚ)⁻¹ * (p i : ℚ), ?_⟩
    rw [hv_def, rho_intCast hpnn]
    push_cast
    simp
  have hGR : (1 : ℝ) ≤ G := by exact_mod_cast hGpos
  set J := Finset.univ.filter (fun k => 0 < c k) with hJ
  refine ⟨J, v, fun k => c k / G, ?_, hvrat, ?_, ?_⟩
  · by_contra hJe
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hJe
    apply hu'0
    funext i
    have : (u' i : ℝ) = 0 := by
      rw [hu'R]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : c k = 0 := le_antisymm (not_lt.1 (hJe (Finset.mem_univ k))) (hc0 k)
      rw [this, zero_mul]
    exact_mod_cast this
  · intro k hk
    have hk' : 0 < c k := (Finset.mem_filter.1 hk).2
    refine ⟨div_pos hk' (by linarith), ?_⟩
    rw [div_lt_one (by linarith)]
    linarith [hc1 k]
  · funext i
    simp only [liftR, hlv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_filter_of_ne (fun k _ hk => ?_)]
    · have e1 : (p i : ℝ) = (u' i : ℝ) / G := by
        rw [hp i (Finset.mem_univ _)]
        push_cast
        field_simp
      rw [e1, hu'R, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    · by_contra hck
      apply hk
      have : c k = 0 := le_antisymm (not_lt.1 hck) (hc0 k)
      rw [this]
      simp

/-- The barycentric weights of the starring point on its carrier face, and that it is not a
vertex of that face. -/
lemma exists_mu {τ : Finset (Fin (n + 1) → ℝ)} {v : Fin (n + 1) → ℝ}
    {c : (Fin (n + 1) → ℝ) → ℝ} (hτ : ∀ p ∈ τ, IsRationalPoint p) (hv : IsRationalPoint v)
    (hτind : AffineIndependent ℝ ((↑) : τ → Fin (n + 1) → ℝ))
    (hc : ∀ p ∈ τ, 0 < c p ∧ c p < 1) (hrel : liftR v = ∑ p ∈ τ, c p • liftR p) :
    ∃ μ : (Fin (n + 1) → ℝ) → ℝ, Bary τ μ v ∧ (∀ p ∈ τ, 0 < μ p) ∧ v ∉ τ := by
  classical
  set S : (Fin (n + 1) → ℝ) → ℝ := fun x => ∑ i, |(lift x i : ℝ)| with hS_def
  have hSpos : ∀ x, IsRationalPoint x → 0 < S x := by
    intro x hx
    obtain ⟨_, _, hg⟩ := lift_spec hx
    apply sum_abs_pos
    intro h0
    apply ne_zero_of_gcd_eq_one hg
    funext i
    have := congrFun h0 i
    simpa using this
  have hL : ∀ x, IsRationalPoint x → liftR x = S x • x := fun x hx => lift_col_real hx
  have hvec : S v • v = ∑ p ∈ τ, c p • S p • p := by
    rw [← hL v hv, hrel]
    exact Finset.sum_congr rfl fun p hp => by rw [hL p (hτ p hp)]
  have hsum1 : ∀ x : Fin (n + 1) → ℝ, IsRationalPoint x → ∑ i, x i = 1 := fun x hx => hx.1.2
  have hSv : S v = ∑ p ∈ τ, c p * S p := by
    have := congrArg (fun y : Fin (n + 1) → ℝ => ∑ i, y i) hvec
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
    rw [← Finset.mul_sum, hsum1 v hv, mul_one, Finset.sum_comm] at this
    rw [this]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum1 p (hτ p hp), mul_one]
  have hSv0 := hSpos v hv
  set μ : (Fin (n + 1) → ℝ) → ℝ := fun p => if p ∈ τ then c p * S p / S v else 0 with hμ
  have hμτ : ∀ p ∈ τ, μ p = c p * S p / S v := fun p hp => by simp [μ, hp]
  have hbary : Bary τ μ v := by
    refine ⟨fun p hp => by simp [μ, hp], fun p => ?_, ?_, ?_⟩
    · by_cases hp : p ∈ τ
      · rw [hμτ p hp]
        exact div_nonneg (mul_nonneg (hc p hp).1.le (hSpos p (hτ p hp)).le) hSv0.le
      · simp [μ, hp]
    · rw [Finset.sum_congr rfl hμτ, ← Finset.sum_div, ← hSv, div_self hSv0.ne']
    · rw [Finset.sum_congr rfl fun p hp => by rw [hμτ p hp]]
      have : ∑ p ∈ τ, (c p * S p / S v) • p = (S v)⁻¹ • ∑ p ∈ τ, c p • S p • p := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [smul_smul, smul_smul, div_eq_inv_mul, mul_assoc]
      rw [this, ← hvec, smul_smul, inv_mul_cancel₀ hSv0.ne', one_smul]
  have hpos : ∀ p ∈ τ, 0 < μ p := fun p hp => by
    rw [hμτ p hp]
    exact div_pos (mul_pos (hc p hp).1 (hSpos p (hτ p hp))) hSv0
  refine ⟨μ, hbary, hpos, fun hvτ => ?_⟩
  have hz := hτind.eq_zero_of_sum_eq_zero_subtype
    (w := fun p => μ p - if p = v then 1 else 0) (by
      rw [Finset.sum_sub_distrib, hbary.2.2.1, Finset.sum_ite_eq' τ v (fun _ => (1 : ℝ)),
        if_pos hvτ, sub_self]) (by
      simp only [sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib,
        hbary.2.2.2, Finset.sum_ite_eq' τ v (fun p => p), if_pos hvτ, sub_self])
    v hvτ
  simp only [sub_eq_zero] at hz
  rw [hμτ v hvτ, mul_div_assoc, div_self hSv0.ne', mul_one] at hz
  exact (hc v hvτ).2.ne hz

end CannonFloydParry.S7

/-!
# Cannon–Floyd–Parry, Theorem 7.1

Every rational subdivision of `Δₙ` has a refinement that is an integral subdivision: star at a
well-chosen rational point of an `n`-simplex of index `> 1`; the measure
`∑_σ (n + 2) ^ ind σ` over the `n`-simplices strictly decreases.
-/

namespace CannonFloydParry.S7

open Finset Geometry

variable {n : ℕ}

/-- The descent measure: `∑ (n + 2) ^ ind σ` over the `n`-simplices `σ` of `K`. -/
noncomputable def measure (K : SimplicialComplex ℝ (Fin (n + 1) → ℝ)) (h : K.faces.Finite) : ℕ :=
  ∑ s ∈ h.toFinset.filter (fun s => s.card = n + 1), (n + 2) ^ indS s

lemma refines_refl (K : SimplicialComplex ℝ (Fin (n + 1) → ℝ)) : Refines K K :=
  ⟨rfl, fun s hs => ⟨s, hs, subset_rfl⟩⟩

lemma refines_trans {K₁ K₂ K₃ : SimplicialComplex ℝ (Fin (n + 1) → ℝ)} (h₁ : Refines K₁ K₂)
    (h₂ : Refines K₂ K₃) : Refines K₁ K₃ := by
  refine ⟨h₁.1.trans h₂.1, fun s hs => ?_⟩
  obtain ⟨t, ht, hst⟩ := h₁.2 s hs
  obtain ⟨u, hu, htu⟩ := h₂.2 t ht
  exact ⟨u, hu, hst.trans htu⟩

lemma integral_of_all_one {K : SimplicialComplex ℝ (Fin (n + 1) → ℝ)}
    (hK : IsRationalSubdivision n K) (h : ∀ s ∈ K.faces, s.card = n + 1 → indS s = 1) :
    IsIntegralSubdivision n K :=
  ⟨hK.1, fun s hs hc => (indS_facts (hK.2 s hs hc) hc).2 (h s hs hc)⟩

lemma mem_simplex_of_face {K : SimplicialComplex ℝ (Fin (n + 1) → ℝ)} (hK : IsSubdivision n K)
    {s : Finset (Fin (n + 1) → ℝ)} (hs : s ∈ K.faces) {p : Fin (n + 1) → ℝ} (hp : p ∈ s) :
    p ∈ Simplex n := by
  rw [← hK.2]
  exact K.subset_space hs hp

lemma card_face_le {K : SimplicialComplex ℝ (Fin (n + 1) → ℝ)} (hK : IsSubdivision n K)
    {s : Finset (Fin (n + 1) → ℝ)} (hs : s ∈ K.faces) : s.card ≤ n + 1 :=
  card_le_of_affInd (K.indep hs) fun _ hp => mem_simplex_of_face hK hs hp

lemma erase_union_eq {σ τ : Finset (Fin (n + 1) → ℝ)} {j : Fin (n + 1) → ℝ} (hτσ : τ ⊆ σ)
    (hj : j ∈ τ) : σ.erase j ∪ τ = σ := by
  ext p
  simp only [mem_union, mem_erase]
  constructor
  · rintro (⟨-, h⟩ | h)
    · exact h
    · exact hτσ h
  · intro h
    by_cases hpj : p = j
    · exact Or.inr (hpj ▸ hj)
    · exact Or.inl ⟨hpj, h⟩

/-- An `n`-simplex of the starred complex through `v` comes from an `n`-simplex of `K`
containing `τ`, with one vertex of `τ` replaced by `v`. -/
lemma classify_B {K : SimplicialComplex ℝ (Fin (n + 1) → ℝ)} (hK : IsSubdivision n K)
    {τ t : Finset (Fin (n + 1) → ℝ)} {v : Fin (n + 1) → ℝ} (hvt : v ∉ t) (ht : ¬ τ ⊆ t)
    (hu : t ∪ τ ∈ K.faces) (hc : (insert v t).card = n + 1) :
    (t ∪ τ).card = n + 1 ∧ ∃ j ∈ τ, t = (t ∪ τ).erase j := by
  rw [card_insert_of_notMem hvt] at hc
  have hle := card_face_le hK hu
  obtain ⟨j, hjτ, hjt⟩ := not_subset.1 ht
  have hju : j ∈ t ∪ τ := mem_union_right _ hjτ
  have hsub : t ⊆ (t ∪ τ).erase j := fun p hp =>
    mem_erase.2 ⟨fun h => hjt (h ▸ hp), mem_union_left _ hp⟩
  have hcard := card_erase_of_mem hju
  have heq : t = (t ∪ τ).erase j := eq_of_subset_of_card_le hsub (by omega)
  refine ⟨?_, j, hjτ, heq⟩
  have h2 : #t ≤ #(t ∪ τ) - 1 := hcard ▸ card_le_card hsub
  have h3 := card_pos.2 ⟨j, hju⟩
  clear heq hsub hcard
  omega

/-- One starring step. -/
lemma step {K : SimplicialComplex ℝ (Fin (n + 1) → ℝ)} (hK : IsRationalSubdivision n K)
    {σ : Finset (Fin (n + 1) → ℝ)} (hσ : σ ∈ K.faces) (hc : σ.card = n + 1) (h1 : indS σ ≠ 1) :
    ∃ (K' : SimplicialComplex ℝ (Fin (n + 1) → ℝ)) (hK' : IsRationalSubdivision n K'),
      Refines K' K ∧ measure K' hK'.1.1 < measure K hK.1.1 := by
  have hσr := hK.2 σ hσ hc
  obtain ⟨f, hinj, hr⟩ := exists_enum hc
  have hfσ : ∀ k, f k ∈ σ := fun k => by rw [← mem_coe, ← hr]; exact Set.mem_range_self k
  have hvf : ∀ k, IsRationalPoint (f k) := fun k => hσr.1 _ (hfσ k)
  have hind := affInd_of_range hσr.2 hr hinj
  obtain ⟨J, v, c, hJ, hv, hc01, hrel⟩ :=
    exists_key_point hvf hind (by rw [ind_eq_indS hr]; exact h1)
  set τ := J.image f with hτ_def
  set c' : (Fin (n + 1) → ℝ) → ℝ := fun p => c (Function.invFun f p) with hc'_def
  have hc'f : ∀ k, c' (f k) = c k := fun k => by
    simp only [c']
    rw [Function.leftInverse_invFun hinj k]
  have hτσ : τ ⊆ σ := fun p hp => by
    obtain ⟨k, -, rfl⟩ := mem_image.1 hp
    exact hfσ k
  have hτK : τ ∈ K.faces := K.down_closed hσ hτσ (hJ.image f)
  have hrel' : liftR v = ∑ p ∈ τ, c' p • liftR p := by
    rw [hrel, hτ_def, sum_image (fun a _ b _ h => hinj h)]
    exact sum_congr rfl fun k _ => by rw [hc'f]
  have hc' : ∀ p ∈ τ, 0 < c' p ∧ c' p < 1 := fun p hp => by
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hp
    rw [hc'f]
    exact hc01 k hk
  have hτrat : ∀ p ∈ τ, IsRationalPoint p := fun p hp => hσr.1 p (hτσ hp)
  obtain ⟨μ, hμ, hμpos, hvτ⟩ := exists_mu hτrat hv (K.indep hτK) hc' hrel'
  have hd : StarData K τ v μ := ⟨hτK, hμ, hμpos, hvτ⟩
  have hfin' := hd.finite_star hK.1.1
  have hsub' : IsSubdivision n (star hd) := ⟨hfin', by rw [hd.space_star, hK.1.2]⟩
  -- the new `n`-simplices
  have hnewmem : ∀ σ' ∈ K.faces, τ ⊆ σ' → ∀ j ∈ τ, insert v (σ'.erase j) ∈ (star hd).faces :=
    fun σ' hσ' hτσ' j hj => Or.inr ⟨σ'.erase j, fun h => notMem_erase j σ' (h hj),
      by rw [erase_union_eq hτσ' hj]; exact hσ', rfl⟩
  have hrat' : IsRationalSubdivision n (star hd) := by
    refine ⟨hsub', fun s hs hcs => ?_⟩
    rcases hs with ⟨hs, -⟩ | ⟨t, ht, hu, rfl⟩
    · exact hK.2 s hs hcs
    · have hvt := hd.v_notMem_of_union hu
      obtain ⟨hcu, -⟩ := classify_B hK.1 hvt ht hu hcs
      have hur := hK.2 _ hu hcu
      refine ⟨fun p hp => ?_, (star hd).indep (Or.inr ⟨t, ht, hu, rfl⟩)⟩
      rcases mem_insert.1 hp with rfl | hp
      · exact hv
      · exact hur.1 p (mem_union_left _ hp)
  refine ⟨star hd, hrat', ⟨by rw [hd.space_star], fun s hs => hd.refines_faces hs⟩, ?_⟩
  -- the measure decreases
  set F := hK.1.1.toFinset.filter (fun s => s.card = n + 1) with hF
  set F' := hfin'.toFinset.filter (fun s => s.card = n + 1) with hF'
  set FA := F.filter (fun s => ¬ τ ⊆ s) with hFA
  set FT := F.filter (fun s => τ ⊆ s) with hFT
  set g : Finset (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) → Finset (Fin (n + 1) → ℝ) :=
    fun q => insert v (q.1.erase q.2) with hg
  set P := FT ×ˢ τ with hP
  set wt : Finset (Fin (n + 1) → ℝ) → ℕ := fun s => (n + 2) ^ indS s with hwt
  have hsubset : F' ⊆ FA ∪ P.image g := by
    intro s hs
    rw [hF', mem_filter, Set.Finite.mem_toFinset] at hs
    obtain ⟨hs, hcs⟩ := hs
    rcases hs with ⟨hs, hτs⟩ | ⟨t, ht, hu, rfl⟩
    · refine mem_union_left _ ?_
      rw [hFA, mem_filter, hF, mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hs, hcs⟩, hτs⟩
    · refine mem_union_right _ ?_
      have hvt := hd.v_notMem_of_union hu
      obtain ⟨hcu, j, hj, hteq⟩ := classify_B hK.1 hvt ht hu hcs
      refine mem_image.2 ⟨(t ∪ τ, j), ?_, ?_⟩
      · rw [hP, mem_product, hFT, mem_filter, hF, mem_filter, Set.Finite.mem_toFinset]
        exact ⟨⟨⟨hu, hcu⟩, subset_union_right⟩, hj⟩
      · simp only [g]
        rw [← hteq]
  have hlt_each : ∀ σ' ∈ FT, ∑ j ∈ τ, wt (g (σ', j)) < wt σ' := by
    intro σ' hσ'
    rw [hFT, mem_filter, hF, mem_filter, Set.Finite.mem_toFinset] at hσ'
    obtain ⟨⟨hσ'K, hσ'c⟩, hτσ'⟩ := hσ'
    have hσ'r := hK.2 σ' hσ'K hσ'c
    have hd0 := (indS_facts hσ'r hσ'c).1
    have hbound : ∀ j ∈ τ, wt (g (σ', j)) ≤ (n + 2) ^ (indS σ' - 1) := by
      intro j hj
      have hlt := indS_insert_erase_lt hσ'r hσ'c hτσ' hj hv (hd.v_notMem hσ'K) hc' hrel'
        ((star hd).indep (hnewmem σ' hσ'K hτσ' j hj))
      exact Nat.pow_le_pow_right (by omega) (by simp only [g]; omega)
    have hτcard : τ.card ≤ n + 1 := (card_le_card hτσ').trans hσ'c.le
    calc ∑ j ∈ τ, wt (g (σ', j)) ≤ τ.card • (n + 2) ^ (indS σ' - 1) :=
          sum_le_card_nsmul _ _ _ hbound
      _ ≤ (n + 1) * (n + 2) ^ (indS σ' - 1) := by
          rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hτcard
      _ < (n + 2) * (n + 2) ^ (indS σ' - 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = wt σ' := by
          simp only [wt]
          rw [← pow_succ']
          congr 1
          omega
  have hσFT : σ ∈ FT := by
    rw [hFT, mem_filter, hF, mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hσ, hc⟩, hτσ⟩
  have hsplit : measure K hK.1.1 = ∑ s ∈ FA, wt s + ∑ s ∈ FT, wt s := by
    exact (sum_filter_add_sum_filter_not F (fun s => τ ⊆ s) wt).symm.trans (add_comm _ _)
  have h1' : measure (star hd) hrat'.1.1 ≤ ∑ s ∈ FA ∪ P.image g, wt s :=
    sum_le_sum_of_subset hsubset
  have h2' : ∑ s ∈ FA ∪ P.image g, wt s ≤ ∑ s ∈ FA, wt s + ∑ s ∈ P.image g, wt s := by
    have := sum_union_inter (s₁ := FA) (s₂ := P.image g) (f := wt)
    omega
  have h3' : ∑ s ∈ P.image g, wt s ≤ ∑ q ∈ P, wt (g q) :=
    sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
  have h4' : ∑ q ∈ P, wt (g q) < ∑ s ∈ FT, wt s := by
    rw [hP, sum_product]
    exact sum_lt_sum_of_nonempty ⟨σ, hσFT⟩ hlt_each
  omega

theorem exists_refines_isIntegralSubdivision' {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)} (hK : IsRationalSubdivision n K) :
    ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
      Refines K' K ∧ IsIntegralSubdivision n K' := by
  suffices h : ∀ N, ∀ (K : SimplicialComplex ℝ (Fin (n + 1) → ℝ))
      (hK : IsRationalSubdivision n K), measure K hK.1.1 < N →
        ∃ K' : SimplicialComplex ℝ (Fin (n + 1) → ℝ), Refines K' K ∧ IsIntegralSubdivision n K' from
    h _ K hK (Nat.lt_succ_self _)
  intro N
  induction N with
  | zero => intro K hK h; omega
  | succ N ih =>
    intro K hK hN
    by_cases hall : ∀ s ∈ K.faces, s.card = n + 1 → indS s = 1
    · exact ⟨K, refines_refl K, integral_of_all_one hK hall⟩
    · push Not at hall
      obtain ⟨σ, hσ, hc, h1⟩ := hall
      obtain ⟨K', hK', hR, hlt⟩ := step hK hσ hc h1
      obtain ⟨K'', hR', hI⟩ := ih K' hK' (by omega)
      exact ⟨K'', refines_trans hR' hR, hI⟩

end CannonFloydParry.S7

open CannonFloydParry in
theorem solution {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)} (hK : IsRationalSubdivision n K) :
    ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
      Refines K' K ∧ IsIntegralSubdivision n K' := by
  exact S7.exists_refines_isIntegralSubdivision' hK
