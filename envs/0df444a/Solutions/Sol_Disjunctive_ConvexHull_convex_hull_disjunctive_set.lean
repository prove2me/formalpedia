-- Prove2me | solution 1 for Disjunctive.ConvexHull.convex_hull_disjunctive_set
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:41:08.207977+00:00
-- url     : https://prove2.me/submissions/0f9e901a-892c-4a12-b6ca-cfb96ca4c019

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

set_option autoImplicit false

namespace P2MD6F

/-- A set cut out by finitely many linear inequalities. -/
def Polyh {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) : Prop :=
  ∃ s : Finset ((V →ₗ[ℝ] ℝ) × ℝ), S = {x | ∀ p ∈ s, p.2 ≤ p.1 x}

section basic
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma polyh_half (f : V →ₗ[ℝ] ℝ) (g : ℝ) : Polyh {x : V | g ≤ f x} :=
  ⟨{(f, g)}, by ext x; simp⟩

lemma polyh_inter {S T : Set V} (hS : Polyh S) (hT : Polyh T) : Polyh (S ∩ T) := by
  classical
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hT
  refine ⟨s ∪ t, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ p (hp | hp)
    · exact h1 p hp
    · exact h2 p hp
  · intro h
    exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩

lemma polyh_iInter {ι : Type*} [Fintype ι] (S : ι → Set V) (h : ∀ i, Polyh (S i)) :
    Polyh (⋂ i, S i) := by
  classical
  choose s hs using h
  refine ⟨Finset.univ.biUnion s, ?_⟩
  ext x
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro hx p ⟨i, hp⟩
    have := hx i
    rw [hs i] at this
    exact this p hp
  · intro hx i
    rw [hs i]
    exact fun p hp => hx p ⟨i, hp⟩

lemma polyh_eq (f : V →ₗ[ℝ] ℝ) (g : ℝ) : Polyh {x : V | f x = g} := by
  have : {x : V | f x = g} = {x | g ≤ f x} ∩ {x | -g ≤ (-f) x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, LinearMap.neg_apply, neg_le_neg_iff]
    constructor
    · intro h; exact ⟨h.ge, h.le⟩
    · intro h; exact le_antisymm h.2 h.1
  rw [this]
  exact polyh_inter (polyh_half _ _) (polyh_half _ _)

lemma polyh_vec_ge {ι : Type*} [Fintype ι] (φ : V →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) :
    Polyh {x : V | c ≤ φ x} := by
  have : {x : V | c ≤ φ x} = ⋂ i, {x | c i ≤ (LinearMap.proj i ∘ₗ φ) x} := by
    ext x
    simp [Pi.le_def]
  rw [this]
  exact polyh_iInter _ (fun i => polyh_half _ _)

lemma polyh_vec_eq {ι : Type*} [Fintype ι] (φ : V →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) :
    Polyh {x : V | φ x = c} := by
  have : {x : V | φ x = c} = ⋂ i, {x | (LinearMap.proj i ∘ₗ φ) x = c i} := by
    ext x
    simp [funext_iff]
  rw [this]
  exact polyh_iInter _ (fun i => polyh_eq _ _)

lemma polyh_preimage {W : Type*} [AddCommGroup W] [Module ℝ W] (L : W →ₗ[ℝ] V) {S : Set V}
    (hS : Polyh S) : Polyh (L ⁻¹' S) := by
  classical
  obtain ⟨s, rfl⟩ := hS
  refine ⟨s.image (fun p => (p.1 ∘ₗ L, p.2)), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Finset.mem_image]
  constructor
  · rintro hx q ⟨p, hp, rfl⟩
    exact hx p hp
  · intro hx p hp
    exact hx _ ⟨p, hp, rfl⟩

lemma polyh_convex {S : Set V} (hS : Polyh S) : Convex ℝ S := by
  obtain ⟨s, rfl⟩ := hS
  have : {x : V | ∀ p ∈ s, p.2 ≤ p.1 x} = ⋂ p ∈ s, {x | p.2 ≤ p.1 x} := by
    ext x; simp
  rw [this]
  exact convex_iInter₂ fun p _ => convex_halfSpace_ge p.1.isLinear p.2

end basic

lemma polyh_isClosed {n : ℕ} {S : Set (Fin n → ℝ)} (hS : Polyh S) : IsClosed S := by
  obtain ⟨s, rfl⟩ := hS
  have : {x : Fin n → ℝ | ∀ p ∈ s, p.2 ≤ p.1 x} = ⋂ p ∈ s, {x | p.2 ≤ p.1 x} := by
    ext x; simp
  rw [this]
  exact isClosed_biInter fun p _ =>
    isClosed_le continuous_const (LinearMap.continuous_of_finiteDimensional p.1)

lemma exists_between_finsets {α : Type*} (P N : Finset α) (l w : α → ℝ)
    (h : ∀ p ∈ P, ∀ q ∈ N, l p ≤ w q) : ∃ t, (∀ p ∈ P, l p ≤ t) ∧ ∀ q ∈ N, t ≤ w q := by
  by_cases hP : P.Nonempty
  · exact ⟨P.sup' hP l, fun p hp => Finset.le_sup' l hp,
      fun q hq => Finset.sup'_le hP l (fun p hp => h p hp q hq)⟩
  · refine ⟨-∑ q ∈ N, |w q|, fun p hp => absurd ⟨p, hp⟩ hP, fun q hq => ?_⟩
    have h1 := Finset.single_le_sum (f := fun q => |w q|) (fun q _ => abs_nonneg (w q)) hq
    have h2 := neg_abs_le (w q)
    linarith

/-- One step of Fourier–Motzkin elimination. -/
lemma polyh_elim_one {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set (E × ℝ)}
    (hS : Polyh S) : Polyh (Prod.fst '' S) := by
  classical
  obtain ⟨s, rfl⟩ := hS
  set a : ((E × ℝ →ₗ[ℝ] ℝ) × ℝ) → (E →ₗ[ℝ] ℝ) := fun q => q.1 ∘ₗ LinearMap.inl ℝ E ℝ with ha
  set c : ((E × ℝ →ₗ[ℝ] ℝ) × ℝ) → ℝ := fun q => q.1 ((0 : E), (1 : ℝ)) with hc
  have key : ∀ q : (E × ℝ →ₗ[ℝ] ℝ) × ℝ, ∀ x : E, ∀ t : ℝ, q.1 (x, t) = a q x + t * c q := by
    intro q x t
    have : ((x, t) : E × ℝ) = LinearMap.inl ℝ E ℝ x + t • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul]
    simp [ha, hc, smul_eq_mul]
  refine ⟨(s.filter (fun q => c q = 0)).image (fun q => (a q, q.2)) ∪
      ((s.filter (fun q => 0 < c q)) ×ˢ (s.filter (fun q => c q < 0))).image
        (fun pq => (c pq.1 • a pq.2 - c pq.2 • a pq.1, c pq.1 * pq.2.2 - c pq.2 * pq.1.2)), ?_⟩
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨x', t⟩, hS, rfl⟩ r hr
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
      Prod.exists] at hr
    rcases hr with ⟨f, g, ⟨hq, hcq⟩, rfl⟩ | ⟨f1, g1, f2, g2, ⟨⟨hp, hcp⟩, ⟨hq, hcq⟩⟩, rfl⟩
    · have := hS (f, g) hq
      rw [key] at this
      simp only at hcq this ⊢
      rw [hcq] at this
      linarith
    · have h1 := hS (f1, g1) hp
      have h2 := hS (f2, g2) hq
      rw [key] at h1 h2
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h1 h2 hcp hcq ⊢
      nlinarith [mul_le_mul_of_nonneg_left h2 hcp.le, mul_le_mul_of_nonneg_left h1 (neg_nonneg.mpr hcq.le)]
  · intro hx
    obtain ⟨t, ht1, ht2⟩ := exists_between_finsets (s.filter (fun q => 0 < c q))
      (s.filter (fun q => c q < 0)) (fun q => (q.2 - a q x) / c q) (fun q => (q.2 - a q x) / c q)
      (by
        intro p hp q hq
        rw [Finset.mem_filter] at hp hq
        have h := hx _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _
          (Finset.mk_mem_product (Finset.mem_filter.mpr hp) (Finset.mem_filter.mpr hq))))
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
        rw [div_le_iff₀ hp.2]
        set u := (q.2 - a q x) / c q with hu
        have hu' : u * c q = q.2 - a q x := by
          rw [hu]; field_simp [hq.2.ne]
        by_contra hcon
        rw [not_le] at hcon
        nlinarith [mul_lt_mul_of_neg_left hcon hq.2])
    refine ⟨(x, t), ?_, rfl⟩
    intro q hq
    rw [key]
    rcases lt_trichotomy (c q) 0 with hneg | hz | hpos
    · have := ht2 q (Finset.mem_filter.mpr ⟨hq, hneg⟩)
      rw [le_div_iff_of_neg hneg] at this
      linarith
    · have h := hx _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (Finset.mem_filter.mpr ⟨hq, hz⟩)))
      simp only at h
      rw [hz]
      linarith
    · have := ht1 q (Finset.mem_filter.mpr ⟨hq, hpos⟩)
      rw [div_le_iff₀ hpos] at this
      linarith

lemma polyh_elim_fin.{u} (k : ℕ) : ∀ {E : Type u} [AddCommGroup E] [Module ℝ E]
    (S : Set (E × (Fin k → ℝ))), Polyh S → Polyh (Prod.fst '' S) := by
  induction k with
  | zero =>
    intro E _ _ S hS
    have : Prod.fst '' S = (LinearMap.inl ℝ E (Fin 0 → ℝ)) ⁻¹' S := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, LinearMap.inl_apply]
      constructor
      · rintro ⟨⟨x', y⟩, h, rfl⟩
        have : y = 0 := Subsingleton.elim _ _
        subst this
        exact h
      · intro h
        exact ⟨(x, 0), h, rfl⟩
    rw [this]
    exact polyh_preimage _ hS
  | succ k ih =>
    intro E _ _ S hS
    let ψ : ((E × ℝ) × (Fin k → ℝ)) →ₗ[ℝ] (E × (Fin (k + 1) → ℝ)) :=
      { toFun := fun q => (q.1.1, Fin.cons q.1.2 q.2)
        map_add' := by
          rintro ⟨⟨x1, t1⟩, y1⟩ ⟨⟨x2, t2⟩, y2⟩
          refine Prod.ext (by simp) (funext fun i => ?_)
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := by
          rintro r ⟨⟨x1, t1⟩, y1⟩
          refine Prod.ext (by simp) (funext fun i => ?_)
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    have h1 : Polyh (ψ ⁻¹' S) := polyh_preimage ψ hS
    have h2 : Polyh (Prod.fst '' (ψ ⁻¹' S)) := ih (E := E × ℝ) _ h1
    have h3 := polyh_elim_one h2
    have : Prod.fst '' (Prod.fst '' (ψ ⁻¹' S)) = Prod.fst '' S := by
      ext x
      constructor
      · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
        exact ⟨ψ q, hq, rfl⟩
      · rintro ⟨⟨x, y⟩, hS, rfl⟩
        refine ⟨(x, y 0), ⟨((x, y 0), Fin.tail y), ?_, rfl⟩, rfl⟩
        show (x, Fin.cons (y 0) (Fin.tail y)) ∈ S
        rw [Fin.cons_self_tail]
        exact hS
    rw [← this]
    exact h3

lemma polyh_elim_fd {E : Type*} [AddCommGroup E] [Module ℝ E] {F : Type*} [AddCommGroup F]
    [Module ℝ F] [FiniteDimensional ℝ F] {S : Set (E × F)} (hS : Polyh S) :
    Polyh (Prod.fst '' S) := by
  let e := (Module.finBasis ℝ F).equivFun
  let ψ : (E × (Fin (Module.finrank ℝ F) → ℝ)) →ₗ[ℝ] (E × F) :=
    LinearMap.prodMap LinearMap.id (e.symm : (Fin (Module.finrank ℝ F) → ℝ) →ₗ[ℝ] F)
  have h1 : Polyh (ψ ⁻¹' S) := polyh_preimage ψ hS
  have h2 := polyh_elim_fin _ _ h1
  have : Prod.fst '' (ψ ⁻¹' S) = Prod.fst '' S := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨ψ q, hq, rfl⟩
    · rintro ⟨⟨x, y⟩, hS, rfl⟩
      refine ⟨(x, e y), ?_, rfl⟩
      show (x, e.symm (e y)) ∈ S
      rw [LinearEquiv.symm_apply_apply]
      exact hS
  rw [← this]
  exact h2

open Disjunctive.ConvexHull in
lemma polyh_lifted {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) (Qidx : Set Q) :
    Polyh (LiftedPolyhedron m A b Qidx) := by
  classical
  let LX : ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun p => p.1 - ∑ h, p.2.1 h
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
        abel
      map_smul' := by
        intro r p
        simp [Finset.smul_sum, smul_sub] }
  let LT : ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) →ₗ[ℝ] ℝ :=
    { toFun := fun p => ∑ h, p.2.2 h
      map_add' := by
        intro p q
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro r p
        simp [Finset.mul_sum] }
  let LC : (h : Q) → ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) →ₗ[ℝ] (Fin (m h) → ℝ) :=
    fun h =>
    { toFun := fun p => (A h).mulVec (p.2.1 h) - p.2.2 h • b h
      map_add' := by
        intro p q
        simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Matrix.mulVec_add, add_smul]
        abel
      map_smul' := by
        intro r p
        simp [Matrix.mulVec_smul, smul_sub, smul_smul] }
  let Ly : (h : Q) → ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) →ₗ[ℝ] (Fin n → ℝ) :=
    fun h => LinearMap.proj h ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _
  let Lt : (h : Q) → ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) →ₗ[ℝ] ℝ :=
    fun h => LinearMap.proj h ∘ₗ LinearMap.snd ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _
  let B : Q → Set ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) := fun h =>
    if h ∈ Qidx then {p | 0 ≤ LC h p} ∩ {p | 0 ≤ Lt h p}
    else {p | Ly h p = 0} ∩ {p | Lt h p = 0}
  have hB : ∀ h, Polyh (B h) := by
    intro h
    by_cases hh : h ∈ Qidx
    · simp only [B, hh, if_true]
      exact polyh_inter (polyh_vec_ge _ _) (polyh_half _ _)
    · simp only [B, hh, if_false]
      exact polyh_inter (polyh_vec_eq _ _) (polyh_eq _ _)
  have hEq : LiftedPolyhedron m A b Qidx =
      ({p | LX p = 0} ∩ {p | LT p = 1}) ∩ ⋂ h, B h := by
    ext p
    simp only [LiftedPolyhedron, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨?_, h4⟩, fun h => ?_⟩
      · show p.1 - ∑ h, p.2.1 h = 0
        rw [h1, sub_self]
      · by_cases hh : h ∈ Qidx
        · simp only [B, hh, if_true]
          exact ⟨(h2 h hh).1, (h2 h hh).2⟩
        · simp only [B, hh, if_false]
          exact ⟨(h3 h hh).1, (h3 h hh).2⟩
    · rintro ⟨⟨h1, h4⟩, hb⟩
      refine ⟨sub_eq_zero.mp h1, fun h hh => ?_, fun h hh => ?_, h4⟩
      · have := hb h
        simp only [B, hh, if_true] at this
        exact ⟨this.1, this.2⟩
      · have := hb h
        simp only [B, hh, if_false] at this
        exact ⟨this.1, this.2⟩
  rw [hEq]
  exact polyh_inter (polyh_inter (polyh_vec_eq _ _) (polyh_eq _ _)) (polyh_iInter _ hB)

end P2MD6F

open Disjunctive.ConvexHull in
theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) :
    closure (convexHull ℝ (DisjunctiveSet m A b)) =
      ProjX (LiftedPolyhedron m A b (FeasibleIndices m A b)) := by
  classical
  have hProj : ProjX (LiftedPolyhedron m A b (FeasibleIndices m A b)) =
      Prod.fst '' (LiftedPolyhedron m A b (FeasibleIndices m A b)) := by
    ext x
    simp [ProjX]
  have hP : P2MD6F.Polyh (ProjX (LiftedPolyhedron m A b (FeasibleIndices m A b))) := by
    rw [hProj]
    exact P2MD6F.polyh_elim_fd (P2MD6F.polyh_lifted m A b _)
  apply subset_antisymm
  · apply closure_minimal _ (P2MD6F.polyh_isClosed hP)
    apply convexHull_min _ (P2MD6F.polyh_convex hP)
    intro x hx
    simp only [DisjunctiveSet, Set.mem_iUnion] at hx
    obtain ⟨h, hx⟩ := hx
    have hfe : h ∈ FeasibleIndices m A b := ⟨x, hx⟩
    refine ⟨(Pi.single h x, Pi.single h 1), ?_, ?_, ?_, ?_⟩
    · simp
    · intro h' hh'
      by_cases hne : h' = h
      · subst hne
        refine ⟨?_, by simp⟩
        intro i
        have := hx i
        simp only [Pi.single_eq_same, one_smul, Pi.zero_apply, Pi.sub_apply]
        linarith
      · simp [Pi.single_eq_of_ne hne]
    · intro h' hh'
      have hne : h' ≠ h := fun e => hh' (e ▸ hfe)
      simp [Pi.single_eq_of_ne hne]
    · simp
  · rintro x ⟨⟨y, t⟩, hx, hfeas, hout, ht⟩
    simp only at hx hfeas hout ht
    set QS := FeasibleIndices m A b with hQS
    set S : Finset Q := Finset.univ.filter (fun h => h ∈ QS) with hS
    have hsumS : ∀ f : Q → Fin n → ℝ, (∀ h, h ∉ QS → f h = 0) → ∑ h, f h = ∑ h ∈ S, f h := by
      intro f hf
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun h _ => ?_
      split_ifs with hh
      · rfl
      · exact hf h hh
    have hsumT : ∑ h ∈ S, t h = 1 := by
      rw [← ht, hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun h _ => ?_
      split_ifs with hh
      · rfl
      · exact ((hout h hh).2).symm
    have hxS : x = ∑ h ∈ S, y h := by
      rw [hx]; exact hsumS y (fun h hh => (hout h hh).1)
    have hSne : S.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty] at hsumT
      exact zero_ne_one hsumT
    set k : ℝ := (S.card : ℝ) with hk
    have hkpos : 0 < k := by
      rw [hk]; exact_mod_cast hSne.card_pos
    let pt : Q → Fin n → ℝ := fun h =>
      if hh : h ∈ QS then (show (Poly (A h) (b h)).Nonempty from hh).some else 0
    have hpt : ∀ h ∈ QS, pt h ∈ Poly (A h) (b h) := by
      intro h hh
      simp only [pt, hh, dif_pos]
      exact (show (Poly (A h) (b h)).Nonempty from hh).some_mem
    set c : Fin n → ℝ := k⁻¹ • ∑ h ∈ S, pt h with hc
    have hmem : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (1 - ε) • x + ε • c ∈ convexHull ℝ (DisjunctiveSet m A b) := by
      intro ε hε0 hε1
      let lam : Q → ℝ := fun h => (1 - ε) * t h + ε / k
      let q : Q → Fin n → ℝ := fun h => (lam h)⁻¹ • ((1 - ε) • y h + (ε / k) • pt h)
      have hlam : ∀ h ∈ S, 0 < lam h := by
        intro h hh
        have hh' : h ∈ QS := (Finset.mem_filter.mp hh).2
        have := (hfeas h hh').2
        have h1 : 0 ≤ (1 - ε) * t h := mul_nonneg (by linarith) this
        have h2 : 0 < ε / k := div_pos hε0 hkpos
        show 0 < (1 - ε) * t h + ε / k
        linarith
      have hsum : ∑ h ∈ S, lam h • q h = (1 - ε) • x + ε • c := by
        have : ∀ h ∈ S, lam h • q h = (1 - ε) • y h + (ε / k) • pt h := by
          intro h hh
          exact smul_inv_smul₀ (hlam h hh).ne' _
        rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.smul_sum,
          ← Finset.smul_sum, ← hxS, hc, smul_smul, div_eq_mul_inv]
      rw [← hsum]
      refine (convex_convexHull ℝ _).sum_mem (fun h hh => (hlam h hh).le) ?_ ?_
      · show ∑ h ∈ S, ((1 - ε) * t h + ε / k) = 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumT, Finset.sum_const, nsmul_eq_mul,
          ← hk]
        field_simp
        ring
      · intro h hh
        apply subset_convexHull
        simp only [DisjunctiveSet, Set.mem_iUnion]
        refine ⟨h, ?_⟩
        have hh' : h ∈ QS := (Finset.mem_filter.mp hh).2
        intro i
        have hy := (hfeas h hh').1 i
        have hp := hpt h hh' i
        simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hy
        simp only [q, Matrix.mulVec_smul, Matrix.mulVec_add, Pi.smul_apply, Pi.add_apply,
          smul_eq_mul]
        rw [le_inv_mul_iff₀ (hlam h hh)]
        show ((1 - ε) * t h + ε / k) * b h i ≤ _
        have e1 : 0 ≤ 1 - ε := by linarith
        have e2 : 0 ≤ ε / k := (div_pos hε0 hkpos).le
        nlinarith [mul_le_mul_of_nonneg_left (show t h * b h i ≤ ((A h).mulVec (y h)) i by linarith) e1,
          mul_le_mul_of_nonneg_left hp e2]
    have hcont : Continuous (fun ε : ℝ => (1 - ε) • x + ε • c) := by fun_prop
    have htend : Filter.Tendsto (fun j : ℕ => (1 - 1 / ((j : ℝ) + 1)) • x + (1 / ((j : ℝ) + 1)) • c)
        Filter.atTop (nhds x) := by
      have h0 : ((1 : ℝ) - 0) • x + (0 : ℝ) • c = x := by simp
      have := (hcont.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [h0] at this
      exact this
    refine mem_closure_of_tendsto htend (Filter.Eventually.of_forall fun j => hmem _ ?_ ?_)
    · positivity
    · rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
