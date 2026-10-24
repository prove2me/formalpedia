-- Prove2me | solution 1 for Disjunctive.ConvexHull.tightness_lifted_representation_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:29:56.304458+00:00
-- url     : https://prove2.me/submissions/367ee671-5d7c-4e98-b654-0f98eb2ee396

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

namespace DK88
open Set

def IsPoly {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : Prop :=
  ∃ s : Set (Module.Dual ℝ E × ℝ), s.Finite ∧ S = {v | ∀ p ∈ s, p.2 ≤ p.1 v}

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma IsPoly.inter {S T : Set E} (hS : IsPoly S) (hT : IsPoly T) : IsPoly (S ∩ T) := by
  obtain ⟨s, hs, rfl⟩ := hS; obtain ⟨t, ht, rfl⟩ := hT
  refine ⟨s ∪ t, hs.union ht, ?_⟩
  ext v; simp only [mem_inter_iff, mem_setOf_eq, mem_union]
  constructor
  · rintro ⟨h1, h2⟩ p (hp | hp); exacts [h1 p hp, h2 p hp]
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩

lemma IsPoly.iInter {ι : Type*} [Finite ι] {S : ι → Set E} (hS : ∀ i, IsPoly (S i)) :
    IsPoly (⋂ i, S i) := by
  choose s hs hS using hS
  refine ⟨⋃ i, s i, finite_iUnion hs, ?_⟩
  ext v; simp only [mem_iInter, hS, mem_setOf_eq, mem_iUnion]
  constructor
  · rintro h p ⟨i, hp⟩; exact h i p hp
  · intro h i p hp; exact h p ⟨i, hp⟩

lemma IsPoly.half (f : Module.Dual ℝ E) (c : ℝ) : IsPoly {v | c ≤ f v} :=
  ⟨{(f, c)}, finite_singleton _, by ext; simp⟩

lemma IsPoly.eq (f : Module.Dual ℝ E) (c : ℝ) : IsPoly {v | f v = c} := by
  have := (IsPoly.half f c).inter (IsPoly.half (-f) (-c))
  convert this using 1
  ext v; simp only [mem_setOf_eq, mem_inter_iff, LinearMap.neg_apply]
  constructor
  · intro h; constructor <;> linarith
  · rintro ⟨h1, h2⟩; linarith

lemma IsPoly.preimage {F : Type*} [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) {S : Set F}
    (hS : IsPoly S) : IsPoly (L ⁻¹' S) := by
  obtain ⟨s, hs, rfl⟩ := hS
  refine ⟨(fun p => ((p.1 ∘ₗ L : Module.Dual ℝ E), p.2)) '' s, hs.image _, ?_⟩
  ext v; constructor
  · rintro h _ ⟨q, hq, rfl⟩; exact h q hq
  · intro h q hq; exact h _ ⟨q, hq, rfl⟩

lemma IsPoly.vec_le {ι : Type*} [Finite ι] (L : E →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) :
    IsPoly {v | c ≤ L v} := by
  have := IsPoly.iInter (fun j : ι => IsPoly.half ((LinearMap.proj j : (ι → ℝ) →ₗ[ℝ] ℝ) ∘ₗ L) (c j))
  convert this using 1
  ext v; simp [Pi.le_def]

lemma IsPoly.vec_eq {ι : Type*} [Finite ι] (L : E →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) :
    IsPoly {v | L v = c} := by
  have := IsPoly.iInter (fun j : ι => IsPoly.eq ((LinearMap.proj j : (ι → ℝ) →ₗ[ℝ] ℝ) ∘ₗ L) (c j))
  convert this using 1
  ext v; simp [funext_iff]

lemma IsPoly.convex {S : Set E} (hS : IsPoly S) : Convex ℝ S := by
  obtain ⟨s, hs, rfl⟩ := hS
  intro x hx y hy a b ha hb hab p hp
  have h1 := hx p hp; have h2 := hy p hp
  simp only [map_add, map_smul, smul_eq_mul]
  have e : p.2 = a * p.2 + b * p.2 := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma IsPoly.isClosed [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsPoly S) : IsClosed S := by
  obtain ⟨s, hs, rfl⟩ := hS
  have : {v : E | ∀ p ∈ s, p.2 ≤ p.1 v} = ⋂ p ∈ s, {v | p.2 ≤ p.1 v} := by ext; simp
  rw [this]
  exact isClosed_biInter fun p _ =>
    isClosed_le continuous_const (LinearMap.continuous_of_finiteDimensional p.1)
end

lemma sandwich {L U : Set ℝ} (hL : L.Finite) (hU : U.Finite) (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t, (∀ l ∈ L, l ≤ t) ∧ ∀ u ∈ U, t ≤ u := by
  rcases L.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨t, ht⟩ := hU.bddBelow; exact ⟨t, by simp, fun u hu => ht hu⟩
  · exact ⟨sSup L, fun l hl => le_csSup hL.bddAbove hl,
      fun u hu => csSup_le hne fun l hl => h l hl u hu⟩

/-- Fourier–Motzkin elimination of one real variable. -/
lemma IsPoly.fst_image {V : Type*} [AddCommGroup V] [Module ℝ V] {S : Set (V × ℝ)}
    (hS : IsPoly S) : IsPoly (Prod.fst '' S) := by
  obtain ⟨s, hs, rfl⟩ := hS
  let a : Module.Dual ℝ (V × ℝ) × ℝ → ℝ := fun p => p.1 (0, 1)
  let φ0 : Module.Dual ℝ (V × ℝ) × ℝ → Module.Dual ℝ V := fun p => p.1 ∘ₗ LinearMap.inl ℝ V ℝ
  have key : ∀ (p : Module.Dual ℝ (V × ℝ) × ℝ) (v : V) (t : ℝ), p.1 (v, t) = φ0 p v + t * a p := by
    intro p v t
    have : ((v, t) : V × ℝ) = LinearMap.inl ℝ V ℝ v + t • ((0 : V), (1:ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul]; simp [φ0, a, smul_eq_mul]
  let s0 := {p ∈ s | a p = 0}
  let sp := {p ∈ s | 0 < a p}
  let sn := {p ∈ s | a p < 0}
  let g : (Module.Dual ℝ (V × ℝ) × ℝ) × (Module.Dual ℝ (V × ℝ) × ℝ) → Module.Dual ℝ V × ℝ :=
    fun pq => (a pq.1 • φ0 pq.2 - a pq.2 • φ0 pq.1, a pq.1 * pq.2.2 - a pq.2 * pq.1.2)
  refine ⟨(fun p => (φ0 p, p.2)) '' s0 ∪ g '' (sp ×ˢ sn), ?_, ?_⟩
  · exact ((hs.subset (sep_subset _ _)).image _).union
      (((hs.subset (sep_subset _ _)).prod (hs.subset (sep_subset _ _))).image _)
  ext v
  constructor
  · rintro ⟨⟨v', t⟩, hvt, rfl⟩ q hq
    rcases hq with ⟨p, ⟨hp, hp0⟩, rfl⟩ | ⟨⟨p, q'⟩, ⟨⟨hp, hpa⟩, ⟨hq', hqa⟩⟩, rfl⟩
    · have := hvt p hp; rw [key] at this; simp only [hp0, mul_zero, add_zero] at this
      exact this
    · have h1 := hvt p hp; have h2 := hvt q' hq'; rw [key] at h1 h2
      simp only [g, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left h1 (neg_nonneg.2 hqa.le),
        mul_le_mul_of_nonneg_left h2 hpa.le]
  · intro hv
    have h0 : ∀ p ∈ s, a p = 0 → p.2 ≤ φ0 p v := fun p hp hp0 => hv _ (Or.inl ⟨p, ⟨hp, hp0⟩, rfl⟩)
    have hpn : ∀ p ∈ s, ∀ q ∈ s, 0 < a p → a q < 0 →
        a p * q.2 - a q * p.2 ≤ a p * φ0 q v - a q * φ0 p v := by
      intro p hp q hq hpa hqa
      have := hv _ (Or.inr ⟨(p, q), ⟨⟨hp, hpa⟩, ⟨hq, hqa⟩⟩, rfl⟩)
      simpa [g] using this
    obtain ⟨t, htL, htU⟩ := sandwich (L := (fun p => (p.2 - φ0 p v) / a p) '' sp)
      (U := (fun q => (φ0 q v - q.2) / (-a q)) '' sn)
      ((hs.subset (sep_subset _ _)).image _) ((hs.subset (sep_subset _ _)).image _) (by
        rintro _ ⟨p, ⟨hp, hpa⟩, rfl⟩ _ ⟨q, ⟨hq, hqa⟩, rfl⟩
        rw [div_le_div_iff₀ hpa (neg_pos.2 hqa)]
        have := hpn p hp q hq hpa hqa
        nlinarith)
    refine ⟨(v, t), ?_, rfl⟩
    intro p hp; rw [key]
    rcases lt_trichotomy (a p) 0 with hn | hz | hpos
    · have := htU _ ⟨p, ⟨hp, hn⟩, rfl⟩
      rw [le_div_iff₀ (by linarith)] at this; nlinarith
    · rw [hz, mul_zero, add_zero]; exact h0 p hp hz
    · have := htL _ ⟨p, ⟨hp, hpos⟩, rfl⟩
      rw [div_le_iff₀ hpos] at this; linarith

lemma proj_fin : ∀ (k : ℕ) {V : Type} [AddCommGroup V] [Module ℝ V]
    (S : Set (V × (Fin k → ℝ))), IsPoly S → IsPoly (Prod.fst '' S) := by
  intro k
  induction k with
  | zero =>
    intro V _ _ S hS
    convert hS.preimage (LinearMap.inl ℝ V (Fin 0 → ℝ)) using 1
    ext v; constructor
    · rintro ⟨⟨v, w⟩, h, rfl⟩
      have : w = 0 := Subsingleton.elim _ _
      subst this; simpa using h
    · intro h; exact ⟨_, h, rfl⟩
  | succ k ih =>
    intro V _ _ S hS
    let g : (V × ℝ) × (Fin k → ℝ) →ₗ[ℝ] V × (Fin (k+1) → ℝ) :=
      { toFun := fun z => (z.1.1, Fin.cons z.1.2 z.2)
        map_add' := by
          intro x y; ext i
          · simp
          · refine Fin.cases ?_ ?_ i <;> simp
        map_smul' := by
          intro c x; ext i
          · simp
          · refine Fin.cases ?_ ?_ i <;> simp }
    have h1 := (ih (g ⁻¹' S) (hS.preimage g)).fst_image
    convert h1 using 1
    ext v; constructor
    · rintro ⟨⟨v, w⟩, h, rfl⟩
      refine ⟨(v, w 0), ⟨((v, w 0), Fin.tail w), ?_, rfl⟩, rfl⟩
      simpa [g, Fin.cons_self_tail] using h
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨g z, hz, rfl⟩

lemma proj_general {V : Type} [AddCommGroup V] [Module ℝ V] {W : Type*} [AddCommGroup W]
    [Module ℝ W] [FiniteDimensional ℝ W] (S : Set (V × W)) (hS : IsPoly S) :
    IsPoly (Prod.fst '' S) := by
  let e := (Module.finBasis ℝ W).equivFun
  let L : V × (Fin (Module.finrank ℝ W) → ℝ) →ₗ[ℝ] V × W :=
    LinearMap.prodMap LinearMap.id e.symm.toLinearMap
  convert proj_fin _ _ (hS.preimage L) using 1
  ext v; constructor
  · rintro ⟨⟨v, w⟩, h, rfl⟩
    refine ⟨(v, e w), ?_, rfl⟩
    simpa [L] using h
  · rintro ⟨z, hz, rfl⟩
    exact ⟨L z, hz, rfl⟩

end DK88

namespace DK88
open Set Disjunctive.ConvexHull

section main
variable {n : ℕ} {Q : Type*} [Fintype Q] [DecidableEq Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)

lemma lp_nonneg {Qidx : Set Q} {x : Fin n → ℝ} {y : Q → Fin n → ℝ} {y0 : Q → ℝ}
    (hp : (x, (y, y0)) ∈ LiftedPolyhedron m A b Qidx) : ∀ h, 0 ≤ y0 h := by
  intro h
  by_cases hh : h ∈ Qidx
  · exact (hp.2.1 h hh).2
  · exact (hp.2.2.1 h hh).2.ge

lemma lift_mem {Qidx : Set Q} {k : Q} {x : Fin n → ℝ} (hk : k ∈ Qidx)
    (hx : x ∈ Poly (A k) (b k)) :
    (x, (Pi.single k x, Pi.single k 1)) ∈ LiftedPolyhedron m A b Qidx := by
  classical
  refine ⟨by simp, fun h _ => ?_, fun h hh => ?_, by simp⟩
  · by_cases e : h = k
    · subst e
      refine ⟨fun i => ?_, by simp⟩
      simp only [Pi.single_eq_same, one_smul, Pi.zero_apply, Pi.sub_apply, sub_nonneg]
      exact hx i
    · simp [Pi.single_eq_of_ne e]
  · have e : h ≠ k := fun e => hh (e ▸ hk)
    simp [Pi.single_eq_of_ne e]

lemma scaled_mem {k : Q} {v : Fin n → ℝ} {t : ℝ} (ht : 0 < t)
    (hv : 0 ≤ (A k).mulVec v - t • b k) : t⁻¹ • v ∈ Poly (A k) (b k) := by
  intro i
  have := hv i
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, le_inv_mul_iff₀ ht]
  linarith

lemma add_single_mem {Qidx : Set Q} {x : Fin n → ℝ} {y : Q → Fin n → ℝ} {y0 : Q → ℝ} {h : Q}
    (hp : (x, (y, y0)) ∈ LiftedPolyhedron m A b Qidx) (hh : h ∈ Qidx) (u : Fin n → ℝ)
    (hu : 0 ≤ (A h).mulVec (y h + u) - y0 h • b h) :
    (x + u, (y + Pi.single h u, y0)) ∈ LiftedPolyhedron m A b Qidx := by
  classical
  obtain ⟨hx, hQ, hN, hs⟩ := hp
  dsimp only at hx hQ hN hs
  refine ⟨?_, fun h' hh' => ?_, fun h' hh' => ?_, hs⟩
  · simp [Finset.sum_add_distrib, hx]
  · by_cases e : h' = h
    · subst e; refine ⟨by simpa using hu, (hQ h' hh').2⟩
    · simpa [Pi.single_eq_of_ne e] using hQ h' hh'
  · have e : h' ≠ h := fun e => hh' (e ▸ hh)
    simpa [Pi.single_eq_of_ne e] using hN h' hh'

end main
end DK88

namespace DK88
open Set Disjunctive.ConvexHull

section ti
variable {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)

/-- Homogenized lifted system with `Σ y0 = s`. -/
def ConeSet (Qidx : Set Q) : Set (((Fin n → ℝ) × ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) :=
  {p | p.1.1 = ∑ h, p.2.1 h ∧
        (∀ h ∈ Qidx, 0 ≤ (A h).mulVec (p.2.1 h) - p.2.2 h • (b h) ∧ 0 ≤ p.2.2 h) ∧
        (∀ h, h ∉ Qidx → p.2.1 h = 0 ∧ p.2.2 h = 0) ∧
        ∑ h, p.2.2 h = p.1.2}

lemma isPoly_cone (Qidx : Set Q) : IsPoly (ConeSet m A b Qidx) := by
  classical
  let M1 : ((Fin n → ℝ) × ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ)) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun p => p.1.1 - ∑ h, p.2.1 h
      map_add' := by
        intro x y; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
        abel
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_sub] }
  let M2 : ∀ h, ((Fin n → ℝ) × ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ)) →ₗ[ℝ] (Fin (m h) → ℝ) := fun h =>
    { toFun := fun p => (A h).mulVec (p.2.1 h) - p.2.2 h • b h
      map_add' := by
        intro x y; simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Matrix.mulVec_add, add_smul]; abel
      map_smul' := by intro c x; simp [Matrix.mulVec_smul, smul_sub, smul_smul] }
  let M3 : ∀ h, Module.Dual ℝ (((Fin n → ℝ) × ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) := fun h =>
    { toFun := fun p => p.2.2 h, map_add' := by intro x y; simp,
      map_smul' := by intro c x; simp }
  let M4 : ∀ h, ((Fin n → ℝ) × ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ)) →ₗ[ℝ] (Fin n → ℝ) := fun h =>
    { toFun := fun p => p.2.1 h, map_add' := by intro x y; simp,
      map_smul' := by intro c x; simp }
  let M5 : Module.Dual ℝ (((Fin n → ℝ) × ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) :=
    { toFun := fun p => ∑ h, p.2.2 h - p.1.2,
      map_add' := by intro x y; simp [Finset.sum_add_distrib]; ring,
      map_smul' := by intro c x; simp [Finset.mul_sum, mul_sub] }
  let C : Q → Set (((Fin n → ℝ) × ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) := fun h =>
    {p | if h ∈ Qidx then (0 ≤ M2 h p ∧ 0 ≤ M3 h p) else (M4 h p = 0 ∧ M3 h p = 0)}
  have hC : ∀ h, IsPoly (C h) := by
    intro h
    by_cases hh : h ∈ Qidx
    · have := (IsPoly.vec_le (M2 h) 0).inter (IsPoly.half (M3 h) 0)
      convert this using 1; ext p; simp only [C, hh, if_true]; rfl
    · have := (IsPoly.vec_eq (M4 h) 0).inter (IsPoly.eq (M3 h) 0)
      convert this using 1; ext p; simp only [C, hh, if_false]; rfl
  have hEq : ConeSet m A b Qidx = {p | M1 p = 0} ∩ (⋂ h, C h) ∩ {p | M5 p = 0} := by
    ext ⟨⟨x, s⟩, y, y0⟩
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨sub_eq_zero.2 h1, mem_iInter.2 fun h => ?_⟩, sub_eq_zero.2 h4⟩
      show (if h ∈ Qidx then _ else _)
      split_ifs with hh
      · exact h2 h hh
      · exact h3 h hh
    · rintro ⟨⟨h1, h2⟩, h4⟩
      have h1' : x - ∑ h, y h = 0 := h1
      have h4' : ∑ h, y0 h - s = 0 := h4
      have h2' : ∀ h, ((x, s), (y, y0)) ∈ C h := mem_iInter.1 h2
      refine ⟨sub_eq_zero.1 h1', fun h hh => ?_, fun h hh => ?_, sub_eq_zero.1 h4'⟩
      · have := h2' h; simp only [C, Set.mem_setOf_eq] at this; rw [if_pos hh] at this
        exact this
      · have := h2' h; simp only [C, Set.mem_setOf_eq] at this; rw [if_neg hh] at this
        exact this
  rw [hEq]
  exact ((IsPoly.vec_eq M1 0).inter (IsPoly.iInter hC)).inter (IsPoly.eq M5 0)

lemma isClosed_coneProj (Qidx : Set Q) : IsClosed (Prod.fst '' ConeSet m A b Qidx) :=
  (proj_general _ (isPoly_cone m A b Qidx)).isClosed

/-- Recession directions of `P` lie in the Minkowski sum of recession cones. -/
lemma rec_dir (Qidx : Set Q) (x0 d : Fin n → ℝ)
    (h : ∀ t : ℝ, 1 ≤ t → x0 + t • d ∈ ProjX (LiftedPolyhedron m A b Qidx)) :
    d ∈ MinkowskiSumOver Qidx (fun h => RecessionCone (A h)) := by
  have hmem : ((d, (0:ℝ)) : (Fin n → ℝ) × ℝ) ∈ Prod.fst '' ConeSet m A b Qidx := by
    have ht : Filter.Tendsto (fun t : ℝ => ((t⁻¹ • x0 + d, t⁻¹) : (Fin n → ℝ) × ℝ))
        Filter.atTop (nhds (d, 0)) := by
      have h1 : Filter.Tendsto (fun t : ℝ => t⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
      have h2 : Filter.Tendsto (fun t : ℝ => t⁻¹ • x0 + d) Filter.atTop (nhds d) := by
        have := (h1.smul_const x0).add_const d
        simpa using this
      exact h2.prodMk_nhds h1
    apply (isClosed_coneProj m A b Qidx).mem_of_tendsto ht
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with t ht1
    have ht0 : 0 < t := by linarith
    obtain ⟨⟨y, y0⟩, hx, hQ, hN, hs⟩ := h t ht1
    dsimp only at hx hQ hN hs
    refine ⟨((t⁻¹ • x0 + d, t⁻¹), (t⁻¹ • y, t⁻¹ • y0)), ⟨?_, fun h hh => ?_, fun h hh => ?_, ?_⟩, rfl⟩
    · simp only [Pi.smul_apply]
      rw [← Finset.smul_sum, ← hx, smul_add, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
    · simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul]
      refine ⟨?_, mul_nonneg (inv_nonneg.2 ht0.le) (hQ h hh).2⟩
      rw [← smul_smul, ← smul_sub]
      exact smul_nonneg (inv_nonneg.2 ht0.le) (hQ h hh).1
    · simp [hN h hh]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, hs, mul_one]
  obtain ⟨⟨⟨x, s⟩, y, y0⟩, ⟨hx, hQ, hN, hs⟩, he⟩ := hmem
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  dsimp only at hx hQ hN hs
  have hnn : ∀ h, 0 ≤ y0 h := fun h => by
    by_cases hh : h ∈ Qidx
    · exact (hQ h hh).2
    · exact (hN h hh).2.ge
  have hz : ∀ h, y0 h = 0 := fun h =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hs h (Finset.mem_univ h)
  refine ⟨y, hx, fun h hh => ?_, fun h hh => (hN h hh).1⟩
  have := (hQ h hh).1
  rwa [hz h, zero_smul, sub_zero] at this

end ti
end DK88

open Disjunctive.ConvexHull in
theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (hF : (DisjunctiveSet m A b).Nonempty) :
    ProjX (LiftedPolyhedron m A b Set.univ) = ProjX (LiftedPolyhedron m A b (FeasibleIndices m A b)) ↔
      ∀ k, k ∉ FeasibleIndices m A b →
        RecessionCone (A k) ⊆ MinkowskiSumOver (FeasibleIndices m A b) (fun h => RecessionCone (A h)) := by
  classical
  set QS := FeasibleIndices m A b with hQS
  constructor
  · intro hEq k hk d hd
    obtain ⟨x0, hx0⟩ := hF
    obtain ⟨h0, hh0⟩ := Set.mem_iUnion.1 hx0
    have h0Q : h0 ∈ QS := ⟨x0, hh0⟩
    have hne : k ≠ h0 := fun e => hk (e ▸ h0Q)
    apply DK88.rec_dir m A b QS x0 d
    intro t ht1
    rw [← hEq]
    have hL := DK88.lift_mem m A b (Qidx := Set.univ) (Set.mem_univ h0) hh0
    have := DK88.add_single_mem m A b hL (Set.mem_univ k) (t • d) (by
      simp only [Pi.single_eq_of_ne hne, zero_add, zero_smul, sub_zero, Matrix.mulVec_smul]
      exact smul_nonneg (by linarith) hd)
    exact ⟨_, this⟩
  · intro hC
    apply Set.Subset.antisymm
    · rintro x ⟨⟨y, y0⟩, hx, hQ, -, hs⟩
      dsimp only at hx hQ hs
      have hy0 : ∀ k, k ∉ QS → y0 k = 0 := by
        intro k hk
        rcases (hQ k (Set.mem_univ k)).2.lt_or_eq with hpos | h0
        · exact absurd ⟨_, DK88.scaled_mem m A b hpos (hQ k (Set.mem_univ k)).1⟩ hk
        · exact h0.symm
      have hrec : ∀ k, ∃ z : Q → Fin n → ℝ, k ∉ QS → (y k = ∑ h, z h ∧
          (∀ h ∈ QS, z h ∈ RecessionCone (A h)) ∧ ∀ h, h ∉ QS → z h = 0) := by
        intro k
        by_cases hk : k ∈ QS
        · exact ⟨0, fun h => absurd hk h⟩
        · have hyk : y k ∈ RecessionCone (A k) := by
            have := (hQ k (Set.mem_univ k)).1
            rwa [hy0 k hk, zero_smul, sub_zero] at this
          obtain ⟨z, hz⟩ := hC k hk hyk
          exact ⟨z, fun _ => hz⟩
      choose z hz using hrec
      let w : Q → Q → Fin n → ℝ := fun k => if k ∈ QS then 0 else z k
      have hw0 : ∀ k h, h ∉ QS → w k h = 0 := by
        intro k h hh; simp only [w]; split_ifs with hk
        · rfl
        · exact (hz k hk).2.2 h hh
      have hwC : ∀ k h, h ∈ QS → 0 ≤ (A h).mulVec (w k h) := by
        intro k h hh; simp only [w]; split_ifs with hk
        · simp
        · exact (hz k hk).2.1 h hh
      have hwsum : ∀ k, ∑ h, w k h = if k ∈ QS then 0 else y k := by
        intro k; simp only [w]; split_ifs with hk
        · simp
        · exact (hz k hk).1.symm
      let y' : Q → Fin n → ℝ := fun h => (if h ∈ QS then y h else 0) + ∑ k, w k h
      refine ⟨(y', y0), ?_, fun h hh => ⟨?_, (hQ h (Set.mem_univ h)).2⟩, fun h hh => ⟨?_, hy0 h hh⟩, hs⟩
      · dsimp only
        simp only [y', Finset.sum_add_distrib]
        rw [Finset.sum_comm, hx]
        simp only [hwsum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k _
        split_ifs <;> simp
      · simp only [y', if_pos hh, Matrix.mulVec_add, Matrix.mulVec_sum]
        have h1 := (hQ h (Set.mem_univ h)).1
        have h2 : 0 ≤ ∑ k, (A h).mulVec (w k h) := Finset.sum_nonneg fun k _ => hwC k h hh
        have : (A h).mulVec (y h) + ∑ k, (A h).mulVec (w k h) - y0 h • b h =
          ((A h).mulVec (y h) - y0 h • b h) + ∑ k, (A h).mulVec (w k h) := by abel
        rw [this]; exact add_nonneg h1 h2
      · simp only [y', if_neg hh, zero_add]
        exact Finset.sum_eq_zero fun k _ => hw0 k h hh
    · rintro x ⟨p, hx, hQ, hN, hs⟩
      exact ⟨p, hx, fun h _ => by
        by_cases hh : h ∈ QS
        · exact hQ h hh
        · rw [(hN h hh).1, (hN h hh).2]; simp, fun h hh => absurd (Set.mem_univ h) hh, hs⟩
