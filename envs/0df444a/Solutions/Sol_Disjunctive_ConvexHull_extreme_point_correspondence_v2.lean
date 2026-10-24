-- Prove2me | solution 1 for Disjunctive.ConvexHull.extreme_point_correspondence_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:38:56.567038+00:00
-- url     : https://prove2.me/submissions/2758305e-f8f9-43df-a7ea-1980b895f22e

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

namespace DJ88
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

end DJ88

namespace DJ88
open Set Disjunctive.ConvexHull

section generic
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma ext_seg {S : Set E} {p p1 p2 : E} (h : p ∈ extremePoints ℝ S) (h1 : p1 ∈ S) (h2 : p2 ∈ S)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (heq : a • p1 + b • p2 = p) : p1 = p :=
  h.2 h1 h2 ⟨a, b, ha, hb, hab, heq⟩

lemma ext_pm {S : Set E} {p d : E} (h : p ∈ extremePoints ℝ S) (h1 : p + d ∈ S)
    (h2 : p + -d ∈ S) : d = 0 := by
  have := ext_seg h h1 h2 (a := 1/2) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
    (by module)
  simpa using this

lemma ext_sum {K : Set E} (hK : Convex ℝ K) {x : E} (hx : x ∈ extremePoints ℝ K) {ι : Type*}
    (t : Finset ι) (w : ι → ℝ) (z : ι → E) (hw : ∀ i ∈ t, 0 < w i) (hsum : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ K) (hc : ∑ i ∈ t, w i • z i = x) : ∀ i ∈ t, z i = x := by
  classical
  by_contra hne; push_neg at hne; obtain ⟨j, hj, hjx⟩ := hne
  have hconv := ((Convex.mem_extremePoints_iff_convex_sdiff hK).1 hx).2
  set t' := t.filter (fun i => z i ≠ x) with ht'
  have hW : 0 < ∑ i ∈ t', w i :=
    Finset.sum_pos (fun i hi => hw i (Finset.mem_filter.1 hi).1) ⟨j, Finset.mem_filter.2 ⟨hj, hjx⟩⟩
  have hmem : t'.centerMass w z ∈ K \ {x} :=
    hconv.centerMass_mem (fun i hi => (hw i (Finset.mem_filter.1 hi).1).le) hW
      (fun i hi => ⟨hz i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
  apply hmem.2
  have h1 := Finset.sum_filter_add_sum_filter_not t (fun i => z i ≠ x) (fun i => w i • z i)
  have h2 := Finset.sum_filter_add_sum_filter_not t (fun i => z i ≠ x) w
  have h3 : ∑ i ∈ t.filter (fun i => ¬ z i ≠ x), w i • z i =
      (∑ i ∈ t.filter (fun i => ¬ z i ≠ x), w i) • x := by
    rw [Finset.sum_smul]; apply Finset.sum_congr rfl; intro i hi
    rw [not_not.1 (Finset.mem_filter.1 hi).2]
  rw [h3, hc] at h1
  rw [hsum] at h2
  have h4 : ∑ i ∈ t', w i • z i = (∑ i ∈ t', w i) • x := by
    rw [← ht'] at h1 h2
    have : ∑ i ∈ t.filter (fun i => ¬ z i ≠ x), w i = 1 - ∑ i ∈ t', w i := by linarith
    rw [this, sub_smul, one_smul] at h1
    calc ∑ i ∈ t', w i • z i
        = (∑ i ∈ t', w i • z i + (x - (∑ i ∈ t', w i) • x)) - (x - (∑ i ∈ t', w i) • x) := by abel
      _ = x - (x - (∑ i ∈ t', w i) • x) := by rw [h1]
      _ = _ := by abel
  show (∑ i ∈ t', w i)⁻¹ • ∑ i ∈ t', w i • z i = x
  rw [h4, smul_smul, inv_mul_cancel₀ hW.ne', one_smul]

lemma rec_lemma [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {K : Set E} (hK : Convex ℝ K) (hc : IsClosed K) {w d u : E}
    (hw : ∀ s : ℝ, 0 ≤ s → w + s • d ∈ K) (hu : u ∈ K) : u + d ∈ K := by
  have ht : Filter.Tendsto (fun s : ℝ => u + d + s⁻¹ • (w - u)) Filter.atTop (nhds (u + d)) := by
    have : Filter.Tendsto (fun s : ℝ => s⁻¹ • (w - u)) Filter.atTop (nhds ((0:ℝ) • (w - u))) :=
      tendsto_inv_atTop_zero.smul_const _
    rw [zero_smul] at this
    simpa using tendsto_const_nhds.add this
  apply hc.mem_of_tendsto ht
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with s hs
  have hs0 : 0 < s := by linarith
  have := hK hu (hw s hs0.le) (a := 1 - s⁻¹) (b := s⁻¹)
    (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hs) (by positivity) (by ring)
  convert this using 1
  rw [smul_add, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul, sub_smul, one_smul, smul_sub]
  abel
end generic

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

omit [DecidableEq Q] in
theorem part2 (Qidx : Set Q) (xbar : Fin n → ℝ) (y : Q → Fin n → ℝ) (y0 : Q → ℝ)
    (hext : (xbar, (y, y0)) ∈ Set.extremePoints ℝ (LiftedPolyhedron m A b Qidx)) :
    ∃ k ∈ Qidx, y k = xbar ∧ y0 k = 1 ∧ (∀ h, h ≠ k → y h = 0 ∧ y0 h = 0) ∧
        xbar ∈ Set.extremePoints ℝ (Poly (A k) (b k)) := by
  classical
  have hp := hext.1
  have hnn := lp_nonneg m A b hp
  obtain ⟨hx, hQ, hN, hs⟩ := hp
  dsimp only at hx hQ hN hs
  -- Step 1
  have hzero : ∀ h, y0 h = 0 → y h = 0 := by
    intro h h0
    by_cases hh : h ∈ Qidx
    swap; · exact (hN h hh).1
    have hA : 0 ≤ (A h).mulVec (y h) := by
      have := (hQ h hh).1; rwa [h0, zero_smul, sub_zero] at this
    have key := ext_pm hext (d := (y h, (Pi.single h (y h), (0 : Q → ℝ)))) (by
        have := add_single_mem m A b hext.1 hh (y h) (by
          rw [h0, zero_smul, sub_zero, Matrix.mulVec_add]; exact add_nonneg hA hA)
        simpa using this) (by
        have := add_single_mem m A b hext.1 hh (-y h) (by
          rw [h0, zero_smul, sub_zero, add_neg_cancel, Matrix.mulVec_zero])
        simpa [Pi.single_neg] using this)
    exact congrArg Prod.fst key
  -- Step 2
  have hone : ∀ h, 0 < y0 h → y0 h = 1 := by
    intro h hpos; by_contra hne
    have hle : y0 h ≤ 1 := hs ▸ Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ h)
    have hlt : y0 h < 1 := lt_of_le_of_ne hle hne
    have hh : h ∈ Qidx := by
      by_contra hh; linarith [(hN h hh).2]
    set t := y0 h with ht
    have h1t : 0 < 1 - t := sub_pos.2 hlt
    have hz := scaled_mem m A b hpos (hQ h hh).1
    set z := t⁻¹ • y h
    have hL := lift_mem m A b hh hz
    let R : (Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ)) :=
      ((1-t)⁻¹ • (xbar - y h), (fun h' => (1-t)⁻¹ • (y h' - (Pi.single h (y h) : Q → Fin n → ℝ) h'),
        fun h' => (1-t)⁻¹ * (y0 h' - (Pi.single h t : Q → ℝ) h')))
    have hR : R ∈ LiftedPolyhedron m A b Qidx := by
      refine ⟨?_, fun h' hh' => ?_, fun h' hh' => ?_, ?_⟩
      · simp only [R]
        rw [← Finset.smul_sum, Finset.sum_sub_distrib, ← hx]
        simp
      · by_cases e : h' = h
        · subst e; simp [R, ← ht]
        · simp only [R, Pi.single_eq_of_ne e, sub_zero]
          refine ⟨?_, mul_nonneg (inv_nonneg.2 h1t.le) (hnn h')⟩
          rw [Matrix.mulVec_smul, ← smul_smul, ← smul_sub]
          exact smul_nonneg (inv_nonneg.2 h1t.le) (hQ h' hh').1
      · have e : h' ≠ h := fun e => hh' (e ▸ hh)
        simp [R, Pi.single_eq_of_ne e, hN h' hh']
      · simp only [R]
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, hs]
        simp [inv_mul_cancel₀ h1t.ne']
    have heq : t • (z, (Pi.single h z, Pi.single h (1:ℝ))) + (1 - t) • R = (xbar, (y, y0)) := by
      have ht0 : t ≠ 0 := hpos.ne'
      have ht1 : 1 - t ≠ 0 := h1t.ne'
      ext1
      · simp only [R, z, Prod.smul_fst, Prod.fst_add, smul_smul, mul_inv_cancel₀ ht0,
          mul_inv_cancel₀ ht1, one_smul]
        abel
      · ext1
        · funext h'
          by_cases e : h' = h
          · subst e; simp [R, z, smul_smul, mul_inv_cancel₀ ht0]
          · simp [R, z, Pi.single_eq_of_ne e, smul_smul, mul_inv_cancel₀ ht1]
        · funext h'
          by_cases e : h' = h
          · subst e; simp [R]; rw [← ht]; field_simp; ring
          · simp [R, Pi.single_eq_of_ne e]; field_simp
    have := ext_seg hext hL hR hpos h1t (by ring) heq
    have := congrFun (congrArg (fun q => q.2.2) this) h
    simp at this
    exact hne this.symm
  -- Step 3
  obtain ⟨k, hk⟩ : ∃ k, 0 < y0 k := by
    by_contra hcon; push_neg at hcon
    have := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hcon i); linarith
  have hk1 := hone k hk
  have hother : ∀ h, h ≠ k → y0 h = 0 := by
    intro h hne
    have h1 := Finset.add_sum_erase Finset.univ y0 (Finset.mem_univ k)
    rw [hs, hk1] at h1
    have h2 : ∑ x ∈ Finset.univ.erase k, y0 x = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 h2 h
      (Finset.mem_erase.2 ⟨hne, Finset.mem_univ h⟩)
  have hyk : y k = xbar := by
    rw [hx]; exact (Finset.sum_eq_single k (fun h _ hne => hzero h (hother h hne)) (by simp)).symm
  have kQ : k ∈ Qidx := by
    by_contra hh; have := (hN k hh).2; linarith
  have hxP : xbar ∈ Poly (A k) (b k) := by
    have := scaled_mem m A b (t := 1) (v := xbar) one_pos (by
      have := (hQ k kQ).1; rwa [hk1, hyk] at this)
    simpa using this
  have hy : y = Pi.single k xbar := by
    funext h; by_cases e : h = k
    · subst e; simp [hyk]
    · simp [Pi.single_eq_of_ne e, hzero h (hother h e)]
  have hy0 : y0 = Pi.single k 1 := by
    funext h; by_cases e : h = k
    · subst e; simp [hk1]
    · simp [Pi.single_eq_of_ne e, hother h e]
  refine ⟨k, kQ, hyk, hk1, fun h hne => ⟨hzero h (hother h hne), hother h hne⟩, hxP, ?_⟩
  rintro x1 hx1 x2 hx2 ⟨a, c, ha, hc, hac, heq⟩
  have hseg : ∀ (a c : ℝ) (x1 x2 : Fin n → ℝ), a + c = 1 → a • x1 + c • x2 = xbar →
      a • (x1, (Pi.single k x1, (Pi.single k 1 : Q → ℝ))) +
        c • (x2, (Pi.single k x2, (Pi.single k 1 : Q → ℝ))) = (xbar, (y, y0)) := by
    intro a c x1 x2 hac heq
    rw [hy, hy0]
    ext1
    · simpa using heq
    · ext1
      · funext h; by_cases e : h = k
        · subst e; simpa using heq
        · simp [Pi.single_eq_of_ne e]
      · funext h; by_cases e : h = k
        · subst e; simpa using hac
        · simp [Pi.single_eq_of_ne e]
  exact congrArg Prod.fst (ext_seg hext (lift_mem m A b kQ hx1) (lift_mem m A b kQ hx2) ha hc
      hac (hseg a c x1 x2 hac heq))

end main
end DJ88

namespace DJ88
open Set Disjunctive.ConvexHull

section main2
variable {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)

lemma isPoly_lifted (Qidx : Set Q) : IsPoly (LiftedPolyhedron m A b Qidx) := by
  classical
  let M1 : (Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ)) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun p => p.1 - ∑ h, p.2.1 h
      map_add' := by
        intro x y; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
        abel
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_sub] }
  let M2 : ∀ h, (Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ)) →ₗ[ℝ] (Fin (m h) → ℝ) := fun h =>
    { toFun := fun p => (A h).mulVec (p.2.1 h) - p.2.2 h • b h
      map_add' := by
        intro x y; simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Matrix.mulVec_add, add_smul]; abel
      map_smul' := by intro c x; simp [Matrix.mulVec_smul, smul_sub, smul_smul] }
  let M3 : ∀ h, Module.Dual ℝ ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) := fun h =>
    { toFun := fun p => p.2.2 h, map_add' := by intro x y; simp,
      map_smul' := by intro c x; simp }
  let M4 : ∀ h, (Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ)) →ₗ[ℝ] (Fin n → ℝ) := fun h =>
    { toFun := fun p => p.2.1 h, map_add' := by intro x y; simp,
      map_smul' := by intro c x; simp }
  let M5 : Module.Dual ℝ ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) :=
    { toFun := fun p => ∑ h, p.2.2 h, map_add' := by intro x y; simp [Finset.sum_add_distrib],
      map_smul' := by intro c x; simp [Finset.mul_sum] }
  let C : Q → Set ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) := fun h =>
    {p | if h ∈ Qidx then (0 ≤ M2 h p ∧ 0 ≤ M3 h p) else (M4 h p = 0 ∧ M3 h p = 0)}
  have hC : ∀ h, IsPoly (C h) := by
    intro h
    by_cases hh : h ∈ Qidx
    · have := (IsPoly.vec_le (M2 h) 0).inter (IsPoly.half (M3 h) 0)
      convert this using 1; ext p; simp only [C, hh, if_true]; rfl
    · have := (IsPoly.vec_eq (M4 h) 0).inter (IsPoly.eq (M3 h) 0)
      convert this using 1; ext p; simp only [C, hh, if_false]; rfl
  have hEq : LiftedPolyhedron m A b Qidx = {p | M1 p = 0} ∩ (⋂ h, C h) ∩ {p | M5 p = 1} := by
    ext ⟨x, y, y0⟩
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨sub_eq_zero.2 h1, mem_iInter.2 fun h => ?_⟩, h4⟩
      show (if h ∈ Qidx then _ else _)
      split_ifs with hh
      · exact h2 h hh
      · exact h3 h hh
    · rintro ⟨⟨h1, h2⟩, h4⟩
      have h1' : x - ∑ h, y h = 0 := h1
      have h2' : ∀ h, (x, (y, y0)) ∈ C h := mem_iInter.1 h2
      refine ⟨sub_eq_zero.1 h1', fun h hh => ?_, fun h hh => ?_, h4⟩
      · have := h2' h; simp only [C, Set.mem_setOf_eq] at this; rw [if_pos hh] at this
        exact this
      · have := h2' h; simp only [C, Set.mem_setOf_eq] at this; rw [if_neg hh] at this
        exact this
  rw [hEq]
  exact ((IsPoly.vec_eq M1 0).inter (IsPoly.iInter hC)).inter (IsPoly.eq M5 1)

theorem part1 : ∀ xstar ∈ Set.extremePoints ℝ (closure (convexHull ℝ (DisjunctiveSet m A b))),
      ∃ k ∈ FeasibleIndices m A b, ∃ y : Q → Fin n → ℝ, ∃ y0 : Q → ℝ,
        (xstar, (y, y0)) ∈ Set.extremePoints ℝ (LiftedPolyhedron m A b (FeasibleIndices m A b)) ∧
        y k = xstar ∧ y0 k = 1 ∧ ∀ h, h ≠ k → y h = 0 ∧ y0 h = 0 := by
  classical
  set Qs := FeasibleIndices m A b with hQs
  set K := closure (convexHull ℝ (DisjunctiveSet m A b)) with hK
  have hKc : IsClosed K := isClosed_closure
  have hKconv : Convex ℝ K := (convex_convexHull ℝ _).closure
  have hFK : ∀ h, Poly (A h) (b h) ⊆ K := fun h x hx =>
    subset_closure (subset_convexHull ℝ _ (mem_iUnion.2 ⟨h, hx⟩))
  have hrec : ∀ h ∈ Qs, ∀ d : Fin n → ℝ, 0 ≤ (A h).mulVec d → ∀ u ∈ K, u + d ∈ K := by
    intro h hh d hd u hu
    obtain ⟨w, hw⟩ := hh
    refine rec_lemma hKconv hKc (w := w) (fun s hs => hFK h ?_) hu
    intro i
    have h1 := hw i; have h2 := hd i
    simp only [Pi.zero_apply] at h2
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg hs h2]
  have hX : IsPoly (Prod.fst '' LiftedPolyhedron m A b Qs) :=
    proj_general _ (isPoly_lifted m A b Qs)
  have hKX : K ⊆ Prod.fst '' LiftedPolyhedron m A b Qs := by
    apply closure_minimal _ hX.isClosed
    apply convexHull_min _ hX.convex
    intro x hx
    obtain ⟨h, hxh⟩ := mem_iUnion.1 hx
    exact ⟨_, lift_mem m A b (show h ∈ Qs from ⟨x, hxh⟩) hxh, rfl⟩
  intro xs hxs
  obtain ⟨⟨x', y, y0⟩, hp, hx'⟩ := hKX hxs.1
  dsimp only at hx'; subst hx'
  have hnn := lp_nonneg m A b hp
  obtain ⟨hx, hQ, hN, hs⟩ := hp
  dsimp only at hx hQ hN hs
  have hpos0 : ∀ h, ¬ 0 < y0 h → y0 h = 0 := fun h hh => le_antisymm (not_lt.1 hh) (hnn h)
  set S := Finset.univ.filter (fun h => 0 < y0 h) with hS
  set D := ∑ h ∈ Finset.univ.filter (fun h => ¬ 0 < y0 h), y h with hD
  set c := ∑ h ∈ S, y h with hc
  have hDR : ∀ u ∈ K, u + D ∈ K := by
    have := Finset.sum_induction (s := Finset.univ.filter (fun h => ¬ 0 < y0 h)) y
      (fun d => ∀ u ∈ K, u + d ∈ K)
      (fun a b ha hb u hu => by rw [← add_assoc]; exact hb _ (ha u hu))
      (fun u hu => by simpa using hu)
      (fun h hh => by
        have h0 := hpos0 h (Finset.mem_filter.1 hh).2
        by_cases hq : h ∈ Qs
        · exact hrec h hq (y h) (by have := (hQ h hq).1; rwa [h0, zero_smul, sub_zero] at this)
        · intro u hu; rw [(hN h hq).1, add_zero]; exact hu)
    exact this
  have hsplit : x' = c + D := by rw [hx, hc, hD, Finset.sum_filter_add_sum_filter_not]
  have hS1 : ∑ h ∈ S, y0 h = 1 := by
    have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun h => 0 < y0 h) y0
    have h2 : ∑ h ∈ Finset.univ.filter (fun h => ¬ 0 < y0 h), y0 h = 0 :=
      Finset.sum_eq_zero (fun h hh => hpos0 h (Finset.mem_filter.1 hh).2)
    rw [h2, add_zero, hs] at h1; exact h1
  have hz : ∀ h ∈ S, (y0 h)⁻¹ • y h ∈ Poly (A h) (b h) := by
    intro h hh
    have hp := (Finset.mem_filter.1 hh).2
    have hq : h ∈ Qs := by by_contra hq; linarith [(hN h hq).2]
    exact scaled_mem m A b hp (hQ h hq).1
  have hcomb : ∑ h ∈ S, y0 h • ((y0 h)⁻¹ • y h) = c := by
    rw [hc]; apply Finset.sum_congr rfl; intro h hh
    rw [smul_smul, mul_inv_cancel₀ (Finset.mem_filter.1 hh).2.ne', one_smul]
  have hcK : c ∈ K := by
    rw [← hcomb]
    exact subset_closure (Convex.sum_mem (convex_convexHull ℝ _) (fun h _ => hnn h) hS1
      (fun h hh => subset_convexHull ℝ _ (mem_iUnion.2 ⟨h, hz h hh⟩)))
  have hcx : c = x' := ext_seg hxs hcK (hDR _ (hDR c hcK)) (a := 1/2) (b := 1/2)
    (by norm_num) (by norm_num) (by norm_num) (by rw [hsplit]; module)
  have hall := ext_sum hKconv hxs S y0 (fun h => (y0 h)⁻¹ • y h)
    (fun h hh => (Finset.mem_filter.1 hh).2) hS1 (fun h hh => hFK h (hz h hh)) (hcomb.trans hcx)
  obtain ⟨k, hk⟩ : S.Nonempty := by
    by_contra hne; rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hS1; exact zero_ne_one hS1
  have hxk : x' ∈ Poly (A k) (b k) := by rw [← hall k hk]; exact hz k hk
  have kQ : k ∈ Qs := ⟨x', hxk⟩
  refine ⟨k, kQ, Pi.single k x', Pi.single k 1, ?_, by simp, by simp,
    fun h hne => ⟨by simp [hne], by simp [hne]⟩⟩
  have hstruct : ∀ (x1 : Fin n → ℝ) (y1 : Q → Fin n → ℝ) (y01 : Q → ℝ) (x2 : Fin n → ℝ)
      (y2 : Q → Fin n → ℝ) (y02 : Q → ℝ) (a c : ℝ),
      (x1, (y1, y01)) ∈ LiftedPolyhedron m A b Qs → (x2, (y2, y02)) ∈ LiftedPolyhedron m A b Qs →
      0 < a → 0 < c →
      a • (x1, (y1, y01)) + c • (x2, (y2, y02)) = (x', (Pi.single k x', Pi.single k 1)) →
      x1 ∈ Poly (A k) (b k) ∧ y1 = Pi.single k x1 ∧ y01 = Pi.single k 1 := by
    intro x1 y1 y01 x2 y2 y02 a c hp1 hp2 ha hc heq
    have hnn1 := lp_nonneg m A b hp1
    have hnn2 := lp_nonneg m A b hp2
    obtain ⟨hx1, hQ1, hN1, hs1⟩ := hp1
    obtain ⟨hx2, hQ2, hN2, hs2⟩ := hp2
    dsimp only at hx1 hQ1 hN1 hs1 hx2 hQ2 hN2 hs2
    have e2 : ∀ h, a • y1 h + c • y2 h = (Pi.single k x' : Q → Fin n → ℝ) h := fun h => by
      have := congrFun (congrArg (fun p => p.2.1) heq) h; simpa using this
    have e3 : ∀ h, a * y01 h + c * y02 h = (Pi.single k (1:ℝ) : Q → ℝ) h := fun h => by
      have := congrFun (congrArg (fun p => p.2.2) heq) h; simpa using this
    have hz1 : ∀ h, h ≠ k → y01 h = 0 := by
      intro h hne
      have := e3 h; rw [Pi.single_eq_of_ne hne] at this
      exact le_antisymm (by nlinarith [mul_nonneg hc.le (hnn2 h), hnn1 h]) (hnn1 h)
    have hk1 : y01 k = 1 := by
      rw [← hs1]; exact (Finset.sum_eq_single k (fun h _ hne => hz1 h hne) (by simp)).symm
    have hy1 : ∀ h, h ≠ k → y1 h = 0 := by
      intro h hne
      by_cases hq : h ∈ Qs
      swap; · exact (hN1 h hq).1
      have hz2 : y02 h = 0 := by
        have := e3 h; rw [Pi.single_eq_of_ne hne] at this
        exact le_antisymm (by nlinarith [mul_nonneg ha.le (hnn1 h), hnn2 h]) (hnn2 h)
      have hA1 : 0 ≤ (A h).mulVec (y1 h) := by
        have := (hQ1 h hq).1; rwa [hz1 h hne, zero_smul, sub_zero] at this
      have hA2 : 0 ≤ (A h).mulVec (y2 h) := by
        have := (hQ2 h hq).1; rwa [hz2, zero_smul, sub_zero] at this
      have e : a • y1 h + c • y2 h = 0 := by have := e2 h; rwa [Pi.single_eq_of_ne hne] at this
      have hneg : -y1 h = (c / a) • y2 h := by
        funext i; have := congrFun e i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        field_simp; linarith
      have hA3 : 0 ≤ (A h).mulVec (-y1 h) := by
        rw [hneg, Matrix.mulVec_smul]; exact smul_nonneg (div_pos hc ha).le hA2
      exact ext_pm hxs (hrec h hq _ hA1 _ hxs.1) (hrec h hq _ hA3 _ hxs.1)
    have hx1' : x1 = y1 k :=
      hx1.trans (Finset.sum_eq_single k (fun h _ hne => hy1 h hne) (by simp))
    refine ⟨?_, ?_, ?_⟩
    · have := scaled_mem m A b (t := 1) (v := x1) one_pos (by
        have := (hQ1 k kQ).1; rwa [hk1, ← hx1'] at this)
      simpa using this
    · funext h; by_cases e : h = k
      · subst e; simp [hx1']
      · simp [Pi.single_eq_of_ne e, hy1 h e]
    · funext h; by_cases e : h = k
      · subst e; simp [hk1]
      · simp [Pi.single_eq_of_ne e, hz1 h e]
  refine ⟨lift_mem m A b kQ hxk, ?_⟩
  rintro ⟨x1, y1, y01⟩ hp1 ⟨x2, y2, y02⟩ hp2 ⟨a, c, ha, hc, hac, heq⟩
  obtain ⟨hP1, hy1, hy01⟩ := hstruct x1 y1 y01 x2 y2 y02 a c hp1 hp2 ha hc heq
  obtain ⟨hP2, -, -⟩ := hstruct x2 y2 y02 x1 y1 y01 c a hp2 hp1 hc ha
    (by rw [add_comm]; exact heq)
  have e1 : a • x1 + c • x2 = x' := congrArg Prod.fst heq
  have hx1 : x1 = x' := ext_seg hxs (hFK k hP1) (hFK k hP2) ha hc hac e1
  subst hy1 hy01 hx1; rfl

end main2
end DJ88

open Disjunctive.ConvexHull in
theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) :
    (∀ xstar ∈ Set.extremePoints ℝ (closure (convexHull ℝ (DisjunctiveSet m A b))),
      ∃ k ∈ FeasibleIndices m A b, ∃ y : Q → Fin n → ℝ, ∃ y0 : Q → ℝ,
        (xstar, (y, y0)) ∈ Set.extremePoints ℝ (LiftedPolyhedron m A b (FeasibleIndices m A b)) ∧
        y k = xstar ∧ y0 k = 1 ∧ ∀ h, h ≠ k → y h = 0 ∧ y0 h = 0)
    ∧
    (∀ (xbar : Fin n → ℝ) (y : Q → Fin n → ℝ) (y0 : Q → ℝ),
      (xbar, (y, y0)) ∈ Set.extremePoints ℝ (LiftedPolyhedron m A b (FeasibleIndices m A b)) →
      ∃ k ∈ FeasibleIndices m A b, y k = xbar ∧ y0 k = 1 ∧ (∀ h, h ≠ k → y h = 0 ∧ y0 h = 0) ∧
        xbar ∈ Set.extremePoints ℝ (Poly (A k) (b k))) :=
  ⟨DJ88.part1 m A b, fun xbar y y0 h => DJ88.part2 m A b _ xbar y y0 h⟩
