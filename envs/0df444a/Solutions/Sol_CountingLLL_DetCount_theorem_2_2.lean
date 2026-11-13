-- Prove2me | solution 1 for CountingLLL.DetCount.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:06:52.951201+00:00
-- url     : https://prove2.me/submissions/34bf4569-b24b-4226-8bf6-c75eae9381e9

import Definitions.Def_AppliedComb_ManyFaces_IndepOutside
import Definitions.Def_CountingLLL_DetCount_CSP

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CountingLLL.DetCount
open CSP
open scoped Classical

/-- Swapping coordinates outside S is an involution even for dependent domains. -/
private noncomputable def swapCoords {V : Type} [DecidableEq V] (Q : V → Type)
    (S : Finset V) (z : ((v : V) → Q v) × ((v : V) → Q v)) :
    ((v : V) → Q v) × ((v : V) → Q v) :=
  (fun v => if v ∈ S then z.1 v else z.2 v,
   fun v => if v ∈ S then z.2 v else z.1 v)

private theorem swapCoords_inv {V : Type} [DecidableEq V] (Q : V → Type)
    (S : Finset V) : Function.Involutive (swapCoords Q S) := by
  intro z
  apply Prod.ext <;> funext u <;> by_cases hu : u ∈ S <;> simp [swapCoords, hu]

/-- Finite-product counting independence for heterogeneous coordinate domains.
The swap-bijection argument adapts the accepted platform proof of
`OAI.MetricEntropyDuality.FiniteProductCounting.card_inter_mul_card_sample`
(https://prove2.me), generalized here to dependent coordinate domains. -/
theorem audit_dependent_disjoint_card {V : Type} [Fintype V] [DecidableEq V]
    (Q : V → Type) [∀ v, Fintype (Q v)] [∀ v, DecidableEq (Q v)]
    (S T : Finset V) (A B : Finset ((v : V) → Q v))
    (hA : ∀ x y, (∀ v ∈ S, x v = y v) → (x ∈ A ↔ y ∈ A))
    (hB : ∀ x y, (∀ v ∈ T, x v = y v) → (x ∈ B ↔ y ∈ B))
    (hST : Disjoint S T) :
    (A ∩ B).card * Fintype.card ((v : V) → Q v) = A.card * B.card := by
  classical
  have hforward : ∀ z ∈ (A ∩ B).product (Finset.univ : Finset ((v : V) → Q v)),
      swapCoords Q S z ∈ A.product B := by
    rintro ⟨x, y⟩ hz
    have hxA := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).1
    have hxB := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).2
    apply Finset.mem_product.mpr
    constructor
    · apply (hA _ x ?_).mpr hxA
      intro u hu
      simp [swapCoords, hu]
    · apply (hB _ x ?_).mpr hxB
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [swapCoords, huS]
  have hreverse : ∀ z ∈ A.product B,
      swapCoords Q S z ∈ (A ∩ B).product (Finset.univ : Finset ((v : V) → Q v)) := by
    rintro ⟨x, y⟩ hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_inter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · apply (hA _ x ?_).mpr hx
      intro u hu
      simp [swapCoords, hu]
    · apply (hB _ y ?_).mpr hy
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [swapCoords, huS]
  have hc := Finset.card_nbij' (swapCoords Q S) (swapCoords Q S)
    hforward hreverse (fun z _ => swapCoords_inv Q S z) (fun z _ => swapCoords_inv Q S z)
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ] using hc

/-- A violation on one scope is independent of satisfying every constraint
in a family whose scopes are disjoint from it. -/
theorem audit_scope_independent (Φ : CSP) (c : Fin Φ.m) (S : Finset (Fin Φ.m))
    (hdisj : ∀ j ∈ S, Disjoint (Φ.scope c) (Φ.scope j)) :
    ((Finset.univ.filter (fun σ : Φ.Config => ¬ Φ.Sat c σ ∧ Φ.SatAll S σ)).card : ℝ) /
        (Fintype.card Φ.Config : ℝ) =
      ((Finset.univ.filter (fun σ : Φ.Config => Φ.SatAll S σ)).card : ℝ) /
        (Fintype.card Φ.Config : ℝ) *
      ((Finset.univ.filter (fun σ : Φ.Config => ¬ Φ.Sat c σ)).card : ℝ) /
        (Fintype.card Φ.Config : ℝ) := by
  classical
  let A : Finset Φ.Config := Finset.univ.filter (fun σ => ¬ Φ.Sat c σ)
  let B : Finset Φ.Config := Finset.univ.filter (Φ.SatAll S)
  let T := S.biUnion Φ.scope
  have hA : ∀ x y : Φ.Config, (∀ v ∈ Φ.scope c, x v = y v) → (x ∈ A ↔ y ∈ A) := by
    intro x y hxy
    have heq : (fun v : ↥(Φ.scope c) => x v.1) = fun v : ↥(Φ.scope c) => y v.1 := by
      funext v
      exact hxy v.1 v.2
    change (x ∈ Finset.univ.filter (fun σ : Φ.Config => ¬ Φ.Sat c σ)) ↔
      (y ∈ Finset.univ.filter (fun σ : Φ.Config => ¬ Φ.Sat c σ))
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, CSP.Sat, heq]
  have hB : ∀ x y : Φ.Config, (∀ v ∈ T, x v = y v) → (x ∈ B ↔ y ∈ B) := by
    intro x y hxy
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, CSP.SatAll]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    have heq : (fun v : ↥(Φ.scope j) => x v.1) = fun v : ↥(Φ.scope j) => y v.1 := by
      funext v
      exact hxy v.1 (Finset.mem_biUnion.mpr ⟨j, hj, v.2⟩)
    simp only [CSP.Sat, heq]
  have hST : Disjoint (Φ.scope c) T := by
    apply Finset.disjoint_left.mpr
    intro v hv hvt
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvt
    exact Finset.disjoint_left.mp (hdisj j hj) hv hvj
  have hc := audit_dependent_disjoint_card (fun v => Fin (Φ.q v)) (Φ.scope c) T A B hA hB hST
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  have hC : (Fintype.card Φ.Config : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Φ.Config))
  have hcR : ((A ∩ B).card : ℝ) * (Fintype.card Φ.Config : ℝ) =
      (A.card : ℝ) * (B.card : ℝ) := by exact_mod_cast hc
  have hab : A ∩ B = Finset.univ.filter (fun σ => ¬ Φ.Sat c σ ∧ Φ.SatAll S σ) := by
    ext σ
    simp [A, B]
  rw [← hab]
  change ((A ∩ B).card : ℝ) / (Fintype.card Φ.Config : ℝ) =
    (B.card : ℝ) / (Fintype.card Φ.Config : ℝ) *
      (A.card : ℝ) / (Fintype.card Φ.Config : ℝ)
  field_simp
  nlinarith

end CountingLLL.DetCount


open MeasureTheory

-- Adapted from the accepted platform proof of AppliedComb.ManyFaces.local_lemma_asymmetric
-- (source: https://prove2.me; Apache 2.0).
namespace LLLAux

open AppliedComb.ManyFaces

set_option linter.unusedSectionVars false

variable {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]

lemma allFail_insert [DecidableEq ι] (A : ι → Set Ω) (a : ι) (S : Finset ι) :
    allFail A (insert a S) = allFail A S \ A a := by
  ext ω
  simp only [allFail, Finset.mem_insert, Set.mem_iInter, Set.mem_compl_iff, Set.mem_sdiff]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Or.inr hj), h a (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩ j (rfl | hj)
    · exact h2
    · exact h1 j hj

lemma allFail_empty (A : ι → Set Ω) : allFail A ∅ = Set.univ := by
  simp [allFail]

lemma allFail_anti (A : ι → Set Ω) {S T : Finset ι} (h : S ⊆ T) :
    allFail A T ⊆ allFail A S := by
  intro ω hω
  simp only [allFail, Set.mem_iInter] at hω ⊢
  exact fun j hj => hω j (h hj)

/-- Removing one failing event: `P(Ā_a ∩ F) = P(F) - P(A_a ∩ F)`. -/
lemma real_allFail_insert [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (a : ι) (S : Finset ι) :
    μ.real (allFail A (insert a S)) = μ.real (allFail A S) - μ.real (A a ∩ allFail A S) := by
  rw [allFail_insert, Set.inter_comm]
  have h := measureReal_inter_add_sdiff (μ := μ) (s := allFail A S) (t := A a)
    (MeasurableSet.of_discrete)
  linarith

lemma prod_le_prod_of_subset_of_le_one' {ι : Type*} [DecidableEq ι] {s t : Finset ι} (h : s ⊆ t)
    (f : ι → ℝ) (h0 : ∀ j, 0 ≤ f j) (h1 : ∀ j, f j ≤ 1) :
    ∏ j ∈ t, f j ≤ ∏ j ∈ s, f j := by
  rw [← Finset.prod_sdiff h]
  have : ∏ j ∈ t \ s, f j ≤ 1 := Finset.prod_le_one (fun j _ => h0 j) (fun j _ => h1 j)
  have hp : 0 ≤ ∏ j ∈ s, f j := Finset.prod_nonneg (fun j _ => h0 j)
  nlinarith

/-- The core of the Local Lemma, proved by induction on the size of the subfamily. -/
theorem core [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (N : ι → Finset ι)
    (hind : ∀ i, IndepOutside μ A N i) (x : ι → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∀ n : ℕ, ∀ S : Finset ι, S.card < n →
      (∏ j ∈ S, (1 - x j) ≤ μ.real (allFail A S)) ∧
      ∀ i, i ∉ S → μ.real (A i ∩ allFail A S) ≤ x i * μ.real (allFail A S) := by
  intro n
  induction n with
  | zero => intro S hS; exact absurd hS (Nat.not_lt_zero _)
  | succ n ih =>
    intro S hSn
    have hSle : S.card ≤ n := Nat.lt_succ_iff.mp hSn
    have h0 : ∀ j, 0 ≤ 1 - x j := fun j => by linarith [(hx j).2]
    have h1 : ∀ j, 1 - x j ≤ 1 := fun j => by linarith [(hx j).1]
    -- the second claim
    have hR : ∀ i, i ∉ S → μ.real (A i ∩ allFail A S) ≤ x i * μ.real (allFail A S) := by
      intro i hi
      set S₂ : Finset ι := S \ N i with hS₂
      set S₁ : Finset ι := S ∩ N i with hS₁
      have hS₂S : S₂ ⊆ S := Finset.sdiff_subset
      have hS₁S : S₁ ⊆ S := Finset.inter_subset_left
      have hS₁N : S₁ ⊆ N i := Finset.inter_subset_right
      have hdisj : Disjoint S₂ (N i) := Finset.sdiff_disjoint
      have hiS₂ : i ∉ S₂ := fun h => hi (hS₂S h)
      -- chain: peel off the elements of `S₁` one at a time
      have chain : ∀ T : Finset ι, T ⊆ S₁ →
          (∏ j ∈ T, (1 - x j)) * μ.real (allFail A S₂) ≤ μ.real (allFail A (S₂ ∪ T)) := by
        intro T
        induction T using Finset.induction_on with
        | empty => intro _; simp
        | insert a T haT ihT =>
          intro hT
          have hTS₁ : T ⊆ S₁ := fun y hy => hT (Finset.mem_insert_of_mem hy)
          have haS₁ : a ∈ S₁ := hT (Finset.mem_insert_self a T)
          have haS : a ∈ S := hS₁S haS₁
          have haN : a ∈ N i := hS₁N haS₁
          set U : Finset ι := S₂ ∪ T with hU
          have haU : a ∉ U := by
            intro h
            rcases Finset.mem_union.mp h with h | h
            · exact (Finset.mem_sdiff.mp h).2 haN
            · exact haT h
          have hUS : U ⊆ S := Finset.union_subset hS₂S (hTS₁.trans hS₁S)
          have hUcard : U.card < n := by
            have : U.card < S.card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
                ⟨hUS, fun h => haU (h ▸ haS)⟩)
            omega
          have hRU := (ih U hUcard).2 a haU
          have hQU := ihT hTS₁
          have heq : S₂ ∪ insert a T = insert a U := by
            rw [hU, Finset.union_insert]
          rw [heq, real_allFail_insert, Finset.prod_insert haT]
          have hnn : 0 ≤ 1 - x a := h0 a
          have hP0 : 0 ≤ μ.real (allFail A S₂) := measureReal_nonneg
          calc (1 - x a) * (∏ j ∈ T, (1 - x j)) * μ.real (allFail A S₂)
              = (1 - x a) * ((∏ j ∈ T, (1 - x j)) * μ.real (allFail A S₂)) := by ring
            _ ≤ (1 - x a) * μ.real (allFail A U) := mul_le_mul_of_nonneg_left hQU hnn
            _ ≤ μ.real (allFail A U) - μ.real (A a ∩ allFail A U) := by nlinarith
      have hchain := chain S₁ le_rfl
      have hSU : S₂ ∪ S₁ = S := Finset.sdiff_union_inter S (N i)
      rw [hSU] at hchain
      -- independence of `A i` from the failures outside `N i`
      have hind' := hind i S₂ hiS₂ hdisj
      have hmono : μ.real (A i ∩ allFail A S) ≤ μ.real (A i ∩ allFail A S₂) :=
        measureReal_mono (Set.inter_subset_inter_right _ (allFail_anti A hS₂S))
      have hprod : ∏ j ∈ N i, (1 - x j) ≤ ∏ j ∈ S₁, (1 - x j) :=
        prod_le_prod_of_subset_of_le_one' hS₁N _ h0 h1
      have hP2 : 0 ≤ μ.real (allFail A S₂) := measureReal_nonneg
      have hxi : 0 < x i := (hx i).1
      calc μ.real (A i ∩ allFail A S) ≤ μ.real (A i ∩ allFail A S₂) := hmono
        _ = μ.real (A i) * μ.real (allFail A S₂) := hind'
        _ ≤ (x i * ∏ j ∈ N i, (1 - x j)) * μ.real (allFail A S₂) :=
            mul_le_mul_of_nonneg_right (hP i) hP2
        _ ≤ (x i * ∏ j ∈ S₁, (1 - x j)) * μ.real (allFail A S₂) := by
            apply mul_le_mul_of_nonneg_right _ hP2
            exact mul_le_mul_of_nonneg_left hprod hxi.le
        _ = x i * ((∏ j ∈ S₁, (1 - x j)) * μ.real (allFail A S₂)) := by ring
        _ ≤ x i * μ.real (allFail A S) := mul_le_mul_of_nonneg_left hchain hxi.le
    -- the first claim
    refine ⟨?_, hR⟩
    rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
    · simp [allFail_empty]
    · set S' : Finset ι := S.erase k with hS'
      have hS'card : S'.card < n := by
        have : S'.card < S.card := Finset.card_erase_lt_of_mem hk
        omega
      obtain ⟨hQ', hR'⟩ := ih S' hS'card
      have hkS' : k ∉ S' := Finset.notMem_erase k S
      have hS : S = insert k S' := (Finset.insert_erase hk).symm
      rw [hS, real_allFail_insert, Finset.prod_insert hkS']
      have hnn : 0 ≤ 1 - x k := h0 k
      have := hR' k hkS'
      calc (1 - x k) * ∏ j ∈ S', (1 - x j) ≤ (1 - x k) * μ.real (allFail A S') :=
            mul_le_mul_of_nonneg_left hQ' hnn
        _ ≤ μ.real (allFail A S') - μ.real (A k ∩ allFail A S') := by nlinarith

end LLLAux

namespace CountingLLL.DetCount
open CSP MeasureTheory ProbabilityTheory AppliedComb.ManyFaces
open scoped Classical BigOperators

private noncomputable def uniformMeasure (Φ : CSP) : Measure Φ.Config :=
  ProbabilityTheory.uniformOn Set.univ

private theorem uniform_real (Φ : CSP) (P : Φ.Config → Prop) :
    (uniformMeasure Φ).real {σ | P σ} = Φ.prob P := by
  classical
  rw [CSP.prob]
  unfold uniformMeasure Measure.real
  have hset : {σ : Φ.Config | P σ} = (Finset.univ.filter P : Finset Φ.Config) := by
    ext σ
    simp
  rw [hset, ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset]
  simp [ENNReal.toReal_div]

private def badEvents (Φ : CSP) (E : Finset (Fin Φ.m)) (i : Fin Φ.m) : Set Φ.Config :=
  {σ | i ∈ E ∧ ¬ Φ.Sat i σ}

private noncomputable def adjustedX {m : ℕ} (E : Finset (Fin m)) (x : Fin m → ℝ) (i : Fin m) : ℝ :=
  if i ∈ E then x i else 1/2

private theorem bad_allFail (Φ : CSP) (E S : Finset (Fin Φ.m)) :
    allFail (badEvents Φ E) S = {σ | Φ.SatAll (S ∩ E) σ} := by
  ext σ
  simp only [allFail, Set.mem_iInter, Set.mem_compl_iff, badEvents, Set.mem_setOf_eq,
    CSP.SatAll, Finset.mem_inter, not_and]
  aesop

private theorem bad_independent (Φ : CSP) (E : Finset (Fin Φ.m)) (i : Fin Φ.m) :
    IndepOutside (uniformMeasure Φ) (badEvents Φ E) (Φ.nbr E) i := by
  intro S hi hS
  by_cases hiE : i ∈ E
  · have hd : ∀ j ∈ S ∩ E, Disjoint (Φ.scope i) (Φ.scope j) := by
      intro j hj
      obtain ⟨hjS, hjE⟩ := Finset.mem_inter.mp hj
      have hne : j ≠ i := fun h => hi (h ▸ hjS)
      by_contra hd
      have hjN : j ∈ Φ.nbr E i := by
        rw [CSP.nbr, Finset.mem_filter]
        exact ⟨hjE, hne, hd⟩
      exact Finset.disjoint_left.mp hS hjS hjN
    have hind := audit_scope_independent Φ i (S ∩ E) hd
    have hset : badEvents Φ E i = {σ | ¬ Φ.Sat i σ} := by ext σ; simp [badEvents, hiE]
    rw [hset, bad_allFail]
    change (uniformMeasure Φ).real {σ | ¬ Φ.Sat i σ ∧ Φ.SatAll (S ∩ E) σ} =
      (uniformMeasure Φ).real {σ | ¬ Φ.Sat i σ} *
      (uniformMeasure Φ).real {σ | Φ.SatAll (S ∩ E) σ}
    rw [uniform_real, uniform_real, uniform_real]
    unfold CSP.prob
    rw [mul_comm, ← mul_div_assoc]
    convert hind using 1
    all_goals repeat' first | (solve | ext w <;> simp) | congr 1
  · have hset : badEvents Φ E i = ∅ := by ext σ; simp [badEvents, hiE]
    rw [hset]
    simp

private theorem adjustedX_range (Φ : CSP) (E : Finset (Fin Φ.m)) (x : Fin Φ.m → ℝ)
    (hx : ∀ c ∈ E, 0 < x c ∧ x c < 1) :
    ∀ i, 0 < adjustedX E x i ∧ adjustedX E x i < 1 := by
  intro i
  by_cases hi : i ∈ E
  · simpa [adjustedX, hi] using hx i hi
  · norm_num [adjustedX, hi]

private theorem bad_prob_bound (Φ : CSP) (E : Finset (Fin Φ.m)) (x : Fin Φ.m → ℝ)
    (hx : ∀ c ∈ E, 0 < x c ∧ x c < 1)
    (h6 : ∀ c ∈ E, Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ x c * ∏ c' ∈ Φ.nbr E c, (1 - x c')) :
    ∀ i, (uniformMeasure Φ).real (badEvents Φ E i) ≤
      adjustedX E x i * ∏ j ∈ Φ.nbr E i, (1 - adjustedX E x j) := by
  intro i
  have heq : (∏ j ∈ Φ.nbr E i, (1 - adjustedX E x j)) =
      ∏ j ∈ Φ.nbr E i, (1 - x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjE : j ∈ E := (Finset.mem_filter.mp hj).1
    simp [adjustedX, hjE]
  by_cases hi : i ∈ E
  · have hset : badEvents Φ E i = {σ | ¬ Φ.Sat i σ} := by ext σ; simp [badEvents, hi]
    rw [hset, uniform_real, heq]
    simpa [adjustedX, hi] using h6 i hi
  · have hset : badEvents Φ E i = ∅ := by ext σ; simp [badEvents, hi]
    rw [hset, measureReal_empty, heq]
    have hp : 0 ≤ ∏ j ∈ Φ.nbr E i, (1 - x j) := by
      apply Finset.prod_nonneg
      intro j hj
      have hjE : j ∈ E := (Finset.mem_filter.mp hj).1
      linarith [(hx j hjE).2]
    simp [adjustedX, hi, hp]

private theorem bad_core (Φ : CSP) (E : Finset (Fin Φ.m)) (x : Fin Φ.m → ℝ)
    (hx : ∀ c ∈ E, 0 < x c ∧ x c < 1)
    (h6 : ∀ c ∈ E, Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ x c * ∏ c' ∈ Φ.nbr E c, (1 - x c'))
    (S : Finset (Fin Φ.m)) :
    (∏ j ∈ S, (1 - adjustedX E x j)) ≤
        (uniformMeasure Φ).real (allFail (badEvents Φ E) S) ∧
      ∀ i, i ∉ S → (uniformMeasure Φ).real (badEvents Φ E i ∩ allFail (badEvents Φ E) S) ≤
        adjustedX E x i * (uniformMeasure Φ).real (allFail (badEvents Φ E) S) := by
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  letI : IsProbabilityMeasure (uniformMeasure Φ) := by unfold uniformMeasure; infer_instance
  exact LLLAux.core (uniformMeasure Φ) (badEvents Φ E) (Φ.nbr E)
    (bad_independent Φ E) (adjustedX E x) (adjustedX_range Φ E x hx)
    (bad_prob_bound Φ E x hx h6) (S.card + 1) S (Nat.lt_succ_self _)

/-- Adding constraints lowers avoidance probability by at most the product of
one-minus-local-lemma parameters. -/
private theorem avoidance_chain (Φ : CSP) (E : Finset (Fin Φ.m)) (x : Fin Φ.m → ℝ)
    (hx : ∀ c ∈ E, 0 < x c ∧ x c < 1)
    (h6 : ∀ c ∈ E, Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ x c * ∏ c' ∈ Φ.nbr E c, (1 - x c'))
    (F T : Finset (Fin Φ.m)) (hdisj : Disjoint F T) (hT : T ⊆ E) :
    (∏ j ∈ T, (1 - x j)) * (uniformMeasure Φ).real (allFail (badEvents Φ E) F) ≤
      (uniformMeasure Φ).real (allFail (badEvents Φ E) (F ∪ T)) := by
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  letI : IsProbabilityMeasure (uniformMeasure Φ) := by unfold uniformMeasure; infer_instance
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      have haE : a ∈ E := hT (Finset.mem_insert_self a T)
      have hTE : T ⊆ E := fun j hj => hT (Finset.mem_insert_of_mem hj)
      have hdisjT : Disjoint F T := Finset.disjoint_left.mpr fun j hjF hjT =>
        Finset.disjoint_left.mp hdisj hjF (Finset.mem_insert_of_mem hjT)
      have haF : a ∉ F := fun haF =>
        Finset.disjoint_left.mp hdisj haF (Finset.mem_insert_self a T)
      have haU : a ∉ F ∪ T := by simp [haF, ha]
      have hind := (bad_core Φ E x hx h6 (F ∪ T)).2 a haU
      have hq := ih hdisjT hTE
      have hqpos : 0 ≤ 1 - x a := by linarith [(hx a haE).2]
      have hratio : adjustedX E x a = x a := by simp [adjustedX, haE]
      rw [hratio] at hind
      rw [Finset.union_insert, LLLAux.real_allFail_insert, Finset.prod_insert ha]
      calc
        (1 - x a) * (∏ j ∈ T, (1 - x j)) * (uniformMeasure Φ).real (allFail (badEvents Φ E) F)
            = (1 - x a) * ((∏ j ∈ T, (1 - x j)) * (uniformMeasure Φ).real (allFail (badEvents Φ E) F)) := by ring
        _ ≤ (1 - x a) * (uniformMeasure Φ).real (allFail (badEvents Φ E) (F ∪ T)) :=
          mul_le_mul_of_nonneg_left hq hqpos
        _ ≤ (uniformMeasure Φ).real (allFail (badEvents Φ E) (F ∪ T)) -
            (uniformMeasure Φ).real (badEvents Φ E a ∩ allFail (badEvents Φ E) (F ∪ T)) := by nlinarith

private theorem event_independent (Φ : CSP) (A : Φ.Config → Prop) (W : Finset (Fin Φ.n))
    (hA : ∀ σ σ', (∀ v ∈ W, σ v = σ' v) → (A σ ↔ A σ'))
    (F : Finset (Fin Φ.m)) (hF : ∀ c ∈ F, Disjoint W (Φ.scope c)) :
    Φ.prob (fun σ => A σ ∧ Φ.SatAll F σ) = Φ.prob A * Φ.prob (Φ.SatAll F) := by
  classical
  let X : Finset Φ.Config := Finset.univ.filter A
  let Y : Finset Φ.Config := Finset.univ.filter (Φ.SatAll F)
  let T := F.biUnion Φ.scope
  have hx : ∀ σ σ' : Φ.Config, (∀ v ∈ W, σ v = σ' v) → (σ ∈ X ↔ σ' ∈ X) := by
    intro σ σ' h
    simpa [X] using hA σ σ' h
  have hy : ∀ σ σ' : Φ.Config, (∀ v ∈ T, σ v = σ' v) → (σ ∈ Y ↔ σ' ∈ Y) := by
    intro σ σ' h
    simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and, CSP.SatAll]
    apply forall_congr'
    intro c
    apply forall_congr'
    intro hc
    have heq : (fun v : ↥(Φ.scope c) => σ v.1) = fun v : ↥(Φ.scope c) => σ' v.1 := by
      funext v
      exact h v.1 (Finset.mem_biUnion.mpr ⟨c, hc, v.2⟩)
    simp only [CSP.Sat, heq]
  have hWT : Disjoint W T := by
    apply Finset.disjoint_left.mpr
    intro v hv ht
    obtain ⟨c, hc, hvc⟩ := Finset.mem_biUnion.mp ht
    exact Finset.disjoint_left.mp (hF c hc) hv hvc
  have hcard := audit_dependent_disjoint_card (fun v => Fin (Φ.q v)) W T X Y hx hy hWT
  have hcardR : ((X ∩ Y).card : ℝ) * (Fintype.card Φ.Config : ℝ) =
      (X.card : ℝ) * (Y.card : ℝ) := by exact_mod_cast hcard
  have hXY : X ∩ Y = Finset.univ.filter (fun σ => A σ ∧ Φ.SatAll F σ) := by
    ext σ
    simp [X, Y]
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  have hC : (Fintype.card Φ.Config : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Φ.Config))
  have hreal : ((X ∩ Y).card : ℝ) / (Fintype.card Φ.Config : ℝ) =
    ((X.card : ℝ) / (Fintype.card Φ.Config : ℝ)) *
      ((Y.card : ℝ) / (Fintype.card Φ.Config : ℝ)) := by
    field_simp
    nlinarith
  unfold CSP.prob
  convert hreal using 1
  all_goals repeat' first | (solve | ext w <;> simp [X, Y]) | congr 1

theorem audit_conditional_lll (Φ : CSP) (E : Finset (Fin Φ.m)) (x : Fin Φ.m → ℝ)
    (hx : ∀ c ∈ E, 0 < x c ∧ x c < 1)
    (h6 : ∀ c ∈ E, Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ x c * ∏ c' ∈ Φ.nbr E c, (1 - x c'))
    (A : Φ.Config → Prop) (W : Finset (Fin Φ.n))
    (hA : ∀ σ σ' : Φ.Config, (∀ v ∈ W, σ v = σ' v) → (A σ ↔ A σ')) :
    Φ.condProb A (Φ.SatAll E) ≤
      Φ.prob A * ∏ c ∈ E.filter (fun c => ¬ Disjoint (Φ.scope c) W), (1 - x c)⁻¹ := by
  classical
  let near : Finset (Fin Φ.m) := E.filter (fun c => ¬ Disjoint (Φ.scope c) W)
  let far : Finset (Fin Φ.m) := E \ near
  have hnearE : near ⊆ E := Finset.filter_subset _ _
  have hfarE : far ⊆ E := Finset.sdiff_subset
  have hdisj : Disjoint far near := Finset.sdiff_disjoint
  have hunion : far ∪ near = E := Finset.sdiff_union_of_subset hnearE
  have hfar : ∀ c ∈ far, Disjoint W (Φ.scope c) := by
    intro c hc
    have hcE := hfarE hc
    have hcnear := (Finset.mem_sdiff.mp hc).2
    have h := fun hd : ¬ Disjoint (Φ.scope c) W => hcnear (Finset.mem_filter.mpr ⟨hcE, hd⟩)
    exact (not_not.mp h).symm
  have hP : 0 < ∏ c ∈ near, (1 - x c) := by
    apply Finset.prod_pos
    intro c hc
    linarith [(hx c (hnearE hc)).2]
  have hden : 0 < Φ.prob (Φ.SatAll E) := by
    have hcore := (bad_core Φ E x hx h6 E).1
    rw [bad_allFail, Finset.inter_self, uniform_real] at hcore
    have hprod : 0 < ∏ j ∈ E, (1 - adjustedX E x j) := by
      apply Finset.prod_pos
      intro j hj
      simp only [adjustedX, if_pos hj]
      linarith [(hx j hj).2]
    exact lt_of_lt_of_le hprod hcore
  have hchain := avoidance_chain Φ E x hx h6 far near hdisj hnearE
  rw [hunion, bad_allFail, bad_allFail, Finset.inter_self, Finset.inter_eq_left.mpr hfarE,
      uniform_real, uniform_real] at hchain
  have hmono : Φ.prob (fun σ => A σ ∧ Φ.SatAll E σ) ≤
      Φ.prob (fun σ => A σ ∧ Φ.SatAll far σ) := by
    letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
    letI : IsProbabilityMeasure (uniformMeasure Φ) := by unfold uniformMeasure; infer_instance
    rw [← uniform_real, ← uniform_real]
    apply measureReal_mono
    · intro σ hσ
      exact ⟨hσ.1, fun c hc => hσ.2 c (hfarE hc)⟩
    · exact measure_ne_top _ _
  have hind := event_independent Φ A W hA far hfar
  rw [hind] at hmono
  have hAn : 0 ≤ Φ.prob A := by unfold CSP.prob; positivity
  have hscaled : (∏ c ∈ near, (1 - x c)) * Φ.prob (fun σ => A σ ∧ Φ.SatAll E σ) ≤
      Φ.prob A * Φ.prob (Φ.SatAll E) := by
    calc
      _ ≤ (∏ c ∈ near, (1 - x c)) * (Φ.prob A * Φ.prob (Φ.SatAll far)) :=
        mul_le_mul_of_nonneg_left hmono hP.le
      _ = Φ.prob A * ((∏ c ∈ near, (1 - x c)) * Φ.prob (Φ.SatAll far)) := by ring
      _ ≤ Φ.prob A * Φ.prob (Φ.SatAll E) := mul_le_mul_of_nonneg_left hchain hAn
  have hnum : Φ.prob (fun σ => A σ ∧ Φ.SatAll E σ) ≤
      (Φ.prob A / (∏ c ∈ near, (1 - x c))) * Φ.prob (Φ.SatAll E) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hP).2
    nlinarith [hscaled]
  unfold CSP.condProb
  apply (div_le_iff₀ hden).2
  have hinv : (∏ c ∈ near, (1 - x c)⁻¹) = (∏ c ∈ near, (1 - x c))⁻¹ := by
    exact Finset.prod_inv_distrib _
  change Φ.prob (fun σ => A σ ∧ Φ.SatAll E σ) ≤
    (Φ.prob A * ∏ c ∈ near, (1 - x c)⁻¹) * Φ.prob (Φ.SatAll E)
  rw [hinv]
  simpa [div_eq_mul_inv] using hnum

end CountingLLL.DetCount

open CountingLLL.DetCount CountingLLL.DetCount.CSP
open scoped Classical BigOperators

/-- Theorem 2.2: the conditional LLL bound for a CSP subfamily. -/
theorem solution (Φ : CSP) (E : Finset (Fin Φ.m)) (x : Fin Φ.m → ℝ)
    (hx : ∀ c ∈ E, 0 < x c ∧ x c < 1)
    (h6 : ∀ c ∈ E, Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ x c * ∏ c' ∈ Φ.nbr E c, (1 - x c'))
    (A : Φ.Config → Prop) (W : Finset (Fin Φ.n))
    (hA : ∀ σ σ' : Φ.Config, (∀ v ∈ W, σ v = σ' v) → (A σ ↔ A σ')) :
    Φ.condProb A (Φ.SatAll E) ≤
      Φ.prob A * ∏ c ∈ E.filter (fun c => ¬ Disjoint (Φ.scope c) W), (1 - x c)⁻¹ :=
  CountingLLL.DetCount.audit_conditional_lll Φ E x hx h6 A W hA
