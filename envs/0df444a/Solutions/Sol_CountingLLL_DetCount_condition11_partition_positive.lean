-- Prove2me | solution 1 for CountingLLL.DetCount.condition11_partition_positive
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T03:58:05.146202+00:00
-- url     : https://prove2.me/submissions/da8ae852-413a-461f-9867-57ab786e8418

import Definitions.Def_CountingLLL_DetCount_CSP
import Theorems.Thm_Combinatorics_finite_symmetric_local_lemma

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

theorem audit_pmax_nonneg (Φ : CSP) : 0 ≤ Φ.pmax := by
  unfold CSP.pmax
  exact NNReal.coe_nonneg _

theorem audit_bad_probability_le (Φ : CSP) (c : Fin Φ.m) :
    ((Finset.univ.filter (fun σ : Φ.Config => ¬ Φ.Sat c σ)).card : ℝ) /
      (Fintype.card Φ.Config : ℝ) ≤ Φ.pmax := by
  have h : Φ.violProb c ≤ Finset.univ.sup Φ.violProb := Finset.le_sup (Finset.mem_univ c)
  have hr : ((Φ.violProb c : NNReal) : ℝ) ≤ ((Finset.univ.sup Φ.violProb : NNReal) : ℝ) := by exact_mod_cast h
  simpa [CSP.violProb, CSP.pmax] using hr

theorem audit_overlap_degree (Φ : CSP) (c : Fin Φ.m) :
    (Finset.univ.filter (fun j => Φ.Overlap c j)).card ≤ Φ.Dmax + 1 := by
  let O : Finset (Fin Φ.m) := Finset.univ.filter (fun j => Φ.Overlap c j)
  have hc : c ∈ O := by
    change c ∈ Finset.univ.filter (fun j => Φ.Overlap c j)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨v, hv⟩ := Φ.scope_nonempty c
    exact fun h => Finset.disjoint_left.mp h hv hv
  have he : O.erase c = Φ.nbr Finset.univ c := by
    ext j
    simp [O, CSP.nbr, eq_comm]
  have hmax : (Φ.nbr Finset.univ c).card ≤ Φ.Dmax := by
    unfold CSP.Dmax CSP.Dsub
    exact Finset.le_sup (f := fun c => (Φ.nbr Finset.univ c).card) (Finset.mem_univ c)
  have hcard := Finset.card_erase_add_one hc
  rw [he] at hcard
  change O.card ≤ Φ.Dmax + 1
  omega

theorem audit_symmetric_numerical (Φ : CSP) (hΦ : Φ.Condition11) :
    4 * Φ.pmax * (((Φ.Dmax + 1 + 1 : ℕ) : ℝ)) < 1 := by
  have hp : 0 ≤ Φ.pmax := audit_pmax_nonneg Φ
  have hd : (0 : ℝ) ≤ Φ.Dmax := Nat.cast_nonneg _
  have he : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  by_cases hzero : Φ.pmax = 0
  · simp [hzero]
  · have hp' : 0 < Φ.pmax := lt_of_le_of_ne hp (Ne.symm hzero)
    have hs : 0 < ((Φ.Dmax : ℝ) + 1) ^ 2 := by positivity
    have hmul : 2 * ((Φ.Dmax : ℝ) + 1)^2 <
        Real.exp 1 * ((Φ.Dmax : ℝ) + 1)^2 := by nlinarith
    have hsq : 0 ≤ (Φ.Dmax : ℝ)^2 := sq_nonneg _
    have hgap : 0 < Real.exp 1 * ((Φ.Dmax : ℝ) + 1)^2 - ((Φ.Dmax : ℝ) + 2) := by nlinarith
    have hprod : 0 < 4 * Φ.pmax *
        (Real.exp 1 * ((Φ.Dmax : ℝ) + 1)^2 - ((Φ.Dmax : ℝ) + 2)) := by positivity
    unfold CSP.Condition11 at hΦ
    push_cast
    nlinarith [hprod]

/-- Condition 1.1 guarantees a satisfying assignment, hence every subfamily has
positive partition function. -/
theorem audit_condition11_positive (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) : 0 < Φ.Z E := by
  classical
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  let A : Fin Φ.m → Finset Φ.Config := fun c => Finset.univ.filter (fun σ => ¬ Φ.Sat c σ)
  have hind : ∀ (i : Fin Φ.m) (S : Finset (Fin Φ.m)),
      (∀ j, j ∈ S → ¬ Φ.Overlap i j) →
      ((Finset.filter (fun w => w ∈ A i)
          (Finset.univ.filter (fun w => ∀ j, j ∈ S → w ∉ A j))).card : ℝ) /
          (Fintype.card Φ.Config : ℝ) =
        ((Finset.univ.filter (fun w => ∀ j, j ∈ S → w ∉ A j)).card : ℝ) /
          (Fintype.card Φ.Config : ℝ) *
          ((A i).card : ℝ) / (Fintype.card Φ.Config : ℝ) := by
    intro i S hnot
    have hd : ∀ j ∈ S, Disjoint (Φ.scope i) (Φ.scope j) := by
      intro j hj
      have h := hnot j hj
      simpa [CSP.Overlap] using h
    have hi := audit_scope_independent Φ i S hd
    have heq : (Finset.univ.filter (fun w : Φ.Config => ∀ j, j ∈ S → w ∉ A j)) =
        Finset.univ.filter (Φ.SatAll S) := by
      ext w
      simp [A, CSP.SatAll]
    rw [heq]
    have heq' : Finset.filter (fun w => w ∈ A i) (Finset.univ.filter (Φ.SatAll S)) =
        Finset.univ.filter (fun σ => ¬ Φ.Sat i σ ∧ Φ.SatAll S σ) := by
      ext w
      simp [A, and_comm]
    rw [heq']
    exact hi
  have hsol : ∃ σ : Φ.Config, ∀ i, σ ∉ A i := by
    apply Combinatorics.finite_symmetric_local_lemma Φ.Config (Fin Φ.m) A Φ.Overlap (Φ.Dmax + 1) Φ.pmax
    · exact audit_overlap_degree Φ
    · exact audit_bad_probability_le Φ
    · intro i S hs
      convert hind i S hs using 1
      all_goals repeat' first | (solve | ext w <;> simp) | congr 1
    · exact audit_symmetric_numerical Φ hΦ
  obtain ⟨σ, hσ⟩ := hsol
  unfold CSP.Z
  apply Finset.card_pos.mpr
  refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro c hc
  have h := hσ c
  change σ ∉ Finset.univ.filter (fun w : Φ.Config => ¬ Φ.Sat c w) at h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h
  exact h

end CountingLLL.DetCount

/-- Every subfamily of a CSP satisfying Condition 1.1 has a satisfying assignment. -/
theorem solution (Φ : CountingLLL.DetCount.CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) : 0 < Φ.Z E :=
  CountingLLL.DetCount.audit_condition11_positive Φ hΦ E
