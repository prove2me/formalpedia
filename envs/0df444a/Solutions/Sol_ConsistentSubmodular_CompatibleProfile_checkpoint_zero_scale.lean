-- Prove2me | solution 1 for ConsistentSubmodular.CompatibleProfile.checkpoint_zero_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:30.340203+00:00
-- url     : https://prove2.me/submissions/a32acfab-966f-41c5-ac93-1e7725864fdc

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Paths
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicFacts

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace Objective

variable {d : ℕ} (f : Objective d)

theorem residual_le_sum_singletons (I : Finset (Fin d)) :
    f.value I - f.value ∅ ≤ ∑ i ∈ I, (f.value {i} - f.value ∅) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.sum_insert ha]
    have hs := f.submodular I {a}
    have hd : Disjoint I {a} := Finset.disjoint_singleton_right.mpr ha
    rw [Finset.union_singleton, Finset.disjoint_iff_inter_eq_empty.mp hd] at hs
    linarith

theorem value_eq_empty_of_singletons (h : ∀ i, f.value {i} - f.value ∅ = 0)
    (I : Finset (Fin d)) : f.value I = f.value ∅ := by
  have hu := f.residual_le_sum_singletons I
  simp only [h, Finset.sum_const_zero] at hu
  have hl := f.monotone ∅ I (Finset.empty_subset _)
  linarith

end Objective

namespace CompatibleProfile

variable {d : ℕ} (P : CompatibleProfile d)

variable {m : ℕ} (Q : CompatibleProfile (m + 1))

theorem constant_of_zero_scale (hzero : Q.residual 0 0 = 0)
    (hopt0 : ∀ i, Q.residual 0 i ≤ Q.residual 0 0) (t : ℕ) (I : Finset (Fin (m + 1))) :
    (Q.objective t).value I = Q.baseline t := by
  apply (Q.objective t).value_eq_empty_of_singletons
  intro i
  have hu := (Q.residualOn_antitone (Nat.zero_le t) {i}).trans (hopt0 i)
  have hl := Q.residualOn_nonnegative t {i}
  rw [hzero] at hu
  exact le_antisymm hu hl

theorem multilinearValue_eq_baseline_of_zero_scale (hzero : Q.residual 0 0 = 0)
    (hopt0 : ∀ i, Q.residual 0 i ≤ Q.residual 0 0) (t : ℕ) (p : Point m) :
    Q.multilinearValue t p = Q.baseline t := by
  unfold multilinearValue
  have hfun : (Q.objective t).value = fun _ => Q.baseline t :=
    funext (Q.constant_of_zero_scale hzero hopt0 t)
  rw [hfun, finiteExpectation_const]

end CompatibleProfile

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.CompatibleProfile
variable {d : ℕ} (P : CompatibleProfile d)
variable {m : ℕ} (Q : CompatibleProfile (m + 1))

theorem solution (hzero : Q.residual 0 0 = 0)
    (hopt0 : ∀ i, Q.residual 0 i ≤ Q.residual 0 0) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (Q.objective t.val).value {t} ≤ Q.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      Q.SafePath 0 ((3 : ℝ) / 4 * (Q.objective 0).value {0}) entry ∧
      Q.SafePath m ((3 : ℝ) / 4 * (Q.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by
  have hval (t : ℕ) (i : Fin (m + 1)) (p : Point m) :
      (3 : ℝ) / 4 * (Q.objective t).value {i} ≤ Q.multilinearValue t p := by
    rw [Q.constant_of_zero_scale hzero hopt0, Q.multilinearValue_eq_baseline_of_zero_scale hzero hopt0]
    exact mul_le_of_le_one_left ((Q.objective t).nonnegative ∅) (by norm_num)
  refine ⟨vertex 0, PolygonalPath.constant (vertex 0),
    PolygonalPath.segment (vertex 0) (vertex (Fin.last m)), simplex_vertex 0,
    (by rw [supportCard_vertex]; omega), (fun t => hval t.val t _), rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact PolygonalPath.segment_terminal _ _
  · constructor
    · intro j
      exact ⟨simplex_vertex 0, hval 0 0 _⟩
    · intro j
      exact Fin.elim0 j
  · constructor
    · intro j
      constructor
      · change IsSimplex (if j = 0 then vertex 0 else vertex (Fin.last m))
        split_ifs <;> exact simplex_vertex _
      · exact hval m (Fin.last m) _
    · intro j x hx hx'
      change Fin 1 at j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      exact ⟨(simplex_vertex 0).mix (simplex_vertex (Fin.last m)) hx hx', hval m (Fin.last m) _⟩
  · simp

end
