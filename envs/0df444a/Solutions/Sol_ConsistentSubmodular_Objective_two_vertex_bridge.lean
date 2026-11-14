-- Prove2me | solution 1 for ConsistentSubmodular.Objective.two_vertex_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:31.392239+00:00
-- url     : https://prove2.me/submissions/2f306154-3de4-45ad-85d2-e02ac9d43a4d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Simplex
import Theorems.Thm_ConsistentSubmodular_sum_weight_disjoint

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteExpectation_mul (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) :
    finiteExpectation p (fun S => c * v S) = c * finiteExpectation p v := by
  simp only [finiteExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem finiteExpectation_hit (p : ι → ℝ) (L : Finset ι) :
    finiteExpectation p (fun S => if (L ∩ S).Nonempty then 1 else 0) =
      1 - ∏ i ∈ L, (1 - p i) := by
  have hterm (S : Finset ι) : bernoulliWeight p S * (if (L ∩ S).Nonempty then 1 else 0) =
      bernoulliWeight p S - (if Disjoint S L then bernoulliWeight p S else 0) := by
    have hiff : (L ∩ S).Nonempty ↔ ¬Disjoint S L := by
      rw [Finset.inter_comm, Finset.not_disjoint_iff_nonempty_inter]
    by_cases hd : Disjoint S L <;> simp [hiff, hd]
  unfold finiteExpectation
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, sum_bernoulliWeight, sum_weight_disjoint]

theorem finiteExpectation_weighted_hit (p : ι → ℝ) (L : Finset ι) (w : ℝ) :
    finiteExpectation p (fun S => if (L ∩ S).Nonempty then w else 0) =
      w * (1 - ∏ i ∈ L, (1 - p i)) := by
  have hpoint : (fun S => if (L ∩ S).Nonempty then w else 0) =
      (fun S => w * (if (L ∩ S).Nonempty then 1 else 0)) := by
    funext S
    split_ifs <;> simp
  rw [hpoint, finiteExpectation_mul, finiteExpectation_hit]

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {m n : ℕ}

theorem solution (f : Objective (m + 1)) (a b : Fin (m + 1)) (hab : a ≠ b)
    (V : ℝ) (hV : 0 ≤ V) (ha : V ≤ f.value {a}) (hb : V ≤ f.value {b})
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (3 : ℝ) / 4 * V ≤ finiteExpectation (mix (vertex a) (vertex b) x) f.value := by
  classical
  let p := mix (vertex a) (vertex b) x
  have hp : IsSimplex p := (simplex_vertex a).mix (simplex_vertex b) hx hx1
  have hc : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i => ⟨hp.1 i, hp.coordinate_le_one i⟩
  have hm := finiteExpectation_mono p hc (v := fun I => if ({a, b} ∩ I).Nonempty then V else 0)
    (w := f.value) (by
      intro I
      split_ifs with hn
      · obtain ⟨i, hi⟩ := hn
        have hiI := (Finset.mem_inter.mp hi).2
        have hiab := (Finset.mem_inter.mp hi).1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hiab
        rcases hiab with rfl | rfl
        · exact ha.trans (f.monotone _ _ (Finset.singleton_subset_iff.mpr hiI))
        · exact hb.trans (f.monotone _ _ (Finset.singleton_subset_iff.mpr hiI))
      · exact f.nonnegative I)
  rw [finiteExpectation_weighted_hit] at hm
  have hprod : (∏ i ∈ ({a, b}:Finset (Fin (m + 1))), (1 - p i)) = x * (1 - x) := by
    dsimp [p]
    rw [prod_mix_vertices_complement _ a b hab]
    simp
  rw [hprod] at hm
  have hquad : x * (1 - x) ≤ (1 : ℝ) / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hh := mul_nonneg hV (sub_nonneg.mpr hquad)
  dsimp [p] at hm
  nlinarith only [hm, hh]

end
