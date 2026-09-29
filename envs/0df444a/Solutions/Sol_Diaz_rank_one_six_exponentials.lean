-- Prove2me | solution 1 for Diaz.rank_one_six_exponentials
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:12:04.862909+00:00
-- url     : https://prove2.me/submissions/786986c5-2647-46af-a400-d561f7928007

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {F k : Type*} [Field F] [Field k] [Algebra k F]
    (V : Set F)
    (hsix : ∀ M : Fin 2 → Fin 3 → F, (∀ i j, M i j ∈ V) →
      LinearIndependent k M → LinearIndependent k (fun j i => M i j) →
      LinearIndependent F M)
    {a b : F} {y : Fin 3 → F}
    (hab : LinearIndependent k ![a, b]) (hy : LinearIndependent k y)
    (hV : ∀ j, a * y j ∈ V ∧ b * y j ∈ V) : False := by
  set M : Fin 2 → Fin 3 → F := ![fun j => a * y j, fun j => b * y j] with hM
  have ha0 : a ≠ 0 := by
    intro h
    have := hab.ne_zero 0
    simp [h] at this
  have hb0 : b ≠ 0 := by
    intro h
    have := hab.ne_zero 1
    simp [h] at this
  have hmem : ∀ i j, M i j ∈ V := by
    intro i j
    fin_cases i
    · simpa [hM] using (hV j).1
    · simpa [hM] using (hV j).2
  have hrows : LinearIndependent k M := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hpt : ∀ j, (g 0 • a + g 1 • b) * y j = 0 := by
      intro j
      have h := congrFun hg j
      simp [hM, Fin.sum_univ_two] at h
      rw [add_mul, smul_mul_assoc, smul_mul_assoc]
      exact h
    have hy0 : y 0 ≠ 0 := hy.ne_zero 0
    have hcoef : g 0 • a + g 1 • b = 0 := by
      have := hpt 0
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hy0
    have := Fintype.linearIndependent_iff.mp hab g (by
      simpa [Fin.sum_univ_two] using hcoef)
    exact this i
  have hcols : LinearIndependent k (fun j i => M i j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 : ∑ j, g j • (a * y j) = 0 := by
      have := congrFun hg 0
      simpa [hM] using this
    have hsum : a * ∑ j, g j • y j = 0 := by
      rw [Finset.mul_sum]
      rw [← h0]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [Algebra.smul_def]
      ring
    have : ∑ j, g j • y j = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd h ha0
      · exact h
    exact Fintype.linearIndependent_iff.mp hy g this j
  have hF := hsix M hmem hrows hcols
  have hdep : b • M 0 + (-a) • M 1 = 0 := by
    funext j
    simp [hM, smul_eq_mul]
    ring
  have := Fintype.linearIndependent_iff.mp hF ![b, -a] (by
    simpa [Fin.sum_univ_two] using hdep) 0
  simp at this
  exact hb0 this
