-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityB.theorem_3_2_biconjugate
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:29:48.814473+00:00
-- url     : https://prove2.me/submissions/de315391-e9f4-4a8c-9cd8-121ab5936c24

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConjF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsClosedConvexF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE
import Definitions.Def_DiscreteConvex_IntegralConvexityB_NeverBot

open DiscreteConvex.IntegralConvexityB

/-- The non-convex function `f(x) = -x²` on `ℝ¹`. -/
noncomputable def negSq : (Unit → ℝ) → EReal := fun x => ((-(x () ^ 2) : ℝ) : EReal)

lemma conj_negSq_top (p : Unit → ℝ) : ConjF negSq p = ⊤ := by
  unfold ConjF
  refine sSup_eq_top.mpr ?_
  intro b hb
  induction b using EReal.rec with
  | bot =>
    refine ⟨((dotProduct p (fun _ => (0 : ℝ)) : ℝ) : EReal) - negSq (fun _ => 0),
      ⟨fun _ => 0, rfl⟩, ?_⟩
    simp [negSq, dotProduct]
  | top => exact absurd hb (lt_irrefl _)
  | coe M =>
    set t : ℝ := |p ()| + |M| + 1 with ht
    refine ⟨((dotProduct p (fun _ => t) : ℝ) : EReal) - negSq (fun _ => t),
      ⟨fun _ => t, rfl⟩, ?_⟩
    have hval : ((dotProduct p (fun _ => t) : ℝ) : EReal) - negSq (fun _ => t) =
        ((p () * t + t ^ 2 : ℝ) : EReal) := by
      simp only [negSq, dotProduct, Finset.univ_unique, Finset.sum_singleton]
      rw [← EReal.coe_sub]; congr 1; ring
    rw [hval, EReal.coe_lt_coe_iff]
    have h1 : -|p ()| ≤ p () := neg_abs_le _
    have h2 : 0 ≤ |p ()| := abs_nonneg _
    have h3 : M ≤ |M| := le_abs_self _
    have h4 : 0 ≤ |M| := abs_nonneg _
    have ht0 : 0 ≤ t := by rw [ht]; linarith
    nlinarith [mul_le_mul_of_nonneg_right h1 ht0]

theorem solution : ¬ (∀ {V : Type} [Fintype V] (f : (V → ℝ) → EReal)
    (hdom : (DomE f).Nonempty) (hnb : NeverBot f),
    (IsProperConvex (ConjF f) ∧ IsClosedConvexF (ConjF f)) ∧
      (∀ g : (V → ℝ) → EReal, IsClosedConvexF g → IsProperConvex g →
        ConjF (ConjF g) = g)) := by
  intro h
  have hdom : (DomE negSq).Nonempty := ⟨fun _ => 0, by simp [DomE, negSq]⟩
  have hnb : NeverBot negSq := fun x => EReal.coe_ne_bot _
  obtain ⟨⟨⟨-, -, ⟨p, hp⟩⟩, -⟩, -⟩ := @h Unit _ negSq hdom hnb
  exact hp.1 (conj_negSq_top p)

#print axioms solution
