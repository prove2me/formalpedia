-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityC.argmin_infconv_attained_iff
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:31:50.97196+00:00
-- url     : https://prove2.me/submissions/c38d797b-6d49-439d-a81d-43d5869e4cbf

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConvE
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LinearWeight

namespace Cex169349d3

open DiscreteConvex.ConjugacyDualityC

/-- `g1 p = p 0`: finite everywhere, unbounded below. -/
noncomputable def g1 : (Fin 1 → ℤ) → WithTop ℝ := fun p => (((p 0 : ℤ) : ℝ) : WithTop ℝ)

/-- `g2 = +∞` everywhere. -/
noncomputable def g2 : (Fin 1 → ℤ) → WithTop ℝ := fun _ => ⊤

theorem infConv_top (p : Fin 1 → ℤ) : InfConv g1 g2 p = ⊤ := by
  unfold InfConv
  have : {L : WithTop ℝ | ∃ p1 p2 : Fin 1 → ℤ, p = p1 + p2 ∧ L = g1 p1 + g2 p2} = {⊤} := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p1, p2, -, rfl⟩
      simp [g2]
    · rintro rfl
      exact ⟨p, 0, by simp, by simp [g2]⟩
  rw [this, csInf_singleton]

theorem infConvE_ne_bot (p : Fin 1 → ℤ) : InfConvE g1 g2 p ≠ ⊥ := by
  unfold InfConvE
  have : {L : EReal | ∃ p1 p2 : Fin 1 → ℤ, p = p1 + p2 ∧
      L = ToEReal (g1 p1) + ToEReal (g2 p2)} = {⊤} := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p1, p2, -, rfl⟩
      have h2 : ToEReal (g2 p2) = ⊤ := rfl
      have h1 : ToEReal (g1 p1) = ((((p1 0 : ℤ) : ℝ)) : EReal) := rfl
      rw [h1, h2]
      exact EReal.coe_add_top _
    · rintro rfl
      refine ⟨p, 0, by simp, ?_⟩
      have h2 : ToEReal (g2 0) = ⊤ := rfl
      have h1 : ToEReal (g1 p) = ((((p 0 : ℤ) : ℝ)) : EReal) := rfl
      rw [h1, h2]
      exact (EReal.coe_add_top _).symm
  rw [this, sInf_singleton]
  exact bot_lt_top.ne'

theorem argmin_g1_empty : ArgMin (LinearWeight g1 (0 : Fin 1 → ℝ)) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  have h := hp (fun _ => p 0 - 1)
  simp only [LinearWeight, g1, Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero,
    WithTop.coe_zero, add_zero] at h
  have h' : ((p 0 : ℤ) : ℝ) ≤ ((p 0 - 1 : ℤ) : ℝ) := WithTop.coe_le_coe.mp h
  push_cast at h'
  linarith

theorem argmin_infconv_univ : ArgMin (LinearWeight (InfConv g1 g2) (0 : Fin 1 → ℝ)) = Set.univ := by
  ext p
  simp only [Set.mem_univ, iff_true]
  intro y
  simp [LinearWeight, infConv_top]

end Cex169349d3

open DiscreteConvex.ConjugacyDualityC Classical Pointwise in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g1 g2 : (V → ℤ) → WithTop ℝ)
    (hfin : ∀ p : V → ℤ, InfConvE g1 g2 p ≠ ⊥)
    (hattained : ∀ p : V → ℤ, InfConv g1 g2 p ≠ ⊤ →
      ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ InfConv g1 g2 p = g1 p1 + g2 p2),
    ∀ x : V → ℝ, ArgMin (LinearWeight (InfConv g1 g2) x) =
      ArgMin (LinearWeight g1 x) + ArgMin (LinearWeight g2 x)) := by
  intro h
  have e := h (V := Fin 1) Cex169349d3.g1 Cex169349d3.g2 Cex169349d3.infConvE_ne_bot
    (fun p hp => absurd (Cex169349d3.infConv_top p) hp) 0
  rw [Cex169349d3.argmin_infconv_univ, Cex169349d3.argmin_g1_empty, Set.empty_add] at e
  exact Set.univ_nonempty.ne_empty e
