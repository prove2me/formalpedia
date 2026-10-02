-- Prove2me | solution 1 for DiscreteConvex.CombinatorialC.prop_2_28_exists_boundary_arc
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:04:31.760064+00:00
-- url     : https://prove2.me/submissions/41781d22-174a-4699-bfcd-241debe62d4a

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsCircuit
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR

set_option autoImplicit false

namespace CexD35783a6

open DiscreteConvex.CombinatorialC

/-- The directed 2-cycle on `Fin 2`: arc `i` goes from `i` to `i + 1`. -/
def srcC : Fin 2 → Fin 2 := fun i => i
def dstC : Fin 2 → Fin 2 := fun i => i + 1
def piC : Fin 2 → ℝ := fun _ => 1
def w1C : Fin 2 → ℝ := ![1, -5]
def w2C : Fin 2 → ℝ := fun _ => 0

theorem suppPos_piC : SuppPosR piC = Finset.univ := by
  ext i; simp [SuppPosR, piC]

theorem card_eq_C : ∀ v : Fin 2, (Finset.univ.filter fun a : Fin 2 => srcC a = v).card =
    (Finset.univ.filter fun a : Fin 2 => dstC a = v).card := by decide

theorem circuit_piC : IsCircuit srcC dstC piC := by
  refine ⟨fun _ => Or.inl rfl, ?_, 1, fun i => i, fun i => i, ⟨fun _ _ h => h, fun i => rfl⟩, ?_⟩
  · intro v
    simp only [Boundary, piC]
    rw [Finset.sum_const, Finset.sum_const, card_eq_C v, sub_self]
  · ext i; simp [SuppPosR, SuppNegR, piC]

theorem cex : ¬ (∀ {V A : Type} [Fintype A] [Fintype V] [DecidableEq V]
    [DecidableEq A] (src dst : A → V) (S : Finset A) (w1 w2 : A → ℝ) (pi1 : A → ℝ) (a : A)
    (hpi1 : IsCircuit src dst pi1) (ha : a ∈ SuppPosR pi1 ∩ S)
    (hw1 : dotProduct w1 pi1 ≤ 0) (hw2 : dotProduct w2 (-pi1) ≤ 0)
    (haw : 0 < w1 a - w2 a),
    ∃ b ∈ SuppPosR pi1 ∩ S, w1 b - w2 b < 0) := by
  intro h
  obtain ⟨b, hb, hbw⟩ := h srcC dstC {0} w1C w2C piC 0 circuit_piC
    (by simp [suppPos_piC])
    (by norm_num [dotProduct, Fin.sum_univ_two, w1C, piC])
    (by simp [dotProduct, w2C])
    (by simp [w1C, w2C])
  have hb0 : b = 0 := by simpa using (Finset.mem_inter.mp hb).2
  subst hb0
  simp [w1C, w2C] at hbw
  linarith

end CexD35783a6

theorem solution : ¬ (∀ {V A : Type} [Fintype A] [Fintype V] [DecidableEq V]
    [DecidableEq A] (src dst : A → V) (S : Finset A) (w1 w2 : A → ℝ) (pi1 : A → ℝ) (a : A)
    (hpi1 : DiscreteConvex.CombinatorialC.IsCircuit src dst pi1)
    (ha : a ∈ DiscreteConvex.CombinatorialC.SuppPosR pi1 ∩ S)
    (hw1 : dotProduct w1 pi1 ≤ 0) (hw2 : dotProduct w2 (-pi1) ≤ 0)
    (haw : 0 < w1 a - w2 a),
    ∃ b ∈ DiscreteConvex.CombinatorialC.SuppPosR pi1 ∩ S, w1 b - w2 b < 0) := by
  exact CexD35783a6.cex
