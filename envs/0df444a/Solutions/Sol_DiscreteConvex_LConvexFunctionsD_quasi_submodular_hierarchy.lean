-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.quasi_submodular_hierarchy
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:36:52.355985+00:00
-- url     : https://prove2.me/submissions/7e6c65b0-10e2-4afe-9c97-52b8f73de124

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSB
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSB
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightPlus

set_option autoImplicit false

open DiscreteConvex.LConvexFunctionsD

namespace QSBCex

/-- `dom g = {(t, 0) : t ∈ {0,1}}` (coordinates `true`, `false`), `g(t,0) = 1 - t`. -/
noncomputable def g (p : Bool → ℤ) : WithTop ℝ :=
  if p false = 0 ∧ 0 ≤ p true ∧ p true ≤ 1 then (((1 - p true : ℤ) : ℝ) : WithTop ℝ) else ⊤

theorem g_sbf : SBF g := by
  intro p q
  by_cases hp : p false = 0 ∧ 0 ≤ p true ∧ p true ≤ 1
  · by_cases hq : q false = 0 ∧ 0 ≤ q true ∧ q true ≤ 1
    · have hs : (p ⊔ q) false = 0 ∧ 0 ≤ (p ⊔ q) true ∧ (p ⊔ q) true ≤ 1 := by
        simp only [Pi.sup_apply]
        refine ⟨by rw [hp.1, hq.1]; simp, le_sup_of_le_left hp.2.1, sup_le hp.2.2 hq.2.2⟩
      have hi : (p ⊓ q) false = 0 ∧ 0 ≤ (p ⊓ q) true ∧ (p ⊓ q) true ≤ 1 := by
        simp only [Pi.inf_apply]
        refine ⟨by rw [hp.1, hq.1]; simp, le_inf hp.2.1 hq.2.1, inf_le_of_left_le hp.2.2⟩
      unfold g
      rw [if_pos hp, if_pos hq, if_pos hs, if_pos hi]
      simp only [Pi.sup_apply, Pi.inf_apply]
      rcases le_total (p true) (q true) with h | h
      · rw [sup_eq_right.mpr h, inf_eq_left.mpr h, add_comm]
      · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]
    · have : g q = ⊤ := by unfold g; rw [if_neg hq]
      rw [this]; simp
  · have : g p = ⊤ := by unfold g; rw [if_neg hp]
    rw [this]; simp

theorem not_ssqsb : ¬ SSQSB g := by
  intro h
  let p : Bool → ℤ := fun b => if b then 1 else 0
  let q : Bool → ℤ := fun b => if b then 0 else 1
  have hpq1 : p ⊔ q = fun _ => 1 := by funext b; cases b <;> simp [p, q]
  have hpq2 : p ⊓ q = fun _ => 0 := by funext b; cases b <;> simp [p, q]
  have h1 := (h p q).1
  rw [hpq1, hpq2] at h1
  have gq : g q = ⊤ := by unfold g; simp [q]
  have g1 : g (fun _ => 1) = ⊤ := by unfold g; simp
  have g0 : g (fun _ => 0) = ((1 : ℝ) : WithTop ℝ) := by unfold g; simp
  have gp : g p = ((0 : ℝ) : WithTop ℝ) := by unfold g; simp [p]
  rw [gq, g1, g0, gp] at h1
  have := h1 le_rfl
  rw [WithTop.coe_le_coe] at this
  norm_num at this

end QSBCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ),
    (SBF g → SSQSB g) ∧ (SSQSB g → QSB g) ∧
    (SSQSB g → SSQSBw g) ∧ (QSB g → QSBw g) ∧
    (SBF g ↔ ∀ x : V → ℝ, QSBw (LinearWeightPlus g x))) := by
  intro h
  exact QSBCex.not_ssqsb ((h QSBCex.g).1 QSBCex.g_sbf)

#print axioms solution
