-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.closedN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:33:35.348016+00:00
-- url     : https://prove2.me/submissions/e92a2a1c-6ccd-4ec3-8be0-98b292446eb8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_closedG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution : ClosedN := by
  intro k r
  have hG : IsClosedSubgroup (GV k r) := closedG k r
  have memU : ∀ y ∈ Nset k r, y ∈ GV k r := fun y hy => by
    obtain ⟨h, -, -⟩ := hy
    exact h
  have toQ : ∀ y : Mat k r, y ∈ Nset k r → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y j c = if j = c then 1 else 0) := by
    intro y hy c hc j hj
    obtain ⟨_, h1, h2⟩ := hy
    by_cases hcr : c.val < r
    · have e : eI k r ⟨c.val, hcr⟩ = c := Fin.ext rfl
      have h3 := h1 ⟨c.val, hcr⟩ j (by show c.val ≤ j.val; omega)
      rw [e] at h3
      exact h3
    · exact h2 j c (by omega) hc (by omega)
  have ofQ : ∀ y : Mat k r, y ∈ GV k r → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y j c = if j = c then 1 else 0) → y ∈ Nset k r := by
    intro y hyU hQ
    refine ⟨hyU, ?_, ?_⟩
    · intro a i hai
      have ha := a.isLt
      have e : (eI k r a).val = a.val := rfl
      exact hQ (eI k r a) (by omega) i (by omega)
    · intro i j hj1 hj2 hi
      exact hQ j hj2 i (by omega)
  have mulQ : ∀ y z : Mat k r, (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y j c = if j = c then 1 else 0) → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        z j c = if j = c then 1 else 0) → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        (y * z) j c = if j = c then 1 else 0) := by
    intro y z hy hz c hc j hj
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · rw [hy c hc j hj, hz c hc c (by omega)]
      simp
    · intro l _ hlc
      by_cases hl : min c.val r ≤ l.val
      · rw [hz c hc l hl, if_neg hlc, mul_zero]
      · have hjl : j ≠ l := fun h => by rw [h] at hj; exact hl hj
        rw [hy l (by omega) j (by omega), if_neg hjl, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have invQ : ∀ y : Mat k r, IsUnit y.det → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y j c = if j = c then 1 else 0) → (∀ c : Fin (2 * r + k + 1), c.val ≤ r + k → ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val →
        y⁻¹ j c = if j = c then 1 else 0) := by
    intro y hu hy
    have hx : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hu
    have main : ∀ m : ℕ, ∀ c : Fin (2 * r + k + 1), c.val = m → c.val ≤ r + k →
        ∀ j : Fin (2 * r + k + 1), min c.val r ≤ j.val → y⁻¹ j c = if j = c then 1 else 0 := by
      intro m
      refine Nat.strong_induction_on m ?_
      intro m ih c hcm hc j hj
      have h1 := congrFun (congrFun hx j) c
      rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single c] at h1
      · rw [hy c hc c (by omega)] at h1
        simpa using h1
      · intro l _ hlc
        by_cases hl : min c.val r ≤ l.val
        · rw [hy c hc l hl, if_neg hlc, mul_zero]
        · have hjl : j ≠ l := fun h => by rw [h] at hj; exact hl hj
          rw [ih l.val (by omega) l rfl (by omega) j (by omega), if_neg hjl, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ c) h
    intro c hc j hj
    exact main c.val c rfl hc j hj
  have hc : ∀ (p : Prop) (i j : Fin (2 * r + k + 1)) (v : ℂ), IsClosed {g : Mat k r | p → g i j = v} := by
    intro p i j v
    by_cases hp : p
    · simp only [hp, true_implies]
      exact isClosed_eq (continuous_id.matrix_elem i j) continuous_const
    · simp only [hp, false_implies, Set.setOf_true]
      exact isClosed_univ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ofQ 1 hG.one_mem (fun c _ j _ => Matrix.one_apply)
  · intro a ha b hb
    exact ofQ _ (hG.mul_mem a (memU a ha) b (memU b hb)) (mulQ a b (toQ a ha) (toQ b hb))
  · intro a ha
    exact ofQ _ (hG.inv_mem a (memU a ha)) (invQ a (hG.unit a (memU a ha)) (toQ a ha))
  · intro a ha
    exact hG.unit a (memU a ha)
  · have e : Nset k r = GV k r ∩ ((⋂ a : Fin r, ⋂ i : Fin (2 * r + k + 1),
        {g : Mat k r | a.val ≤ i.val → g i (eI k r a) = if i = eI k r a then 1 else 0}) ∩
        (⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1),
        {g : Mat k r | r ≤ j.val → j.val ≤ r + k → r ≤ i.val → g i j = if i = j then 1 else 0})) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      exact Iff.rfl
    rw [e]
    refine hG.closed.inter ((isClosed_iInter fun a => isClosed_iInter fun i => hc _ i _ _).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => ?_))
    simpa only [and_imp] using hc (r ≤ j.val ∧ j.val ≤ r + k ∧ r ≤ i.val) i j (if i = j then 1 else 0)
end Formalism.FourierDecayAlt.P.B2x2
