-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.lconvex_basic_operations
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:11:53.748014+00:00
-- url     : https://prove2.me/submissions/9facaff9-2e28-483f-adce-2704d4c894f2

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LinearWeight
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ProjectionZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SeparablePerturbZ

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsB

namespace DisLBHelp

noncomputable def g0 : (Fin 2 → ℤ) → WithTop ℝ := fun q => if q 0 = q 1 then 0 else ⊤

noncomputable def psi0 : Fin 2 → ℤ → WithTop ℝ := fun v d =>
  if v = 0 then (if d = 0 ∨ d = 2 then 0 else ⊤) else (if d = 0 then 0 else ⊤)

lemma sInf_top_of_sub {s : Set (WithTop ℝ)} (h : s ⊆ {⊤}) : sInf s = ⊤ :=
  if_pos (Or.inl h)

lemma g0_nonneg (q : Fin 2 → ℤ) : 0 ≤ g0 q := by
  unfold g0; split_ifs <;> simp

lemma psi0_nonneg (v : Fin 2) (d : ℤ) : 0 ≤ psi0 v d := by
  unfold psi0; split_ifs <;> simp

lemma G_le_zero (p q : Fin 2 → ℤ) (hq : g0 q + ∑ v, psi0 v (p v - q v) = 0) :
    SeparablePerturbZ g0 psi0 p ≤ 0 := by
  unfold SeparablePerturbZ
  have hb : BddBelow {L : WithTop ℝ | ∃ q : Fin 2 → ℤ, L = g0 q + ∑ v, psi0 v (p v - q v)} := by
    refine ⟨0, ?_⟩
    rintro L ⟨q', rfl⟩
    exact add_nonneg (g0_nonneg q') (Finset.sum_nonneg fun v _ => psi0_nonneg v _)
  exact (WithTop.isGLB_sInf' hb).1 ⟨q, hq.symm⟩

lemma G_top (p : Fin 2 → ℤ)
    (h : ∀ t : ℤ, psi0 0 (p 0 - t) + psi0 1 (p 1 - t) = ⊤) :
    SeparablePerturbZ g0 psi0 p = ⊤ := by
  unfold SeparablePerturbZ
  apply sInf_top_of_sub
  rintro L ⟨q, rfl⟩
  rw [Set.mem_singleton_iff, Fin.sum_univ_two]
  unfold g0
  split_ifs with hq
  · rw [zero_add, hq]; exact h _
  · rfl

theorem key : ¬ SBF (SeparablePerturbZ g0 psi0) := by
  intro hS
  have h := hS ![2, 0] ![1, 1]
  have e1 : SeparablePerturbZ g0 psi0 ![2, 0] ≤ 0 :=
    G_le_zero _ ![0, 0] (by simp [g0, psi0, Fin.sum_univ_two])
  have e2 : SeparablePerturbZ g0 psi0 ![1, 1] ≤ 0 :=
    G_le_zero _ ![1, 1] (by simp [g0, psi0])
  have e3 : SeparablePerturbZ g0 psi0 (![2, 0] ⊔ ![1, 1]) = ⊤ := by
    apply G_top
    intro t
    simp only [Pi.sup_apply]
    simp only [psi0]
    norm_num
    omega
  rw [e3, top_add] at h
  have : SeparablePerturbZ g0 psi0 ![2, 0] + SeparablePerturbZ g0 psi0 ![1, 1] ≤ 0 := by
    simpa using add_le_add e1 e2
  exact absurd (top_le_iff.mp (h.trans this)) (by simp)

end DisLBHelp

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g g1 g2 : (V → ℤ) → WithTop ℝ)
    (_hg : SBF g ∧ TRF g),
    (∀ lam : ℝ, 0 < lam →
      SBF (fun p => PosScalarMul lam (g p)) ∧ TRF (fun p => PosScalarMul lam (g p))) ∧
    (∀ a : V → ℤ, ∀ beta : ℤ, beta ≠ 0 →
      SBF (fun p => g (fun v => a v + beta * p v)) ∧
      TRF (fun p => g (fun v => a v + beta * p v))) ∧
    (∀ x : V → ℝ, SBF (LinearWeight g (fun v => - x v)) ∧ TRF (LinearWeight g (fun v => - x v))) ∧
    (∀ U : Set V, (DomZ (ProjectionZ g U)).Nonempty →
      SBF (ProjectionZ g U) ∧ TRF (ProjectionZ g U)) ∧
    (∀ psi : V → ℤ → WithTop ℝ, (DomZ (SeparablePerturbZ g psi)).Nonempty →
      SBF (SeparablePerturbZ g psi) ∧ TRF (SeparablePerturbZ g psi)) ∧
    ((DomZ (fun p => g1 p + g2 p)).Nonempty → SBF g1 → TRF g1 → SBF g2 → TRF g2 →
      SBF (fun p => g1 p + g2 p) ∧ TRF (fun p => g1 p + g2 p))) := by
  intro H
  have hsbf : SBF DisLBHelp.g0 := by
    intro p q
    by_cases hp : p 0 = p 1
    · by_cases hq : q 0 = q 1
      · simp [DisLBHelp.g0, hp, hq]
      · simp [DisLBHelp.g0, hq]
    · simp [DisLBHelp.g0, hp]
  have htrf : TRF DisLBHelp.g0 := ⟨0, fun p => by simp [DisLBHelp.g0]⟩
  have hdom : (DomZ (SeparablePerturbZ DisLBHelp.g0 DisLBHelp.psi0)).Nonempty := by
    refine ⟨![2, 0], ?_⟩
    have := DisLBHelp.G_le_zero ![2, 0] ![0, 0] (by simp [DisLBHelp.g0, DisLBHelp.psi0, Fin.sum_univ_two])
    intro h
    rw [h] at this
    exact absurd (top_le_iff.mp this) (by simp)
  exact DisLBHelp.key
    ((H (V := Fin 2) DisLBHelp.g0 DisLBHelp.g0 DisLBHelp.g0 ⟨hsbf, htrf⟩).2.2.2.2.1
      DisLBHelp.psi0 hdom).1
