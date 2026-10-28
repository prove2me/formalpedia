-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.lnat_convex_operations_and_restrictions
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:13:10.192869+00:00
-- url     : https://prove2.me/submissions/02ccc1b2-27fc-43c3-a1d4-c79a061f3f6d

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LinearWeight
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ProjectionZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SeparablePerturbZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_IntervalRestrict
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_Restriction

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsB

namespace DisLNHelp

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

theorem key (h : SeparablePerturbZ g0 psi0 ![2, 0] + SeparablePerturbZ g0 psi0 ![1, 1] ≥
    SeparablePerturbZ g0 psi0 (![2, 0] ⊔ ![1, 1]) + SeparablePerturbZ g0 psi0 (![2, 0] ⊓ ![1, 1])) :
    False := by
  have e1 : SeparablePerturbZ g0 psi0 ![2, 0] ≤ 0 :=
    G_le_zero _ ![0, 0] (by simp [g0, psi0])
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

lemma lift_elim (G : (Fin 2 → ℤ) → WithTop ℝ) (f : Fin 2 → ℤ) :
    LiftedFunctionL G (fun o => Option.elim o 0 f) = G f := by
  unfold LiftedFunctionL
  congr 1
  funext v
  simp

lemma elim_sup (f f' : Fin 2 → ℤ) :
    ((fun o => Option.elim o 0 f) ⊔ (fun o => Option.elim o 0 f') : Option (Fin 2) → ℤ)
      = fun o => Option.elim o 0 (f ⊔ f') := by
  funext o; cases o <;> simp

lemma elim_inf (f f' : Fin 2 → ℤ) :
    ((fun o => Option.elim o 0 f) ⊓ (fun o => Option.elim o 0 f') : Option (Fin 2) → ℤ)
      = fun o => Option.elim o 0 (f ⊓ f') := by
  funext o; cases o <;> simp

theorem keyLN : ¬ LNaturalConvex (SeparablePerturbZ g0 psi0) := by
  intro hL
  have h := hL.1 (fun o => Option.elim o 0 ![2, 0]) (fun o => Option.elim o 0 ![1, 1])
  rw [elim_sup, elim_inf, lift_elim, lift_elim, lift_elim, lift_elim] at h
  exact key h

lemma g0_LN : LNaturalConvex g0 := by
  refine ⟨?_, ⟨0, fun x => ?_⟩⟩
  · intro x y
    by_cases hx : x (some 0) = x (some 1)
    · by_cases hy : y (some 0) = y (some 1)
      · simp [LiftedFunctionL, g0, hx, hy]
      · simp [LiftedFunctionL, g0, hy]
    · simp [LiftedFunctionL, g0, hx]
  · simp [LiftedFunctionL, g0]

lemma hdom : (DomZ (SeparablePerturbZ g0 psi0)).Nonempty := by
  refine ⟨![2, 0], ?_⟩
  have := G_le_zero ![2, 0] ![0, 0] (by simp [g0, psi0])
  intro h
  rw [h] at this
  exact absurd (top_le_iff.mp this) (by simp)

end DisLNHelp

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g g1 g2 : (V → ℤ) → WithTop ℝ)
    (_hg : LNaturalConvex g) (_hg1 : LNaturalConvex g1) (_hg2 : LNaturalConvex g2),
    ((∀ lam : ℝ, 0 < lam → LNaturalConvex (fun p => PosScalarMul lam (g p))) ∧
     (∀ a : V → ℤ, ∀ beta : ℤ, beta ≠ 0 →
       LNaturalConvex (fun p => g (fun v => a v + beta * p v))) ∧
     (∀ x : V → ℝ, LNaturalConvex (LinearWeight g (fun v => - x v))) ∧
     (∀ U : Set V, (DomZ (ProjectionZ g U)).Nonempty → LNaturalConvex (ProjectionZ g U)) ∧
     (∀ psi : V → ℤ → WithTop ℝ, (DomZ (SeparablePerturbZ g psi)).Nonempty →
        LNaturalConvex (SeparablePerturbZ g psi)) ∧
     ((DomZ (fun p => g1 p + g2 p)).Nonempty → LNaturalConvex (fun p => g1 p + g2 p))) ∧
    (∀ a b : V → WithBot (WithTop ℤ), (DomZ (IntervalRestrict g a b)).Nonempty →
      LNaturalConvex (IntervalRestrict g a b)) ∧
    (∀ U : Finset V, (DomZ (Restriction g U)).Nonempty → LNaturalConvex (Restriction g U))) := by
  intro H
  exact DisLNHelp.keyLN
    ((H (V := Fin 2) DisLNHelp.g0 DisLNHelp.g0 DisLNHelp.g0
      DisLNHelp.g0_LN DisLNHelp.g0_LN DisLNHelp.g0_LN).1.2.2.2.2.1 DisLNHelp.psi0 DisLNHelp.hdom)
