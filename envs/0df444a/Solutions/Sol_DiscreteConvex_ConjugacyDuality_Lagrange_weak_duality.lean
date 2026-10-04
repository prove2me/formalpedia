-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDuality.Lagrange.weak_duality
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:32:49.58331+00:00
-- url     : https://prove2.me/submissions/37590479-5897-46ad-8ea9-32d461423b89

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_InfP
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_SupD

set_option autoImplicit false

namespace WeakDualityCex1177

open DiscreteConvex.ConjugacyDuality DiscreteConvex.ConjugacyDuality.Lagrange

/-- A nonstandard `Zero` instance on `Unit → ℤ`: its "zero" is the constant function `1`. -/
def oddZero : Zero (Unit → ℤ) := ⟨fun _ => 1⟩

/-- Perturbation: finite (value `0`) exactly at `u = 1`, `+∞` elsewhere. -/
noncomputable def cexF : (Unit → ℤ) → (Unit → ℤ) → WithTop ℝ :=
  fun _ u => if u () = 1 then ((0 : ℝ) : WithTop ℝ) else ⊤

theorem infP_le : @InfP Unit Unit oddZero cexF ≤ 0 := by
  unfold InfP
  refine sInf_le_of_le (b := ToEReal (@PrimalValue Unit Unit oddZero cexF (fun _ => 0)))
    ⟨fun _ => 0, rfl⟩ (le_of_eq ?_)
  have h1 : @PrimalValue Unit Unit oddZero cexF (fun _ => 0) = ((0 : ℝ) : WithTop ℝ) := by
    show cexF (fun _ => 0) (fun _ => 1) = _
    simp [cexF]
  rw [h1]
  rfl

theorem one_le_dual : (1 : EReal) ≤ DualObjective cexF (fun _ => 1) := by
  unfold DualObjective
  refine le_sInf ?_
  rintro v ⟨x, rfl⟩
  unfold LagrangianKernel
  refine le_sInf ?_
  rintro w ⟨u, rfl⟩
  by_cases h : u () = 1
  · have hF : cexF x u = ((0 : ℝ) : WithTop ℝ) := by simp [cexF, h]
    rw [hF]
    have hs : (∑ i : Unit, (u i : ℝ) * ((fun _ => (1 : ℤ)) i : ℝ)) = 1 := by
      simp [h]
    rw [hs]
    show (1 : EReal) ≤ ((0 : ℝ) : EReal) + ((1 : ℝ) : EReal)
    simp
  · have hF : cexF x u = ⊤ := by simp [cexF, h]
    rw [hF]
    show (1 : EReal) ≤ (⊤ : EReal) + _
    rw [EReal.top_add_coe]
    exact le_top

theorem one_le_supD : (1 : EReal) ≤ SupD cexF :=
  le_trans one_le_dual (le_sSup ⟨fun _ => 1, rfl⟩)

theorem cex : ¬ (∀ {V U : Type} [Fintype U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ), InfP F ≥ SupD F) := by
  intro h
  have h1 := @h Unit Unit _ oddZero cexF
  have h2 : (1 : EReal) ≤ 0 := le_trans one_le_supD (le_trans h1 infP_le)
  rw [← EReal.coe_one, ← EReal.coe_zero, EReal.coe_le_coe_iff] at h2
  norm_num at h2

end WeakDualityCex1177

open DiscreteConvex.ConjugacyDuality.Lagrange in
theorem solution : ¬ (∀ {V U : Type} [Fintype U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ), InfP F ≥ SupD F) := by
  exact WeakDualityCex1177.cex
