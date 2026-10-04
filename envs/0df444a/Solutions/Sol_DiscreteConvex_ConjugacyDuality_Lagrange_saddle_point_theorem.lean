-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDuality.Lagrange.saddle_point_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:16:26.037244+00:00
-- url     : https://prove2.me/submissions/267ca93f-023a-43ed-801f-1ce3269a8210

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_LagrangianKernel
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_InfP
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_SupD
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_OptP
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_OptD

set_option autoImplicit false

namespace SaddleCex

open DiscreteConvex.ConjugacyDuality DiscreteConvex.ConjugacyDuality.Lagrange

/-- A nonstandard `Zero` instance on `Unit → ℤ`: its "zero" is the constant function `1`. -/
def oddZero : Zero (Unit → ℤ) := ⟨fun _ => 1⟩

/-- Indicator of the genuine zero vector: `0` at `u = 0`, `+∞` elsewhere. -/
noncomputable def ind : (Unit → ℤ) → WithTop ℝ :=
  fun u => if u () = 0 then ((0 : ℝ) : WithTop ℝ) else ⊤

noncomputable def cexF : (Unit → ℤ) → (Unit → ℤ) → WithTop ℝ := fun _ => ind

theorem conj_ind (p : Unit → ℤ) : ConvexConjugate ind p = ((0 : ℝ) : WithTop ℝ) := by
  unfold ConvexConjugate
  have hS : sSup {v : EReal | ∃ x : Unit → ℤ,
      v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (ind x)} = ((0 : ℝ) : EReal) := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro v ⟨x, rfl⟩
      by_cases h : x () = 0
      · have hx : ind x = ((0 : ℝ) : WithTop ℝ) := by simp [ind, h]
        rw [hx]
        have hs : (∑ i : Unit, (p i : ℝ) * (x i : ℝ)) = 0 := by simp [h]
        rw [hs]
        show ((0 : ℝ) : EReal) - ((0 : ℝ) : EReal) ≤ ((0 : ℝ) : EReal)
        simp
      · have hx : ind x = ⊤ := by simp [ind, h]
        rw [hx]
        show _ - (⊤ : EReal) ≤ _
        rw [EReal.sub_top]
        exact bot_le
    · refine le_sSup ⟨fun _ => 0, ?_⟩
      have hx : ind (fun _ => 0) = ((0 : ℝ) : WithTop ℝ) := by simp [ind]
      rw [hx]
      show ((0 : ℝ) : EReal) = ((∑ i : Unit, (p i : ℝ) * (((fun _ => (0 : ℤ)) i : ℤ) : ℝ) : ℝ) : EReal)
          - ((0 : ℝ) : EReal)
      simp
  rw [hS]
  rfl

theorem conj_zero (u : Unit → ℤ) :
    ConvexConjugate (fun _ : Unit → ℤ => ((0 : ℝ) : WithTop ℝ)) u = ind u := by
  unfold ConvexConjugate
  have hT : ∀ p : Unit → ℤ,
      ((∑ i, (u i : ℝ) * (p i : ℝ) : ℝ) : EReal) - ToEReal ((0 : ℝ) : WithTop ℝ)
        = (((u () : ℝ) * (p () : ℝ) : ℝ) : EReal) := by
    intro p
    show ((∑ i, (u i : ℝ) * (p i : ℝ) : ℝ) : EReal) - ((0 : ℝ) : EReal) = _
    simp
  by_cases h : u () = 0
  · have hi : ind u = ((0 : ℝ) : WithTop ℝ) := by simp [ind, h]
    rw [hi]
    have hS : sSup {v : EReal | ∃ p : Unit → ℤ,
        v = ((∑ i, (u i : ℝ) * (p i : ℝ) : ℝ) : EReal) - ToEReal ((0 : ℝ) : WithTop ℝ)}
          = ((0 : ℝ) : EReal) := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro v ⟨p, rfl⟩
        rw [hT p, h]
        simp
      · refine le_sSup ⟨0, ?_⟩
        rw [hT 0, h]
        simp
    rw [hS]
    rfl
  · have hi : ind u = ⊤ := by simp [ind, h]
    rw [hi]
    have h1 : (1 : ℤ) ≤ u () * u () := by
      rw [← abs_mul_abs_self]
      have := Int.one_le_abs h
      nlinarith
    have h1r : (1 : ℝ) ≤ (u () : ℝ) * (u () : ℝ) := by exact_mod_cast h1
    have hS : sSup {v : EReal | ∃ p : Unit → ℤ,
        v = ((∑ i, (u i : ℝ) * (p i : ℝ) : ℝ) : EReal) - ToEReal ((0 : ℝ) : WithTop ℝ)}
          = ⊤ := by
      refine sSup_eq_top.mpr ?_
      intro b hb
      induction b using EReal.rec with
      | bot =>
        refine ⟨(((u () : ℝ) * ((0 : ℤ) : ℝ) : ℝ) : EReal), ⟨fun _ => 0, (hT (fun _ => 0)).symm⟩, ?_⟩
        exact EReal.bot_lt_coe _
      | top => exact absurd hb (lt_irrefl _)
      | coe r =>
        set k : ℕ := ⌈r⌉₊ + 1 with hk
        have hkr : r < (k : ℝ) := by
          rw [hk]; push_cast
          linarith [Nat.le_ceil r]
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by rw [hk]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈r⌉₊]
        refine ⟨(((u () : ℝ) * (((u () * (k : ℤ) : ℤ)) : ℝ) : ℝ) : EReal),
          ⟨fun _ => u () * (k : ℤ), (hT (fun _ => u () * (k : ℤ))).symm⟩, ?_⟩
        rw [EReal.coe_lt_coe_iff]
        push_cast
        nlinarith
    rw [hS]
    rfl

theorem hF_cex : ∀ x : Unit → ℤ, ConvexConjugate (ConvexConjugate (cexF x)) = cexF x := by
  intro x
  funext u
  have h1 : ConvexConjugate (cexF x) = fun _ => ((0 : ℝ) : WithTop ℝ) := by
    funext p
    exact conj_ind p
  rw [h1]
  exact conj_zero u

theorem kernel_le_zero (x y : Unit → ℤ) : LagrangianKernel cexF x y ≤ ((0 : ℝ) : EReal) := by
  unfold LagrangianKernel
  refine sInf_le_of_le ⟨fun _ => 0, rfl⟩ (le_of_eq ?_)
  have hx : cexF x (fun _ => 0) = ((0 : ℝ) : WithTop ℝ) := by simp [cexF, ind]
  rw [hx]
  show ((0 : ℝ) : EReal) + ((∑ i : Unit, (((fun _ => (0 : ℤ)) i : ℤ) : ℝ) * (y i : ℝ) : ℝ) : EReal)
    = ((0 : ℝ) : EReal)
  simp

theorem kernel_ge_zero (x y : Unit → ℤ) : ((0 : ℝ) : EReal) ≤ LagrangianKernel cexF x y := by
  unfold LagrangianKernel
  refine le_sInf ?_
  rintro w ⟨u, rfl⟩
  by_cases h : u () = 0
  · have hx : cexF x u = ((0 : ℝ) : WithTop ℝ) := by simp [cexF, ind, h]
    rw [hx]
    have hs : (∑ i : Unit, (u i : ℝ) * (y i : ℝ)) = 0 := by simp [h]
    rw [hs]
    show ((0 : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) + ((0 : ℝ) : EReal)
    simp
  · have hx : cexF x u = ⊤ := by simp [cexF, ind, h]
    rw [hx]
    show ((0 : ℝ) : EReal) ≤ (⊤ : EReal) + _
    rw [EReal.top_add_coe]
    exact le_top

theorem kernel_eq_zero (x y : Unit → ℤ) : LagrangianKernel cexF x y = ((0 : ℝ) : EReal) :=
  le_antisymm (kernel_le_zero x y) (kernel_ge_zero x y)

theorem dual_eq_zero (y : Unit → ℤ) : DualObjective cexF y = ((0 : ℝ) : EReal) := by
  unfold DualObjective
  apply le_antisymm
  · exact sInf_le_of_le ⟨fun _ => 0, (kernel_eq_zero _ y).symm⟩ le_rfl
  · refine le_sInf ?_
    rintro v ⟨x, rfl⟩
    rw [kernel_eq_zero]

theorem supD_eq_zero : SupD cexF = ((0 : ℝ) : EReal) := by
  unfold SupD
  apply le_antisymm
  · refine sSup_le ?_
    rintro v ⟨y, rfl⟩
    rw [dual_eq_zero]
  · exact le_sSup_of_le ⟨fun _ => 0, (dual_eq_zero _).symm⟩ le_rfl

theorem primal_top (x : Unit → ℤ) : @PrimalValue Unit Unit oddZero cexF x = ⊤ := by
  show cexF x (fun _ => 1) = ⊤
  simp [cexF, ind]

theorem infP_top : @InfP Unit Unit oddZero cexF = ⊤ := by
  unfold InfP
  apply le_antisymm le_top
  refine le_sInf ?_
  rintro v ⟨x, rfl⟩
  rw [primal_top]
  rfl

theorem cex : ¬ (∀ {V U : Type} [Fintype U] [DecidableEq U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ)
    (hF : ∀ x : V → ℤ, ConvexConjugate (ConvexConjugate (F x)) = F x),
    ((OptP F).Nonempty ∧ (OptD F).Nonempty ∧
        InfP F ≠ ⊤ ∧ InfP F ≠ ⊥ ∧ SupD F ≠ ⊤ ∧ SupD F ≠ ⊥ ∧ InfP F = SupD F) ↔
      (∃ xbar : V → ℤ, ∃ ybar : U → ℤ,
        LagrangianKernel F xbar ybar ≠ ⊤ ∧ LagrangianKernel F xbar ybar ≠ ⊥ ∧
        (∀ x : V → ℤ, LagrangianKernel F x ybar ≤ LagrangianKernel F xbar ybar) ∧
        (∀ y : U → ℤ, LagrangianKernel F xbar ybar ≤ LagrangianKernel F xbar y) ∧
        xbar ∈ OptP F ∧ ybar ∈ OptD F)) := by
  intro h
  have h2 := (@h Unit Unit _ _ oddZero cexF hF_cex)
  have hR : (∃ xbar : Unit → ℤ, ∃ ybar : Unit → ℤ,
        LagrangianKernel cexF xbar ybar ≠ ⊤ ∧ LagrangianKernel cexF xbar ybar ≠ ⊥ ∧
        (∀ x : Unit → ℤ, LagrangianKernel cexF x ybar ≤ LagrangianKernel cexF xbar ybar) ∧
        (∀ y : Unit → ℤ, LagrangianKernel cexF xbar ybar ≤ LagrangianKernel cexF xbar y) ∧
        xbar ∈ @OptP Unit Unit _ oddZero cexF ∧ ybar ∈ OptD cexF) := by
    refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [kernel_eq_zero]; exact EReal.coe_ne_top 0
    · rw [kernel_eq_zero]; exact EReal.coe_ne_bot 0
    · intro x; rw [kernel_eq_zero, kernel_eq_zero]
    · intro y; rw [kernel_eq_zero, kernel_eq_zero]
    · show ToEReal (@PrimalValue Unit Unit oddZero cexF _) = @InfP Unit Unit oddZero cexF
      rw [primal_top, infP_top]; rfl
    · show DualObjective cexF _ = SupD cexF
      rw [dual_eq_zero, supD_eq_zero]
  have hL := h2.mpr hR
  exact hL.2.2.1 infP_top

end SaddleCex

open DiscreteConvex.ConjugacyDuality in
open DiscreteConvex.ConjugacyDuality.Lagrange in
theorem solution : ¬ (∀ {V U : Type} [Fintype U] [DecidableEq U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ)
    (hF : ∀ x : V → ℤ, ConvexConjugate (ConvexConjugate (F x)) = F x),
    ((OptP F).Nonempty ∧ (OptD F).Nonempty ∧
        InfP F ≠ ⊤ ∧ InfP F ≠ ⊥ ∧ SupD F ≠ ⊤ ∧ SupD F ≠ ⊥ ∧ InfP F = SupD F) ↔
      (∃ xbar : V → ℤ, ∃ ybar : U → ℤ,
        LagrangianKernel F xbar ybar ≠ ⊤ ∧ LagrangianKernel F xbar ybar ≠ ⊥ ∧
        (∀ x : V → ℤ, LagrangianKernel F x ybar ≤ LagrangianKernel F xbar ybar) ∧
        (∀ y : U → ℤ, LagrangianKernel F xbar ybar ≤ LagrangianKernel F xbar y) ∧
        xbar ∈ OptP F ∧ ybar ∈ OptD F)) := by
  exact SaddleCex.cex

#print axioms solution
