-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDuality.Lagrange.lagrangian_kernel_recovers_F
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:48:16.524232+00:00
-- url     : https://prove2.me/submissions/a374b6cc-d77c-4711-a1d2-239e51108662

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_LagrangianKernel
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_PrimalValue

set_option autoImplicit false

namespace KernelRecoversCexA5d5

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

theorem cex : ¬ (∀ {V U : Type} [Fintype U] [DecidableEq U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ)
    (hF : ∀ x : V → ℤ, ConvexConjugate (ConvexConjugate (F x)) = F x),
    (∀ x : V → ℤ, ∀ u : U → ℤ,
        ToEReal (F x u) = sSup {v : EReal | ∃ y : U → ℤ,
          v = LagrangianKernel F x y - ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}) ∧
    (∀ x : V → ℤ,
        ToEReal (PrimalValue F x) =
          sSup {v : EReal | ∃ y : U → ℤ, v = LagrangianKernel F x y})) := by
  intro h
  have h2 := (@h Unit Unit _ _ oddZero cexF hF_cex).2 (fun _ => 0)
  have hP : @PrimalValue Unit Unit oddZero cexF (fun _ => 0) = ⊤ := by
    show cexF (fun _ => 0) (fun _ => 1) = ⊤
    simp [cexF, ind]
  rw [hP] at h2
  have hle : sSup {v : EReal | ∃ y : Unit → ℤ, v = LagrangianKernel cexF (fun _ => 0) y}
      ≤ ((0 : ℝ) : EReal) := by
    refine sSup_le ?_
    rintro v ⟨y, rfl⟩
    exact kernel_le_zero _ y
  rw [← h2] at hle
  exact absurd hle (by
    show ¬ ((⊤ : EReal) ≤ ((0 : ℝ) : EReal))
    exact not_le.mpr (EReal.coe_lt_top 0))

end KernelRecoversCexA5d5

open DiscreteConvex.ConjugacyDuality in
open DiscreteConvex.ConjugacyDuality.Lagrange in
theorem solution : ¬ (∀ {V U : Type} [Fintype U] [DecidableEq U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ)
    (hF : ∀ x : V → ℤ, ConvexConjugate (ConvexConjugate (F x)) = F x),
    (∀ x : V → ℤ, ∀ u : U → ℤ,
        ToEReal (F x u) = sSup {v : EReal | ∃ y : U → ℤ,
          v = LagrangianKernel F x y - ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}) ∧
    (∀ x : V → ℤ,
        ToEReal (PrimalValue F x) =
          sSup {v : EReal | ∃ y : U → ℤ, v = LagrangianKernel F x y})) := by
  exact KernelRecoversCexA5d5.cex
