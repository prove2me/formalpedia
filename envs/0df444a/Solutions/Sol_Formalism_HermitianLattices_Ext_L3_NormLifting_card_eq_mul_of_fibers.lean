-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.card_eq_mul_of_fibers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:24.155224+00:00
-- url     : https://prove2.me/submissions/e6a08453-2a46-4fd1-ae66-f566113edcef

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution {X Y : Type*} [Finite X] (f : X → Y) (c : ℕ)
    (hc : ∀ y, Nat.card {x : X // f x = y} = c) : Nat.card X = c * Nat.card Y := by

  classical
  by_cases hY : Finite Y
  · haveI := Fintype.ofFinite Y
    haveI := Fintype.ofFinite X
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma,
      Finset.sum_congr rfl (fun y _ => hc y), Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card (α := Y), mul_comm]
  · haveI : Infinite Y := not_finite_iff_infinite.mp hY
    rw [Nat.card_eq_zero_of_infinite (α := Y), mul_zero]
    obtain ⟨y, hy⟩ := (Set.finite_range f).infinite_compl.nonempty
    have hc0 : c = 0 := by
      rw [← hc y, Nat.card_eq_zero]
      left
      exact ⟨fun x => hy ⟨x.1, x.2⟩⟩
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun x => ?_⟩
    have h1 := hc (f x)
    rw [hc0, Nat.card_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact h1.false ⟨x, rfl⟩
    · exact absurd (inferInstance : Finite {x' : X // f x' = f x}) (not_finite_iff_infinite.mpr h1)
end Formalism.HermitianLattices.Ext.L3.NormLifting
