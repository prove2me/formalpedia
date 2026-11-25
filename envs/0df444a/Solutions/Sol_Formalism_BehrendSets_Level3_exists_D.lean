-- Prove2me | solution 1 for Formalism.BehrendSets.Level3.exists_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:31.058863+00:00
-- url     : https://prove2.me/submissions/e9421663-0b8c-40b6-9aff-d1a41193e7a5

import Definitions.Def_Formalism_BehrendSets_StatementE
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_CoeffPowEqZeroOfLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Level3
namespace Formalism.BehrendSets.Level3
theorem _root_.solution (Q : ℕ) : ∃ D : ℤ⟦X⟧, D + X * D ^ Q = 1 := by
  set P : ℤ⟦X⟧ := X * (PowerSeries.mk 1) ^ Q with hP
  have hP0 : constantCoeff P = 0 := by simp [hP]
  have hP1' : coeff 1 P = 1 := by
    rw [hP, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      map_pow]
    simp
  have hP1 : IsUnit (coeff 1 P) := by rw [hP1']; exact isUnit_one
  set y := P.substInvOfIsUnit hP1
  have hy : HasSubst y := HasSubst.substInvOfIsUnit P hP1
  have e1 : subst y P = X := subst_substInvOfIsUnit_right P hP0 hP1
  set φ := substAlgHom (R := ℤ) hy
  have hφ : ∀ f : ℤ⟦X⟧, subst y f = φ f := fun f => by rw [coe_substAlgHom]
  rw [hφ, hP, map_mul, map_pow, ← hφ X, subst_X hy] at e1
  have e2 : φ (PowerSeries.mk 1) * (1 - y) = 1 := by
    have := congrArg φ (mk_one_mul_one_sub_eq_one ℤ)
    rwa [map_mul, map_sub, map_one, ← hφ X, subst_X hy] at this
  refine ⟨1 - y, ?_⟩
  have : X * (1 - y) ^ Q = y := by
    calc X * (1 - y) ^ Q = y * (φ (PowerSeries.mk 1)) ^ Q * (1 - y) ^ Q := by rw [e1]
      _ = y * (φ (PowerSeries.mk 1) * (1 - y)) ^ Q := by rw [mul_pow, mul_assoc]
      _ = y := by rw [e2, one_pow, mul_one]
  rw [this]
  ring
end Formalism.BehrendSets.Level3
