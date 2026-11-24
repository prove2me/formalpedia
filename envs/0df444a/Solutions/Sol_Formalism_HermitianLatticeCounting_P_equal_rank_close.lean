-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.equal_rank_close
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:43.850805+00:00
-- url     : https://prove2.me/submissions/7ad4b78e-c0c9-429b-a3bc-29a979534331

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open CellDecomposition
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.SEqKClose := by
  intro C k f g Hh NT hC hg hH hNT hNTH hρ
  set ρ := ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) with hρd
  have hρ0 : 0 ≤ ρ := by positivity
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast (by omega : 2 ≤ C)
  have h1 : (2 / g) ^ (k * k * f) ≤ ((C : ℝ) / g) ^ (k * k * f) :=
    pow_le_pow_left₀ (by positivity) (by gcongr) _
  have h2 : ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) ≤ ((C * k * f : ℕ) : ℝ) ^ (4 * k * f) := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC)
  have h3 : NT ^ k * Hh ^ ((C - 1) * k) ≤ Hh ^ (C * k) := by
    calc NT ^ k * Hh ^ ((C - 1) * k) ≤ Hh ^ k * Hh ^ ((C - 1) * k) := by gcongr
      _ = Hh ^ (C * k) := by
          rw [← pow_add]; congr 1
          obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
          simp; ring
  calc (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * Hh ^ ((C - 1) * k)
      = (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * (NT ^ k * Hh ^ ((C - 1) * k)) := by ring
    _ ≤ ((C : ℝ) / g) ^ (k * k * f) * ((C * k * f : ℕ) : ℝ) ^ (4 * k * f) * Hh ^ (C * k) := by gcongr
    _ = ρ ^ k := by
        rw [hρd, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
        have e1 : k * k * f = k * f * k := by ring
        have e2 : 4 * k * f = 4 * f * k := by ring
        rw [e1, e2]; ring
    _ ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ hρ0 hρ _
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
end Formalism.HermitianLatticeCounting.P
