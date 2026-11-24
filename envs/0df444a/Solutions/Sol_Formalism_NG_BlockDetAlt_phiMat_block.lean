-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.phiMat_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:42.841654+00:00
-- url     : https://prove2.me/submissions/3a66f8ed-1cbb-47d5-9a58-f3a8360d8580

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') (p q : g) (n : ℕ) :
    coefMat n (Matrix.of fun i j => phiMat R' Θ (p, i) (q, j)) =
      (if n = 0 ∧ p = q then 1 else 0) -
        (if n = 1 then (Θ p q : X' → Matrix d d (FractionRing O)) else 0) := by
  have hX : ∀ (c : X' → FractionRing O) (k : ℕ),
      PowerSeries.coeff k (PowerSeries.X * PowerSeries.C c) = if k = 1 then c else 0 := by
    intro c k
    rw [mul_comm, ← pow_one (PowerSeries.X : PowerSeries (X' → FractionRing O)), PowerSeries.coeff_C_mul_X_pow]
  ext x' i j
  simp only [coefMat, phiMat, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, hX,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hn0 : n = 0 <;> by_cases hn1 : n = 1 <;> by_cases hpq : p = q <;> by_cases hij : i = j <;>
    simp [hn0, hn1, hpq, hij, PowerSeries.coeff_one, Matrix.one_apply] <;> omega
end Formalism.NG.BlockDetAlt
