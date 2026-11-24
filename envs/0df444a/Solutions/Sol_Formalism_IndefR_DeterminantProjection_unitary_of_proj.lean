-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.unitary_of_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:15.474797+00:00
-- url     : https://prove2.me/submissions/a1f2533a-e1ec-4171-9664-d5cf247d2827

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.DeterminantProjection
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.IndefR.DeterminantProjection
theorem _root_.solution (σ : A →+* A) (J R : Matrix n n A) (hRR : R * R = R)
    (hJR : J * R = (R.map σ)ᵀ * J) (x : A) (hx : σ x * x = 1) :
    ((1 + (x - 1) • R).map σ)ᵀ * J * (1 + (x - 1) • R) = J := by
  have hm : ((1 + (x - 1) • R).map σ)ᵀ = 1 + (σ x - 1) • (R.map σ)ᵀ := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  have h1 : (R.map σ)ᵀ * J = J * R := hJR.symm
  have h2 : (R.map σ)ᵀ * J * R = J * R := by rw [h1, Matrix.mul_assoc, hRR]
  have e : (1 + (σ x - 1) • (R.map σ)ᵀ) * J * (1 + (x - 1) • R)
      = J + (x - 1) • (J * R) + (σ x - 1) • ((R.map σ)ᵀ * J)
        + ((σ x - 1) * (x - 1)) • ((R.map σ)ᵀ * J * R) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    module
  have hs : (x - 1) + ((σ x - 1) + (σ x - 1) * (x - 1)) = 0 := by linear_combination hx
  rw [hm, e, h2, h1, add_assoc, add_assoc, ← add_smul, ← add_smul, hs, zero_smul, add_zero]
end Formalism.IndefR.DeterminantProjection
