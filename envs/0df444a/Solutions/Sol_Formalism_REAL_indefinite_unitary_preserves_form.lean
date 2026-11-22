-- Prove2me | solution 1 for Formalism.REAL.indefinite_unitary_preserves_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:43:42.325773+00:00
-- url     : https://prove2.me/submissions/0c84d442-adfe-46e7-a5a1-a65b67aa0071

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Formalism.REAL
variable {n : ℕ}
private lemma Jm_mul_Jm_eq_one (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g * Jm ε * gᴴ = Jm ε ∧ IsUnit g := by
  unfold inUJ at hg
  have h1 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [mul_assoc]
      _ = 1 := by rw [hg, Jm_mul_Jm_eq_one]
  have h2 : g * (Jm ε * gᴴ * Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp h1
    | exact (Matrix.mul_eq_one_comm).mp h1
    | exact Matrix.mul_eq_one_comm.1 h1
  refine ⟨?_, ⟨⟨g, _, h2, h1⟩, rfl⟩⟩
  calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
        simp only [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
    _ = Jm ε := by rw [h2, one_mul]
end Formalism.REAL
