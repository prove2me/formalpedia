-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_exists_ty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:08.920811+00:00
-- url     : https://prove2.me/submissions/a6097b1f-1083-49a3-a62b-a5a29b75902d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_eq__0ffcd36dceb3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (Q : M.Par) (v : ℕ → ℝ)
    (hv : ∀ j : Fin (Q.k - 1), Q.lo (j.1 + 1) ≤ v (j.1 + 1) ∧ v (j.1 + 1) ≤ Q.hi (j.1 + 1) ∧
      ∃ n : ℤ, v (j.1 + 1) - Q.lo (j.1 + 1) = n) :
    ∃ τ : M.Ty Q, ∀ j : Fin (Q.k - 1), M.rho Q τ (j.1 + 1) = v (j.1 + 1) := by
  refine ⟨fun j => ⟨⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊, ?_⟩, ?_⟩
  · obtain ⟨h1, h2, -⟩ := hv j
    have : ⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊ ≤ Q.wid (j.1 + 1) := by
      unfold M.Par.wid
      exact Nat.floor_le_floor (by linarith)
    omega
  · intro j
    rw [cb_rho_eq' Q _ j]
    obtain ⟨h1, -, n, hn⟩ := hv j
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := hn ▸ sub_nonneg.mpr h1
    have hn0' : (0 : ℤ) ≤ n := by exact_mod_cast hn0
    lift n to ℕ using hn0'
    rw [Int.cast_natCast] at hn
    show Q.lo (j.1 + 1) + ((⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊ : ℕ) : ℝ) = v (j.1 + 1)
    rw [hn, Nat.floor_natCast]
    linarith
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
