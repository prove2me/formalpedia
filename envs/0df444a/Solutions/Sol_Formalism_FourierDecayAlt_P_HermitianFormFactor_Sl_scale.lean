-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Sl_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:01:37.151914+00:00
-- url     : https://prove2.me/submissions/8b076e6c-0fc0-49c6-b1b5-7f5e50bc5bf3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qf_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qf_definite
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qf_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {T : Q → Q → ℂ} (hT : (Matrix.of T).PosDef) {ρ : ℝ} (hρ : 0 ≤ ρ) : Sl P T ρ = ρ • Sl P T 1 := by
  ext B
  rcases hρ.eq_or_lt with h0 | hpos
  · have hne : (Sl P T 1).Nonempty := ⟨0, by simp only [Sl, Set.mem_setOf_eq, qf_zero]; norm_num⟩
    rw [← h0, Set.zero_smul_set hne, Set.mem_zero]
    simp only [Sl, Set.mem_setOf_eq]
    constructor
    · intro h
      have hc : cm B = 0 := qf_definite hT (cm B) (by simpa using h)
      funext j i
      exact congrFun (congrFun hc i) j
    · rintro rfl
      simp [qf_zero]
  · rw [Set.mem_smul_set_iff_inv_smul_mem₀ hpos.ne']
    simp only [Sl, Set.mem_setOf_eq, qf_smul]
    rw [inv_pow, one_pow, inv_mul_le_iff₀ (by positivity), mul_one]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
