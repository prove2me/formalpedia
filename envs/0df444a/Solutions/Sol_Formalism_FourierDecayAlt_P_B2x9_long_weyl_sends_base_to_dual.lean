-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.long_weyl_sends_base_to_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:08:42.685799+00:00
-- url     : https://prove2.me/submissions/c8a96bfe-38bd-4767-bf8b-0a5232450460

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_e0_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
private lemma w0_apply_iF_col (c : ℂ) (i : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c i (iF k r') = if i = iL k r' then c else 0 := by
  have h0 : (iF k r').val = 0 := rfl
  show (if i.val = 0 ∧ (iF k r').val = 2 * (1 + r') + k then (star c)⁻¹
    else if i.val = 2 * (1 + r') + k ∧ (iF k r').val = 0 then c
    else if i = iF k r' ∧ 0 < i.val ∧ i.val < 2 * (1 + r') + k then (1 : ℂ) else 0) = _
  have h3 : ¬ (i = iF k r' ∧ 0 < i.val ∧ i.val < 2 * (1 + r') + k) := by
    rintro ⟨h1, h2, -⟩
    rw [h1, h0] at h2
    exact lt_irrefl 0 h2
  by_cases h : i = iL k r'
  · have hi : i.val = 2 * (1 + r') + k := by rw [h]; rfl
    rw [if_neg (by omega), if_pos ⟨hi, h0⟩, if_pos h]
  · have hi : i.val ≠ 2 * (1 + r') + k := fun h' => h (Fin.ext h')
    rw [if_neg (by omega), if_neg (by omega), if_neg h3, if_neg h]
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9.S1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9.S1
namespace Formalism.FourierDecayAlt.P.B2x9.S2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x9.S2
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (c : ℂ) : w0 k r' c *ᵥ e0 k r' = c • es0 k r' := by
  rw [e0_eq, dual_base_vector_eq_single]
  ext i
  have hcol : (w0 k r' c *ᵥ Pi.single (iF k r') 1) i = w0 k r' c i (iF k r') := by
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hcol, w0_apply_iF_col, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.B2x9
