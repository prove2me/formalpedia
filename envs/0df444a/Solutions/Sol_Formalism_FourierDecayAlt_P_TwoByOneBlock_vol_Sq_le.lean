-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.vol_Sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:50.318931+00:00
-- url     : https://prove2.me/submissions/969820ec-a833-4ab5-9d6f-80f8eb1f902a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Sq_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Sq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Set
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (n : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    volume {x : Fin (n + 1) → ℂ | Sq (n + 1) x ≤ b} = ENNReal.ofReal (b ^ (n + 1)) * Vb (n + 1) := by
  have hset : {x : Fin (n + 1) → ℂ | Sq (n + 1) x ≤ b} = √b • {x : Fin (n + 1) → ℂ | Sq (n + 1) x ≤ 1} := by
    rcases hb.eq_or_lt with rfl | hb'
    · rw [Real.sqrt_zero, zero_smul_set ⟨0, by simp [Sq]⟩]
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_zero]
      constructor
      · intro hx
        have h0 : Sq (n + 1) x = 0 := le_antisymm hx (Sq_nonneg x)
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).1 h0 i (Finset.mem_univ i)
        simpa using this
      · rintro rfl; simp [Sq]
    · have hs : √b ≠ 0 := (Real.sqrt_pos.2 hb').ne'
      ext x
      rw [mem_smul_set_iff_inv_smul_mem₀ hs]
      simp only [Set.mem_ofPred_eq, Sq_smul, inv_pow, Real.sq_sqrt hb]
      rw [inv_mul_le_iff₀ hb', mul_one]
  have hfr : Module.finrank ℝ (Fin (n + 1) → ℂ) = 2 * (n + 1) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [hset, Measure.addHaar_smul, hfr, pow_mul, Real.sq_sqrt hb, abs_of_nonneg (pow_nonneg hb _)]
  rfl
end Formalism.FourierDecayAlt.P.TwoByOneBlock
