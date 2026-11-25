-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.split_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:48:07.337119+00:00
-- url     : https://prove2.me/submissions/4a21047e-0c6e-44e3-b491-0aca0e0e50c2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLevelMinors
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
theorem _root_.solution {x a a' C β : ℝ} (e : ℕ) (hx : 1 ≤ x) (ha : 0 < a) (ha' : 0 < a') (hC : 0 < C)
    (hβ : 0 ≤ β) (h1 : a ≤ C * x ^ e) (h2 : a' ≤ C * x ^ e) :
    x ^ (-(2 * (e : ℝ) * β)) ≤ C ^ β * C ^ β * (a ^ (-β) * a' ^ (-β)) := by
  have hx0 : 0 < x := by linarith
  have hxe : 0 < x ^ e := pow_pos hx0 e
  have hCb : 0 < C ^ β := Real.rpow_pos_of_pos hC β
  have hxb : 0 < x ^ ((e : ℝ) * β) := Real.rpow_pos_of_pos hx0 _
  have one : ∀ b : ℝ, 0 < b → b ≤ C * x ^ e → x ^ (-((e : ℝ) * β)) ≤ C ^ β * b ^ (-β) := by
    intro b hb hbC
    have h := Real.rpow_le_rpow hb.le hbC hβ
    rw [Real.mul_rpow hC.le hxe.le, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le] at h
    have hbb : 0 < b ^ β := Real.rpow_pos_of_pos hb β
    have key : 1 / (C ^ β * x ^ ((e : ℝ) * β)) ≤ 1 / b ^ β := one_div_le_one_div_of_le hbb h
    rw [Real.rpow_neg hx0.le, Real.rpow_neg hb.le]
    have e1 : (x ^ ((e : ℝ) * β))⁻¹ = C ^ β * (1 / (C ^ β * x ^ ((e : ℝ) * β))) := by
      field_simp
    rw [e1, ← one_div]
    exact mul_le_mul_of_nonneg_left key hCb.le
  have k1 := one a ha h1
  have k2 := one a' ha' h2
  have hsplit : x ^ (-(2 * (e : ℝ) * β)) = x ^ (-((e : ℝ) * β)) * x ^ (-((e : ℝ) * β)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [hsplit]
  calc x ^ (-((e : ℝ) * β)) * x ^ (-((e : ℝ) * β))
      ≤ (C ^ β * a ^ (-β)) * (C ^ β * a' ^ (-β)) :=
        mul_le_mul k1 k2 (Real.rpow_nonneg hx0.le _)
          (mul_nonneg hCb.le (Real.rpow_nonneg ha.le _))
    _ = C ^ β * C ^ β * (a ^ (-β) * a' ^ (-β)) := by ring
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
