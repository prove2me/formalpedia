-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.datum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:42.588038+00:00
-- url     : https://prove2.me/submissions/76ec7a7b-abfa-431d-a13e-ac3adb12b46f

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_stdChar_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_stdChar_eq_one_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_mem_subring_iff
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable (p : ℕ) [hp : Fact p.Prime]
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution : LocalDatum ℚ_[p] (PadicInt.subring p) (stdChar p) where
  t2 := inferInstance
  isOpen := by
    have : ((PadicInt.subring p : Subring ℚ_[p]) : Set ℚ_[p]) = Metric.closedBall 0 1 := by
      ext x; simp
    rw [this]
    exact IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
  isCompact := by
    have : ((PadicInt.subring p : Subring ℚ_[p]) : Set ℚ_[p]) = Metric.closedBall 0 1 := by
      ext x; simp
    rw [this]
    exact isCompact_closedBall 0 1
  unif := by
    have hp0' : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    refine ⟨Units.mk0 (p : ℚ_[p]) hp0', ?_, fun x => ?_⟩
    · rw [mem_subring_iff]; simpa using Padic.norm_int_le_one (p := p) (p : ℤ)
    · obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
      refine ⟨k, ?_⟩
      rw [mem_subring_iff, Units.val_mk0, norm_mul, norm_pow, Padic.norm_p, inv_pow,
        inv_mul_le_iff₀ (by positivity)]
      simpa using hk.le
  artin := inferInstance
  red := inferInstance
  unitRep := by
    intro x
    by_cases hx : x = 0
    · exact ⟨1, (PadicInt.subring p).one_mem, by simp [hx]⟩
    · exact ⟨0, (PadicInt.subring p).zero_mem, by simpa using hx⟩
  unitary := by
    intro x
    rw [AddChar.map_neg_eq_inv, stdChar_apply, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [Complex.conj_ofReal, Complex.conj_ofNat]
  selfDual := by
    intro a
    constructor
    · intro h
      have := h 1 (PadicInt.subring p).one_mem
      rw [mul_one, stdChar_eq_one_iff] at this
      exact this
    · intro ha r hr
      rw [stdChar_eq_one_iff]
      exact (PadicInt.subring p).mul_mem ha hr
end Formalism.FourierDecayAlt.P.A5x7
