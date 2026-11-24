-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.coeff_gLog_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:16.147693+00:00
-- url     : https://prove2.me/submissions/45d9d0a9-b51d-4a1e-8a03-111ba105d2aa

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_pow_inj
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_coeff_gLog
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)
open Formalism.L2.Th1.D.KernelCokernelKilling
open MvPowerSeries
variable {K : Type} [Field K] {τ : Type} [DecidableEq τ] {l d : ℕ}
namespace Formalism.L2.Th1.D.KernelCokernelKilling
theorem _root_.solution (hl : 2 ≤ l) (φ : ZMod d → τ) (s : ZMod d) (e : ℕ) :
    coeff (Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)) (gLog K l φ s) =
      ((l : K) ^ e)⁻¹ := by
  have hk : (l ^ 2) ^ e ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by omega))
  rw [coeff_gLog, Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    rw [Finsupp.single_eq_single_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h2, _⟩
    · exact (pow_inj hl h2).symm
    · exact absurd h2 hk
  · intro he
    exfalso
    apply he
    rw [Finset.mem_range]
    have hdeg : (Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)).degree = (l ^ 2) ^ e := by
      first
      | exact Finsupp.degree_single _ _
      | simp [Finsupp.degree, Finsupp.support_single_ne_zero _ hk]
      | simp
    rw [hdeg]
    have : e < (l ^ 2) ^ e := by
      first
      | exact Nat.lt_pow_self (by nlinarith)
      | exact Nat.lt_pow_self (by nlinarith) e
    first
    | exact Nat.lt_succ_of_lt this
    | omega
end Formalism.L2.Th1.D.KernelCokernelKilling
