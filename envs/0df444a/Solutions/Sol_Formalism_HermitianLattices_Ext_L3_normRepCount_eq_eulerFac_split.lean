-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.normRepCount_eq_eulerFac_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:16.10392+00:00
-- url     : https://prove2.me/submissions/4b15d9f4-3bb0-4585-9d52-e459b2146bcf

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localDensity
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_conjIdeal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_conjIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) M n : ℝ) =
      (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) *
        (Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P))⁻¹ := by
  have hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P :=
    fun h => hc ((conjIdeal_conjIdeal hK P).symm.trans h).symm
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hPbot
  have hN1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hP.ne_top
  have hN2 : (1 : ℝ) < (Ideal.absNorm P : ℝ) := by
    have : 2 ≤ Ideal.absNorm P := by omega
    exact_mod_cast (by omega : 1 < Ideal.absNorm P)
  have hx : 0 < 1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by
    rw [zpow_neg, zpow_natCast, sub_pos]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hN2 (by omega))
  rw [(localDensity K hK P hP M k hM hk n hn hnP).2 hc, Formalism.HermitianLatticesTheory.eulerFac, Formalism.HermitianLatticesTheory.eulerFac, if_neg hc,
    if_neg hc', absNorm_conjIdeal hK, ← Real.rpow_add hx,
    show (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one, inv_inv]
end Formalism.HermitianLattices.Ext.L3
