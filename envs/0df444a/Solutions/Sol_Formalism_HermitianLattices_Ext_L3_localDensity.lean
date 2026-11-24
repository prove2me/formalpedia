-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localDensity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:33.517343+00:00
-- url     : https://prove2.me/submissions/e9346e6d-dbe8-4c8e-b66d-3daee8007f40

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_C2_cast_geom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_C2_inert_alg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_C2_split_alg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_sq_absNorm_of_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_normRepCount_inert_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_normRepCount_pow_succ_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_normRepCount_pow_succ_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_normRepCount_split_one


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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution : LocalDensity := by
  intro K _ _ _ hK P hP M k hM hk n hn hnP
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hPbot
  constructor
  · intro hc
    obtain ⟨q, hq⟩ := exists_sq_absNorm_of_inert hK hP hc
    have hq0 : (q : ℝ) ≠ 0 := by
      intro h0
      have h1 : q = 0 := by exact_mod_cast h0
      rw [h1] at hq
      exact hN0 (by simpa using hq)
    have hsq : Real.sqrt (Ideal.absNorm P : ℝ) = q := by
      rw [hq]
      push_cast
      exact Real.sqrt_sq (Nat.cast_nonneg q)
    rw [hsq]
    have h1 : ((normRepCount K (P ^ 1) M n : ℕ) : ℝ) =
        (q : ℝ) ^ (2 * M - 1) * (1 - (-1 : ℝ) ^ M * (q : ℝ) ^ (-(M : ℤ))) := by
      rw [pow_one]
      have h3 := normRepCount_inert_one hK hP hc M hM n hn hnP q hq
      have h2 : ((normRepCount K P M n : ℕ) : ℝ) = (q : ℝ) ^ (M - 1) * ((q : ℝ) ^ M - (-1) ^ M) := by
        exact_mod_cast h3
      rw [h2, C2.inert_alg _ hq0 M hM]
    exact C2.cast_geom (fun j => normRepCount K (P ^ j) M n) q (2 * M - 1) _
      (fun j hj => normRepCount_pow_succ_inert hK hP hc M j hM hj n hn hnP q hq) h1 k hk
  · intro hc
    have hN : ((Ideal.absNorm P : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN0
    have h1 : ((normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ 1) M n : ℕ) : ℝ) =
        (Ideal.absNorm P : ℝ) ^ (2 * M - 1) * (1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))) := by
      rw [pow_one]
      have h3 := normRepCount_split_one hK hP hc M hM n hn hnP
      have h2 : ((normRepCount K (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) M n : ℕ) : ℝ) =
          (Ideal.absNorm P : ℝ) ^ (2 * M - 1) - (Ideal.absNorm P : ℝ) ^ (M - 1) := by
        exact_mod_cast h3
      rw [h2, C2.split_alg _ hN M hM]
    exact C2.cast_geom (fun j => normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ j) M n)
      (Ideal.absNorm P) (2 * M - 1) _
      (fun j hj => normRepCount_pow_succ_split hK hP hc M j hM hj n hn hnP) h1 k hk
end Formalism.HermitianLattices.Ext.L3
