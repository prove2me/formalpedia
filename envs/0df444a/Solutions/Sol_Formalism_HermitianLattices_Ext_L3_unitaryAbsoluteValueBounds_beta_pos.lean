-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.beta_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:12.365802+00:00
-- url     : https://prove2.me/submissions/6a2e670b-99eb-4a8e-b41b-e8323784d104

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_etaF_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_one_lt_q

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    0 < 1 - etaF K F 𝔭 ^ M * (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ)) := by
  have hq := one_lt_q h𝔭
  have hlt : (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ)) < 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have hpos : 0 < (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ)) := zpow_pos (by linarith) _
  rcases etaF_eq (K := K) 𝔭 with h | h <;> rw [h]
  · rw [one_pow, one_mul]; linarith
  · rcases neg_one_pow_eq_or ℝ M with h' | h' <;> rw [h'] <;> linarith
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
