-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U3.alphaStd_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:42:50.243376+00:00
-- url     : https://prove2.me/submissions/43f2263d-6150-4573-9ab3-66abb9c85128

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormOneMkIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaStdOneNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U3_absNorm_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ThirdPropositionSlot_alphaStd_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_absNorm_pos


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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.U3
open ExtendedPrimeIdeals EndomorphismScalars NormOneGroup
namespace Formalism.HermitianLattices.Ext.L3.U3
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : alphaStd K 𝔭 1 ≠ 0 := by
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by
    have h0 := absNorm_pos h𝔭
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := mt Ideal.absNorm_eq_one_iff.1 h𝔭.ne_top
    exact_mod_cast (show 2 ≤ Ideal.absNorm 𝔭 by omega)
  have h3 : (Ideal.absNorm 𝔭 : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
  have h4 : 0 < (Ideal.absNorm 𝔭 : ℝ)⁻¹ := inv_pos.2 (by linarith)
  rw [ThirdPropositionSlot.alphaStd_one]
  unfold etaF
  split_ifs
  · nlinarith
  · nlinarith
end Formalism.HermitianLattices.Ext.L3.U3
