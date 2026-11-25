-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot.normRepCount_extP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:40.018947+00:00
-- url     : https://prove2.me/submissions/54e6289d-1904-4b52-bc13-8a0646119da4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ThirdPropositionSlot_map_comap_eq_of_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ThirdPropositionSlot_extP_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ThirdPropositionSlot_alphaStd_one
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_comap_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_comap_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_etaF_comap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {j : ℕ} (hj : 1 ≤ j) :
    (normRepCount K (extP K 𝔭 ^ j) 1 1 : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ j * alphaStd K 𝔭 1 := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have h1 : (1 : 𝓞 K) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hd := localDensity K hK P hP 1 j le_rfl hj 1 (map_one _) h1
  rw [alphaStd_one, etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [map_comap_eq_of_inert hK hF hP hc, hd.1 hc, if_pos hc, ← absNorm_comap_inert hK hF hP hc]
    push_cast
    rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    simp
  · rw [extP_split hK hF hP hc, hd.2 hc, if_neg hc, absNorm_comap_split hK hF hP hc]
    simp
end Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
