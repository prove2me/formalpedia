-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IsotropicCounts.isoCount_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:17:40.276118+00:00
-- url     : https://prove2.me/submissions/0af2b33e-c09e-44f9-9668-c1f17f0444b4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MapMkConjTranspose
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsoCountOneInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IsotropicCounts_isoCount_one_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IsotropicCounts_isoCount_one_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_etaF_comap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IsotropicCounts
open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) :
    (isoCount 𝔭 1 (diagonal u) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2) * alphaStd K 𝔭 m := by
  have hF := hFF.out
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  unfold alphaStd
  rw [etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [isoCount_one_inert hK hP hc u hu hunit, if_pos hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, ← mul_pow, inv_neg]
    congr 2
    ring
  · rw [isoCount_one_split hK hP hc u hu hunit, if_neg hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, one_pow, one_mul]
end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
