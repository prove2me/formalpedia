-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.absNorm_comap_inert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:05.2165+00:00
-- url     : https://prove2.me/submissions/62ec0859-5a31-4c0f-aecd-e84c24c24718

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_comap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_sub_conjO_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_eq_card
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_card_quot_inert


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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 = Ideal.absNorm P := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card, absNorm_eq_card]
  exact SplitPrimeIdeals.card_quot_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ
end Formalism.HermitianLattices.Ext.L3
