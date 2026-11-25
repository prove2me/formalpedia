-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.comap_eq_comap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:17:42.325699+00:00
-- url     : https://prove2.me/submissions/7a6a5cba-2804-48c4-a697-b0be718bf4d4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_comap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap_eq_comap_iff


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P Q : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) ↔ Q = P ∨ Q = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  rw [conjIdeal_eq_comap]
  exact SplitPrimeIdeals.comap_eq_comap_iff conjO_conjO (conjO_eq_iff_mem_range hF) hP hQ
end Formalism.HermitianLattices.Ext.L3
