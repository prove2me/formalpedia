-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.etaF_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:08:29.313151+00:00
-- url     : https://prove2.me/submissions/049235a9-129f-48b6-8798-45f9dea5f349

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_comap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_sub_conjO_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_map_comap_of_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_not_isPrime_map_of_split


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    etaF K F (P.comap (algebraMap (𝓞 F) (𝓞 K))) = if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then -1 else 1 := by
  rw [conjIdeal_eq_comap]
  unfold etaF
  by_cases hc : P.comap (conjO K) = P
  · obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    rw [SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ, if_pos hP.isPrime,
      if_pos hc]
  · rw [if_neg (SplitPrimeIdeals.not_isPrime_map_of_split conjO_conjO (conjO_eq_iff_mem_range hF) hP hc),
      if_neg hc]
end Formalism.HermitianLattices.Ext.L3
