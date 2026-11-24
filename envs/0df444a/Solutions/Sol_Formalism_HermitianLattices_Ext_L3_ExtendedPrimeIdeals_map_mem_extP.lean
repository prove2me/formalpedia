-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals.map_mem_extP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:19.935438+00:00
-- url     : https://prove2.me/submissions/9cf28c1f-84d4-4364-a5aa-26d335335775

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_comap_extP_pow


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k : ℕ} {s : 𝓞 F} (hs : s ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) s ∈ extP K 𝔭 ^ k := by
  rw [← Ideal.mem_comap, MeanB.comap_extP_pow]
  exact hs
end Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
