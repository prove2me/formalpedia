-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.algebraMap_ne_zero_of_mem_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:42.0808+00:00
-- url     : https://prove2.me/submissions/3d94733e-f068-4db2-a5d2-3915346139ee

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_hcompl_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) : algebraMap (𝓞 K) K s ≠ 0 := by
  intro h0
  have hs0 : s = 0 := RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm)
  exact ((mem_hcompl_iff hp s).mp hs).1 (hs0 ▸ p.zero_mem)
end Formalism.HermitianLattices.Ext.L3.WA
