-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrA.map_le_extP_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:53.245896+00:00
-- url     : https://prove2.me/submissions/381e3318-4320-4128-b1d1-4dea5432a943

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_comap_extP_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module IsDedekindDomain Function
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BrA
theorem _root_.solution (I 𝔭 : Ideal (𝓞 F)) (e : ℕ) :
    I.map (algebraMap (𝓞 F) (𝓞 K)) ≤ extP K 𝔭 ^ e ↔ I ≤ 𝔭 ^ e := by
  rw [Ideal.map_le_iff_le_comap, MeanB.comap_extP_pow]
end Formalism.HermitianLattices.Ext.L3.BrA
