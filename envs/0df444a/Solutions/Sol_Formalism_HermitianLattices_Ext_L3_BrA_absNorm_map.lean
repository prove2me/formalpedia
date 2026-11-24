-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrA.absNorm_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.396922+00:00
-- url     : https://prove2.me/submissions/7751385d-201d-4780-8db4-f855ce925504

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_finrank_ringOfIntegers

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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 F) (𝓞 K))) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, finrank_ringOfIntegers hK hF]
end Formalism.HermitianLattices.Ext.L3.BrA
