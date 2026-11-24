-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrA.finrank_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:52.812994+00:00
-- url     : https://prove2.me/submissions/c7142556-9af9-4955-a341-26d05f0c95d3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_finrank_eq_two


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    finrank (𝓞 F) (𝓞 K) = 2 := by
  rw [← MeanB.finrank_eq_two hK hF]
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K).symm
end Formalism.HermitianLattices.Ext.L3.BrA
