-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxCube.absNorm_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:26:15.69138+00:00
-- url     : https://prove2.me/submissions/e95ce36a-cbcc-4aa7-a676-1556d63b1cda

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemIdeal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxCube_absNorm_le_of_mem_ideal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_absNorm_le_of_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_ne_zero_of_mem_boxSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxCube
open BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxCube
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {T : ℝ}
    {n : 𝓞 F} (hn : n ∈ boxSet K F T) (hb : n ∈ b) :
    (Ideal.absNorm b : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K :=
  (absNorm_le_of_mem_ideal hb (ne_zero_of_mem_boxSet hn)).trans (absNorm_le_of_mem hK hF hn)
end Formalism.HermitianLattices.Ext.L3.BoxCube
