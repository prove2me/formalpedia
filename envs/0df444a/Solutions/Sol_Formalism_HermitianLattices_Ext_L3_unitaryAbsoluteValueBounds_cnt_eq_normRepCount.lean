-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cnt_eq_normRepCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:09.980375+00:00
-- url     : https://prove2.me/submissions/239f7506-27d5-42d3-9eb8-6fe1ee3553b5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemRangeLinPart
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_normRepCount_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) :
    cnt hF 𝔭 k M n = normRepCount K (extP K 𝔭 ^ k) M n :=
  (normRepCount_eq _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k) M n).symm
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
