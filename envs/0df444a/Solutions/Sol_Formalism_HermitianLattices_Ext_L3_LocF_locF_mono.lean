-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.locF_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:36:34.838952+00:00
-- url     : https://prove2.me/submissions/ef431afc-5e63-4e29-bedd-8157e164225b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {W : Type} [AddCommGroup W] [Module (𝓞 K) W]
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) {L M : Submodule (𝓞 K) W} (h : L ≤ M) :
    locF 𝔭 L ≤ locF 𝔭 M :=
  Formalism.HermitianLatticesTheory.locBasic_locS_mono _ h
end Formalism.HermitianLattices.Ext.L3.LocF
