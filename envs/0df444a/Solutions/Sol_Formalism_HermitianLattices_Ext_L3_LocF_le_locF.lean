-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.le_locF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:12.821148+00:00
-- url     : https://prove2.me/submissions/8932c0ec-6931-49b2-af1e-c7c69fdf349d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


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
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) : L ≤ locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_le_locS _ L
end Formalism.HermitianLattices.Ext.L3.LocF
