-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:38.50463+00:00
-- url     : https://prove2.me/submissions/2ff7daa7-d7fd-4210-bb8e-1b61c9c2c59b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_isUnitIn_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_isUnitIn_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type*} [Field K] {S : Subring K}
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, IsUnitIn S (f i)) :
    IsUnitIn S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IsUnitIn S) (fun _ _ => isUnitIn_mul) isUnitIn_one hf
end Formalism.HermitianLattices.Ext.L3.LocF
