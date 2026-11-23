-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallC.psi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:45.894296+00:00
-- url     : https://prove2.me/submissions/7fe551b2-4ad8-4d31-b18a-bcb596198bdb

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FundamentalDomainPiBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory Module
open scoped Classical
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallC
variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι]
namespace Formalism.HermitianLattices.Ext.L3.BallC
theorem _root_.solution [IsEmpty {w : InfinitePlace K // w.IsReal}] (y : ι → mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) : psi K ι y w i = (y i).2 w := rfl
end Formalism.HermitianLattices.Ext.L3.BallC
