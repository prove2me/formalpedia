-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.nrComplexPlaces_eq_fDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:22.982573+00:00
-- url     : https://prove2.me/submissions/84d9e855-dc39-4bae-b0b7-5df5cb44519f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    InfinitePlace.nrComplexPlaces K = Formalism.HermitianLatticesTheory.fDeg K := by
  have h0 : InfinitePlace.nrRealPlaces K = 0 := by
    classical
    unfold InfinitePlace.nrRealPlaces
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h0, zero_add]
end Formalism.HermitianLattices.Ext.L3
