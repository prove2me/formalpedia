-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_fixF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:58.360422+00:00
-- url     : https://prove2.me/submissions/1b51dc6d-2ef1-4854-901a-0ccfe2f9a1ee

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFixF

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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra F K), IsFixF K F := by
  haveI : FiniteDimensional ℚ (starFixed K) := IntermediateField.finiteDimensional_left (starFixed K)
  haveI : NumberField (starFixed K) := ⟨⟩
  refine ⟨starFixed K, inferInstance, inferInstance, inferInstance, fun a => ?_⟩
  constructor
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact b.2
end Formalism.HermitianLattices.Ext.L3
