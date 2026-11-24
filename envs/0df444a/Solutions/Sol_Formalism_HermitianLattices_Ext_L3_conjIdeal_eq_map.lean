-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.conjIdeal_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:20.032321+00:00
-- url     : https://prove2.me/submissions/014f75ee-fab5-46b0-9c3d-d371d796fa90

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_comap

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
theorem _root_.solution (P : Ideal (𝓞 K)) : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (conjO K) := by
  rw [conjIdeal_eq_comap]
  apply le_antisymm
  · intro x hx
    have h := Ideal.mem_map_of_mem (conjO K) (show conjO K x ∈ P from hx)
    rwa [conjO_conjO] at h
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simpa only [Ideal.mem_comap, conjO_conjO] using hx
end Formalism.HermitianLattices.Ext.L3
