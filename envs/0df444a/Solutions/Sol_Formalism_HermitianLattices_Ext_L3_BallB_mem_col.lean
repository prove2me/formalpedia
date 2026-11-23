-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.mem_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:23.668435+00:00
-- url     : https://prove2.me/submissions/972af6a6-344e-479c-b689-63019c1902fd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution {I : Ideal (𝓞 K)} {z c : 𝓞 K} : c ∈ col I z ↔ c * z ∈ I := Iff.rfl
end Formalism.HermitianLattices.Ext.L3.BallB
