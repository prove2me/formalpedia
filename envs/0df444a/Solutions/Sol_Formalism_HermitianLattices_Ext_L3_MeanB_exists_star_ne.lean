-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:41.812707+00:00
-- url     : https://prove2.me/submissions/f777da11-4849-4710-a760-b6f213729b35

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ θ : K, star θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 K)
  obtain ⟨θ, t, e, h⟩ := hK.2.2 P hP
  refine ⟨algebraMap (𝓞 K) K θ, fun h' => h ?_⟩
  rw [h'] at e
  have : t = θ := RingOfIntegers.coe_injective e
  rw [this, sub_self]; exact P.zero_mem
end Formalism.HermitianLattices.Ext.L3.MeanB
