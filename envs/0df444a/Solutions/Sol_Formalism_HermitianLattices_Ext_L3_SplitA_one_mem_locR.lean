-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitA.one_mem_locR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:35:49.608335+00:00
-- url     : https://prove2.me/submissions/0ac94a44-bb80-4b51-8fd8-bb9619cf5e2b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.SplitA
theorem _root_.solution (p : Ideal (𝓞 K)) : (1 : K) ∈ Formalism.HermitianLatticesTheory.locR (K := K) p :=
  ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩
end Formalism.HermitianLattices.Ext.L3.SplitA
