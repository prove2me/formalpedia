-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.div_mem_locRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:20.64788+00:00
-- url     : https://prove2.me/submissions/abd05d4d-a522-4cee-abbb-7c3fb01c5237

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locR_iff


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsPrime) (r : 𝓞 K) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P) :
    algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s ∈ locRing P :=
  show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P from (WA.mem_locR_iff hP _).2 ⟨r, s, hs, rfl⟩
end Formalism.HermitianLattices.Ext.L3.U0
