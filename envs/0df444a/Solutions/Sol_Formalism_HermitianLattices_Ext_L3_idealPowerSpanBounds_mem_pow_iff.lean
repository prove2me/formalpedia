-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mem_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:43.263072+00:00
-- url     : https://prove2.me/submissions/e5d6587c-9b0e-4440-b3b1-2f66954c9c75

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 F) : ι a ∈ extP K 𝔭 ^ k ↔ a ∈ 𝔭 ^ k := by
  have h : Ideal.comap ι (Ideal.map ι (𝔭 ^ k)) = 𝔭 ^ k :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  change ι a ∈ (Ideal.map ι 𝔭) ^ k ↔ a ∈ 𝔭 ^ k
  rw [← Ideal.map_pow]
  constructor
  · intro ha
    rw [← h]
    exact Ideal.mem_comap.mpr ha
  · intro ha
    exact Ideal.mem_map_of_mem _ ha
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
