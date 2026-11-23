-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.conjO_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:22.232022+00:00
-- url     : https://prove2.me/submissions/a3afd6dd-81fd-42f6-80d5-419e96484b5a

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
theorem _root_.solution (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    ∀ z ∈ extP K 𝔭 ^ k, conjO K z ∈ extP K 𝔭 ^ k := by
  intro z hz
  have hcomp : (conjO K).comp ι = ι := RingHom.ext (fun a => conjO_map hF a)
  have hJ : extP K 𝔭 ^ k = Ideal.map ι (𝔭 ^ k) := by
    rw [Ideal.map_pow]
    rfl
  rw [hJ] at hz ⊢
  have h1 := Ideal.mem_map_of_mem (conjO K) hz
  rwa [Ideal.map_map, hcomp] at h1
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
