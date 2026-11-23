-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mem_of_unit_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:21.252397+00:00
-- url     : https://prove2.me/submissions/a02542cd-de22-4c98-9d32-4409fd6676a3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_inv_theta

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) {N : ℕ}
    {z : 𝓞 K} (hz : δ * z ∈ extP K 𝔭 ^ N) : z ∈ extP K 𝔭 ^ N := by
  obtain ⟨e, he⟩ := exists_inv_theta hδ N
  have e2 : z = e * (δ * z) - (δ * e - 1) * z := by ring
  rw [e2]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ e hz) (Ideal.mul_mem_right z _ he)
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
