-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.mem_SP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:32:59.774116+00:00
-- url     : https://prove2.me/submissions/260bf131-2b4f-41ab-aec6-e4d9ad9cfdc4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K} :
    a ∈ SP K 𝔭 ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z : 𝓞 K, jK z = jK (ι t) * a := by
  show InP 𝔭 0 a ↔ _
  constructor
  · rintro ⟨t, ht, z, -, e⟩
    exact ⟨t, ht, z, e⟩
  · rintro ⟨t, ht, z, e⟩
    exact ⟨t, ht, z, by simp, e⟩
end Formalism.HermitianLattices.Ext.L3.HU
