-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.InL.form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:10:00.604377+00:00
-- url     : https://prove2.me/submissions/82fe5a3c-5317-481b-b162-a323f92252f4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_form_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_form_smul


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCA
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.WCA
namespace InL
theorem _root_.solution (hp : 𝔭.IsPrime) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {i k : ℕ} {v w : V} (hv : InL 𝔭 A i v) (hw : InL 𝔭 A k w) :
    InI 𝔭 (i + k) (h v w) := by
  obtain ⟨t, ht, e⟩ := hv
  obtain ⟨u, hu, f⟩ := hw
  obtain ⟨z, hz, g⟩ := form_mem hF hA e f
  exact ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, z, hz, by rw [g, form_smul hF]⟩
end InL
end Formalism.HermitianLattices.Ext.L3.WCA
