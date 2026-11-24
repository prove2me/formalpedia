-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.aut_mem_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:29:16.481991+00:00
-- url     : https://prove2.me/submissions/78b8dfda-5937-4ea3-9bf0-859865838f91

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_aut_mem
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
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h A) (J : Ideal (𝓞 K)) {x : V} (hx : x ∈ J • A) : g x ∈ J • A := by
  have hs : ∀ (r : 𝓞 K) (v : V), g (r • v) = r • g v := fun r v => by
    rw [← algebraMap_smul K r v, map_smul, algebraMap_smul]
  refine Submodule.smul_induction_on (p := fun w => g w ∈ J • A) hx (fun r hr a ha => ?_)
    (fun u w hu hw => ?_)
  · simp only [hs]
    exact Submodule.smul_mem_smul hr (aut_mem hg ha)
  · simp only [map_add]
    exact Submodule.add_mem _ hu hw
end Formalism.HermitianLattices.Ext.L3.HU
