-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.form_mem_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:49:48.345846+00:00
-- url     : https://prove2.me/submissions/f5b380d6-64ae-410c-8943-a6ba503d85d2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul


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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {J : Ideal (𝓞 K)}
    {l q : V} (hl : l ∈ A) (hq : q ∈ J • A) : ∃ z ∈ J, κ z = h l q := by
  induction hq using Submodule.smul_induction_on' with
  | smul a ha m hm =>
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hA l hl m hm)
    refine ⟨a * r, Ideal.mul_mem_right _ _ ha, ?_⟩
    rw [← algebraMap_smul K a, map_smul, smul_eq_mul, map_mul, hr]
  | add x _ y _ hx hy =>
    obtain ⟨z, hz, e⟩ := hx
    obtain ⟨w, hw, f⟩ := hy
    exact ⟨z + w, add_mem hz hw, by rw [map_add, map_add, e, f]⟩
end Formalism.HermitianLattices.Ext.L3.WCA
