-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.exists_div_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:49:51.194257+00:00
-- url     : https://prove2.me/submissions/af81534e-de97-40af-a3a2-514527e58eb6

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
theorem _root_.solution {s n : 𝓞 F} {v k : ℕ}
    (H : ∀ z ∈ extP K 𝔭 ^ (v + k), ∃ z' ∈ extP K 𝔭 ^ k, ι s * z = ι n * z') {p : V}
    (hp : p ∈ extP K 𝔭 ^ (v + k) • A) : ∃ p' ∈ extP K 𝔭 ^ k • A, ι s • p = ι n • p' := by
  induction hp using Submodule.smul_induction_on' with
  | smul a ha m hm =>
    obtain ⟨a', ha', e⟩ := H a ha
    exact ⟨a' • m, Submodule.smul_mem_smul ha' hm, by rw [smul_smul, smul_smul, e]⟩
  | add x _ y _ hx hy =>
    obtain ⟨z, hz, e⟩ := hx
    obtain ⟨w, hw, f⟩ := hy
    exact ⟨z + w, add_mem hz hw, by rw [smul_add, smul_add, e, f]⟩
end Formalism.HermitianLattices.Ext.L3.WCA
