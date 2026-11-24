-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.mem_SP_iff_locF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:30.943909+00:00
-- url     : https://prove2.me/submissions/e23a503a-6147-4cb8-8cf8-bd2c10fd7289

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_one


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K} :
    a ∈ SP K 𝔭 ↔ a ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have hp : 𝔭.IsPrime := inferInstance
  have key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s},
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, (Ideal.ne_top_iff_one _).mp hp.ne_top, map_one _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨t₁, ht₁, rfl⟩ := hx
      obtain ⟨t₂, ht₂, rfl⟩ := hy
      exact ⟨t₁ * t₂, fun hm => (hp.mem_or_mem hm).elim ht₁ ht₂, map_mul _ _ _⟩
  change a ∈ SP K 𝔭 ↔ ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s},
    s • a ∈ (1 : Submodule (𝓞 K) K)
  rw [mem_SP]
  constructor
  · rintro ⟨t, ht, z, e⟩
    refine ⟨ι t, Submonoid.subset_closure ⟨t, ht, rfl⟩, ?_⟩
    rw [Submodule.mem_one]
    exact ⟨z, by rw [e, Algebra.smul_def]⟩
  · rintro ⟨s, hs, hsa⟩
    obtain ⟨t, ht, rfl⟩ := key s hs
    rw [Submodule.mem_one] at hsa
    obtain ⟨z, hz⟩ := hsa
    exact ⟨t, ht, z, by rw [hz, Algebra.smul_def]⟩
end Formalism.HermitianLattices.Ext.L3.HU
