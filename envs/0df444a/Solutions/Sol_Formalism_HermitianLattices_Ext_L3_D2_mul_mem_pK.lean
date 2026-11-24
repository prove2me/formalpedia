-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mul_mem_pK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:31:37.762659+00:00
-- url     : https://prove2.me/submissions/f3e73d2b-178b-4e51-9166-d7eec73e40a8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {i j : ℕ} {a b : K} (ha : a ∈ pK K 𝔭 i)
    (hb : b ∈ pK K 𝔭 j) : a * b ∈ pK K 𝔭 (i + j) := by
  obtain ⟨t, ht, z, hz, e⟩ := (mem_pK h𝔭).1 ha
  obtain ⟨t', ht', z', hz', e'⟩ := (mem_pK h𝔭).1 hb
  refine (mem_pK h𝔭).2 ⟨t * t', fun h => (h𝔭.isPrime.mem_or_mem h).elim ht ht', z * z', ?_, ?_⟩
  · rw [pow_add]; exact Ideal.mul_mem_mul hz hz'
  · rw [map_mul, e, e', show ((t * t' : 𝓞 F) : F) = (t : F) * (t' : F) from rfl, map_mul]; ring
end Formalism.HermitianLattices.Ext.L3.D2
