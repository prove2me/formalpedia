-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.congrP_algebraMap_iff_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:12.976914+00:00
-- url     : https://prove2.me/submissions/6c137200-6a11-4879-800d-de0ba559771d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_comap_extP_pow
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_mem_pow_of_mul_mem
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a b : 𝓞 F) :
    CongrP (K := K) 𝔭 k (algebraMap F K (a : F)) (algebraMap F K (b : F)) ↔ a - b ∈ 𝔭 ^ k := by
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    have : z = algebraMap (𝓞 F) (𝓞 K) (t * (a - b)) := by
      apply RingOfIntegers.coe_injective
      rw [e, algebraMap_comp]
      simp
    rw [this, ← Ideal.mem_comap, comap_extP_pow] at hz
    exact MeanA.mem_pow_of_mul_mem h𝔭 ht hz
  · intro h
    refine ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), algebraMap (𝓞 F) (𝓞 K) (a - b), ?_, ?_⟩
    · rw [← Ideal.mem_comap, comap_extP_pow]; exact h
    · rw [algebraMap_comp]; simp
end Formalism.HermitianLattices.Ext.L3.MeanB
