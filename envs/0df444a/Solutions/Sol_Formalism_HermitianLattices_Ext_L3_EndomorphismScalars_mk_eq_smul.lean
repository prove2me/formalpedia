-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.EndomorphismScalars.mk_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:03.702881+00:00
-- url     : https://prove2.me/submissions/aae3f22a-4d4a-46eb-aac1-4229747a4a25

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V}
namespace Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (x : ↥L) :
    ∃ a : 𝓞 K, (Submodule.Quotient.mk x : Qk L 𝔭 k) = a • Submodule.Quotient.mk ⟨e, he.1⟩ := by
  obtain ⟨t, ht, a, hta⟩ := he.2.2 x x.2
  obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
  refine ⟨algebraMap (𝓞 F) (𝓞 K) s * a, ?_⟩
  have hmem : (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x ∈
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
    Submodule.smul_mem_smul (algebraMap_mem_extP_pow_of_mem_pow hs) Submodule.mem_top
  have hL : (algebraMap (𝓞 F) (𝓞 K) t) • x = a • (⟨e, he.1⟩ : ↥L) :=
    Subtype.ext (by rw [Submodule.coe_smul, Submodule.coe_smul]; exact hta)
  have hx : x = (algebraMap (𝓞 F) (𝓞 K) s * a) • (⟨e, he.1⟩ : ↥L) -
      (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x := by
    rw [map_sub, map_mul, map_one, sub_smul, one_smul, mul_smul, mul_smul, hL]
    abel
  conv_lhs => rw [hx]
  rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).mpr hmem, sub_zero,
    Submodule.Quotient.mk_smul]
end Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
