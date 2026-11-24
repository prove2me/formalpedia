-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.congrP_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:45.213586+00:00
-- url     : https://prove2.me/submissions/bd81103c-5e4e-4890-8403-5f7c38f4bee0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_mul_mem
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a c : 𝓞 K) :
    CongrP 𝔭 k (algebraMap (𝓞 K) K a) (algebraMap (𝓞 K) K c) ↔
      Ideal.Quotient.mk (extP K 𝔭 ^ k) a = Ideal.Quotient.mk (extP K 𝔭 ^ k) c := by
  rw [Ideal.Quotient.eq]
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    have e' : z = ι t * (a - c) := by
      apply RingOfIntegers.coe_injective
      rw [e, map_mul, map_sub]
      rfl
    have ht' : t ∉ 𝔭 ^ (0 + 1) := by rwa [zero_add, pow_one]
    exact mem_of_mul_mem h𝔭 ht' (by rw [zero_add, ← e']; exact hz)
  · intro hm
    exact ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), a - c, hm, by simp⟩
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
