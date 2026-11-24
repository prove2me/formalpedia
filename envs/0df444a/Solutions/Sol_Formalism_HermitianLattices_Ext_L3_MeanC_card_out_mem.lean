-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanC.card_out_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:57.849417+00:00
-- url     : https://prove2.me/submissions/2bc8e4ef-932a-4a4c-bd0d-6b39484ac3fb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_card_quot_pow
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
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.MeanC
namespace Formalism.HermitianLattices.Ext.L3.MeanC
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) {j k : ℕ} (hjk : j ≤ k) :
    Nat.card {n' : 𝓞 F ⧸ 𝔭 ^ k // Quotient.out n' ∈ 𝔭 ^ j} * Ideal.absNorm 𝔭 ^ j =
      Ideal.absNorm 𝔭 ^ k := by
  have hle : 𝔭 ^ k ≤ 𝔭 ^ j := Ideal.pow_le_pow_right hjk
  let f : (𝓞 F ⧸ 𝔭 ^ k) →+* (𝓞 F ⧸ 𝔭 ^ j) := Ideal.Quotient.factor hle
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  have hset : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k,
      Quotient.out n' ∈ 𝔭 ^ j ↔ n' ∈ f.toAddMonoidHom.ker := by
    intro n'
    rw [AddMonoidHom.mem_ker]
    conv_rhs => rw [← Ideal.Quotient.mk_out n']
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, f,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  have e1 : Nat.card {n' : 𝓞 F ⧸ 𝔭 ^ k // Quotient.out n' ∈ 𝔭 ^ j} =
      Nat.card f.toAddMonoidHom.ker := Nat.card_congr (Equiv.subtypeEquivRight hset)
  have h2 : (f.toAddMonoidHom.ker).index = Nat.card (𝓞 F ⧸ 𝔭 ^ j) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hf).toEquiv
  have h1 := AddSubgroup.card_mul_index (f.toAddMonoidHom.ker)
  rw [h2, card_quot_pow, card_quot_pow] at h1
  rw [e1, h1]
end Formalism.HermitianLattices.Ext.L3.MeanC
