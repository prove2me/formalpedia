-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalFactorEquality.finite_vF_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:28:00.532861+00:00
-- url     : https://prove2.me/submissions/77f3b7a6-7b47-47d9-92c8-2b93e189142c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLatticeOfFibReps
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalFactorEquality
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits
namespace Formalism.HermitianLattices.Ext.L3.LocalFactorEquality
theorem _root_.solution {n : 𝓞 F} (hn : n ≠ 0) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | vF 𝔭.1 n ≠ 0}.Finite := by
  have hnF : ¬ IsField (𝓞 F) := NumberField.RingOfIntegers.not_isField F
  have hI : Ideal.span {n} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  let f : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    fun 𝔭 => ⟨𝔭.1, 𝔭.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 hnF⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h)
  refine ((Ideal.finite_factors hI).preimage hf.injOn).subset ?_
  intro 𝔭 h𝔭
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at h𝔭 ⊢
  show 𝔭.1 ∣ Ideal.span {n}
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply h𝔭
  unfold vF

  have hset : {e : ℕ | n ∈ 𝔭.1 ^ e} = {0} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro he
      by_contra h0
      exact hmem (Ideal.pow_le_self h0 he)
    · rintro rfl
      simp
  rw [hset, csSup_singleton]
end Formalism.HermitianLattices.Ext.L3.LocalFactorEquality
