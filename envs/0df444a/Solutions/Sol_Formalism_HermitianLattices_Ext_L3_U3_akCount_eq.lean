-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U3.akCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:00:52.860581+00:00
-- url     : https://prove2.me/submissions/b4750bf8-20ca-40e8-9f6c-45749e494763

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormOneMkIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaStdOneNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U3_absNorm_extP_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U3_absNorm_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_EndomorphismScalars_endHom_bijective
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_EndomorphismScalars_endHom_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ExtendedPrimeIdeals_exists_isGen
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ExtendedPrimeIdeals_vd_spec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_preimage
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_exists_val
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormOneGroup_card_normOne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormOneGroup_cond_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormOneGroup_normOne_mk_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_absNorm_extP_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_absNorm_pos


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.U3
open ExtendedPrimeIdeals EndomorphismScalars NormOneGroup
namespace Formalism.HermitianLattices.Ext.L3.U3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hvk : vd h L 𝔭 ≤ k) :
    akCount h L 𝔭 k = Ideal.absNorm 𝔭 ^ (2 * vd h L 𝔭) *
      normRepCount K (extP K 𝔭 ^ (k - vd h L 𝔭)) 1 1 := by
  obtain ⟨e, he⟩ := exists_isGen hL h1 h𝔭
  obtain ⟨n, hn⟩ := MeanB.exists_val hF hs hLi ⟨e, he.1⟩
  obtain ⟨hv, hv'⟩ := vd_spec hF hd h1 h𝔭 he hn
  generalize vd h L 𝔭 = v at hv hv' hvk ⊢
  have hq := absNorm_pos h𝔭
  have hfin : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := Nat.finite_of_card_ne_zero (by
    rw [absNorm_extP_pow hK hF]
    positivity)
  let π : (𝓞 K ⧸ extP K 𝔭 ^ k) →+* (𝓞 K ⧸ extP K 𝔭 ^ (k - v)) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.sub_le k v))
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have s1 : akCount h L 𝔭 k =
      Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} := by
    unfold akCount
    refine (Nat.card_congr (Equiv.subtypeEquiv
      (Equiv.ofBijective _ (endHom_bijective h𝔭 he k)) fun a => ?_)).symm
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Equiv.ofBijective_apply, endHom_mk, cond_iff hF hs hLi h𝔭 he hn hv hv' hvk b]
    exact normOne_mk_iff hF 𝔭 (k - v) b
  have s2 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (NormOne (extP K 𝔭 ^ (k - v)))
  have s3 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // True} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (fun _ => True)
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial),
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), absNorm_extP_pow hK hF,
    absNorm_extP_pow hK hF] at s3
  have s4 : Nat.card π.toAddMonoidHom.ker = Ideal.absNorm 𝔭 ^ (2 * v) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq (2 * (k - v)))
    rw [← s3, ← pow_add]
    congr 1
    omega
  rw [s1, s2, s4, card_normOne]
end Formalism.HermitianLattices.Ext.L3.U3
