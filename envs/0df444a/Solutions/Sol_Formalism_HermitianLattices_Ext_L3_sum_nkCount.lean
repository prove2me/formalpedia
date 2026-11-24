-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.sum_nkCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:41:12.190404+00:00
-- url     : https://prove2.me/submissions/bbfe4227-6c3b-4dcd-be4c-6422966658ca

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_finite_quot_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_one_lt_absNorm
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_card_quot_extP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_congrP_algebraMap_iff_sub_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_exists_val
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_val_congr
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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, nkCount h L 𝔭 k (Quotient.out n') =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V * k) := by
  classical
  haveI := MeanC.finite_quot_pow h𝔭 k
  have hN := MeanC.one_lt_absNorm h𝔭
  haveI : Finite (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :=
    Nat.finite_of_card_ne_zero (by
      rw [MeanB.card_quot_extP hK hF hL h𝔭 k]; exact pow_ne_zero _ (by omega))
  let nv : ↥L → 𝓞 F := fun y => (MeanB.exists_val hF hs hLi y).choose
  have hnv : ∀ y : ↥L, h (y : V) (y : V) = algebraMap F K (nv y : F) :=
    fun y => (MeanB.exists_val hF hs hLi y).choose_spec
  let rep : (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) → ↥L :=
    fun x => (Submodule.Quotient.mk_surjective _ x).choose
  have hrep : ∀ x, Submodule.Quotient.mk (rep x) = x :=
    fun x => (Submodule.Quotient.mk_surjective _ x).choose_spec
  let φ : (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) → 𝓞 F ⧸ 𝔭 ^ k :=
    fun x => Ideal.Quotient.mk _ (nv (rep x))
  have hfib : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k,
      nkCount h L 𝔭 k (Quotient.out n') = Nat.card {x // φ x = n'} := by
    intro n'
    unfold nkCount
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · rintro ⟨y, hy, hc⟩
      rw [hnv y, MeanB.congrP_algebraMap_iff_sub_mem h𝔭] at hc
      have hyx : rep x - y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
        (Submodule.Quotient.eq _).mp ((hrep x).trans hy.symm)
      have h2 := MeanB.val_congr hF hs hLi 𝔭 k hyx (hnv _) (hnv y)
      show Ideal.Quotient.mk _ (nv (rep x)) = n'
      conv_rhs => rw [← Ideal.Quotient.mk_out n']
      rw [Ideal.Quotient.eq]
      have := Ideal.add_mem _ h2 hc
      simpa using this
    · intro hx
      refine ⟨rep x, hrep x, ?_⟩
      rw [hnv, MeanB.congrP_algebraMap_iff_sub_mem h𝔭]
      rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
      exact hx
  letI := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ k)
  rw [finsum_eq_sum_of_fintype]
  simp_rw [hfib]
  rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv φ),
    MeanB.card_quot_extP hK hF hL h𝔭 k]
end Formalism.HermitianLattices.Ext.L3
