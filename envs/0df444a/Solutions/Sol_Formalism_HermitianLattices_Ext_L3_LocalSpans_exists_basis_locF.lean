-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:19.438881+00:00
-- url     : https://prove2.me/submissions/1638aa0e-ba8a-479a-8257-2ffcb2d9a87b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_span_RP
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
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalSpans
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LocalSpans
theorem _root_.solution {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ b : Basis (Fin (finrank K V)) K V, (∀ i, b i ∈ L) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L := by
  have : 𝔭.IsPrime := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := fun h => RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h ▸ h𝔭))
  have : IsDedekindDomain (RP K 𝔭) := IsLocalization.isDedekindDomain (𝓞 K) (sF_le 𝔭) _
  have : IsPrincipalIdealRing (RP K 𝔭) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) 𝔭 hp0
  let M : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (L : Set V)
  have : Submodule.IsLattice K M :=
    { fg := by
        obtain ⟨s, hs⟩ := hL.fg
        refine ⟨s, ?_⟩
        show _ = Submodule.span (RP K 𝔭) (L : Set V)
        rw [← hs, Submodule.span_span_of_tower]
      span_eq_top := by
        rw [eq_top_iff, ← hL.span_eq_top]
        exact Submodule.span_mono Submodule.subset_span }
  let b0 := Module.Free.chooseBasis (RP K 𝔭) M
  let b1 := b0.extendOfIsLattice K
  have hb1 : ∀ i, b1 i = (b0 i : V) := fun i => Basis.extendOfIsLattice_apply K b0 i
  have hmem : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b1 i ∈ L := fun i => by
    rw [← mem_locF, ← mem_span_RP, hb1]
    exact (b0 i).2
  choose t ht htL using hmem
  have ht0 : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) ≠ 0 := by
    intro i h0
    have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
    have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
    exact ht i (h2 ▸ 𝔭.zero_mem)
  let b2 := b1.unitsSMul fun i => Units.mk0 _ (ht0 i)
  have hb2 : ∀ i, b2 i = algebraMap (𝓞 F) (𝓞 K) (t i) • b1 i := fun i => by
    rw [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, algebraMap_smul]
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b2).symm
  refine ⟨b2.reindex e, fun i => ?_, ?_⟩
  · rw [Basis.reindex_apply, hb2]
    exact htL _
  · ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Basis.range_reindex]
    have : Submodule.span (RP K 𝔭) (Set.range b2) = M := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [hb2]
        exact Submodule.subset_span (htL i)
      · have h1 : M = Submodule.map M.subtype (Submodule.span (RP K 𝔭) (Set.range b0)) := by
          rw [b0.span_eq, Submodule.map_top, Submodule.range_subtype]
        refine h1.le.trans ?_
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)))⁻¹,
          ⟨1, _, ⟨t i, ht i, rfl⟩, by simp⟩⟩
        have : M.subtype (b0 i) = c • b2 i := by
          rw [hb2, Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t i)), smul_smul,
            inv_mul_cancel₀ (ht0 i), one_smul, hb1]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [this]
end Formalism.HermitianLattices.Ext.L3.LocalSpans
