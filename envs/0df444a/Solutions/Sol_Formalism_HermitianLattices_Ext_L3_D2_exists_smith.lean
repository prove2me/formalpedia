-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_smith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:44:42.343593+00:00
-- url     : https://prove2.me/submissions/f61de6a3-ea0a-43ee-87dc-357374dd03b7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsUnif0_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_exists_basis_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_span_RP
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open LocalSpans
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (a b : Basis (Fin (finrank K V)) K V) (e : Fin (finrank K V) → 𝓞 K) (c : 𝓞 K),
      c ≠ 0 ∧ (∀ i, e i ≠ 0) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) = locF 𝔭 A₀ ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 B₀ ∧ ∀ i, c • b i = e i • a i := by
  have : 𝔭.IsPrime := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := fun h => RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h ▸ h𝔭))
  have : IsDedekindDomain (RP K 𝔭) := IsLocalization.isDedekindDomain (𝓞 K) (sF_le 𝔭) _
  have : IsPrincipalIdealRing (RP K 𝔭) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) 𝔭 hp0
  obtain ⟨a0, -, ha0⟩ := exists_basis_locF hA₀ h𝔭
  obtain ⟨b0, -, hb0⟩ := exists_basis_locF hB₀ h𝔭

  obtain ⟨⟨c, hc⟩, hcint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun p : Fin (finrank K V) × Fin (finrank K V) => a0.repr (b0 p.1) p.2)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by
    simpa using hc0
  let MA : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (Set.range a0)
  let MB : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (Set.range b0)
  let μ : V →ₗ[RP K 𝔭] V := ((algebraMap (𝓞 K) K c) • (LinearMap.id : V →ₗ[K] V)).restrictScalars (RP K 𝔭)
  have hμ : ∀ x, μ x = algebraMap (𝓞 K) K c • x := fun x => rfl
  have hμi : Function.Injective μ := fun x y hxy => by
    rw [hμ, hμ] at hxy
    exact smul_right_injective V hcK hxy
  let N' : Submodule (RP K 𝔭) V := MB.map μ
  have hN' : N' ≤ MA := by
    show Submodule.map μ (Submodule.span _ _) ≤ MA
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hμ, ← a0.sum_repr (b0 i), Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨z, hz⟩ := hcint (i, j)
    rw [smul_smul]
    have : algebraMap (𝓞 K) K c * a0.repr (b0 i) j = algebraMap (𝓞 K) K z := by
      rw [hz, Algebra.smul_def]
    rw [this, algebraMap_smul, ← algebraMap_smul (RP K 𝔭)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hliA : LinearIndependent (RP K 𝔭) a0 := a0.linearIndependent.restrict_scalars' (RP K 𝔭)
  have hliB : LinearIndependent (RP K 𝔭) b0 := b0.linearIndependent.restrict_scalars' (RP K 𝔭)
  have hfA : finrank (RP K 𝔭) MA = finrank K V := by
    rw [finrank_span_eq_card hliA, Fintype.card_fin]
  have hfB : finrank (RP K 𝔭) MB = finrank K V := by
    rw [finrank_span_eq_card hliB, Fintype.card_fin]
  let N : Submodule (RP K 𝔭) MA := N'.comap MA.subtype
  have hfN : finrank (RP K 𝔭) N = finrank (RP K 𝔭) MA := by
    rw [hfA, ← hfB, (Submodule.comapSubtypeEquivOfLe hN').finrank_eq,
      (Submodule.equivMapOfInjective μ hμi MB).finrank_eq]
  obtain ⟨b', α, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq (Basis.span hliA) hfN
  have hlatA : Submodule.IsLattice K MA :=
    { fg := Submodule.fg_span (Set.finite_range _)
      span_eq_top := by
        rw [eq_top_iff, ← a0.span_eq]
        exact Submodule.span_mono Submodule.subset_span }
  let a := b'.extendOfIsLattice K
  have ha : ∀ i, a i = (b' i : V) := fun i => Basis.extendOfIsLattice_apply K b' i
  have hα0 : ∀ i, α i ≠ 0 := fun i h0 => by
    have h1 := hab i
    rw [h0, zero_smul] at h1
    exact ab'.ne_zero i (Subtype.ext h1)
  have hα : ∀ i, ∃ (z : 𝓞 K) (t : 𝓞 F), t ∉ 𝔭 ∧ (α i : K) =
      algebraMap (𝓞 K) K z * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ := fun i => by
    obtain ⟨z, s, ⟨t, ht, rfl⟩, hz⟩ := (α i).2
    exact ⟨z, t, ht, hz⟩
  choose e t ht he using hα
  have ht0 : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) ≠ 0 := by
    intro i h0
    have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
    have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
    exact ht i (h2 ▸ 𝔭.zero_mem)
  have he0 : ∀ i, e i ≠ 0 := fun i h0 => hα0 i (Subtype.ext (by rw [he, h0]; simp))
  have heK : ∀ i, algebraMap (𝓞 K) K (e i) ≠ 0 := fun i => by
    simpa using he0 i
  let b := a.unitsSMul fun i => Units.mk0 (algebraMap (𝓞 K) K (e i) * (algebraMap (𝓞 K) K c)⁻¹)
    (mul_ne_zero (heK i) (inv_ne_zero hcK))
  have hb : ∀ i, b i = (algebraMap (𝓞 K) K (e i) * (algebraMap (𝓞 K) K c)⁻¹) • a i := fun i => by
    rw [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hcb : ∀ i, algebraMap (𝓞 K) K c • b i = algebraMap (𝓞 K) K (e i) • a i := fun i => by
    rw [hb, smul_smul, mul_comm, mul_assoc, inv_mul_cancel₀ hcK, mul_one]
  have habV : ∀ i, (((ab' i : N) : MA) : V) = (α i : K) • a i := fun i => by
    rw [hab, ha]
    rfl
  have hτ : ∀ i, μ (b i) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) • (((ab' i : N) : MA) : V) :=
    fun i => by
      rw [hμ, hcb, habV, he, smul_smul, mul_comm, mul_assoc, inv_mul_cancel₀ (ht0 i), mul_one]
  have hsA : Submodule.span (RP K 𝔭) (Set.range a) = MA := by
    have h1 : Set.range a = MA.subtype '' Set.range b' := by
      rw [← Set.range_comp]
      exact congrArg _ (funext ha)
    rw [h1, ← Submodule.map_span, b'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsN : Submodule.span (RP K 𝔭) (Set.range fun i => (((ab' i : N) : MA) : V)) = N' := by
    have h1 : (Set.range fun i => (((ab' i : N) : MA) : V)) =
        MA.subtype '' (N.subtype '' Set.range ab') := by
      rw [← Set.range_comp, ← Set.range_comp]
      rfl
    rw [h1, ← Submodule.map_span, ← Submodule.map_span, ab'.span_eq, Submodule.map_top,
      Submodule.range_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hN']
  have hsB : Submodule.span (RP K 𝔭) (Set.range b) = MB := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨y, hy, hyx⟩ : (((ab' i : N) : MA) : V) ∈ N' := (ab' i).2
      have h1 : μ (b i) = μ (algebraMap (𝓞 F) (𝓞 K) (t i) • y) := by
        rw [hτ, ← hyx, hμ, hμ, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t i)), smul_comm]
      rw [hμi h1, ← algebraMap_smul (RP K 𝔭)]
      exact Submodule.smul_mem _ _ hy
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h1 : μ (b0 j) ∈ N' := ⟨b0 j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
      have h2 : N' ≤ (Submodule.span (RP K 𝔭) (Set.range b)).map μ := by
        rw [← hsN, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        let u : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)))⁻¹,
          ⟨1, _, ⟨t i, ht i, rfl⟩, by simp⟩⟩
        refine ⟨u • b i, Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
        rw [map_smul, hτ, Subalgebra.smul_def, smul_smul, inv_mul_cancel₀ (ht0 i), one_smul]
      obtain ⟨y, hy, hyx⟩ := h2 h1
      exact hμi hyx ▸ hy
  refine ⟨a, b, e, c, hc0, he0, ?_, ?_, fun i => ?_⟩
  · rw [← ha0]
    ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Submodule.span_span_of_tower, hsA]
  · rw [← hb0]
    ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Submodule.span_span_of_tower, hsB]
  · rw [← algebraMap_smul K, ← algebraMap_smul K (e i), hcb]
end Formalism.HermitianLattices.Ext.L3.D2
