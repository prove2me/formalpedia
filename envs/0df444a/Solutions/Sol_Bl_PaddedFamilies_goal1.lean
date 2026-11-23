-- Prove2me | solution 1 for Bl.PaddedFamilies.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:22.467203+00:00
-- url     : https://prove2.me/submissions/9e24218b-d98c-4b05-a405-310c7bbebfb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Lemmata_PaddedFamilies_PadFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.PaddedFamilies
open NumberField IsDedekindDomain
private lemma pad_fam {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Lb : Submodule (𝓞 E) (Fin n → E)) {ι : Type} [Fintype ι] (hcard : Fintype.card ι ≤ n)
    (X : ι → Fin n → E) (hX : ∀ j, X j ∈ Lb) (c : E)
    (hc : ∀ z ∈ Lb, c • z ∈ Submodule.span (𝓞 E) (Set.range X)) :
    ∃ x : Fin n → Fin n → E, (∀ i, x i ∈ Lb) ∧
      ∀ z ∈ Lb, ∃ a : Fin n → 𝓞 E, c • z = ∑ i, ((a i : 𝓞 E) : E) • x i := by
  classical
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  refine ⟨Function.extend e X 0, fun i => ?_, fun z hz => ?_⟩
  · by_cases h : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := h
      rw [e.injective.extend_apply]
      exact hX j
    · rw [Function.extend_apply' _ _ _ h]
      exact Lb.zero_mem
  · have hsub : Set.range X ⊆ Set.range (Function.extend e X 0) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨e j, e.injective.extend_apply _ _ _⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp
      (Submodule.span_mono hsub (hc z hz))
    exact ⟨a, ha.symm⟩
end Bl.PaddedFamilies
end

set_option autoImplicit false
open Bl Bl.PaddedFamilies
open NumberField IsDedekindDomain
namespace Bl.PaddedFamilies
theorem _root_.solution :
  PI.SelfDualLoc.W.LocBasis := by
  intro F E _ _ _ _ _ n v Lb hfin hspan
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.iff_fg.mp hfin)
  set M := Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl with hMdef
  have hM : M ≤ nonZeroDivisors (𝓞 E) := map_le_nonZeroDivisors_of_injective _
    (FaithfulSMul.algebraMap_injective _ _) v.asIdeal.primeCompl_le_nonZeroDivisors
  let A : Subalgebra (𝓞 E) E := Localization.subalgebra.ofField E M hM
  have : IsLocalization M A := inferInstance
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain (𝓞 E) hM A
  let : Algebra (𝓞 F) A := ((algebraMap (𝓞 E) A).comp (algebraMap (𝓞 F) (𝓞 E))).toAlgebra
  have : IsScalarTower (𝓞 F) (𝓞 E) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsPrincipalIdealRing A :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot
  have h1 : ∀ z : M, ((IsLocalization.mk' A (1 : 𝓞 E) z : A) : E) * ((z : 𝓞 E) : E) = 1 := by
    intro z
    have h := IsLocalization.mk'_spec A (1 : 𝓞 E) z
    rw [map_one] at h
    exact congrArg Subtype.val h
  let N : Submodule A (Fin n → E) := Submodule.span A (S : Set (Fin n → E))
  have : Module.Free A N := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis A N
  have hb : ∀ j, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      (algebraMap F E (t : F)) • (b j : Fin n → E) ∈ Lb := by
    intro j
    obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff M).mp (b j).2
    obtain ⟨t, ht, hzt⟩ := z.2
    refine ⟨t, ht, ?_⟩
    rw [hS] at hy
    have key : ((z : 𝓞 E) : E) • (b j : Fin n → E) = y := by
      rw [hz]
      change ((z : 𝓞 E) : E) • (((IsLocalization.mk' A (1 : 𝓞 E) z : A) : E) • y) = y
      rw [smul_smul, mul_comm, h1, one_smul]
    rw [← hzt] at key
    rw [← key] at hy
    exact hy
  choose t ht hX using hb
  have hlin : LinearIndependent E (fun j => (b j : Fin n → E)) :=
    (b.linearIndependent.map' N.subtype (Submodule.ker_subtype N)).localization
      (Rₛ := E) (S := nonZeroDivisors A)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A N) ≤ n := by
    have := hlin.fintype_card_le_finrank
    rwa [Module.finrank_fin_fun] at this
  let ι := Module.Free.ChooseBasisIndex A N
  let zt : ι → M := fun j => ⟨algebraMap (𝓞 F) (𝓞 E) (t j), t j, ht j, rfl⟩
  let f : (↥S × ι) → A := fun p =>
    b.repr ⟨p.1, Submodule.subset_span p.1.2⟩ p.2 * IsLocalization.mk' A (1 : 𝓞 E) (zt p.2)
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite M f
  obtain ⟨u, hu, hmu⟩ := m.2
  have hmE : ((m : 𝓞 E) : E) = algebraMap F E (u : F) := by
    rw [← hmu]
    rfl
  let X : ι → Fin n → E := fun j => algebraMap F E (t j : F) • (b j : Fin n → E)
  have hc : ∀ z ∈ Lb, algebraMap F E (u : F) • z ∈ Submodule.span (𝓞 E) (Set.range X) := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem g hg =>
      have hsum := congrArg Subtype.val (b.sum_repr ⟨g, Submodule.subset_span hg⟩)
      rw [Submodule.coe_sum] at hsum
      simp only [Submodule.coe_smul] at hsum
      rw [← hsum, Finset.smul_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      obtain ⟨r, hr⟩ := hm (⟨g, hg⟩, j)
      have hrE : (r : E) = ((m : 𝓞 E) : E) *
          (((b.repr ⟨g, Submodule.subset_span hg⟩ j : A) : E) *
            ((IsLocalization.mk' A (1 : 𝓞 E) (zt j) : A) : E)) := congrArg Subtype.val hr
      have htE : ((IsLocalization.mk' A (1 : 𝓞 E) (zt j) : A) : E) * algebraMap F E (t j : F) = 1 :=
        h1 (zt j)
      have heq : algebraMap F E (u : F) •
          ((b.repr ⟨g, Submodule.subset_span hg⟩ j : A) • (b j : Fin n → E)) = r • X j := by
        change algebraMap F E (u : F) •
          (((b.repr ⟨g, Submodule.subset_span hg⟩ j : A) : E) • (b j : Fin n → E)) =
            (r : E) • (algebraMap F E (t j : F) • (b j : Fin n → E))
        rw [smul_smul, smul_smul, hrE, hmE, mul_assoc, mul_assoc, htE, mul_one]
      rw [heq]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl⟩)
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ a hx
  obtain ⟨x, hx1, hx2⟩ := pad_fam Lb hcard X hX _ hc
  exact ⟨x, u, hu, hx1, hx2⟩
end Bl.PaddedFamilies
