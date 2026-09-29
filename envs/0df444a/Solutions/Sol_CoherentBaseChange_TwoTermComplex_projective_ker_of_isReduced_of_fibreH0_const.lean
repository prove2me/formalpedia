-- Prove2me | solution 1 for CoherentBaseChange.TwoTermComplex.projective_ker_of_isReduced_of_fibreH0_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/46fdc72e-87ec-5e0a-9367-8f193b673bc4

import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Nilpotent.Defs
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const

set_option autoImplicit false

noncomputable section

universe u v w

open scoped TensorProduct
p2m_open "CoherentBaseChange P2MW.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const.CoherentBaseChange"

namespace CBCSol

section SplitKer

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

def kerRetraction (d : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : d ∘ₗ s = LinearMap.id) :
    M →ₗ[R] LinearMap.ker d :=
  (LinearMap.id - s ∘ₗ d).codRestrict (LinearMap.ker d) (fun x => by
    simp only [LinearMap.mem_ker, map_sub, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, ← LinearMap.comp_apply d s, hs, sub_self])

theorem kerRetraction_apply_coe (d : M →ₗ[R] N) {s : N →ₗ[R] M}
    (hs : d ∘ₗ s = LinearMap.id) (x : M) :
    (kerRetraction d hs x : M) = x - s (d x) := rfl

theorem kerRetraction_comp_subtype (d : M →ₗ[R] N) {s : N →ₗ[R] M}
    (hs : d ∘ₗ s = LinearMap.id) :
    (kerRetraction d hs) ∘ₗ (LinearMap.ker d).subtype = LinearMap.id := by
  ext ⟨x, hx⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply,
    kerRetraction_apply_coe, LinearMap.mem_ker.mp hx, map_zero, sub_zero]

variable (A : Type*) [CommRing A] [Algebra R A]

def kerBaseChangeHomOf (d : M →ₗ[R] N) :
    A ⊗[R] (LinearMap.ker d) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  ((LinearMap.ker d).subtype.baseChange A).codRestrict (LinearMap.ker (d.baseChange A)) (fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    suffices h : d ∘ₗ (LinearMap.ker d).subtype = 0 by rw [h]; simp
    ext ⟨y, hy⟩; exact hy)

theorem kerBaseChangeHomOf_apply_coe (d : M →ₗ[R] N) (x : A ⊗[R] (LinearMap.ker d)) :
    (kerBaseChangeHomOf A d x : A ⊗[R] M) = (LinearMap.ker d).subtype.baseChange A x := rfl

theorem kerBaseChangeHomOf_bijective [Module.Projective R N] (d : M →ₗ[R] N)
    (hd : Function.Surjective d) :
    Function.Bijective (kerBaseChangeHomOf A d) := by
  obtain ⟨s, hs⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hd)
  refine ⟨?_, ?_⟩
  · have hri : ((kerRetraction d hs).baseChange A) ∘ₗ ((LinearMap.ker d).subtype.baseChange A)
        = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, kerRetraction_comp_subtype, LinearMap.baseChange_id]
    intro x y hxy
    have heq : (kerRetraction d hs).baseChange A ((LinearMap.ker d).subtype.baseChange A x)
        = (kerRetraction d hs).baseChange A ((LinearMap.ker d).subtype.baseChange A y) := by
      rw [← kerBaseChangeHomOf_apply_coe, ← kerBaseChangeHomOf_apply_coe, hxy]
    simpa only [← LinearMap.comp_apply, hri, LinearMap.id_apply] using heq
  · rintro ⟨y, hy⟩
    have hyk : y ∈ LinearMap.ker (d.lTensor A) := by
      rwa [LinearMap.mem_ker, ← d.baseChange_eq_ltensor, ← LinearMap.mem_ker]
    obtain ⟨x, hx⟩ := (lTensor_exact A (LinearMap.exact_subtype_ker_map d) hd y).mp hyk
    refine ⟨x, Subtype.ext ?_⟩
    simp only [kerBaseChangeHomOf_apply_coe, LinearMap.baseChange_eq_ltensor]
    exact hx

theorem projective_ker_of_surjective_of_projective
    [Module.Projective R M] [Module.Projective R N]
    (d : M →ₗ[R] N) (hd : Function.Surjective d) :
    Module.Projective R (LinearMap.ker d) := by
  obtain ⟨s, hs⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hd)
  exact Module.Projective.of_split (LinearMap.ker d).subtype (kerRetraction d hs)
    (kerRetraction_comp_subtype d hs)

theorem finite_ker_of_surjective_of_projective
    [Module.Finite R M] [Module.Projective R N]
    (d : M →ₗ[R] N) (hd : Function.Surjective d) :
    Module.Finite R (LinearMap.ker d) := by
  obtain ⟨s, hs⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hd)
  exact Module.Finite.of_surjective (kerRetraction d hs)
    (Function.LeftInverse.surjective
      (congrFun <| congrArg DFunLike.coe <| kerRetraction_comp_subtype d hs))

end SplitKer

section FittingFree

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

abbrev κ (𝔭 : PrimeSpectrum R) : Type u := 𝔭.asIdeal.ResidueField

theorem span_one_tmul_eq_top (𝔭 : PrimeSpectrum R) :
    Submodule.span (κ 𝔭) (Set.range fun x : M => (1 : κ 𝔭) ⊗ₜ[R] x) = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  induction t using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a x =>
    have : a ⊗ₜ[R] x = a • ((1 : κ 𝔭) ⊗ₜ[R] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add s t hs ht => exact Submodule.add_mem _ hs ht

theorem exists_basis_one_tmul [Module.Finite R M] (𝔭 : PrimeSpectrum R) :
    ∃ (ι : Type v) (_ : Fintype ι) (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M)),
      ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i := by
  obtain ⟨ι, a, -, haspan, hli⟩ :=
    exists_linearIndependent' (κ 𝔭) (fun x : M => (1 : κ 𝔭) ⊗ₜ[R] x)
  haveI : Finite ι := hli.finite_of_isNoetherian
  let _ : Fintype ι := Fintype.ofFinite ι
  refine ⟨ι, inferInstance, a, Module.Basis.mk hli ?_, fun i => ?_⟩
  · rw [haspan, span_one_tmul_eq_top]
  · simp only [Module.Basis.mk_apply, Function.comp_apply]

theorem subsingleton_residue_tensor_coker (𝔭 : PrimeSpectrum R) {ι : Type v} [Fintype ι]
    (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M)) (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i) :
    Subsingleton (κ 𝔭 ⊗[R] (M ⧸ LinearMap.range (Fintype.linearCombination R m))) := by
  classical
  set φ := Fintype.linearCombination R m with hφ
  have hrange : LinearMap.range (φ.baseChange (κ 𝔭)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨(1 : κ 𝔭) ⊗ₜ[R] Pi.single i 1, ?_⟩
    rw [LinearMap.baseChange_tmul, hb i, hφ, Fintype.linearCombination_apply_single, one_smul]
  have hexact : Function.Exact (φ.baseChange (κ 𝔭))
      ((LinearMap.range φ).mkQ.baseChange (κ 𝔭)) := by
    have := lTensor_exact (κ 𝔭) (LinearMap.exact_map_mkQ_range φ)
      (Submodule.Quotient.mk_surjective _)
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hsurj : Function.Surjective ((LinearMap.range φ).mkQ.baseChange (κ 𝔭)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (Submodule.Quotient.mk_surjective _)
  have hker : LinearMap.ker ((LinearMap.range φ).mkQ.baseChange (κ 𝔭)) = ⊤ := by
    rw [LinearMap.exact_iff.mp hexact, hrange]
  have hzero : (LinearMap.range φ).mkQ.baseChange (κ 𝔭) = 0 := LinearMap.ker_eq_top.mp hker
  refine ⟨fun p q => ?_⟩
  obtain ⟨p', rfl⟩ := hsurj p
  obtain ⟨q', rfl⟩ := hsurj q
  rw [hzero]
  rfl

theorem baseChange_injective_of_le [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R) {ι : Type v}
    [Fintype ι] (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M))
    (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i) {𝔮 : PrimeSpectrum R} (hle : 𝔮 ≤ 𝔭) :
    Function.Injective ((Fintype.linearCombination R m).baseChange (κ 𝔮)) := by
  set φ := Fintype.linearCombination R m with hφ
  set M' := M ⧸ LinearMap.range φ
  have h𝔭 : 𝔭 ∉ Module.support R M' := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact subsingleton_residue_tensor_coker 𝔭 m b hb
  have h𝔮 : 𝔮 ∉ Module.support R M' := fun h => h𝔭 (Module.mem_support_mono hle h)
  have hsub : Subsingleton (κ 𝔮 ⊗[R] M') := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton] at h𝔮
    exact h𝔮
  have hexact : Function.Exact (φ.baseChange (κ 𝔮))
      ((LinearMap.range φ).mkQ.baseChange (κ 𝔮)) := by
    have := lTensor_exact (κ 𝔮) (LinearMap.exact_map_mkQ_range φ)
      (Submodule.Quotient.mk_surjective _)
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hsurjφ : Function.Surjective (φ.baseChange (κ 𝔮)) := by
    rw [← LinearMap.range_eq_top, ← LinearMap.exact_iff.mp hexact, LinearMap.ker_eq_top]
    ext x
    exact hsub.elim _ _
  haveI : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact (inferInstance : IsEmpty (PrimeSpectrum R)).false 𝔮
  haveI : StrongRankCondition R := commRing_strongRankCondition R
  have hdom : Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] (ι → R)) = e := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card,
      ← hconst 𝔭, Module.finrank_eq_card_basis b]
  have hcod : Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e := hconst 𝔮
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdom.trans hcod.symm)).mpr
    hsurjφ

theorem coeff_mem_of_rel [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R) {ι : Type v} [Fintype ι]
    (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M))
    (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i) {𝔮 : PrimeSpectrum R} (hle : 𝔮 ≤ 𝔭)
    (x : ι → R) (hx : Fintype.linearCombination R m x = 0) (i : ι) : x i ∈ 𝔮.asIdeal := by
  classical
  have hinj := baseChange_injective_of_le hconst 𝔭 m b hb hle
  have h1x : (1 : κ 𝔮) ⊗ₜ[R] x = 0 := by
    apply hinj
    rw [LinearMap.baseChange_tmul, hx, TensorProduct.tmul_zero, map_zero]
  have hcoord : TensorProduct.piScalarRight R (κ 𝔮) (κ 𝔮) ι ((1 : κ 𝔮) ⊗ₜ[R] x) i = 0 := by
    rw [h1x, map_zero, Pi.zero_apply]
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul] at hcoord
  rw [← Ideal.ker_algebraMap_residueField 𝔮.asIdeal, RingHom.mem_ker,
    Algebra.algebraMap_eq_smul_one]
  exact hcoord

theorem algebraMap_coeff_eq_zero [IsReduced R] [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R)
    {ι : Type v} [Fintype ι] (m : ι → M) (b : Module.Basis ι (κ 𝔭) (κ 𝔭 ⊗[R] M))
    (hb : ∀ i, b i = (1 : κ 𝔭) ⊗ₜ[R] m i)
    (x : ι → R) (hx : Fintype.linearCombination R m x = 0) (i : ι) :
    algebraMap R (Localization.AtPrime 𝔭.asIdeal) (x i) = 0 := by
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  have hdis := ((IsLocalization.isPrime_iff_isPrime_disjoint 𝔭.asIdeal.primeCompl
    (Localization.AtPrime 𝔭.asIdeal) P).mp hP)
  let 𝔮 : PrimeSpectrum R := ⟨P.under R, hdis.1⟩
  have hle : 𝔮 ≤ 𝔭 := by
    intro r hr
    by_contra hnot
    exact Set.disjoint_left.mp hdis.2 hnot hr
  have hmem : x i ∈ 𝔮.asIdeal := coeff_mem_of_rel hconst 𝔭 m b hb hle x hx i
  exact Ideal.mem_comap.mp hmem

theorem free_localizedModule_of_isReduced [IsReduced R] [Module.Finite R M] {e : ℕ}
    (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e)
    (𝔭 : PrimeSpectrum R) :
    Module.Free (Localization.AtPrime 𝔭.asIdeal)
      (LocalizedModule 𝔭.asIdeal.primeCompl M) := by
  classical
  obtain ⟨ι, _, m, b, hb⟩ := exists_basis_one_tmul (M := M) 𝔭
  set Rp := Localization.AtPrime 𝔭.asIdeal
  set S := 𝔭.asIdeal.primeCompl
  set Mp := LocalizedModule S M
  let f : M →ₗ[R] Mp := LocalizedModule.mkLinearMap S M
  let bv : ι → Mp := fun i => f (m i)
  have hspan : Submodule.span Rp (Set.range bv) = ⊤ := by
    let ebc : Rp ⊗[R] M ≃ₗ[Rp] Mp := (IsLocalizedModule.isBaseChange S Rp f).equiv
    let E : κ 𝔭 ⊗[Rp] Mp ≃ₗ[κ 𝔭] κ 𝔭 ⊗[R] M :=
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (κ 𝔭) (κ 𝔭)) ebc.symm)
        ≪≫ₗ TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp (κ 𝔭) (κ 𝔭) M
    refine IsLocalRing.span_eq_top_of_tmul_eq_basis (R := Rp) bv (b.map E.symm) ?_
    intro i
    rw [Module.Basis.map_apply, LinearEquiv.eq_symm_apply, hb i]
    simp only [E, bv, f, LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
      LinearEquiv.refl_apply]
    have hsymm : ebc.symm (LocalizedModule.mkLinearMap S M (m i)) = (1 : Rp) ⊗ₜ[R] m i := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
    rw [hsymm, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  have hli : LinearIndependent Rp bv := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite S c
    choose r hr using hs
    have hrel : f (∑ j, r j • m j) = 0 := by
      have : ∑ j, (algebraMap R Rp (r j)) • bv j = (s : R) • ∑ j, c j • bv j := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hr j, smul_assoc]
      rw [hc, smul_zero] at this
      rw [map_sum]
      simpa only [bv, map_smul, algebraMap_smul] using this
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S f).mp hrel
    have hx : Fintype.linearCombination R m (fun j => (t : R) * r j) = 0 := by
      rw [Fintype.linearCombination_apply]
      simp only [mul_smul, ← Finset.smul_sum] at ht ⊢
      exact ht
    have hzero := algebraMap_coeff_eq_zero hconst 𝔭 m b hb _ hx i
    rw [map_mul] at hzero
    have ht_unit : IsUnit (algebraMap R Rp (t : R)) := IsLocalization.map_units Rp t
    have hri : algebraMap R Rp (r i) = 0 := (ht_unit.mul_right_eq_zero).mp hzero
    have hs_unit : IsUnit (algebraMap R Rp (s : R)) := IsLocalization.map_units Rp s
    have : (s : R) • c i = 0 := by rw [← hr i, hri]
    rw [Algebra.smul_def] at this
    exact (hs_unit.mul_right_eq_zero).mp this
  exact Module.Free.of_basis (Module.Basis.mk hli (by rw [hspan]))

theorem projective_of_isReduced_of_finrank_const [IsReduced R] [Module.FinitePresentation R M]
    {e : ℕ} (hconst : ∀ 𝔮 : PrimeSpectrum R, Module.finrank (κ 𝔮) (κ 𝔮 ⊗[R] M) = e) :
    Module.Projective R M := by
  refine Module.projective_of_localization_maximal (fun I hI => ?_)
  haveI := free_localizedModule_of_isReduced hconst ⟨I, hI.isPrime⟩
  exact Module.Projective.of_free

end FittingFree

end CBCSol

namespace CoherentBaseChange
p2m_export "CoherentBaseChange" "TwoTermComplex"
namespace TwoTermComplex
p2m_export "CoherentBaseChange.TwoTermComplex" "fibreH0 fibreH1 kerBaseChangeHom mk C0 d C1"
p2m_open "CoherentBaseChange.TwoTermComplex CoherentBaseChange"

open CBCSol

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)

private def _root_.CoherentBaseChange.TwoTermComplex.fibreRank (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank (κ 𝔭) (LinearMap.range (G.d.baseChange (κ 𝔭)))

p2m_export "CoherentBaseChange.TwoTermComplex" "fibreRank"
private theorem _root_.CoherentBaseChange.TwoTermComplex.fibreH0_add_fibreRank (𝔭 : PrimeSpectrum R) :
    G.fibreH0 𝔭 + G.fibreRank 𝔭 = Module.finrank (κ 𝔭) (κ 𝔭 ⊗[R] G.C0) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.d.baseChange (κ 𝔭))
  show Module.finrank (κ 𝔭) (LinearMap.ker (G.d.baseChange (κ 𝔭)))
      + Module.finrank (κ 𝔭) (LinearMap.range (G.d.baseChange (κ 𝔭))) = _
  omega

p2m_export "CoherentBaseChange.TwoTermComplex" "fibreH0_add_fibreRank"
private theorem _root_.CoherentBaseChange.TwoTermComplex.fibreRank_add_fibreH1 (𝔭 : PrimeSpectrum R) :
    G.fibreRank 𝔭 + G.fibreH1 𝔭 = Module.finrank (κ 𝔭) (κ 𝔭 ⊗[R] G.C1) := by
  have h := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (G.d.baseChange (κ 𝔭)))
  show Module.finrank (κ 𝔭) (LinearMap.range (G.d.baseChange (κ 𝔭)))
      + Module.finrank (κ 𝔭)
          ((κ 𝔭 ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange (κ 𝔭))) = _
  omega

p2m_export "CoherentBaseChange.TwoTermComplex" "fibreRank_add_fibreH1"

private theorem _root_.CoherentBaseChange.TwoTermComplex.fibre_euler [StrongRankCondition R] (𝔭 : PrimeSpectrum R) :
    (G.fibreH0 𝔭 : ℤ) - (G.fibreH1 𝔭 : ℤ)
      = (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ) := by
  have h0 := G.fibreH0_add_fibreRank 𝔭
  have h1 := G.fibreRank_add_fibreH1 𝔭
  rw [Module.finrank_baseChange] at h0 h1
  have h0' : (G.fibreH0 𝔭 : ℤ) + (G.fibreRank 𝔭 : ℤ) = (Module.finrank R G.C0 : ℤ) := by
    exact_mod_cast h0
  have h1' : (G.fibreRank 𝔭 : ℤ) + (G.fibreH1 𝔭 : ℤ) = (Module.finrank R G.C1 : ℤ) := by
    exact_mod_cast h1
  omega

p2m_export "CoherentBaseChange.TwoTermComplex" "fibre_euler"

private abbrev _root_.CoherentBaseChange.TwoTermComplex.coker : Type v := G.C1 ⧸ LinearMap.range G.d

p2m_export "CoherentBaseChange.TwoTermComplex" "coker"
scoped instance coker_finitePresentation : Module.FinitePresentation R G.coker :=
  haveI : Module.FinitePresentation R G.C1 := Module.finitePresentation_of_projective R G.C1
  Module.finitePresentation_of_surjective (LinearMap.range G.d).mkQ
    (Submodule.Quotient.mk_surjective _) (by
      rw [Submodule.ker_mkQ]; exact Submodule.fg_range G.d)

private def _root_.CoherentBaseChange.TwoTermComplex.cokerBaseChangeEquiv (𝔭 : PrimeSpectrum R) :
    ((κ 𝔭 ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange (κ 𝔭))) ≃ₗ[κ 𝔭] κ 𝔭 ⊗[R] G.coker := by
  have hexact : Function.Exact (G.d.baseChange (κ 𝔭))
      ((LinearMap.range G.d).mkQ.baseChange (κ 𝔭)) := by
    have := lTensor_exact (κ 𝔭) (LinearMap.exact_map_mkQ_range G.d)
      (Submodule.Quotient.mk_surjective _)
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hsurj : Function.Surjective ((LinearMap.range G.d).mkQ.baseChange (κ 𝔭)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (Submodule.Quotient.mk_surjective _)
  exact hexact.linearEquivOfSurjective hsurj

p2m_export "CoherentBaseChange.TwoTermComplex" "cokerBaseChangeEquiv"
private theorem _root_.CoherentBaseChange.TwoTermComplex.finrank_residue_tensor_coker (𝔭 : PrimeSpectrum R) :
    Module.finrank (κ 𝔭) (κ 𝔭 ⊗[R] G.coker) = G.fibreH1 𝔭 :=
  ((G.cokerBaseChangeEquiv 𝔭).finrank_eq).symm

p2m_export "CoherentBaseChange.TwoTermComplex" "finrank_residue_tensor_coker"

private theorem _root_.CoherentBaseChange.TwoTermComplex.fibreH1_eq_of_fibreH0_const {c : ℕ} (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c)
    (𝔭 𝔮 : PrimeSpectrum R) : G.fibreH1 𝔭 = G.fibreH1 𝔮 := by
  haveI : Nontrivial R :=
    ⟨0, 1, fun h01 => 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (h01 ▸ 𝔭.asIdeal.zero_mem))⟩
  haveI : StrongRankCondition R := commRing_strongRankCondition R
  have h𝔭 := G.fibre_euler 𝔭
  have h𝔮 := G.fibre_euler 𝔮
  rw [h0 𝔭] at h𝔭
  rw [h0 𝔮] at h𝔮
  omega

p2m_export "CoherentBaseChange.TwoTermComplex" "fibreH1_eq_of_fibreH0_const"

private theorem _root_.CoherentBaseChange.TwoTermComplex.projective_coker_of_isReduced_of_fibreH0_const [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) : Module.Projective R G.coker := by
  refine Module.projective_of_localization_maximal (fun I hI => ?_)
  let 𝔪 : PrimeSpectrum R := ⟨I, hI.isPrime⟩
  haveI := free_localizedModule_of_isReduced (M := G.coker) (e := G.fibreH1 𝔪)
    (fun 𝔮 => by rw [G.finrank_residue_tensor_coker, G.fibreH1_eq_of_fibreH0_const h0 𝔮 𝔪]) 𝔪
  exact Module.Projective.of_free

p2m_export "CoherentBaseChange.TwoTermComplex" "projective_coker_of_isReduced_of_fibreH0_const"

private theorem _root_.CoherentBaseChange.TwoTermComplex.exists_retraction_range [Module.Projective R G.coker] :
    ∃ r : G.C1 →ₗ[R] LinearMap.range G.d,
      r ∘ₗ (LinearMap.range G.d).subtype = LinearMap.id := by
  obtain ⟨s, hs⟩ := (LinearMap.range G.d).mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.Quotient.mk_surjective _))
  have hsec : ∀ q, (LinearMap.range G.d).mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  have hmem : ∀ x : G.C1, x - s ((LinearMap.range G.d).mkQ x) ∈ LinearMap.range G.d := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hsec, sub_self]
  let r : G.C1 →ₗ[R] LinearMap.range G.d :=
    (LinearMap.id - s ∘ₗ (LinearMap.range G.d).mkQ).codRestrict (LinearMap.range G.d) hmem
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  have hx0 : (LinearMap.range G.d).mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
  simp [r, LinearMap.codRestrict_apply, hx0]

p2m_export "CoherentBaseChange.TwoTermComplex" "exists_retraction_range"

private theorem _root_.CoherentBaseChange.TwoTermComplex.projective_range_of_isReduced_of_fibreH0_const [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) : Module.Projective R (LinearMap.range G.d) := by
  haveI := G.projective_coker_of_isReduced_of_fibreH0_const h0
  obtain ⟨r, hr⟩ := G.exists_retraction_range
  exact Module.Projective.of_split (LinearMap.range G.d).subtype r hr

p2m_export "CoherentBaseChange.TwoTermComplex" "projective_range_of_isReduced_of_fibreH0_const"

private theorem _root_.CoherentBaseChange.TwoTermComplex.projective_ker_of_isReduced_impl [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) : Module.Projective R (LinearMap.ker G.d) := by
  haveI := G.projective_range_of_isReduced_of_fibreH0_const h0
  rw [← LinearMap.ker_rangeRestrict]
  exact projective_ker_of_surjective_of_projective G.d.rangeRestrict
    (LinearMap.surjective_rangeRestrict G.d)

p2m_export "CoherentBaseChange.TwoTermComplex" "projective_ker_of_isReduced_impl"

theorem kerBaseChangeHom_eq (A : Type w) [CommRing A] [Algebra R A] :
    G.kerBaseChangeHom A = kerBaseChangeHomOf A G.d := rfl

private theorem _root_.CoherentBaseChange.TwoTermComplex.kerBaseChangeHom_bijective_of_isReduced_impl [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) (A : Type w) [CommRing A] [Algebra R A] :
    Function.Bijective (G.kerBaseChangeHom A) := by
  haveI := G.projective_coker_of_isReduced_of_fibreH0_const h0
  haveI := G.projective_range_of_isReduced_of_fibreH0_const h0
  set d' := G.d.rangeRestrict with hd'
  set ι := (LinearMap.range G.d).subtype with hι
  have hfac : G.d = ι ∘ₗ d' := (LinearMap.subtype_comp_codRestrict _ _ _).symm
  obtain ⟨r, hr⟩ := G.exists_retraction_range
  have hιinj : Function.Injective (ι.baseChange A) := by
    have hri : (r.baseChange A) ∘ₗ (ι.baseChange A) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (congrFun (congrArg DFunLike.coe hri))
  have hbc : G.d.baseChange A = (ι.baseChange A) ∘ₗ (d'.baseChange A) := by
    rw [← LinearMap.baseChange_comp]; exact congrArg (LinearMap.baseChange A) hfac
  have hker : ∀ x, x ∈ LinearMap.ker (G.d.baseChange A) ↔ x ∈ LinearMap.ker (d'.baseChange A) := by
    intro x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hbc, LinearMap.comp_apply]
    exact ⟨fun h => hιinj (by rw [map_zero]; exact h), fun h => by rw [h, map_zero]⟩
  have hbij := kerBaseChangeHomOf_bijective A d' (LinearMap.surjective_rangeRestrict G.d)
  have hkd : LinearMap.ker d' = LinearMap.ker G.d := LinearMap.ker_rangeRestrict G.d
  rw [kerBaseChangeHom_eq]
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨s, hs⟩ := d'.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (LinearMap.surjective_rangeRestrict G.d))
    let ρ : G.C0 →ₗ[R] LinearMap.ker G.d :=
      (LinearEquiv.ofEq _ _ hkd).toLinearMap ∘ₗ kerRetraction d' hs
    have hρ : ρ ∘ₗ (LinearMap.ker G.d).subtype = LinearMap.id := by
      ext ⟨w, hw⟩
      have hw' : d' w = 0 := by rw [← LinearMap.mem_ker, hkd]; exact hw
      simp [ρ, hw', kerRetraction_apply_coe]
    have hri : (ρ.baseChange A) ∘ₗ ((LinearMap.ker G.d).subtype.baseChange A) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hρ, LinearMap.baseChange_id]
    have hsub_inj : Function.Injective ((LinearMap.ker G.d).subtype.baseChange A) :=
      Function.LeftInverse.injective (congrFun (congrArg DFunLike.coe hri))
    apply hsub_inj
    have hxy' := congrArg (fun t : LinearMap.ker (G.d.baseChange A) => (t : A ⊗[R] G.C0)) hxy
    exact hxy'
  · obtain ⟨z, hz⟩ := z
    have hz' : z ∈ LinearMap.ker (d'.baseChange A) := (hker z).mp hz
    obtain ⟨w, hw⟩ := hbij.2 ⟨z, hz'⟩
    refine ⟨((LinearEquiv.ofEq _ _ hkd).toLinearMap).baseChange A w, ?_⟩
    apply Subtype.ext
    have hw0 := congrArg (fun t : LinearMap.ker (d'.baseChange A) => (t : A ⊗[R] G.C0)) hw
    change (LinearMap.ker G.d).subtype.baseChange A
      (((LinearEquiv.ofEq _ _ hkd).toLinearMap).baseChange A w) = z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have hcomp : (LinearMap.ker G.d).subtype ∘ₗ (LinearEquiv.ofEq _ _ hkd).toLinearMap
        = (LinearMap.ker d').subtype := by
      ext; simp
    rw [hcomp]
    exact hw0

p2m_export "CoherentBaseChange.TwoTermComplex" "kerBaseChangeHom_bijective_of_isReduced_impl"

private theorem _root_.CoherentBaseChange.TwoTermComplex.finrank_residue_ker_of_isReduced_impl [IsReduced R] {c : ℕ}
    (h0 : ∀ 𝔭, G.fibreH0 𝔭 = c) (𝔭 : PrimeSpectrum R) :
    Module.finrank (κ 𝔭) (κ 𝔭 ⊗[R] LinearMap.ker G.d) = c := by
  have hb := G.kerBaseChangeHom_bijective_of_isReduced_impl h0 (κ 𝔭)
  rw [(LinearEquiv.ofBijective (G.kerBaseChangeHom (κ 𝔭)) hb).finrank_eq]
  exact h0 𝔭

p2m_export "CoherentBaseChange.TwoTermComplex" "finrank_residue_ker_of_isReduced_impl"
end CoherentBaseChange.TwoTermComplex
p2m_reactivate "P2MW.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const.CoherentBaseChange P2MW.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const.CoherentBaseChange.TwoTermComplex"
p2m_reactivate "P2MW.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const.CoherentBaseChange"

theorem solution
    {R : Type u} [CommRing R] [IsReduced R] (G : TwoTermComplex.{u, v} R) {c : ℕ}
    (h0 : ∀ 𝔭 : PrimeSpectrum R, G.fibreH0 𝔭 = c) :
    Module.Projective R (LinearMap.ker G.d) ∧
      (∀ (A : Type w) [CommRing A] [Algebra R A], Function.Bijective (G.kerBaseChangeHom A)) ∧
      ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
        (𝔭.asIdeal.ResidueField ⊗[R] LinearMap.ker G.d) = c :=
  ⟨G.projective_ker_of_isReduced_impl h0,
    fun A _ _ => G.kerBaseChangeHom_bijective_of_isReduced_impl h0 A,
    fun 𝔭 => G.finrank_residue_ker_of_isReduced_impl h0 𝔭⟩

end
end S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const
end P2MW
export P2MW.S_CoherentBaseChange_TwoTermComplex_projective_ker_of_isReduced_of_fibreH0_const (solution)
