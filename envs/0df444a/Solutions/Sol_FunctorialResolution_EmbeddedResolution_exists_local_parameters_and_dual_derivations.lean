-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_local_parameters_and_dual_derivations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:34:41.4962+00:00
-- url     : https://prove2.me/submissions/bfd2dd09-cec7-4f5b-8918-3ac5af9b8c03

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_local_parameters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
  [Algebra k (IsLocalRing.ResidueField A)]
  [IsScalarTower k A (IsLocalRing.ResidueField A)]
  [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution :
    ∃ (h : ℕ) (y : Fin h → A) (δ : Fin h → Derivation k A A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      ∀ i j : Fin h, δ i (y j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨h, y, hspan, hind⟩ := exists_local_parameters k A
  obtain ⟨v, hv⟩ : ∃ v : Fin h → (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      v = fun i => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (y i)) :=
    ⟨_, rfl⟩
  rw [← hv] at hind
  have hψ : ∀ i : Fin h, ∃ ψ : (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)
      →ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A,
      ∀ j, ψ (v j) = if i = j then 1 else 0 := by
    intro i
    obtain ⟨g, hg⟩ := LinearMap.exists_extend
      ((Finsupp.lapply i).comp (hind.repr : _ →ₗ[IsLocalRing.ResidueField A] _))
    refine ⟨g, fun j => ?_⟩
    have hmem : v j ∈ Submodule.span (IsLocalRing.ResidueField A) (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self j)
    have h1 : hind.repr ⟨v j, hmem⟩ = Finsupp.single j 1 := hind.repr_eq_single j _ rfl
    have h2 := LinearMap.congr_fun hg ⟨v j, hmem⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      h1, Finsupp.lapply_apply, Finsupp.single_apply] at h2
    rw [h2]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  choose ψ hψ' using hψ
  simp only [hv] at hψ'
  have hsurj : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) :=
    Ideal.Quotient.mk_surjective
  have hσ : ∀ c, algebraMap A (IsLocalRing.ResidueField A) (Function.surjInv hsurj c) = c :=
    Function.surjInv_eq hsurj
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin h → (KaehlerDifferential k A →ₗ[A] A),
      ∀ i j, φ i (Module.Free.chooseBasis A (KaehlerDifferential k A) j)
        = Function.surjInv hsurj (ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            (Module.Free.chooseBasis A (KaehlerDifferential k A) j))) :=
    ⟨fun i => (Module.Free.chooseBasis A (KaehlerDifferential k A)).constr A
        (fun j => Function.surjInv hsurj (ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          (Module.Free.chooseBasis A (KaehlerDifferential k A) j)))),
      fun i j => by simp⟩
  have hres : ∀ (i : Fin h) (ω : KaehlerDifferential k A),
      algebraMap A (IsLocalRing.ResidueField A) (φ i ω)
        = ψ i ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] ω) := by
    intro i
    have hmaps : (Algebra.linearMap A (IsLocalRing.ResidueField A)).comp (φ i)
        = ((ψ i).restrictScalars A).comp
            (TensorProduct.mk A (IsLocalRing.ResidueField A) (KaehlerDifferential k A) 1) := by
      refine (Module.Free.chooseBasis A (KaehlerDifferential k A)).ext (fun j => ?_)
      simp only [LinearMap.comp_apply, Algebra.linearMap_apply, hφ, hσ,
        LinearMap.coe_restrictScalars, TensorProduct.mk_apply]
    intro ω
    have hh := LinearMap.congr_fun hmaps ω
    simpa using hh
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin h) (Fin h) A,
      M = Matrix.of fun i j => φ i (KaehlerDifferential.D k A (y j)) := ⟨_, rfl⟩
  have hMapp : ∀ a b, M a b = φ a (KaehlerDifferential.D k A (y b)) := by
    intro a b; rw [hMdef]; rfl
  have hMres : ∀ a b, algebraMap A (IsLocalRing.ResidueField A) (M a b)
      = if a = b then 1 else 0 := by
    intro a b
    rw [hMapp, hres a, hψ' a b]
  have hmapM : M.map (algebraMap A (IsLocalRing.ResidueField A)) = 1 := by
    ext a b
    rw [Matrix.map_apply, hMres, Matrix.one_apply]
  have hdet1 : algebraMap A (IsLocalRing.ResidueField A) M.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmapM, Matrix.det_one]
  have hdet : IsUnit M.det := by
    by_contra hcon
    have h1 : Ideal.span ({M.det} : Set A) ≠ ⊤ := fun hq =>
      hcon (Ideal.span_singleton_eq_top.mp hq)
    have hmem : M.det ∈ IsLocalRing.maximalIdeal A :=
      IsLocalRing.le_maximalIdeal h1 (Ideal.mem_span_singleton_self _)
    have hzero : algebraMap A (IsLocalRing.ResidueField A) M.det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hdet1] at hzero
    exact one_ne_zero hzero
  have hinvMul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  refine ⟨h, y, fun i => (∑ l : Fin h, (M⁻¹ i l) • φ l).compDer (KaehlerDifferential.D k A),
    hspan, ?_⟩
  intro i j
  have hsum : (∑ l : Fin h, M⁻¹ i l * M l j) = if i = j then 1 else 0 := by
    rw [← Matrix.mul_apply, hinvMul, Matrix.one_apply]
  show (∑ l : Fin h, (M⁻¹ i l) • φ l) (KaehlerDifferential.D k A (y j)) = if i = j then 1 else 0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  calc (∑ l : Fin h, M⁻¹ i l * φ l (KaehlerDifferential.D k A (y j)))
      = ∑ l : Fin h, M⁻¹ i l * M l j := by
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [hMapp]
    _ = if i = j then 1 else 0 := hsum
end FunctorialResolution.EmbeddedResolution
