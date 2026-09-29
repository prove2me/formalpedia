-- Prove2me | solution 1 for FullLevelTate.Datum.exists_injective_equivariant_of_eigenIsoHom_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/724ca132-b1c7-59d6-97b8-f57735e4f1ab

import Definitions.Def_FullLevelTate_IsoHom
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_BostonLenstraRibet_exists_embedding_of_irreducible_of_odd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FullLevelTate_Datum_exists_injective_equivariant_of_eigenIsoHom_ne_bot
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

namespace FLTateC1a

open Polynomial
open scoped TensorProduct

private theorem baseChange_quad_c1a {O' : Type} [CommRing O'] {V : Type} [AddCommGroup V] [Module O' V]
    (K : Type) [Field K] [Algebra O' K]
    (G H U : Module.End O' V) (a : O') :
    (G * G - H * G + a • U).baseChange K =
      G.baseChange K ∘ₗ G.baseChange K - H.baseChange K ∘ₗ G.baseChange K
        + algebraMap O' K a • U.baseChange K := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul k v =>
      simp only [LinearMap.baseChange_tmul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.mul_apply, LinearMap.comp_apply, TensorProduct.tmul_add, TensorProduct.tmul_sub,
        TensorProduct.tmul_smul, algebraMap_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem baseChange_quad'_c1a {O' : Type} [CommRing O'] {V : Type} [AddCommGroup V] [Module O' V]
    (K : Type) [Field K] [Algebra O' K]
    (G : Module.End O' V) (a b : O') :
    (G * G - a • G + b • (1 : Module.End O' V)).baseChange K =
      G.baseChange K ∘ₗ G.baseChange K - algebraMap O' K a • G.baseChange K
        + algebraMap O' K b • (1 : Module.End K (K ⊗[O'] V)) := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul k v =>
      simp only [LinearMap.baseChange_tmul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.mul_apply, LinearMap.comp_apply, Module.End.one_apply, TensorProduct.tmul_add,
        TensorProduct.tmul_sub, TensorProduct.tmul_smul, algebraMap_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem trace_det_of_charpoly_c1a {O' : Type} [CommRing O'] [IsLocalRing O'] (K : Type) [Field K]
    [Algebra O' K] (ρ : GaloisRepAdic O')
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a b : K)
    (h : (LinearMap.charpoly (ρ.ρ σ)).map (algebraMap O' K) = X ^ 2 - C a * X + C b) :
    algebraMap O' K (LinearMap.trace O' ρ.V (ρ.ρ σ)) = a ∧ algebraMap O' K (LinearMap.det (ρ.ρ σ)) = b := by
  classical
  let bs := Module.finBasisOfFinrankEq O' ρ.V ρ.finrank_eq
  have h1 : ((LinearMap.charpoly (ρ.ρ σ)).map (algebraMap O' K)).coeff 1 = -a := by
    rw [h]; simp
  have h0 : ((LinearMap.charpoly (ρ.ρ σ)).map (algebraMap O' K)).coeff 0 = b := by
    rw [h]; simp
  rw [Polynomial.coeff_map] at h1 h0
  constructor
  · rw [LinearMap.trace_eq_matrix_trace O' bs, Matrix.trace_eq_neg_charpoly_coeff, LinearMap.charpoly_toMatrix,
      map_neg, Fintype.card_fin]
    rw [show (2 - 1 : ℕ) = 1 from rfl, h1, neg_neg]
  · rw [← LinearMap.det_toMatrix bs, Matrix.det_eq_sign_charpoly_coeff, LinearMap.charpoly_toMatrix, Fintype.card_fin,
      map_mul, map_pow, map_neg, map_one, h0]
    ring

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} {O' : Type} [CommRing O'] [IsLocalRing O']

private theorem rel_frobenius_c1a (D : FullLevelTate.Datum q M' O')
    (K : Type) [Field K] [Algebra O' K]
    {H : Subgroup (CuspidalType.GL2 q)} {W : Type} [AddCommGroup W] [Module K W] (χ : Representation K H W)
    (hcentral : ∀ c : (ZMod q)ˣ, ∃ h : H, (h : CuspidalType.GL2 q) = CuspidalType.scalarElem q c ∧ χ h = 1)
    (hk : ModularCurve.HeckeAlg →+* K)
    (S : Finset ℕ) (ρ : GaloisRepAdic O')
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ¬ ℓ ∣ M' → ℓ ∉ (↑S : Set ℕ) →
      (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt s ℓ →
          (LinearMap.charpoly (ρ.ρ s)).map (algebraMap O' K) =
            X ^ 2 - C (hk (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)) * X + C ((ℓ : K))) :
    ∀ (ℓ : ℕ) (_ : ℓ.Prime), ℓ ≠ q → ¬ ℓ ∣ M' → ℓ ∉ (↑S : Set ℕ) →
      (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          ∀ f ∈ {f : W →ₗ[K] K ⊗[O'] D.V |
              ∃ e : D.eigenIsoHom K χ hk, ((e : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V) = f},
            (D.gal τ * D.gal τ - LinearMap.trace O' ρ.V (ρ.ρ τ) • D.gal τ
                + LinearMap.det (ρ.ρ τ) • (1 : Module.End O' D.V)).baseChange K ∘ₗ f = 0 := by
  intro ℓ hℓ hℓq hℓM hℓS hℓm A hA τ hτ f hf
  obtain ⟨e, rfl⟩ := hf
  have hcop : ℓ.Coprime q := (Nat.coprime_primes hℓ Fact.out).mpr hℓq
  obtain ⟨htr, hdet⟩ := trace_det_of_charpoly_c1a K ρ τ _ _ (hρ ℓ hℓ hℓq hℓM hℓS hℓm A hA τ hτ)

  have hES := congrArg (fun T : Module.End O' D.V =>
      T.baseChange K ∘ₗ ((e : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V)) (D.eichlerShimura ℓ hℓ hcop hℓM hℓm A hA τ hτ)
  simp only [LinearMap.baseChange_zero, LinearMap.zero_comp, baseChange_quad_c1a, LinearMap.add_comp,
    LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_assoc, map_natCast] at hES

  obtain ⟨h, hh, hχ⟩ := hcentral (ZMod.unitOfCoprime ℓ hcop)
  have hcent : (D.gl2 (CuspidalType.scalarElem q (ZMod.unitOfCoprime ℓ hcop))).baseChange K ∘ₗ
      ((e : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V) = ((e : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V) := by
    have hm := (D.mem_isoHom_iff K χ _).mp (e : D.isoHom K χ).2 h
    rw [hχ, hh] at hm
    rw [← hm]
    exact LinearMap.comp_id _

  have heig : (D.hecke (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K ∘ₗ
      ((D.gal τ).baseChange K ∘ₗ ((e : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V)) =
        hk (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) •
          ((D.gal τ).baseChange K ∘ₗ ((e : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V)) := by
    have hm := (D.mem_eigenIsoHom_iff K χ hk _).mp (D.eigenIsoHomGal K χ hk τ e).2 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)
    exact congrArg (fun x : D.isoHom K χ => (x : W →ₗ[K] K ⊗[O'] D.V)) hm
  rw [heig, hcent] at hES
  rw [baseChange_quad'_c1a, LinearMap.add_comp, LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.smul_comp,
    LinearMap.comp_assoc, htr, hdet]
  rw [Module.End.one_eq_id, LinearMap.id_comp]
  exact hES

end FLTateC1a

private theorem c1b_map_mem_smul_top {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (g : M →ₗ[R] N) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : g x ∈ I • (⊤ : Submodule R N) := by
  exact Submodule.smul_top_le_comap_smul_top I g hx

private theorem c1b_end_mem_smul_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) (X : Module.End R M)
    (hX : ∀ v : M, X v ∈ I • (⊤ : Submodule R M)) :
    X ∈ I • (⊤ : Submodule R (Module.End R M)) := by
  let b := Module.Free.chooseBasis R M
  have hXeq : X = ∑ i, LinearMap.smulRightₗ (b.coord i) (X (b i)) := by
    refine LinearMap.ext fun v => ?_
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul, LinearMap.sum_apply, LinearMap.smulRightₗ_apply, LinearMap.smulRight_apply,
      Module.Basis.coord_apply]
  rw [hXeq]
  exact Submodule.sum_mem _ fun i _ => c1b_map_mem_smul_top I (LinearMap.smulRightₗ (b.coord i)) (hX (b i))

private theorem c1b_baseChange_eq_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (A : Type) [CommRing A] [Algebra R A] (hA : ∀ r ∈ I, algebraMap R A r = 0)
    (T : Module.End R M) (hT : ∀ v : M, T v - v ∈ I • (⊤ : Submodule R M)) : T.baseChange A = 1 := by
  have key : ∀ (a : A) (m : M), m ∈ I • (⊤ : Submodule R M) → (a ⊗ₜ[R] m : A ⊗[R] M) = 0 := by
    intro a m hm
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr n _
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, hA r hr, zero_mul,
        TensorProduct.zero_tmul]
    · intro x y hx hy
      rw [TensorProduct.tmul_add, hx, hy, add_zero]
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a m =>
    rw [LinearMap.baseChange_tmul]
    show a ⊗ₜ[R] T m = a ⊗ₜ[R] m
    have h := key a (T m - m) (hT m)
    rwa [TensorProduct.tmul_sub, sub_eq_zero] at h
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem c1b_trace_det_sub_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) (h x : Module.End R M)
    (hh : ∀ v : M, h v - v ∈ I • (⊤ : Submodule R M)) :
    LinearMap.trace R M (h * x) - LinearMap.trace R M x ∈ I ∧
      LinearMap.det (h * x) - LinearMap.det x ∈ I := by
  have h1 : h.baseChange (R ⧸ I) = 1 :=
    c1b_baseChange_eq_one I (R ⧸ I)
      (fun r hr => by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hr) h hh
  constructor
  · rw [← Ideal.Quotient.eq, ← Ideal.Quotient.algebraMap_eq, ← LinearMap.trace_baseChange,
      ← LinearMap.trace_baseChange, LinearMap.baseChange_mul, h1, one_mul]
  · rw [← Ideal.Quotient.eq, ← Ideal.Quotient.algebraMap_eq, ← LinearMap.det_baseChange,
      ← LinearMap.det_baseChange, LinearMap.baseChange_mul, h1, one_mul]

private theorem c1b_rel_conj {R V V₂ G : Type} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup V₂] [Module R V₂] [Module.Free R V₂] [Module.Finite R V₂] [Group G]
    (gal : G →* Module.End R V) (ρ' : G →* Module.End R V₂) (g τ : G) :
    gal (g * τ * g⁻¹) * gal (g * τ * g⁻¹) - LinearMap.trace R V₂ (ρ' (g * τ * g⁻¹)) • gal (g * τ * g⁻¹)
        + LinearMap.det (ρ' (g * τ * g⁻¹)) • (1 : Module.End R V) =
      gal g * (gal τ * gal τ - LinearMap.trace R V₂ (ρ' τ) • gal τ + LinearMap.det (ρ' τ) • (1 : Module.End R V))
        * gal g⁻¹ := by
  have hinv : gal g⁻¹ * gal g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : gal g * gal g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have htr : LinearMap.trace R V₂ (ρ' (g * τ * g⁻¹)) = LinearMap.trace R V₂ (ρ' τ) := by
    rw [map_mul ρ', map_mul ρ', LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ', inv_mul_cancel, map_one,
      one_mul]
  have hdet : LinearMap.det (ρ' (g * τ * g⁻¹)) = LinearMap.det (ρ' τ) := by
    rw [map_mul ρ', map_mul ρ', map_mul, map_mul, mul_comm (LinearMap.det (ρ' g)), mul_assoc, ← map_mul,
      ← map_mul ρ', mul_inv_cancel, map_one, map_one, mul_one]
  rw [htr, hdet, map_mul gal, map_mul gal]
  have e1 : gal g * gal τ * gal g⁻¹ * (gal g * gal τ * gal g⁻¹) = gal g * (gal τ * gal τ) * gal g⁻¹ := by
    calc gal g * gal τ * gal g⁻¹ * (gal g * gal τ * gal g⁻¹)
        = gal g * gal τ * (gal g⁻¹ * gal g) * gal τ * gal g⁻¹ := by simp only [mul_assoc]
      _ = gal g * (gal τ * gal τ) * gal g⁻¹ := by rw [hinv, mul_one, mul_assoc (gal g) (gal τ) (gal τ)]
  rw [e1]
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hinv']

private theorem c1b_rel_sub_mem {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (I : Ideal R) (h y : Module.End R V) (tr' tr d' d : R)
    (hh : h - 1 ∈ I • (⊤ : Submodule R (Module.End R V))) (htr : tr' - tr ∈ I) (hd : d' - d ∈ I) :
    h * y * (h * y) - tr' • (h * y) + d' • (1 : Module.End R V) - (y * y - tr • y + d • (1 : Module.End R V))
      ∈ I • (⊤ : Submodule R (Module.End R V)) := by
  set J := I • (⊤ : Submodule R (Module.End R V)) with hJ
  have mulL : ∀ (a : Module.End R V) {X : Module.End R V}, X ∈ J → a * X ∈ J := fun a X hX => by
    simpa using c1b_map_mem_smul_top I (LinearMap.mulLeft R a) hX
  have mulR : ∀ (a : Module.End R V) {X : Module.End R V}, X ∈ J → X * a ∈ J := fun a X hX => by
    simpa using c1b_map_mem_smul_top I (LinearMap.mulRight R a) hX
  have smulI : ∀ r : R, r ∈ I → ∀ X : Module.End R V, r • X ∈ J := fun r hr X =>
    Submodule.smul_mem_smul hr Submodule.mem_top
  have hδy : (h - 1) * y ∈ J := mulR y hh
  have hhy : h * y = (h - 1) * y + y := by rw [sub_mul, one_mul, sub_add_cancel]
  rw [hhy]
  have key : ((h - 1) * y + y) * ((h - 1) * y + y) - tr' • ((h - 1) * y + y) + d' • (1 : Module.End R V)
        - (y * y - tr • y + d • (1 : Module.End R V)) =
      ((h - 1) * y * ((h - 1) * y) + (h - 1) * y * y + y * ((h - 1) * y))
        - ((tr' - tr) • ((h - 1) * y + y) + tr • ((h - 1) * y)) + (d' - d) • (1 : Module.End R V) := by
    simp only [add_mul, mul_add, sub_smul, smul_add]
    abel
  rw [key]
  refine J.add_mem (J.sub_mem (J.add_mem (J.add_mem ?_ ?_) ?_) (J.add_mem ?_ ?_)) ?_
  · exact mulL _ hδy
  · exact mulR _ hδy
  · exact mulL _ hδy
  · exact smulI _ htr _
  · exact J.smul_mem tr hδy
  · exact smulI _ hd _

private theorem c1b_natCast_not_mem_maximalIdeal (O' : Type) [CommRing O'] [IsLocalRing O'] (ℓ : ℕ)
    (hℓ : ℓ.Prime) (hchar : ringChar (IsLocalRing.ResidueField O') ≠ ℓ) :
    (ℓ : O') ∉ IsLocalRing.maximalIdeal O' := by
  intro hmem
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, ringChar.spec] at hmem
  rcases (Nat.dvd_prime hℓ).mp hmem with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hchar h1

private theorem c1b_mem_of_forall_sub_mem {O' : Type} [CommRing O'] [IsNoetherianRing O'] [IsLocalRing O']
    {M : Type} [AddCommGroup M] [Module O' M] [Module.Finite O' M] (Z : Submodule O' M) (x : M)
    (h : ∀ n : ℕ, ∃ z ∈ Z, x - z ∈ (IsLocalRing.maximalIdeal O' ^ n) • (⊤ : Submodule O' M)) : x ∈ Z := by
  rw [← Submodule.Quotient.mk_eq_zero, IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal O')]
  intro n
  obtain ⟨z, hz, hxz⟩ := h n
  have hmk : (Submodule.Quotient.mk x : M ⧸ Z) = Z.mkQ (x - z) := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero Z).mpr hz, sub_zero]
  rw [hmk, SModEq.sub_mem, sub_zero]
  have hmap := Submodule.mem_map_of_mem (f := Z.mkQ) hxz
  rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hmap

private theorem c1b_of_not_mem_excluded {q M' : ℕ} [NeZero M'] {S : Finset ℕ} (O' : Type) [CommRing O']
    [IsLocalRing O'] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ℓ ∉ S ∪ ({q} ∪ (M'.primeFactors ∪ {ringChar (IsLocalRing.ResidueField O')}))) :
    ℓ ≠ q ∧ ¬ ℓ ∣ M' ∧ ℓ ∉ (↑S : Set ℕ) ∧ (ℓ : O') ∉ IsLocalRing.maximalIdeal O' := by
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at h
  obtain ⟨hS, hq, hM', hchar⟩ := h
  exact ⟨hq, fun hd => hM' (Nat.mem_primeFactors.mpr ⟨hℓ, hd, NeZero.ne M'⟩), by simpa using hS,
    c1b_natCast_not_mem_maximalIdeal O' ℓ hℓ fun h' => hchar h'.symm⟩

private theorem c1b_core (O' : Type) [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O']
    {V : Type} [AddCommGroup V] [Module O' V] [Module.Free O' V] [Module.Finite O' V]
    {V₂ : Type} [AddCommGroup V₂] [Module O' V₂] [Module.Free O' V₂] [Module.Finite O' V₂]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O' V)
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O' V₂)
    (hgal : ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ v : V, gal σ v - v ∈ (IsLocalRing.maximalIdeal O' ^ n) • (⊤ : Submodule O' V))
    (hρ' : ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ v : V₂, ρ' σ v - v ∈ (IsLocalRing.maximalIdeal O' ^ n) • (⊤ : Submodule O' V₂))
    (K : Type) [Field K] [Algebra O' K] {W : Type} [AddCommGroup W] [Module K W]
    (E : Set (W →ₗ[K] K ⊗[O'] V))
    (hE : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : W →ₗ[K] K ⊗[O'] V),
      f ∈ E → (gal σ).baseChange K ∘ₗ f ∈ E)
    (D : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hdense : ∀ L L' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L → FiniteDimensional ℚ L' →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ τ ∈ D, ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ L, (g * τ * g⁻¹ * σ⁻¹) x = x) ∧ (∀ x ∈ L', (g * τ * g⁻¹ * σ⁻¹) x = x))
    (hrel : ∀ τ ∈ D, ∀ f ∈ E,
      (gal τ * gal τ - LinearMap.trace O' V₂ (ρ' τ) • gal τ
        + LinearMap.det (ρ' τ) • (1 : Module.End O' V)).baseChange K ∘ₗ f = 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ∀ f ∈ E,
      (gal σ * gal σ - LinearMap.trace O' V₂ (ρ' σ) • gal σ
        + LinearMap.det (ρ' σ) • (1 : Module.End O' V)).baseChange K ∘ₗ f = 0 := by
  intro f hf
  let Z : Submodule O' (Module.End O' V) :=
    { carrier := {T | ∀ w : W, T.baseChange K (f w) = 0}
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro w
        rw [LinearMap.baseChange_zero, LinearMap.zero_apply]
      add_mem' := by
        intro S T hS hT
        simp only [Set.mem_setOf_eq] at hS hT ⊢
        intro w
        rw [LinearMap.baseChange_add, LinearMap.add_apply, hS w, hT w, add_zero]
      smul_mem' := by
        intro r T hT
        simp only [Set.mem_setOf_eq] at hT ⊢
        intro w
        rw [LinearMap.baseChange_smul, LinearMap.smul_apply, hT w, smul_zero] }
  have memZ : ∀ T : Module.End O' V, T ∈ Z ↔ ∀ w : W, T.baseChange K (f w) = 0 := fun T => Iff.rfl
  suffices hZ : gal σ * gal σ - LinearMap.trace O' V₂ (ρ' σ) • gal σ
      + LinearMap.det (ρ' σ) • (1 : Module.End O' V) ∈ Z by
    rw [memZ] at hZ
    exact LinearMap.ext fun w => by rw [LinearMap.comp_apply, LinearMap.zero_apply]; exact hZ w
  refine c1b_mem_of_forall_sub_mem Z _ fun n => ?_
  obtain ⟨L, hL, hLgal⟩ := hgal n
  obtain ⟨L', hL', hL'ρ⟩ := hρ' n
  obtain ⟨τ, hτD, g, hfixL, hfixL'⟩ := hdense L L' hL hL' σ
  refine ⟨gal (g * τ * g⁻¹) * gal (g * τ * g⁻¹) - LinearMap.trace O' V₂ (ρ' (g * τ * g⁻¹)) • gal (g * τ * g⁻¹)
      + LinearMap.det (ρ' (g * τ * g⁻¹)) • (1 : Module.End O' V), ?_, ?_⟩
  · rw [memZ]
    intro w
    rw [c1b_rel_conj gal ρ' g τ, LinearMap.baseChange_mul, LinearMap.baseChange_mul, Module.End.mul_apply,
      Module.End.mul_apply]
    have h0 := LinearMap.congr_fun (hrel τ hτD _ (hE g⁻¹ f hf)) w
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h0
    rw [h0, map_zero]
  · set h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := g * τ * g⁻¹ * σ⁻¹ with hh
    have hσ' : g * τ * g⁻¹ = h * σ := by rw [hh, inv_mul_cancel_right]
    rw [hσ', map_mul gal, map_mul ρ', ← Submodule.neg_mem_iff, neg_sub]
    have hδ : gal h - 1 ∈ (IsLocalRing.maximalIdeal O' ^ n) • (⊤ : Submodule O' (Module.End O' V)) :=
      c1b_end_mem_smul_top _ _ fun v => by rw [LinearMap.sub_apply, Module.End.one_apply]; exact hLgal h hfixL v
    obtain ⟨htr, hdet⟩ := c1b_trace_det_sub_mem (IsLocalRing.maximalIdeal O' ^ n) (ρ' h) (ρ' σ) (hL'ρ h hfixL')
    exact c1b_rel_sub_mem _ (gal h) (gal σ) _ _ _ _ hδ htr hdet

private theorem c1b_exists_isFrobeniusAt_conj_apply_eq (L L' : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [FiniteDimensional ℚ L'] (S' : Finset ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S' ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        (∀ x ∈ L, (g * τ * g⁻¹ * σ⁻¹) x = x) ∧ (∀ x ∈ L', (g * τ * g⁻¹ * σ⁻¹) x = x) := by

  haveI : FiniteDimensional ℚ ↥(L ⊔ L') := IntermediateField.finiteDimensional_sup L L'
  let N : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ ↥(L ⊔ L') (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ ↥(L ⊔ L') (AlgebraicClosure ℚ)

  haveI : @IsGalois ℚ _ (AlgebraicClosure ℚ) _ DivisionRing.toRatAlgebra :=
    @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
  haveI hN : Normal ℚ N := normalClosure.normal ℚ ↥(L ⊔ L') (AlgebraicClosure ℚ)
  haveI : CharZero N := charZero_of_injective_algebraMap (algebraMap ℚ N).injective
  haveI : NumberField N := @NumberField.mk _ _ inferInstance inferInstance
  haveI : IsGalois ℚ N := IsGalois.mk
  have hLN : L ≤ N := le_sup_left.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  have hL'N : L' ≤ N := le_sup_right.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  obtain ⟨ℓ, A, τ, g, h1, h2, h3, h4, hmem⟩ :=
    FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker (↥N)
      (H := (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) ↥N).ker) le_rfl S' σ
  have hfix : ∀ x ∈ N, (g * τ * g⁻¹ * σ⁻¹) x = x :=
    (AlgEquiv.restrictNormal_eq_one_iff N (g * τ * g⁻¹ * σ⁻¹)).mp (MonoidHom.mem_ker.mp hmem)
  exact ⟨ℓ, A, τ, g, h1, h2, h3, h4, fun x hx => hfix x (hLN hx), fun x hx => hfix x (hL'N hx)⟩

private theorem c1b_forall_rel_of_forall_isFrobeniusAt
    (q : ℕ) (M' : ℕ) [NeZero M'] (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O']
    {V : Type} [AddCommGroup V] [Module O' V] [Module.Free O' V] [Module.Finite O' V]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O' V)
    (hgal : GaloisActionIsAdicContinuous O' gal)
    (ρ : GaloisRepAdic O')
    (K : Type) [Field K] [Algebra O' K]
    {W : Type} [AddCommGroup W] [Module K W]
    (E : Set (W →ₗ[K] K ⊗[O'] V))
    (hE : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : W →ₗ[K] K ⊗[O'] V),
      f ∈ E → (gal σ).baseChange K ∘ₗ f ∈ E)
    (hrel : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ¬ ℓ ∣ M' → ℓ ∉ (↑S : Set ℕ) →
      (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          ∀ f ∈ E,
            (gal τ * gal τ - LinearMap.trace O' ρ.V (ρ.ρ τ) • gal τ
                + LinearMap.det (ρ.ρ τ) • (1 : Module.End O' V)).baseChange K ∘ₗ f = 0) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ f ∈ E,
      (gal σ * gal σ - LinearMap.trace O' ρ.V (ρ.ρ σ) • gal σ
          + LinearMap.det (ρ.ρ σ) • (1 : Module.End O' V)).baseChange K ∘ₗ f = 0 := by
  intro σ
  refine c1b_core O' gal ρ.ρ hgal ρ.isAdicContinuous K E hE
    {τ | ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)), ℓ.Prime ∧
      ℓ ∉ S ∪ ({q} ∪ (M'.primeFactors ∪ {ringChar (IsLocalRing.ResidueField O')})) ∧
        A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ} ?_ ?_ σ
  · intro L L' hL hL' σ₀
    haveI := hL
    haveI := hL'
    obtain ⟨ℓ, A, τ, g, hℓ, hℓS', hA, hτ, hfixL, hfixL'⟩ := c1b_exists_isFrobeniusAt_conj_apply_eq L L'
      (S ∪ ({q} ∪ (M'.primeFactors ∪ {ringChar (IsLocalRing.ResidueField O')}))) σ₀
    exact ⟨τ, ⟨ℓ, A, hℓ, hℓS', hA, hτ⟩, g, hfixL, hfixL'⟩
  · rintro τ ⟨ℓ, A, hℓ, hℓS', hA, hτ⟩ f hf
    obtain ⟨hq, hM', hS, h𝔪⟩ := c1b_of_not_mem_excluded O' hℓ hℓS'
    exact hrel ℓ hℓ hq hM' hS h𝔪 A hA τ hτ f hf

private theorem c1_blr_dock
    {q : ℕ} [Fact q.Prime] {M' : ℕ}
    {O' : Type} [CommRing O'] [IsLocalRing O']
    (D : FullLevelTate.Datum q M' O')
    (K : Type) [Field K] [CharZero K] [Algebra O' K]
    {H : Subgroup (CuspidalType.GL2 q)} {W : Type} [AddCommGroup W] [Module K W] (χ : Representation K H W)
    (hk : ModularCurve.HeckeAlg →+* K) (hne : D.eigenIsoHom K χ hk ≠ ⊥)
    (ρ : GaloisRepAdic O')
    (hCH : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : D.eigenIsoHom K χ hk),
      (D.gal σ * D.gal σ - LinearMap.trace O' ρ.V (ρ.ρ σ) • D.gal σ
          + LinearMap.det (ρ.ρ σ) • (1 : Module.End O' D.V)).baseChange K ∘ₗ
        ((f : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V) = 0)
    (hirr : ∀ U : Submodule K (K ⊗[O'] ρ.V),
      (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ v ∈ U, (ρ.ρ s).baseChange K v ∈ U) →
        U = ⊥ ∨ U = ⊤)
    (hodd : ∃ c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρ.ρ c * ρ.ρ c = 1 ∧ LinearMap.det (ρ.ρ c) = -1) :
    ∃ φ : K ⊗[O'] ρ.V →ₗ[K] D.eigenIsoHom K χ hk,
      Function.Injective φ ∧
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          φ ∘ₗ (ρ.ρ s).baseChange K = D.eigenIsoHomGal K χ hk s ∘ₗ φ := by
  classical
  letI : AddCommGroup (D.eigenIsoHom K χ hk) := Module.addCommMonoidToAddCommGroup K
  have key : ∀ (X Y Z : W →ₗ[K] K ⊗[O'] D.V) (t d : K),
      X - t • Y + d • Z = 0 → X + (-1 : K) • (t • Y) + d • Z = 0 := by
    intro X Y Z t d h
    rw [← h]
    module
  let b : Module.Basis (Fin 2) K (K ⊗[O'] ρ.V) := (Module.finBasisOfFinrankEq O' ρ.V ρ.finrank_eq).baseChange K
  let ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Matrix (Fin 2) (Fin 2) K :=
    fun σ => LinearMap.toMatrix b b ((ρ.ρ σ).baseChange K)
  have hρM : ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρM (σ * τ) = ρM σ * ρM τ := by
    intro σ τ
    simp only [ρM, map_mul, LinearMap.baseChange_mul, LinearMap.toMatrix_mul]
  have htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρM σ).trace = algebraMap O' K (LinearMap.trace O' ρ.V (ρ.ρ σ)) := by
    intro σ
    simp only [ρM]
    rw [← LinearMap.trace_eq_matrix_trace K b, LinearMap.trace_baseChange]
  have hdet : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρM σ).det = algebraMap O' K (LinearMap.det (ρ.ρ σ)) := by
    intro σ
    simp only [ρM]
    rw [LinearMap.det_toMatrix, LinearMap.det_baseChange]
  have hmul : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : K ⊗[O'] ρ.V),
      b.equivFun ((ρ.ρ σ).baseChange K x) = (ρM σ).mulVec (b.equivFun x) := by
    intro σ x
    simp only [ρM, Module.Basis.equivFun_apply]
    rw [LinearMap.toMatrix_mulVec_repr]
  have hCH' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      D.eigenIsoHomGal K χ hk σ * D.eigenIsoHomGal K χ hk σ - (ρM σ).trace • D.eigenIsoHomGal K χ hk σ
        + (ρM σ).det • (1 : Module.End K (D.eigenIsoHom K χ hk)) = 0 := by
    intro σ
    rw [htr, hdet, sub_eq_add_neg, ← neg_one_smul K]
    refine LinearMap.ext fun f => Subtype.ext (Subtype.ext ?_)
    have h := hCH σ f
    simp only [LinearMap.baseChange_add, LinearMap.baseChange_sub, LinearMap.baseChange_mul,
      LinearMap.baseChange_smul, LinearMap.baseChange_one, LinearMap.add_comp, LinearMap.sub_comp,
      LinearMap.smul_comp] at h
    simp only [Module.End.mul_eq_comp, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_assoc] at h
    rw [← algebraMap_smul K (LinearMap.trace O' ρ.V (ρ.ρ σ)), ← algebraMap_smul K (LinearMap.det (ρ.ρ σ))] at h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply,
      LinearMap.zero_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero,
      FullLevelTate.Datum.coe_eigenIsoHomGal_apply, FullLevelTate.Datum.coe_isoHomGal_apply]
    exact key _ _ _ _ _ h
  have hirrM : ∀ U : Submodule K (Fin 2 → K),
      (∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ v ∈ U, (ρM g).mulVec v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hsurj : Function.Surjective (b.equivFun : K ⊗[O'] ρ.V →ₗ[K] (Fin 2 → K)) := b.equivFun.surjective
    have hstable : ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ∀ v ∈ U.comap (b.equivFun : K ⊗[O'] ρ.V →ₗ[K] (Fin 2 → K)),
          (ρ.ρ s).baseChange K v ∈ U.comap (b.equivFun : K ⊗[O'] ρ.V →ₗ[K] (Fin 2 → K)) := by
      intro s v hv
      rw [Submodule.mem_comap] at hv ⊢
      simp only [LinearEquiv.coe_coe] at hv ⊢
      rw [hmul]
      exact hU s _ hv
    rcases hirr _ hstable with h | h
    · left
      rw [← Submodule.map_comap_eq_of_surjective hsurj U, h, Submodule.map_bot]
    · right
      rw [← Submodule.map_comap_eq_of_surjective hsurj U, h, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  obtain ⟨c, hc1, hc2⟩ := hodd
  have hcM2 : ρM c * ρM c = 1 := by
    rw [← hρM]
    simp only [ρM]
    rw [map_mul, hc1, LinearMap.baseChange_one, LinearMap.toMatrix_one]
  have hcMdet : (ρM c).det = -1 := by
    rw [hdet, hc2, map_neg, map_one]
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hV : ∃ v : D.eigenIsoHom K χ hk, v ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  obtain ⟨φ₀, hφ₀inj, hφ₀⟩ :=
    BostonLenstraRibet.exists_embedding_of_irreducible_of_odd
      (ρV := D.eigenIsoHomGal K χ hk) hρM hCH' hirrM hcM2 hcMdet h2 hV
  refine ⟨φ₀ ∘ₗ (b.equivFun : K ⊗[O'] ρ.V →ₗ[K] (Fin 2 → K)), hφ₀inj.comp b.equivFun.injective, fun s => ?_⟩
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hmul, hφ₀]

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (O' : Type) [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O']
    (D : FullLevelTate.Datum q M' O')
    (K : Type) [Field K] [CharZero K] [Algebra O' K] (hOK : Function.Injective (algebraMap O' K))
    {H : Subgroup (CuspidalType.GL2 q)} {W : Type} [AddCommGroup W] [Module K W] (χ : Representation K H W)
    (hcentral : ∀ c : (ZMod q)ˣ, ∃ h : H, (h : CuspidalType.GL2 q) = CuspidalType.scalarElem q c ∧ χ h = 1)
    (hk : ModularCurve.HeckeAlg →+* K) (hne : D.eigenIsoHom K χ hk ≠ ⊥)
    (S : Finset ℕ) (ρ : GaloisRepAdic O')
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ¬ ℓ ∣ M' → ℓ ∉ (↑S : Set ℕ) →
      (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt s ℓ →
          (LinearMap.charpoly (ρ.ρ s)).map (algebraMap O' K) =
            X ^ 2 - C (hk (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)) * X + C ((ℓ : K)))
    (hirr : ∀ U : Submodule K (K ⊗[O'] ρ.V),
      (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ v ∈ U, (ρ.ρ s).baseChange K v ∈ U) →
        U = ⊥ ∨ U = ⊤)
    (hodd : ∃ c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρ.ρ c * ρ.ρ c = 1 ∧ LinearMap.det (ρ.ρ c) = -1) :
    ∃ φ : K ⊗[O'] ρ.V →ₗ[K] D.eigenIsoHom K χ hk,
      Function.Injective φ ∧
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          φ ∘ₗ (ρ.ρ s).baseChange K = D.eigenIsoHomGal K χ hk s ∘ₗ φ := by
  have hrel := FLTateC1a.rel_frobenius_c1a D K χ hcentral hk S ρ hρ
  have hall := c1b_forall_rel_of_forall_isFrobeniusAt q M' S O' D.gal D.gal_isAdicContinuous ρ K
    {f : W →ₗ[K] K ⊗[O'] D.V | ∃ e : D.eigenIsoHom K χ hk, ((e : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V) = f}
    (fun σ f hf => by
      obtain ⟨e, he⟩ := hf
      exact ⟨D.eigenIsoHomGal K χ hk σ e, by rw [← he]; rfl⟩)
    hrel
  exact c1_blr_dock D K χ hk hne ρ (fun σ f => hall σ _ ⟨f, rfl⟩) hirr hodd

end S_FullLevelTate_Datum_exists_injective_equivariant_of_eigenIsoHom_ne_bot
end P2MW
export P2MW.S_FullLevelTate_Datum_exists_injective_equivariant_of_eigenIsoHom_ne_bot (solution)
