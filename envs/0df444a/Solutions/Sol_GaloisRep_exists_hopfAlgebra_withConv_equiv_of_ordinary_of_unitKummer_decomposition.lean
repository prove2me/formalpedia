-- Prove2me | solution 1 for GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6d6abe12-82b1-583c-afef-5426b9d8db8a

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer
import Theorems.Thm_HopfAlgebra_exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_ratLocalizedAt_of_padicInt_of_withConv_equiv
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false

open scoped Pointwise

local instance c7m_isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance c7m_isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance c7m_isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

noncomputable section

namespace C7ModAux

section inertia_generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_inertiaSubgroup_iff' (A : ValuationSubring L) (g : A.decompositionSubgroup K) :
    g ∈ A.inertiaSubgroup K ↔ ∀ a : A, ((g : L ≃ₐ[K] L) (a : L) - (a : L)) ∈ A.nonunits := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  constructor
  · intro h a
    have h1 : (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) g)
        (IsLocalRing.residue A a) = IsLocalRing.residue A a := by rw [h]; rfl
    have h2 : IsLocalRing.residue A (g • a) = IsLocalRing.residue A a := h1
    have h3 : g • a - a ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.mp h2
    exact (ValuationSubring.coe_mem_nonunits_iff (a := g • a - a)).mpr h3
  · intro h
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) x
    change IsLocalRing.residue A (g • a) = IsLocalRing.residue A a
    exact Ideal.Quotient.eq.mpr ((ValuationSubring.coe_mem_nonunits_iff (a := g • a - a)).mp (h a))

theorem mem_inertiaSubgroupIn_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.inertiaSubgroupIn K ↔
      σ ∈ A.decompositionSubgroup K ∧ ∀ a : A, (σ (a : L) - (a : L)) ∈ A.nonunits := by
  rw [ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, (mem_inertiaSubgroup_iff' A g).mp hg⟩
  · rintro ⟨hD, h⟩
    exact ⟨⟨σ, hD⟩, (mem_inertiaSubgroup_iff' A ⟨σ, hD⟩).mpr h, rfl⟩

theorem mem_nonunits_comap_iff {L' : Type*} [Field L'] (B : ValuationSubring L') (ι : L →+* L') (x : L) :
    x ∈ (B.comap ι).nonunits ↔ ι x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]

theorem mem_inertiaSubgroupIn_comap {K' L' : Type*} [Field K'] [Field L'] [Algebra K' L']
    (B : ValuationSubring L') (ι : L →+* L')
    (σ : L ≃ₐ[K] L) (τ : L' ≃ₐ[K'] L') (hcomm : ∀ x : L, ι (σ x) = τ (ι x))
    (hτ : τ ∈ B.inertiaSubgroupIn K') : σ ∈ (B.comap ι).inertiaSubgroupIn K := by
  obtain ⟨hτD, hτI⟩ := (mem_inertiaSubgroupIn_iff B τ).mp hτ
  have hcomm' : ∀ x : L, ι (σ.symm x) = τ.symm (ι x) := by
    intro x
    apply τ.injective
    rw [← hcomm, σ.apply_symm_apply, τ.apply_symm_apply]
  have hB : ∀ y : L', y ∈ B ↔ τ.symm y ∈ B := by
    intro y
    have h1 : τ • B = B := hτD
    conv_lhs => rw [← h1]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine (mem_inertiaSubgroupIn_iff (B.comap ι) σ).mpr ⟨?_, ?_⟩
  · show σ • B.comap ι = B.comap ι
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    change ι (σ.symm x) ∈ B ↔ ι x ∈ B
    rw [hcomm', ← hB]
  · intro a
    rw [mem_nonunits_comap_iff, map_sub, hcomm]
    exact hτI ⟨ι a, (ValuationSubring.mem_comap).mp a.2⟩

theorem mem_nonunits_smul_iff (g : L ≃ₐ[K] L) (A : ValuationSubring L) (x : L) :
    x ∈ (g • A).nonunits ↔ g.symm x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, map_eq_zero]
  change x = 0 ∨ g⁻¹ • x⁻¹ ∉ A ↔ x = 0 ∨ (g.symm x)⁻¹ ∉ A
  rw [AlgEquiv.smul_def, map_inv₀]
  rfl

theorem mem_inertiaSubgroupIn_smul_iff (g σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    σ ∈ (g • A).inertiaSubgroupIn K ↔ g⁻¹ * σ * g ∈ A.inertiaSubgroupIn K := by
  rw [mem_inertiaSubgroupIn_iff, mem_inertiaSubgroupIn_iff]
  have hD : σ ∈ (g • A).decompositionSubgroup K ↔ g⁻¹ * σ * g ∈ A.decompositionSubgroup K := by
    rw [ValuationSubring.decompositionSubgroup, ValuationSubring.decompositionSubgroup,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ht
    · intro h
      exact ⟨g⁻¹ * σ * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  refine and_congr hD ⟨fun h b => ?_, fun h a => ?_⟩
  · have hb : g (b : L) ∈ g • A := ValuationSubring.smul_mem_pointwise_smul g (b : L) A b.2
    have h1 := h ⟨g (b : L), hb⟩
    rw [mem_nonunits_smul_iff] at h1
    simpa [AlgEquiv.mul_apply, AlgEquiv.aut_inv] using h1
  · have ha : g.symm (a : L) ∈ A := by
      have := a.2
      rwa [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at this
    have h1 := h ⟨g.symm (a : L), ha⟩
    rw [mem_nonunits_smul_iff, map_sub]
    simpa [AlgEquiv.mul_apply, AlgEquiv.aut_inv] using h1

theorem mem_decompositionSubgroup_smul_iff (g σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    σ ∈ (g • A).decompositionSubgroup K ↔ g⁻¹ * σ * g ∈ A.decompositionSubgroup K := by
  rw [ValuationSubring.decompositionSubgroup, ValuationSubring.decompositionSubgroup,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ht
  · intro h
    exact ⟨g⁻¹ * σ * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem valuation_eq_one_iff (A : ValuationSubring L) (x : L) :
    A.valuation x = 1 ↔ x ∈ A ∧ x ∉ A.nonunits := by
  rw [← ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_nonunits_iff, not_lt]
  constructor
  · intro h; exact ⟨h.le, h.ge⟩
  · rintro ⟨h1, h2⟩; exact le_antisymm h1 h2

end inertia_generic

section bridge_facts

variable (p : ℕ) [Fact p.Prime]

theorem localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace
    (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hτ : τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]) :
    localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ :=
  mem_inertiaSubgroupIn_comap (padicIntegers p) (padicEmbedding p).toRingHom (localGaloisToGlobal p τ) τ
    (fun x => padicEmbedding_localGaloisToGlobal p τ x) hτ

theorem padicPlace_liesOverPrime : (padicPlace p).LiesOverPrime p := by
  show ((p : ℕ) : AlgebraicClosure ℚ) ∈ (padicPlace p).nonunits
  rw [padicPlace, mem_nonunits_comap_iff, map_natCast, ValuationSubring.mem_nonunits_iff_or]
  right
  change ¬ ((p : PadicAlgCl p)⁻¹ ∈ (Valued.v : Valuation (PadicAlgCl p) NNReal).valuationSubring)
  rw [Valuation.mem_valuationSubring_iff, not_le, map_inv₀, PadicAlgCl.valuation_p p, one_div, inv_inv]
  exact_mod_cast (Fact.out (p := p.Prime)).one_lt

end bridge_facts

section local_

variable (E : Type) [AddCommGroup E]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) E]
  (p : ℕ) [Fact p.Prime] (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def Loc (E : Type) (_p : ℕ) (_g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : Type := E

scoped instance instAddCommGroupLoc : AddCommGroup (Loc E p g) := inferInstanceAs (AddCommGroup E)

scoped instance instFiniteLoc [Finite E] : Finite (Loc E p g) := inferInstanceAs (Finite E)

def twist : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (MulAut.conj g).toMonoidHom.comp (localGaloisToGlobal p)

theorem twist_apply (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) :
    twist p g σ = g * localGaloisToGlobal p σ * g⁻¹ := rfl

scoped instance instDistribMulActionLoc :
    DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (Loc E p g) :=
  DistribMulAction.compHom E (twist p g)

def toLoc : E ≃+ Loc E p g := AddEquiv.refl E

theorem smul_toLoc (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (x : E) :
    σ • toLoc E p g x = toLoc E p g ((g * localGaloisToGlobal p σ * g⁻¹) • x) := rfl

end local_

end C7ModAux
p2m_reactivate "P2MW.S_GaloisRep_exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition.C7ModAux"

end
p2m_reactivate "P2MW.S_GaloisRep_exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition.C7ModAux"

open C7ModAux in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ)
    (E : Type) [AddCommGroup E] [Finite E]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) E]
    (hE : ∀ x : E, (p ^ N) • x = 0)
    (hlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, ∀ x : E, s • x = x)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (E₁ : AddSubgroup E)
    (hE₁D : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ y ∈ E₁, σ • y ∈ E₁)
    (hE₁I : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ ^ c) → ∀ y ∈ E₁, τ • y = c • y)
    (hEI : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ y : E, τ • y - y ∈ E₁)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i)
    (φ : Fin t → (E →+ E)) (hφ₁ : ∀ i x, φ i x ∈ E₁) (hφ₀ : ∀ i, ∀ y ∈ E₁, φ i y = 0)
    (hdec : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → ∀ x : E, τ • x - x = ∑ i, (k i) • φ i x) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ E,
        (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) ∧
        ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by
  classical
  have hp : p.Prime := Fact.out
  haveI hpN0 : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩

  obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hp (padicPlace p) P
    (C7ModAux.padicPlace_liesOverPrime p) hP

  obtain ⟨F, hFfd, hFlev⟩ := hlev
  haveI := hFfd
  have hN : ∀ x : E, IsOpen (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := fun x =>
    Subgroup.isOpen_mono (fun s hs => by rw [MulAction.mem_stabilizer_iff]; exact hFlev s hs x)
      (IntermediateField.fixingSubgroup_isOpen F)
  obtain ⟨A, _, _, hAfin, hAco, eA, heA_add, heA_act⟩ :=
    HopfAlgebra.exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer ℚ (AlgebraicClosure ℚ) E hN
  obtain ⟨eAp, heAp_add, heAp_act⟩ :=
    HopfAlgebra.exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure p A hAfin eA heA_add heA_act

  let M : Type := Loc E p g
  let tL : E ≃+ M := toLoc E p g
  have hsmul : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (x : E),
      σ • tL x = tL ((g * localGaloisToGlobal p σ * g⁻¹) • x) := fun _ _ => rfl

  have hcD : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      g * localGaloisToGlobal p σ * g⁻¹ ∈ P.decompositionSubgroup ℚ := by
    intro σ
    rw [← hg, mem_decompositionSubgroup_smul_iff]
    have : g⁻¹ * (g * localGaloisToGlobal p σ * g⁻¹) * g = localGaloisToGlobal p σ := by group
    rw [this]
    exact localGaloisToGlobal_mem_decompositionSubgroup p σ
  have hcI : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p],
      g * localGaloisToGlobal p τ * g⁻¹ ∈ P.inertiaSubgroupIn ℚ := by
    intro τ hτ
    rw [← hg, mem_inertiaSubgroupIn_smul_iff]
    have : g⁻¹ * (g * localGaloisToGlobal p τ * g⁻¹) * g = localGaloisToGlobal p τ := by group
    rw [this]
    exact localGaloisToGlobal_mem_inertiaSubgroupIn_padicPlace p τ hτ
  have hconj_apply : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (x : AlgebraicClosure ℚ),
      (g * localGaloisToGlobal p σ * g⁻¹) x = g (localGaloisToGlobal p σ (g.symm x)) := by
    intro σ x
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv]

  have hex : ∀ τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      ∃ a : ℕ, localGaloisToGlobal p τ ζ = ζ ^ a := by
    intro τ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one
      (show (localGaloisToGlobal p τ ζ) ^ p ^ N = 1 by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  let n : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → ℕ := fun τ => Classical.choose (hex τ)
  have hnζ : ∀ τ, localGaloisToGlobal p τ ζ = ζ ^ n τ := fun τ => Classical.choose_spec (hex τ)

  have hgζ : IsPrimitiveRoot (g ζ) (p ^ N) := hζ.map_of_injective g.injective
  have hιζ : IsPrimitiveRoot (padicEmbedding p ζ) (p ^ N) :=
    hζ.map_of_injective (padicEmbedding p).toRingHom.injective
  have hexpQbar : ∀ (τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (ξ : AlgebraicClosure ℚ),
      ξ ^ p ^ N = 1 → (g * localGaloisToGlobal p τ * g⁻¹) ξ = ξ ^ n τ := by
    intro τ ξ hξ
    obtain ⟨j, -, rfl⟩ := hgζ.eq_pow_of_pow_eq_one hξ
    rw [hconj_apply, map_pow, g.symm_apply_apply, map_pow, hnζ, map_pow, map_pow, ← pow_mul, ← pow_mul,
      mul_comm]
  have hn : ∀ (τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (ξ : AlgebraicClosure ℚ_[p]),
      ξ ^ p ^ N = 1 → τ ξ = ξ ^ n τ := by
    intro τ ξ hξ
    obtain ⟨j, -, rfl⟩ := hιζ.eq_pow_of_pow_eq_one hξ
    rw [map_pow, ← padicEmbedding_localGaloisToGlobal, hnζ, map_pow, ← pow_mul, ← pow_mul, mul_comm]

  have hfixμ : ∀ τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      (∀ ξ : AlgebraicClosure ℚ_[p], ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → (g * localGaloisToGlobal p τ * g⁻¹) ξ = ξ := by
    intro τ hτ ξ hξ
    rw [hconj_apply]
    have h1 : (g.symm ξ) ^ p ^ N = 1 := by rw [← map_pow, hξ, map_one]
    have h2 : padicEmbedding p (localGaloisToGlobal p τ (g.symm ξ)) = padicEmbedding p (g.symm ξ) := by
      rw [padicEmbedding_localGaloisToGlobal]
      exact hτ _ (by rw [← map_pow, h1, map_one])
    rw [(padicEmbedding p).toRingHom.injective h2, g.apply_symm_apply]

  have hM : ∀ x : M, IsOpen (MulAction.stabilizer (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) x :
      Set (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) := by
    intro x

    let F' : IntermediateField ℚ (AlgebraicClosure ℚ) := F.map (g.symm : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
    haveI : FiniteDimensional ℚ F' := inferInstance
    have hP' : ∀ U V : Subgroup (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]), V ≤ U →
        U ≤ MulAction.stabilizer (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) x →
        V ≤ MulAction.stabilizer (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) x :=
      fun U V hVU hU => hVU.trans hU
    have hsub : F'.fixingSubgroup.comap (localGaloisToGlobal p) ≤
        MulAction.stabilizer (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) x := by
      intro τ hτ
      rw [Subgroup.mem_comap] at hτ
      rw [MulAction.mem_stabilizer_iff]
      have hmem : g * localGaloisToGlobal p τ * g⁻¹ ∈ F.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        rw [hconj_apply]
        have hy' : g.symm y ∈ F' := (IntermediateField.mem_map F).mpr ⟨y, hy, rfl⟩
        rw [(IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ _ hy', g.apply_symm_apply]
      show tL ((g * localGaloisToGlobal p τ * g⁻¹) • (tL.symm x)) = x
      rw [hFlev _ hmem]
      rfl
    obtain ⟨K, hK, hKle⟩ := (exists_finiteDimensional_comap_localGaloisToGlobal_iff p
      (fun U => U ≤ MulAction.stabilizer (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) x) hP').mp
      ⟨F', inferInstance, hsub⟩
    haveI := hK
    exact Subgroup.isOpen_mono hKle (IntermediateField.fixingSubgroup_isOpen K)
  have hpM : ∀ x : M, (p ^ N) • x = 0 := fun x => hE (tL.symm x)
  let M₁ : AddSubgroup M := E₁.map tL.toAddMonoidHom
  have hM₁mem : ∀ x : E, tL x ∈ M₁ ↔ x ∈ E₁ := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := tL.injective hyx
      rwa [← this]
    · exact fun hx => ⟨x, hx, rfl⟩
  have hM₁ : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]), ∀ y ∈ M₁, σ • y ∈ M₁ := by
    intro σ y hy
    obtain ⟨x, hx, rfl⟩ := hy
    show σ • tL x ∈ M₁
    rw [hsmul, hM₁mem]
    exact hE₁D _ (hcD σ) x hx
  have hmult : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ y ∈ M₁, τ • y = n τ • y := by
    intro τ hτ y hy
    obtain ⟨x, hx, rfl⟩ := hy
    show τ • tL x = n τ • tL x
    rw [hsmul, hE₁I _ (hcI τ hτ) (n τ) (hexpQbar τ) x hx, map_nsmul]
  have hquot : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ x : M, τ • x - x ∈ M₁ := by
    intro τ hτ x
    have : τ • x - x = tL ((g * localGaloisToGlobal p τ * g⁻¹) • tL.symm x - tL.symm x) := by
      rw [map_sub]; rfl
    rw [this, hM₁mem]
    exact hEI _ (hcI τ hτ) _

  let ζ' : AlgebraicClosure ℚ_[p] := padicEmbedding p (g.symm ζ)
  let u' : Fin t → AlgebraicClosure ℚ_[p] := fun i => padicEmbedding p (g.symm (u i))
  let β' : Fin t → AlgebraicClosure ℚ_[p] := fun i => padicEmbedding p (g.symm (β i))
  have hζ' : IsPrimitiveRoot ζ' (p ^ N) :=
    (hζ.map_of_injective g.symm.injective).map_of_injective (padicEmbedding p).toRingHom.injective
  have hβ' : ∀ i, β' i ^ p ^ N = u' i := by
    intro i
    show padicEmbedding p (g.symm (β i)) ^ p ^ N = padicEmbedding p (g.symm (u i))
    rw [← map_pow, ← map_pow, hβ]
  have hu' : ∀ i, (padicIntegers p).valuation (u' i) = 1 := by
    intro i
    have h := hu i
    rw [← hg, valuation_eq_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      mem_nonunits_smul_iff] at h
    rw [valuation_eq_one_iff]
    have h1 : g.symm (u i) ∈ padicPlace p := h.1
    have h2 : g.symm (u i) ∉ (padicPlace p).nonunits := h.2
    rw [padicPlace, ValuationSubring.mem_comap] at h1
    rw [padicPlace, mem_nonunits_comap_iff] at h2
    exact ⟨h1, h2⟩
  have hlocfix : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ x : AlgebraicClosure ℚ,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x) →
      τ (padicEmbedding p (g.symm x)) = padicEmbedding p (g.symm x) := by
    intro τ hτ x hx
    rw [← padicEmbedding_localGaloisToGlobal]
    congr 1
    apply g.injective
    have := hx _ (hcI τ hτ)
    rw [hconj_apply] at this
    rw [this, g.apply_symm_apply]
  have huI' : ∀ i, ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], τ (u' i) = u' i :=
    fun i τ hτ => hlocfix τ hτ (u i) (huI i)
  let φ' : Fin t → (M →+ M) := fun i => tL.toAddMonoidHom.comp ((φ i).comp tL.symm.toAddMonoidHom)
  have hφ'_apply : ∀ i (x : E), φ' i (tL x) = tL (φ i x) := fun _ _ => rfl
  have hφ'₁ : ∀ i (x : M), φ' i x ∈ M₁ := by
    intro i x
    show tL (φ i (tL.symm x)) ∈ M₁
    rw [hM₁mem]
    exact hφ₁ i _
  have hφ'₀ : ∀ i, ∀ y ∈ M₁, φ' i y = 0 := by
    intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    show tL (φ i (tL.symm (tL x))) = 0
    rw [tL.symm_apply_apply, hφ₀ i x hx, map_zero]
  have hdec' : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p],
      (∀ ξ : AlgebraicClosure ℚ_[p], ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β' i) = ζ' ^ (k i) * β' i) → ∀ x : M, τ • x - x = ∑ i, (k i) • φ' i x := by
    intro τ hτ hτμ k hk x
    have hk' : ∀ i, (g * localGaloisToGlobal p τ * g⁻¹) (β i) = ζ ^ (k i) * β i := by
      intro i
      rw [hconj_apply]
      have h1 : padicEmbedding p (localGaloisToGlobal p τ (g.symm (β i))) =
          padicEmbedding p (g.symm (ζ ^ (k i) * β i)) := by
        rw [padicEmbedding_localGaloisToGlobal, map_mul, map_pow, map_mul, map_pow]
        exact hk i
      rw [(padicEmbedding p).toRingHom.injective h1, g.apply_symm_apply]
    have h := hdec _ (hcI τ hτ) (hfixμ τ hτμ) k hk' (tL.symm x)
    have hx : τ • x - x = tL ((g * localGaloisToGlobal p τ * g⁻¹) • tL.symm x - tL.symm x) := by
      rw [map_sub]; rfl
    rw [hx, h, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul]
    rfl

  obtain ⟨Hp, _, _, hfin, hflat, hco, eHp, heHp_add, heHp_act⟩ :=
    HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer
      p hp2 N M hM hpM M₁ hM₁ n hn hmult hquot ζ' hζ' u' β' hu' huI' hβ' φ' hφ'₁ hφ'₀ hdec'

  let eAp' : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃ M :=
    eAp.trans ((DistribMulAction.toAddEquiv E g).toEquiv.trans tL.toEquiv)
  have heAp'_apply : ∀ f, eAp' f = tL (g • eAp f) := fun _ => rfl
  have heAp'_add : ∀ f f', eAp' (f * f') = eAp' f + eAp' f' := by
    intro f f'
    rw [heAp'_apply, heAp'_apply, heAp'_apply, heAp_add, smul_add, map_add]
  have heAp'_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f f' : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
      (∀ a : A, f' a = σ (f a)) → eAp' f' = σ • eAp' f := by
    intro σ f f' hff'
    rw [heAp'_apply, heAp'_apply, heAp_act σ f f' hff', hsmul, smul_smul, smul_smul,
      inv_mul_cancel_right]

  exact HopfAlgebra.exists_finiteFlat_ratLocalizedAt_of_padicInt_of_withConv_equiv p A hAfin hAco Hp hfin
    hflat hco eHp heHp_add heHp_act eAp' heAp'_add heAp'_act eA heA_add heA_act

end S_GaloisRep_exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition
end P2MW
export P2MW.S_GaloisRep_exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition (solution)
