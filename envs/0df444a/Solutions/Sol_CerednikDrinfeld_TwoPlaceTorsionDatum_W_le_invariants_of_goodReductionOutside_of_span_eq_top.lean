-- Prove2me | solution 1 for CerednikDrinfeld.TwoPlaceTorsionDatum.W_le_invariants_of_goodReductionOutside_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/25cc95e4-ed80-5fb8-adb8-a4f387200cd4

import Mathlib
import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Theorems.Thm_ModularCurve_exists_blrDecomposition_heckeTorsion_of_span_eq_top_of_frobeniusQuadratic_of_dense
import Theorems.Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_W_le_invariants_of_goodReductionOutside_of_span_eq_top
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "ModularCurve CerednikDrinfeld P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_W_le_invariants_of_goodReductionOutside_of_span_eq_top.CerednikDrinfeld"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "TwoPlaceTorsionDatum JPrimeTorsionDatum JPrimeTorsionDatum.invariants DegeneracyData HeckeData"
namespace TwoPlaceTorsionDatum
p2m_export "CerednikDrinfeld.TwoPlaceTorsionDatum" "fst snd mk T hecke finiteLevel comm gal"
namespace BLR
p2m_open "CerednikDrinfeld.TwoPlaceTorsionDatum CerednikDrinfeld"

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

local instance isAlgebraicQbar_blr : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_blr : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance normalQbar_blr : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable {p : ℕ} {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
  [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
  {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
  {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}

abbrev heckeModule (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : Module HeckeAlg 𝒥.T :=
  Module.compHom 𝒥.T 𝒥.hecke

abbrev galAction (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : DistribMulAction Γ 𝒥.T :=
  DistribMulAction.compHom 𝒥.T 𝒥.gal

theorem smulComm (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) :
    letI := heckeModule 𝒥; letI := galAction 𝒥
    SMulCommClass Γ HeckeAlg 𝒥.T := by
  letI := heckeModule 𝒥; letI := galAction 𝒥
  exact ⟨fun σ x t => 𝒥.comm σ x t⟩

theorem two_ne_zero_of_mem (hp' : p.Prime) (hp2 : p ≠ 2) (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal]
    (hp : (p : HeckeAlg) ∈ 𝔪) : (2 : HeckeAlg ⧸ 𝔪) ≠ 0 := by
  intro h2
  have hp0 : ((p : ℕ) : HeckeAlg ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  have h20 : ((2 : ℕ) : HeckeAlg ⧸ 𝔪) = 0 := by exact_mod_cast h2
  set r := ringChar (HeckeAlg ⧸ 𝔪)
  have hrp : r ∣ p := (ringChar.spec _ _).mp hp0
  have hr2 : r ∣ 2 := (ringChar.spec _ _).mp h20
  have hr1 : r ≠ 1 := CharP.ringChar_ne_one
  have hr : r = p := ((Nat.dvd_prime hp').mp hrp).resolve_left hr1
  rw [hr] at hr2
  exact hp2 (((Nat.dvd_prime Nat.prime_two).mp hr2).resolve_left hp'.one_lt.ne')

theorem frobeniusPowerDense_ker_inf_fixing (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    {R : Type} [MulOneClass R] (ρ' : Γ →* R) (hfin : GaloisFactorsThroughFiniteLevel ρ')
    (X : Set 𝒥.T) (S : Finset ℕ) :
    letI := galAction 𝒥
    FrobeniusPowerDense S (ρ'.ker ⊓ fixingSubgroup Γ X) := by
  letI := galAction 𝒥
  classical
  obtain ⟨L, hLfin, hL⟩ := hfin
  obtain ⟨L', hL'fin, hL'⟩ := 𝒥.finiteLevel
  haveI : FiniteDimensional ℚ L := hLfin
  haveI : FiniteDimensional ℚ L' := hL'fin
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ E).injective
  haveI : FiniteDimensional ℚ E :=
    normalClosure.is_finiteDimensional ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : Normal ℚ E := normalClosure.normal ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : NumberField E := NumberField.mk
  haveI : IsGalois ℚ E := IsGalois.mk
  have hLE : L ≤ E := le_sup_left.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  have hL'E : L' ≤ E := le_sup_right.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  have hE : ∀ σ : Γ,
      σ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) E).ker →
        ∀ x : AlgebraicClosure ℚ, x ∈ E → σ x = x := by
    intro σ hσ x hx
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) E σ = 1 :=
      MonoidHom.mem_ker.mp hσ
    have h := AlgEquiv.restrictNormalHom_apply E σ ⟨x, hx⟩
    exact h.symm.trans (congrArg (fun y : E => (y : AlgebraicClosure ℚ)) (DFunLike.congr_fun h1 ⟨x, hx⟩))
  refine FrobeniusDensity.frobeniusPowerDense_of_le_ker E (fun σ hσ => Subgroup.mem_inf.mpr ⟨?_, ?_⟩) S
  · exact MonoidHom.mem_ker.mpr (hL σ (fun x hx => hE σ hσ x (hLE hx)))
  · have hσ1 : 𝒥.gal σ = 1 := hL' σ (fun x hx => hE σ hσ x (hL'E hx))
    rw [mem_fixingSubgroup_iff]
    intro y _
    show (𝒥.gal σ) y = y
    rw [hσ1]
    rfl

theorem main (hp2 : p ≠ 2) [Fact p.Prime]
    (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    {M : ℕ} (hgood : 𝒥.fst.GoodReductionOutside M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : (p : HeckeAlg) ∈ 𝔪)
    (F : Type) [Field F] (ι : F →+* HeckeAlg ⧸ 𝔪)
    (ρ : Γ →* Matrix (Fin 2) (Fin 2) F)
    (hatt : ∃ S : Finset ℕ, (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ → ∀ (σ : Γ), A.IsFrobeniusAt σ ℓ →
          Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = ((ρ σ).map ι).trace ∧
            Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = ((ρ σ).map ι).det)
    (hspan : Submodule.span (HeckeAlg ⧸ 𝔪) (Set.range fun σ : Γ => (ρ σ).map ι) = ⊤)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hunr : ∀ σ ∈ A₂.inertiaSubgroupIn ℚ, ρ σ = 1) :
    𝒥.snd.W 𝔪 ≤ 𝒥.snd.invariants := by
  classical
  letI := heckeModule 𝒥; letI := galAction 𝒥; haveI := smulComm 𝒥

  let ρ' : Γ →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪) := (RingHom.mapMatrix ι).toMonoidHom.comp ρ
  have hρ' : ∀ σ, ρ' σ = (ρ σ).map ι := fun σ => rfl

  have h2 : (2 : HeckeAlg ⧸ 𝔪) ≠ 0 := two_ne_zero_of_mem Fact.out hp2 𝔪 hp

  have hspan' : Submodule.span (HeckeAlg ⧸ 𝔪) (Set.range fun σ : Γ => ρ' σ) = ⊤ := hspan

  have hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) M p 𝒥.T := by
    intro ℓ hℓ hℓM A hA σ hσ x _
    have hℓM' : ¬ ℓ ∣ M := fun h => hℓM (dvd_mul_of_dvd_left h p)
    exact hgood.eichlerShimura ℓ hℓ hℓM' A hA σ hσ x

  obtain ⟨S, hSM, hatt⟩ := hatt
  have hS' : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ insert p S → ¬ ℓ ∣ M * p := by
    intro ℓ hℓ hℓS hdvd
    rw [Finset.mem_insert, not_or] at hℓS
    rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h | h
    · exact hSM ℓ hℓ hℓS.2 h
    · exact hℓS.1 ((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp h)
  have hatt' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ insert p S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : Γ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ' σ).trace ∧
          Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ' σ).det := by
    intro ℓ hℓ hℓS A hA σ hσ
    rw [Finset.mem_insert, not_or] at hℓS
    exact hatt ℓ hℓ hℓS.2 A hA σ hσ

  have hfin' : GaloisFactorsThroughFiniteLevel ρ' := by
    obtain ⟨L, hL, h⟩ := hfin
    exact ⟨L, hL, fun σ hσ => by
      show (RingHom.mapMatrix ι) (ρ σ) = 1
      rw [h σ hσ, map_one]⟩
  have hdense : FrobeniusPowerDense (insert p S)
      (ρ'.ker ⊓ fixingSubgroup Γ (heckeTorsion 𝒥.T 𝔪 : Set 𝒥.T)) :=
    frobeniusPowerDense_ker_inf_fixing 𝒥 ρ' hfin' _ _

  have hfinT : Finite (heckeTorsion 𝒥.T 𝔪) := inferInstance

  obtain ⟨n, e, he⟩ :=
    ModularCurve.exists_blrDecomposition_heckeTorsion_of_span_eq_top_of_frobeniusQuadratic_of_dense
      (J := 𝒥.T) M p 𝔪 hp ρ' h2 hspan' hES hS' hatt' hdense hfinT

  intro t ht
  have htT : t ∈ heckeTorsion 𝒥.T 𝔪 := by
    refine (mem_heckeTorsion_iff 𝒥.T 𝔪 t).mpr ?_
    intro x hx
    have hx' : t ∈ (𝒥.snd.hecke x).toAddMonoidHom.ker :=
      (AddSubgroup.mem_iInf.mp ((AddSubgroup.mem_iInf.mp ht) x)) hx
    exact (AddMonoidHom.mem_ker).mp hx'
  simp only [JPrimeTorsionDatum.invariants, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply,
    AddMonoidHom.id_apply, AddEquiv.coe_toAddMonoidHom, sub_eq_zero]
  intro σ hσ
  have hρσ : ρ' σ = 1 := by
    show (RingHom.mapMatrix ι) (ρ σ) = 1
    rw [hunr σ hσ, map_one]
  have hw : mTorsionGaloisRep (G := Γ) 𝒥.T 𝔪 σ ⟨t, htT⟩ = ⟨t, htT⟩ := by
    apply e.injective
    funext i
    rw [he σ ⟨t, htT⟩ i, hρσ, Matrix.one_mulVec]
  have := congrArg (fun w : heckeTorsion 𝒥.T 𝔪 => (w : 𝒥.T)) hw
  first | exact this | simpa using this

end CerednikDrinfeld.TwoPlaceTorsionDatum.BLR

end

p2m_open "ModularCurve CerednikDrinfeld P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_W_le_invariants_of_goodReductionOutside_of_span_eq_top.CerednikDrinfeld"

theorem solution
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}
    (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    {M : ℕ} (hgood : 𝒥.fst.GoodReductionOutside M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : (p : HeckeAlg) ∈ 𝔪)
    (F : Type) [Field F] [Fintype F] (ι : F →+* HeckeAlg ⧸ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
    (hatt : ∃ S : Finset ℕ, (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
          Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = ((ρ σ).map ι).trace ∧
            Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = ((ρ σ).map ι).det)
    (hspan : Submodule.span (HeckeAlg ⧸ 𝔪)
      (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => (ρ σ).map ι) = ⊤)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hunr : ∀ σ ∈ A₂.inertiaSubgroupIn ℚ, ρ σ = 1) :
    𝒥.snd.W 𝔪 ≤ 𝒥.snd.invariants :=
  CerednikDrinfeld.TwoPlaceTorsionDatum.BLR.main hp2 𝒥 hgood 𝔪 hp F ι ρ hatt hspan hfin hunr

end S_CerednikDrinfeld_TwoPlaceTorsionDatum_W_le_invariants_of_goodReductionOutside_of_span_eq_top
end P2MW
export P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_W_le_invariants_of_goodReductionOutside_of_span_eq_top (solution)
