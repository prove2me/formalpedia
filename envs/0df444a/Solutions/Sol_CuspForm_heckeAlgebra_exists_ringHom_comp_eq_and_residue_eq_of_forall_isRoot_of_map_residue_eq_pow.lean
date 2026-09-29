-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_ringHom_comp_eq_and_residue_eq_of_forall_isRoot_of_map_residue_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/02b9599d-a886-5771-b2b4-6bf7bcbcad2d

import Definitions.Def_CuspForm_HeckeAlgebra
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_comp_eq_and_residue_eq_of_forall_isRoot_of_map_residue_eq_pow
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial IsLocalRing

namespace E5PtCdvr

theorem residue_eq_of_isRoot {𝒪 𝒪' : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing 𝒪'] [IsLocalRing 𝒪']
    [Algebra 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')] (P : 𝒪[X]) (hP : P.Monic) (cbar : ResidueField 𝒪)
    (hred : P.map (residue 𝒪) = (X - C cbar) ^ P.natDegree) (y : 𝒪')
    (hroot : (P.map (algebraMap 𝒪 𝒪')).IsRoot y) :
    residue 𝒪' y = ResidueField.map (algebraMap 𝒪 𝒪') cbar := by
  have hn : P.natDegree ≠ 0 := by
    intro hdeg
    have h1 := eq_one_of_monic_natDegree_zero hP hdeg
    rw [h1, Polynomial.map_one, IsRoot, eval_one] at hroot
    exact one_ne_zero hroot
  have h1 : ((P.map (algebraMap 𝒪 𝒪')).map (residue 𝒪')).IsRoot (residue 𝒪' y) := hroot.map
  rw [Polynomial.map_map, ← ResidueField.map_comp_residue, ← Polynomial.map_map, hred] at h1
  rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, IsRoot, eval_pow, eval_sub, eval_X, eval_C] at h1
  exact sub_eq_zero.mp (pow_eq_zero_iff hn |>.mp h1)

end E5PtCdvr

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (N : ℕ) [NeZero N] (S : Set ℕ)
    (F : Type) [Field F] [Algebra 𝒪 F] (hF : Function.Injective (algebraMap 𝒪 F))
    (χ : CuspForm.heckeAlgebra N 2 S →+* F)
    (c : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ResidueField 𝒪)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      ∃ P : 𝒪[X], P.Monic ∧ (P.map (algebraMap 𝒪 F)).IsRoot (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧
        P.map (residue 𝒪) = (X - C (c ℓ hℓ hℓN hℓS)) ^ P.natDegree)
    (d : ∀ (q : ℕ), q.Prime → q ∣ N → q ∉ S → ResidueField 𝒪)
    (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
      ∃ P : 𝒪[X], P.Monic ∧ (P.map (algebraMap 𝒪 F)).IsRoot (χ (CuspForm.heckeAlgebra.U hq hqN hqS)) ∧
        P.map (residue 𝒪) = (X - C (d q hq hqN hqS)) ^ P.natDegree) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪'))
      (_ : CharZero 𝒪') (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪')
      (_ : IsLocalHom (algebraMap 𝒪 𝒪')) (e : 𝒪' →+* F),
    Function.Injective e ∧ e.comp (algebraMap 𝒪 𝒪') = algebraMap 𝒪 F ∧
    ∃ (χ' : CuspForm.heckeAlgebra N 2 S →+* 𝒪') (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪),
      e.comp χ' = χ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = c ℓ hℓ hℓN hℓS) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
        θ (CuspForm.heckeAlgebra.U hq hqN hqS) = d q hq hqN hqS) ∧
      ∀ t : CuspForm.heckeAlgebra N 2 S,
        residue 𝒪' (χ' t) = ResidueField.map (algebraMap 𝒪 𝒪') (θ t) := by
  classical

  let K := FractionRing 𝒪
  letI : Algebra K F := (IsFractionRing.lift hF : K →+* F).toAlgebra
  haveI : IsScalarTower 𝒪 K F := IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (A := 𝒪) hF x).symm
  haveI := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := K) (A := F) fun z => by
    simp only [algebraMap_int_eq, eq_intCast, map_intCast]

  haveI : Module.Finite ℤ (CuspForm.heckeAlgebra N 2 S) := CuspForm.moduleFinite_heckeAlgebra_two N S
  have hχint : ∀ t, IsIntegral ℤ (χ t) := fun t =>
    map_isIntegral_int χ (Algebra.IsIntegral.isIntegral (R := ℤ) t)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := CuspForm.heckeAlgebra N 2 S)
  let T : Set F := (↑(s.image χ) : Set F)
  have hTint : ∀ x ∈ T, IsIntegral K x := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact (hχint t).tower_top
  let K' : IntermediateField K F := IntermediateField.adjoin K T
  haveI : FiniteDimensional K K' := IntermediateField.finiteDimensional_adjoin hTint

  have hχK' : ∀ t, χ t ∈ K' := by
    intro t
    have ht : t ∈ Submodule.span ℤ (↑s : Set (CuspForm.heckeAlgebra N 2 S)) := by rw [hs]; trivial
    refine Submodule.span_induction (p := fun t _ => χ t ∈ K') ?_ ?_ ?_ ?_ ht
    · intro x hx
      exact IntermediateField.subset_adjoin K T (Finset.mem_coe.mpr (Finset.mem_image_of_mem χ hx))
    · show χ 0 ∈ K'
      rw [map_zero]; exact zero_mem K'
    · intro x y _ _ hx hy
      show χ (x + y) ∈ K'
      rw [map_add]; exact add_mem hx hy
    · intro z x _ hx
      show χ (z • x) ∈ K'
      rw [map_zsmul]; exact zsmul_mem hx z

  obtain ⟨hfin, hdvr, hcompl⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal 𝒪 K K'
  haveI : IsScalarTower 𝒪 K' F := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply 𝒪 K F x, IsScalarTower.algebraMap_apply 𝒪 K K' x,
      ← IsScalarTower.algebraMap_apply K K' F]
  let 𝒪' : Subalgebra 𝒪 K' := integralClosure 𝒪 K'
  haveI : Module.Finite 𝒪 𝒪' := hfin
  haveI : IsDiscreteValuationRing 𝒪' := hdvr
  haveI : IsAdicComplete (maximalIdeal 𝒪') 𝒪' := hcompl
  let e : 𝒪' →+* F := (algebraMap K' F).comp (algebraMap 𝒪' K')
  have he : Function.Injective e := (algebraMap K' F).injective.comp Subtype.val_injective
  have hecomp : e.comp (algebraMap 𝒪 𝒪') = algebraMap 𝒪 F := by
    ext x
    show algebraMap K' F (algebraMap 𝒪' K' (algebraMap 𝒪 𝒪' x)) = algebraMap 𝒪 F x
    rw [← IsScalarTower.algebraMap_apply 𝒪 𝒪' K', ← IsScalarTower.algebraMap_apply 𝒪 K' F]
  have hinj' : Function.Injective (algebraMap 𝒪 𝒪') := by
    apply Function.Injective.of_comp (f := e)
    rw [← RingHom.coe_comp, hecomp]
    exact hF
  haveI : CharZero 𝒪' := charZero_of_injective_algebraMap hinj'
  haveI : IsLocalHom (algebraMap 𝒪 𝒪') :=
    RingHom.IsIntegral.isLocalHom (Algebra.IsIntegral.isIntegral (R := 𝒪) (A := 𝒪')) hinj'
  haveI : Finite (ResidueField 𝒪') := ResidueField.finite_of_finite (R := 𝒪) (S := 𝒪') inferInstance

  have hχint' : ∀ t, (⟨χ t, hχK' t⟩ : K') ∈ 𝒪' := by
    intro t
    show IsIntegral 𝒪 (⟨χ t, hχK' t⟩ : K')
    haveI := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := 𝒪) (A := K') fun z => by
      simp only [algebraMap_int_eq, eq_intCast, map_intCast]
    have h1 : IsIntegral ℤ (⟨χ t, hχK' t⟩ : K') := by
      have h2 : IsIntegral ℤ (algebraMap K' F ⟨χ t, hχK' t⟩) := hχint t
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ K' F) (algebraMap K' F).injective).mp h2
    exact h1.tower_top
  let χ₁ : CuspForm.heckeAlgebra N 2 S →+* K' := χ.codRestrict K'.toSubalgebra.toSubring hχK'
  let χ' : CuspForm.heckeAlgebra N 2 S →+* 𝒪' := χ₁.codRestrict 𝒪'.toSubring hχint'
  have heχ' : e.comp χ' = χ := by
    ext t; rfl

  let m : ResidueField 𝒪 →+* ResidueField 𝒪' := ResidueField.map (algebraMap 𝒪 𝒪')
  have hroot' : ∀ (P : 𝒪[X]) (t : CuspForm.heckeAlgebra N 2 S), (P.map (algebraMap 𝒪 F)).IsRoot (χ t) →
      (P.map (algebraMap 𝒪 𝒪')).IsRoot (χ' t) := by
    intro P t h
    have h' : ((P.map (algebraMap 𝒪 𝒪')).map e).IsRoot (e (χ' t)) := by
      rw [Polynomial.map_map, hecomp]; exact h
    exact h'.of_map he
  have hTres : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      residue 𝒪' (χ' (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) = m (c ℓ hℓ hℓN hℓS) := by
    intro ℓ hℓ hℓN hℓS
    obtain ⟨P, hPm, hProot, hPred⟩ := hT ℓ hℓ hℓN hℓS
    exact E5PtCdvr.residue_eq_of_isRoot P hPm _ hPred _ (hroot' P _ hProot)
  have hUres : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
      residue 𝒪' (χ' (CuspForm.heckeAlgebra.U hq hqN hqS)) = m (d q hq hqN hqS) := by
    intro q hq hqN hqS
    obtain ⟨P, hPm, hProot, hPred⟩ := hU q hq hqN hqS
    exact E5PtCdvr.residue_eq_of_isRoot P hPm _ hPred _ (hroot' P _ hProot)

  let ψ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪' := (residue 𝒪').comp χ'
  have hψ : ∀ t, ψ t ∈ m.range := by
    rintro ⟨x, hx⟩
    refine Algebra.adjoin_induction (p := fun x hx => ψ ⟨x, hx⟩ ∈ m.range) ?_ ?_ ?_ ?_ hx
    · rintro y (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
      · refine ⟨c ℓ hℓ hℓN hℓS, ?_⟩
        rw [← hTres ℓ hℓ hℓN hℓS]; rfl
      · refine ⟨d q hq hqN hqS, ?_⟩
        rw [← hUres q hq hqN hqS]; rfl
    · intro z
      refine ⟨z, ?_⟩
      have : (⟨algebraMap ℤ _ z, Subalgebra.algebraMap_mem _ z⟩ : CuspForm.heckeAlgebra N 2 S) =
          algebraMap ℤ (CuspForm.heckeAlgebra N 2 S) z := rfl
      rw [this, map_intCast, eq_intCast, map_intCast]
    · intro y z hy hz hy' hz'
      have : (⟨y + z, add_mem hy hz⟩ : CuspForm.heckeAlgebra N 2 S) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add]
      exact add_mem hy' hz'
    · intro y z hy hz hy' hz'
      have : (⟨y * z, mul_mem hy hz⟩ : CuspForm.heckeAlgebra N 2 S) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul]
      exact mul_mem hy' hz'

  have hmbij : Function.Bijective m.rangeRestrict :=
    ⟨fun x y h => m.injective (congrArg Subtype.val h), m.rangeRestrict_surjective⟩
  let ι : ResidueField 𝒪 ≃+* m.range := RingEquiv.ofBijective m.rangeRestrict hmbij
  let θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪 := ι.symm.toRingHom.comp (ψ.codRestrict m.range hψ)
  have hmθ : ∀ t, m (θ t) = ψ t := by
    intro t
    have h1 : ι (θ t) = ψ.codRestrict m.range hψ t := by
      show ι (ι.symm _) = _
      exact ι.apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    exact h2
  refine ⟨𝒪', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, e, he, hecomp, χ', θ, heχ', ?_, ?_, ?_⟩
  · intro ℓ hℓ hℓN hℓS
    apply m.injective
    rw [hmθ, ← hTres]
    rfl
  · intro q hq hqN hqS
    apply m.injective
    rw [hmθ, ← hUres]
    rfl
  · intro t
    rw [hmθ]
    rfl

end S_CuspForm_heckeAlgebra_exists_ringHom_comp_eq_and_residue_eq_of_forall_isRoot_of_map_residue_eq_pow
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_comp_eq_and_residue_eq_of_forall_isRoot_of_map_residue_eq_pow (solution)
