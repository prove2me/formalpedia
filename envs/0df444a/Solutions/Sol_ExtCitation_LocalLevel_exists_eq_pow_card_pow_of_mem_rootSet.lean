-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_eq_pow_card_pow_of_mem_rootSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/852d5815-d250-548b-9921-92454e3be766

import Mathlib
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Theorems.Thm_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff
import Theorems.Thm_minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot
import Theorems.Thm_ExtCitation_LocalLevel_residue_injOn_rootsOfUnity
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_eq_pow_card_pow_of_mem_rootSet

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField ExtCitation.LocalLevel
open Polynomial

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (m : ℕ) (hm : ¬ q ∣ m)
    (ζ₀ : PadicAlgCl q) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (t : PadicAlgCl q) (ht : t ∈ (minpoly K ζ₀).rootSet (PadicAlgCl q)) :
    ∃ i : ℕ, t = ζ₀ ^ (Nat.card (IsLocalRing.ResidueField (Rw q K)) ^ i) := by
  classical
  have hq : q.Prime := Fact.out
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hm (h0 ▸ dvd_zero q)
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero ((m : ℕ) : PadicAlgCl q) := ⟨by exact_mod_cast hm0.ne'⟩
  have hint0 : IsIntegral K ζ₀ := IsIntegral.of_pow hm0 (by rw [hζ₀.pow_eq_one]; exact isIntegral_one)

  let LK : IntermediateField K (PadicAlgCl q) := K⟮ζ₀⟯
  have hLK : IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ m = 1} = LK := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro ζ hζ
      obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
      exact pow_mem (IntermediateField.mem_adjoin_simple_self K ζ₀) i
    · change K⟮ζ₀⟯ ≤ _
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin K _ hζ₀.pow_eq_one
  haveI : Normal K LK := by
    have hset : {ζ : PadicAlgCl q | ζ ^ m = 1} = (X ^ m - 1 : (↥K)[X]).rootSet (PadicAlgCl q) := by
      ext ζ
      rw [Polynomial.mem_rootSet]
      simp only [Set.mem_setOf_eq, map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
      exact ⟨fun h => ⟨Polynomial.X_pow_sub_C_ne_zero hm0 1, h⟩, fun h => h.2⟩
    haveI : IsSplittingField K (IntermediateField.adjoin K ((X ^ m - 1 : (↥K)[X]).rootSet (PadicAlgCl q))) (X ^ m - 1) :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    have hn : Normal K (IntermediateField.adjoin K ((X ^ m - 1 : (↥K)[X]).rootSet (PadicAlgCl q))) :=
      Normal.of_isSplittingField (X ^ m - 1 : (↥K)[X])
    rw [← hset, hLK] at hn
    exact hn
  let Lw : IntermediateField ℚ_[q] (PadicAlgCl q) := LK.restrictScalars ℚ_[q]
  haveI : FiniteDimensional K LK := IntermediateField.adjoin.finiteDimensional hint0
  haveI : FiniteDimensional ℚ_[q] Lw := by
    change FiniteDimensional ℚ_[q] LK
    exact FiniteDimensional.trans ℚ_[q] K LK
  have hKL : K ≤ Lw := fun x hx => by
    change x ∈ LK
    have : x = algebraMap K (PadicAlgCl q) ⟨x, hx⟩ := rfl
    rw [this]
    exact LK.algebraMap_mem _

  have htL : t ∈ LK := by
    have htm : t ^ m = 1 := by
      have hdvd : minpoly K ζ₀ ∣ X ^ m - 1 := minpoly.dvd K ζ₀ (by simp [hζ₀.pow_eq_one])
      obtain ⟨c, hc⟩ := hdvd
      have := congrArg (Polynomial.aeval t) hc
      rw [map_mul, (Polynomial.mem_rootSet.1 ht).2, zero_mul, map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at this
      exact this
    obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one htm
    exact pow_mem (IntermediateField.mem_adjoin_simple_self K ζ₀) i
  let xζ : LK := ⟨ζ₀, IntermediateField.mem_adjoin_simple_self K ζ₀⟩
  let xt : LK := ⟨t, htL⟩
  have hminx : minpoly K xt = minpoly K xζ := by
    rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
    change minpoly K t = minpoly K ζ₀
    exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint0) (Polynomial.mem_rootSet.1 ht).2
      (minpoly.monic hint0)).symm
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1 ((Normal.minpoly_eq_iff_mem_orbit LK).1 hminx)
  have hσval : ((σ xζ : LK) : PadicAlgCl q) = t := by
    have : σ xζ = xt := hσ
    rw [this]

  obtain ⟨e, f, he, hf, -, hcardκ, -⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw q K
  obtain ⟨e', f', ι, hιval, he', hf', hιmax, -, -⟩ :=
    ExtCitation.LocalLevel.exists_relative_ramification_inertia_Rw q K Lw hKL
  haveI : Finite (IsLocalRing.ResidueField (Rw q K)) := ExtCitation.LocalLevel.finite_residueField_Rw q K
  letI : Fintype (IsLocalRing.ResidueField (Rw q K)) := Fintype.ofFinite _
  have hQ : Fintype.card (IsLocalRing.ResidueField (Rw q K)) = Nat.card (IsLocalRing.ResidueField (Rw q K)) :=
    (Nat.card_eq_fintype_card).symm
  haveI hιloc : IsLocalHom ι := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hxm : x ∈ IsLocalRing.maximalIdeal (Rw q K) := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have : ι x ∈ IsLocalRing.maximalIdeal (Rw q Lw) ^ e' := by
      rw [← hιmax]; exact Ideal.mem_map_of_mem ι hxm
    exact (IsLocalRing.mem_maximalIdeal _).1 (Ideal.pow_le_self he'.ne' this) hx
  let rK := IsLocalRing.residue (Rw q K)
  let rL := IsLocalRing.residue (Rw q Lw)
  let iota : IsLocalRing.ResidueField (Rw q K) →+* IsLocalRing.ResidueField (Rw q Lw) := IsLocalRing.ResidueField.map ι
  letI : Algebra (IsLocalRing.ResidueField (Rw q K)) (IsLocalRing.ResidueField (Rw q Lw)) := iota.toAlgebra

  have hmemRw : ∀ (x : Lw), x ∈ Rw q Lw ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := fun x => by
    change ((x : PadicAlgCl q)) ∈ padicIntegers q ↔ _
    rw [mem_padicIntegers_iff]
    rfl
  let j : Rw q Lw →+* PadicAlgCl q := (algebraMap Lw (PadicAlgCl q)).comp (Rw q Lw).toSubring.subtype
  have hj : ∀ y : Rw q Lw, j y = ((y : Lw) : PadicAlgCl q) := fun _ => rfl
  have hjinj : Function.Injective j := fun y₁ y₂ h12 => Subtype.ext (Subtype.ext h12)

  let σ' : Lw ≃ₐ[ℚ_[q]] Lw := σ.restrictScalars ℚ_[q]
  have hσ' : ∀ y : Lw, ((σ' y : Lw) : PadicAlgCl q) = ((σ (show LK from y) : LK) : PadicAlgCl q) := fun _ => rfl
  have hRw : ∀ y : Lw, σ' y ∈ Rw q Lw ↔ y ∈ Rw q Lw := ExtCitation.LocalLevel.algEquiv_apply_mem_Rw_iff q Lw σ'
  have hRw' : ∀ y : Lw, σ'.symm y ∈ Rw q Lw ↔ y ∈ Rw q Lw :=
    ExtCitation.LocalLevel.algEquiv_apply_mem_Rw_iff q Lw σ'.symm
  let σR : Rw q Lw →+* Rw q Lw :=
    σ'.toAlgHom.toRingHom.restrict (Rw q Lw) (Rw q Lw) (fun y hy => (hRw y).2 hy)
  let σRi : Rw q Lw →+* Rw q Lw :=
    σ'.symm.toAlgHom.toRingHom.restrict (Rw q Lw) (Rw q Lw) (fun y hy => (hRw' y).2 hy)
  have hσR : ∀ y : Rw q Lw, ((σR y : Rw q Lw) : Lw) = σ' (y : Lw) := fun _ => rfl
  have hσRi : ∀ y : Rw q Lw, σRi (σR y) = y := fun y => Subtype.ext (by
    change σ'.symm (σ' (y : Lw)) = y; exact σ'.symm_apply_apply _)
  haveI : IsLocalHom σR := ⟨fun y hy => by
    have := hy.map σRi
    rwa [hσRi] at this⟩
  let σbar : IsLocalRing.ResidueField (Rw q Lw) →+* IsLocalRing.ResidueField (Rw q Lw) := IsLocalRing.ResidueField.map σR

  have hσι : ∀ r : Rw q K, σR (ι r) = ι r := fun r => by
    apply hjinj
    rw [hj, hσR, hσ', hj]
    have e1 : (show LK from ((ι r : Rw q Lw) : Lw)) = algebraMap K LK (r : K) :=
      Subtype.ext (hιval r)
    rw [e1, AlgEquiv.commutes]
    exact (hιval r).symm
  have hσbar_alg : ∀ z : IsLocalRing.ResidueField (Rw q K), σbar (algebraMap _ _ z) = algebraMap _ _ z := by
    intro z
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
    change σbar (iota (rK r)) = iota (rK r)
    change IsLocalRing.ResidueField.map σR (IsLocalRing.ResidueField.map ι (IsLocalRing.residue _ r))
      = IsLocalRing.ResidueField.map ι (IsLocalRing.residue _ r)
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue, hσι]
  let σA : IsLocalRing.ResidueField (Rw q Lw) →ₐ[IsLocalRing.ResidueField (Rw q K)] IsLocalRing.ResidueField (Rw q Lw) :=
    { σbar with commutes' := hσbar_alg }

  have hnorm1 : ‖ζ₀‖ = 1 := by
    have h := congrArg norm hζ₀.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 h
  let y₀ : Rw q Lw := ⟨(show Lw from xζ), (hmemRw _).2 (by change ‖ζ₀‖ ≤ 1; rw [hnorm1])⟩
  have hy₀ : j y₀ = ζ₀ := rfl
  have hy₀m : y₀ ^ m = 1 := hjinj (by rw [map_pow, hy₀, hζ₀.pow_eq_one, map_one])
  have hzbar : IsPrimitiveRoot (rL y₀) m := by
    refine IsPrimitiveRoot.mk_of_lt (rL y₀) hm0 (by rw [← map_pow, hy₀m, map_one]) (fun l hl hlm hl1 => ?_)
    rw [← map_pow, ← map_one rL] at hl1
    have h1 := ExtCitation.LocalLevel.residue_injOn_rootsOfUnity q Lw m hm (y₀ ^ l) 1
      (by rw [← pow_mul, mul_comm, pow_mul, hy₀m, one_pow]) (one_pow m) hl1
    have h2 : ζ₀ ^ l = 1 := by
      have := congrArg j h1
      rwa [map_pow, hy₀, map_one] at this
    exact hζ₀.pow_ne_one_of_pos_of_lt hl.ne' hlm h2
  have hcop : (Fintype.card (IsLocalRing.ResidueField (Rw q K))).Coprime m := by
    rw [hQ, hcardκ]
    exact Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hq).2 hm)
  obtain ⟨-, hroots⟩ := minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot _ _ m (rL y₀) hzbar hcop
  have hroot : Polynomial.aeval (σA (rL y₀)) (minpoly (IsLocalRing.ResidueField (Rw q K)) (rL y₀)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨i, hi⟩ := (hroots _).1 hroot
  have hσA : σA (rL y₀) = rL (σR y₀) := IsLocalRing.ResidueField.map_residue σR y₀
  have hres : rL (σR y₀) = rL (y₀ ^ (Fintype.card (IsLocalRing.ResidueField (Rw q K)) ^ i)) := by
    rw [map_pow, ← hσA, hi]
  have heq := ExtCitation.LocalLevel.residue_injOn_rootsOfUnity q Lw m hm (σR y₀)
    (y₀ ^ (Fintype.card (IsLocalRing.ResidueField (Rw q K)) ^ i))
    (by rw [← map_pow, hy₀m, map_one]) (by rw [← pow_mul, mul_comm, pow_mul, hy₀m, one_pow]) hres
  refine ⟨i, ?_⟩
  have hv := congrArg j heq
  rw [map_pow, hy₀, hj, hσR, hσ'] at hv
  change ((σ xζ : LK) : PadicAlgCl q) = _ at hv
  rw [hσval] at hv
  rw [← hQ]
  exact hv

end S_ExtCitation_LocalLevel_exists_eq_pow_card_pow_of_mem_rootSet
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_eq_pow_card_pow_of_mem_rootSet (solution)
