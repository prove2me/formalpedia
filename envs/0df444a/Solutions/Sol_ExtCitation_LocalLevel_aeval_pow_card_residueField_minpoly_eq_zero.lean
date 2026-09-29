-- Prove2me | solution 1 for ExtCitation.LocalLevel.aeval_pow_card_residueField_minpoly_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e7cae035-208e-5f95-b027-e8fc4b72d1f4

import Mathlib
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Theorems.Thm_Polynomial_aeval_pow_card_eq_pow_card
import Theorems.Thm_ExtCitation_LocalLevel_residue_injOn_rootsOfUnity
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_aeval_pow_card_residueField_minpoly_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField ExtCitation.LocalLevel
open Polynomial

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (m : ℕ) (hm : ¬ q ∣ m)
    (ζ₀ : PadicAlgCl q) (hζ₀ : IsPrimitiveRoot ζ₀ m) :
    ∃ a : ℕ, 0 < a ∧ Nat.card (IsLocalRing.ResidueField (Rw q K)) = q ^ a ∧
      Polynomial.aeval (ζ₀ ^ (q ^ a)) (minpoly K ζ₀) = 0 := by
  classical
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hm (h0 ▸ dvd_zero q)
  haveI : NeZero m := ⟨hm0.ne'⟩

  let LK : IntermediateField K (PadicAlgCl q) := K⟮ζ₀⟯
  let Lw : IntermediateField ℚ_[q] (PadicAlgCl q) := LK.restrictScalars ℚ_[q]
  have hint0 : IsIntegral K ζ₀ := IsIntegral.of_pow hm0 (by rw [hζ₀.pow_eq_one]; exact isIntegral_one)
  haveI : FiniteDimensional K LK := IntermediateField.adjoin.finiteDimensional hint0
  haveI : FiniteDimensional ℚ_[q] Lw := by
    change FiniteDimensional ℚ_[q] LK
    exact FiniteDimensional.trans ℚ_[q] K LK
  have hKL : K ≤ Lw := fun x hx => by
    change x ∈ LK
    have : x = algebraMap K (PadicAlgCl q) ⟨x, hx⟩ := rfl
    rw [this]
    exact LK.algebraMap_mem _

  obtain ⟨e, f, he, hf, hspan, hcardκ, hef⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw q K
  obtain ⟨e', f', ι, hιval, he', hf', hιmax, hcardL, hdeg⟩ :=
    ExtCitation.LocalLevel.exists_relative_ramification_inertia_Rw q K Lw hKL
  haveI : Finite (IsLocalRing.ResidueField (Rw q K)) := ExtCitation.LocalLevel.finite_residueField_Rw q K
  letI : Fintype (IsLocalRing.ResidueField (Rw q K)) := Fintype.ofFinite _

  haveI hιloc : IsLocalHom ι := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hxm : x ∈ IsLocalRing.maximalIdeal (Rw q K) := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have : ι x ∈ IsLocalRing.maximalIdeal (Rw q Lw) ^ e' := by
      rw [← hιmax]; exact Ideal.mem_map_of_mem ι hxm
    have h1 : ι x ∈ IsLocalRing.maximalIdeal (Rw q Lw) := Ideal.pow_le_self he'.ne' this
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 hx
  let rK := IsLocalRing.residue (Rw q K)
  let rL := IsLocalRing.residue (Rw q Lw)
  let iota : IsLocalRing.ResidueField (Rw q K) →+* IsLocalRing.ResidueField (Rw q Lw) := IsLocalRing.ResidueField.map ι
  letI : Algebra (IsLocalRing.ResidueField (Rw q K)) (IsLocalRing.ResidueField (Rw q Lw)) := iota.toAlgebra
  refine ⟨f, hf, hcardκ, ?_⟩

  letI algRΩ : Algebra (Rw q K) (PadicAlgCl q) :=
    ((algebraMap K (PadicAlgCl q)).comp (algebraMap (Rw q K) K)).toAlgebra
  haveI : IsScalarTower (Rw q K) K (PadicAlgCl q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hintR : IsIntegral (Rw q K) ζ₀ := IsIntegral.of_pow hm0 (by rw [hζ₀.pow_eq_one]; exact isIntegral_one)
  set gR : (Rw q K)[X] := minpoly (Rw q K) ζ₀ with hgR
  have hg : minpoly K ζ₀ = gR.map (algebraMap (Rw q K) K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hintR
  have hgRmonic : gR.Monic := minpoly.monic hintR

  let j : Rw q Lw →+* PadicAlgCl q := (algebraMap Lw (PadicAlgCl q)).comp (Rw q Lw).toSubring.subtype
  have hj : ∀ y : Rw q Lw, j y = ((y : Lw) : PadicAlgCl q) := fun _ => rfl
  have hjinj : Function.Injective j := fun y₁ y₂ h12 => Subtype.ext (Subtype.ext h12)
  have hjι : j.comp ι = algebraMap (Rw q K) (PadicAlgCl q) := RingHom.ext fun x => hιval x

  have hmemLK : ∀ i : ℕ, ζ₀ ^ i ∈ Lw := fun i => by
    change ζ₀ ^ i ∈ LK
    exact pow_mem (IntermediateField.mem_adjoin_simple_self K ζ₀) i
  have hnorm1 : ‖ζ₀‖ = 1 := by
    have h := congrArg norm hζ₀.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 h
  have hmemRw : ∀ (x : Lw), ‖(x : PadicAlgCl q)‖ ≤ 1 → x ∈ Rw q Lw := fun x hx => by
    change ((x : PadicAlgCl q)) ∈ padicIntegers q
    rw [mem_padicIntegers_iff]
    exact hx
  have hTpow : ∀ t : PadicAlgCl q, t ∈ (minpoly K ζ₀).rootSet (PadicAlgCl q) → ∃ i : ℕ, ζ₀ ^ i = t := fun t ht => by
    rw [Polynomial.mem_rootSet] at ht
    have htm : t ^ m = 1 := by
      have hdvd : minpoly K ζ₀ ∣ X ^ m - 1 := minpoly.dvd K ζ₀ (by simp [hζ₀.pow_eq_one])
      obtain ⟨c, hc⟩ := hdvd
      have := congrArg (Polynomial.aeval t) hc
      rw [map_mul, ht.2, zero_mul, map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at this
      exact this
    obtain ⟨i, -, hi⟩ := hζ₀.eq_pow_of_pow_eq_one htm
    exact ⟨i, hi⟩

  have hlift : ∀ t : (minpoly K ζ₀).rootSet (PadicAlgCl q), ∃ y : Rw q Lw, j y = (t : PadicAlgCl q) ∧ y ^ m = 1 := fun t => by
    obtain ⟨i, hi⟩ := hTpow t t.2
    refine ⟨⟨⟨ζ₀ ^ i, hmemLK i⟩, hmemRw _ (by change ‖ζ₀ ^ i‖ ≤ 1; rw [norm_pow, hnorm1, one_pow])⟩, ?_, ?_⟩
    · rw [hj]; exact hi
    · apply hjinj
      rw [map_pow, map_one, hj]
      change (ζ₀ ^ i) ^ m = 1
      rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow]
  choose y hy hym using hlift
  have hyinj : Function.Injective (fun t : (minpoly K ζ₀).rootSet (PadicAlgCl q) => rL (y t)) := fun t₁ t₂ h12 => by
    have := ExtCitation.LocalLevel.residue_injOn_rootsOfUnity q Lw m hm (y t₁) (y t₂) (hym t₁) (hym t₂) h12
    apply Subtype.ext
    rw [← hy t₁, ← hy t₂, this]

  set gL : (IsLocalRing.ResidueField (Rw q Lw))[X] := gR.map (rL.comp ι) with hgL
  have hgLmonic : gL.Monic := hgRmonic.map _
  have hgL0 : gL ≠ 0 := hgLmonic.ne_zero
  have hrooty : ∀ t : (minpoly K ζ₀).rootSet (PadicAlgCl q), gL.IsRoot (rL (y t)) := fun t => by
    rw [Polynomial.IsRoot, hgL, Polynomial.eval_map, ← Polynomial.hom_eval₂ _ ι rL]

    have h0 : Polynomial.eval₂ ι (y t) gR = 0 := by
      apply hjinj
      rw [Polynomial.hom_eval₂ _ ι j, hjι, hy, map_zero]
      have h2 := (Polynomial.mem_rootSet.1 t.2).2
      change Polynomial.aeval (t : PadicAlgCl q) gR = 0
      rw [← Polynomial.aeval_map_algebraMap K, ← hg]
      exact h2
    rw [h0, map_zero]

  have hdeg : gL.natDegree = Fintype.card ((minpoly K ζ₀).rootSet (PadicAlgCl q)) := by
    rw [hgL, hgRmonic.natDegree_map, ← hgRmonic.natDegree_map (algebraMap (Rw q K) K), ← hg,
      Polynomial.card_rootSet_eq_natDegree (minpoly.irreducible hint0).separable (IsAlgClosed.splits _)]

  let SR : Finset (IsLocalRing.ResidueField (Rw q Lw)) :=
    Finset.univ.image (fun t : (minpoly K ζ₀).rootSet (PadicAlgCl q) => rL (y t))
  have hSRcard : SR.card = gL.natDegree := by
    rw [Finset.card_image_of_injective _ hyinj, Finset.card_univ, hdeg]
  have hSRsub : SR ⊆ gL.roots.toFinset := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hgL0]
    exact hrooty t
  have hRTcard : gL.roots.toFinset.card ≤ gL.natDegree :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' gL)
  have hSReq : SR = gL.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hSRsub (by rw [hSRcard]; exact hRTcard)

  have hζT : ζ₀ ∈ (minpoly K ζ₀).rootSet (PadicAlgCl q) := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hint0, minpoly.aeval K ζ₀⟩
  let t₀ : (minpoly K ζ₀).rootSet (PadicAlgCl q) := ⟨ζ₀, hζT⟩
  have hQ : Fintype.card (IsLocalRing.ResidueField (Rw q K)) = q ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hcardκ
  have hmapres : (algebraMap (IsLocalRing.ResidueField (Rw q K)) (IsLocalRing.ResidueField (Rw q Lw))).comp rK
      = rL.comp ι := RingHom.ext fun x => rfl
  have e1 : gL = (gR.map rK).map (algebraMap (IsLocalRing.ResidueField (Rw q K)) (IsLocalRing.ResidueField (Rw q Lw))) := by
    rw [hgL, Polynomial.map_map, hmapres]
  have e2 : ∀ z, gL.eval z = Polynomial.aeval z (gR.map rK) := fun z => by
    rw [e1, Polynomial.eval_map, ← Polynomial.aeval_def]
  have hfrob : gL.IsRoot ((rL (y t₀)) ^ (q ^ f)) := by
    rw [Polynomial.IsRoot, e2, ← hQ, Polynomial.aeval_pow_card_eq_pow_card, ← e2]
    have := hrooty t₀
    rw [Polynomial.IsRoot] at this
    rw [this, zero_pow Fintype.card_ne_zero]
  have hxmem : (rL (y t₀)) ^ (q ^ f) ∈ SR := by
    rw [hSReq, Multiset.mem_toFinset, Polynomial.mem_roots hgL0]
    exact hfrob
  obtain ⟨t, -, ht⟩ := Finset.mem_image.1 hxmem
  have hyt : y t = (y t₀) ^ (q ^ f) := by
    apply ExtCitation.LocalLevel.residue_injOn_rootsOfUnity q Lw m hm (y t) ((y t₀) ^ (q ^ f)) (hym t)
      (by rw [← pow_mul, mul_comm, pow_mul, hym t₀, one_pow])
    rw [ht, map_pow]
  have hval : (t : PadicAlgCl q) = ζ₀ ^ (q ^ f) := by rw [← hy t, hyt, map_pow, hy t₀]
  have := (Polynomial.mem_rootSet.1 t.2).2
  rwa [hval] at this

end S_ExtCitation_LocalLevel_aeval_pow_card_residueField_minpoly_eq_zero
end P2MW
export P2MW.S_ExtCitation_LocalLevel_aeval_pow_card_residueField_minpoly_eq_zero (solution)
