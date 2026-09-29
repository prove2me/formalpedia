-- Prove2me | solution 1 for CuspForm.IsNewform.qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7a8c879c-a271-5b57-bf73-777f90314652

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib
import Theorems.Thm_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
import Theorems.Thm_CuspForm_traceLin_atkinLehnerLin_eq_zero_of_isNewform
import Theorems.Thm_CuspForm_qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero
import Theorems.Thm_IsLocalRing_not_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_mul_eq_algebraMap_of_isUnit
import Theorems.Thm_CuspForm_fg_toSubmodule_heckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne
p2m_attr_erase "simp" "CuspForm.coe_heckeULowerLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

open Polynomial IsLocalRing

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (Mg : ℕ) [NeZero Mg]
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg),
      chig (CuspForm.heckeAlgebra.T hℓ hℓMg (Set.notMem_empty ℓ)) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* AlgebraicClosure (FractionRing 𝒪))

    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    (q ^ 2 ∣ Mg → ModularFormClass.qCoeff g q = 0) ∧
    (q ∣ Mg → ¬ q ^ 2 ∣ Mg → ∃ a : ℤ, (a = 1 ∨ a = -1) ∧ ModularFormClass.qCoeff g q = (a : ℂ)) ∧
    (∀ hqMg : ¬ q ∣ Mg,
      ∀ x ∈ (X ^ 2 - C (iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hq hqMg (Set.notMem_empty q)))) * X
              + C ((q : ℕ) : AlgebraicClosure (FractionRing 𝒪))).roots,
        ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
          R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (0 : ResidueField 𝒪)) ^ R.natDegree)) := by
  classical
  refine ⟨fun hsq => CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd hg q hq hsq, ?_, ?_⟩
  ·
    intro hqMg hnsq
    set R : ℕ := Mg / q with hRdef
    have hM : Mg = q * R := (Nat.mul_div_cancel' hqMg).symm
    have hcop : Nat.Coprime q R := by
      rw [Nat.Prime.coprime_iff_not_dvd hq]
      intro hqR
      apply hnsq
      rw [hM, pow_two]
      exact Nat.mul_dvd_mul_left q hqR
    have hbez : (q : ℤ) * Nat.gcdA q R - (R : ℤ) * (-Nat.gcdB q R) = 1 := by
      have h := Nat.gcd_eq_gcd_ab q R
      rw [Nat.Coprime.gcd_eq_one hcop] at h
      push_cast at h
      linear_combination -h
    let W : ModularForm.AtkinLehnerDatum Mg q := ⟨R, hM, Nat.gcdA q R, -Nat.gcdB q R, hbez⟩
    have h0 := CuspForm.traceLin_atkinLehnerLin_eq_zero_of_isNewform W hq hg
    have h1 := CuspForm.qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero W hq hg.isNormalizedEigenform h0
    have h2 : (ModularFormClass.qCoeff g q - 1) * (ModularFormClass.qCoeff g q + 1) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact ⟨1, Or.inl rfl, by push_cast; linear_combination h⟩
    · exact ⟨-1, Or.inr rfl, by push_cast; linear_combination h⟩
  ·
    intro hqMg x hx
    set A : AlgebraicClosure (FractionRing 𝒪) :=
      iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hq hqMg (Set.notMem_empty q))) with hA

    have hP0 : (X ^ 2 - C A * X + C ((q : ℕ) : AlgebraicClosure (FractionRing 𝒪))) ≠ 0 := by
      intro h0
      have := congrArg (fun P : Polynomial (AlgebraicClosure (FractionRing 𝒪)) => P.coeff 2) h0
      simp [coeff_X, coeff_C] at this
    have hroot : x ^ 2 - A * x + (q : AlgebraicClosure (FractionRing 𝒪)) = 0 := by
      have h := (Polynomial.mem_roots hP0).mp hx
      simpa [Polynomial.IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] using h

    have hAint : IsIntegral 𝒪 A := by
      haveI : Module.Finite ℤ (CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ)) :=
        Module.Finite.iff_fg.mpr (CuspForm.fg_toSubmodule_heckeAlgebra Mg (∅ : Set ℕ))
      have hT : IsIntegral ℤ (CuspForm.heckeAlgebra.T hq hqMg (Set.notMem_empty q) :
          CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ)) := Algebra.IsIntegral.isIntegral _
      obtain ⟨P, hPm, hPT⟩ := hT
      set φ : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* AlgebraicClosure (FractionRing 𝒪) :=
        iota.comp chig.rangeRestrict with hφ
      have hφT : φ (CuspForm.heckeAlgebra.T hq hqMg (Set.notMem_empty q)) = A := rfl
      have hev : Polynomial.eval₂ (φ.comp (algebraMap ℤ _)) A P = 0 := by
        rw [← hφT, ← Polynomial.hom_eval₂, hPT, map_zero]
      refine ⟨P.map (Int.castRingHom 𝒪), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hh : (algebraMap 𝒪 (AlgebraicClosure (FractionRing 𝒪))).comp (Int.castRingHom 𝒪) =
          φ.comp (algebraMap ℤ _) := RingHom.ext_int _ _
      rw [hh]
      exact hev

    have hxint : IsIntegral 𝒪 x := by
      let S : Subalgebra 𝒪 (AlgebraicClosure (FractionRing 𝒪)) := Algebra.adjoin 𝒪 {A}
      haveI : Module.Finite 𝒪 S := Module.Finite.iff_fg.mpr hAint.fg_adjoin_singleton
      haveI : Algebra.IsIntegral 𝒪 S := Algebra.IsIntegral.of_finite 𝒪 S
      have hAS : A ∈ S := Algebra.subset_adjoin (Set.mem_singleton A)
      have hxS : IsIntegral S x := by
        have hmon : (X ^ 2 - C (⟨A, hAS⟩ : S) * X + C ((q : ℕ) : S)).Monic := by
          have hre : (X ^ 2 - C (⟨A, hAS⟩ : S) * X + C ((q : ℕ) : S)) =
              X ^ 2 + (C (-(⟨A, hAS⟩ : S)) * X + C ((q : ℕ) : S)) := by
            rw [map_neg]; ring
          rw [hre]
          refine monic_X_pow_add ((degree_add_le _ _).trans_lt (max_lt ?_ ?_))
          · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast (by norm_num : (1 : ℕ) < 2))
          · exact degree_C_le.trans_lt (by exact_mod_cast (by norm_num : (0 : ℕ) < 2))
        refine ⟨X ^ 2 - C (⟨A, hAS⟩ : S) * X + C ((q : ℕ) : S), hmon, ?_⟩
        simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
        have e1 : (algebraMap S (AlgebraicClosure (FractionRing 𝒪))) ⟨A, hAS⟩ = A := rfl
        have e2 : (algebraMap S (AlgebraicClosure (FractionRing 𝒪))) ((q : ℕ) : S) =
            ((q : ℕ) : AlgebraicClosure (FractionRing 𝒪)) := map_natCast _ q
        rw [e1, e2]
        linear_combination hroot
      exact isIntegral_trans x hxS

    set y : AlgebraicClosure (FractionRing 𝒪) := A - x with hy
    have hyint : IsIntegral 𝒪 y := hAint.sub hxint
    have hxy : x * y = algebraMap 𝒪 (AlgebraicClosure (FractionRing 𝒪)) (q : 𝒪) := by
      rw [map_natCast, hy]
      linear_combination -hroot

    have hqu : IsUnit ((q : ℕ) : 𝒪) := by
      by_contra hnu
      have hqm : ((q : ℕ) : 𝒪) ∈ maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
        Nat.Coprime.isCoprime ((Nat.coprime_primes (Fact.out) hq).mpr (Ne.symm hqp))
      obtain ⟨u, v, huv⟩ := hcop
      have h1 : (1 : 𝒪) ∈ maximalIdeal 𝒪 := by
        have := congrArg (fun z : ℤ => (z : 𝒪)) huv
        push_cast at this
        rw [← this]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp𝒪) (Ideal.mul_mem_left _ _ hqm)
      exact (maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    exact IsLocalRing.not_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_mul_eq_algebraMap_of_isUnit
      x y hyint ((q : ℕ) : 𝒪) hqu hxy

end S_CuspForm_IsNewform_qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne
end P2MW
export P2MW.S_CuspForm_IsNewform_qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne (solution)
