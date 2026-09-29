-- Prove2me | solution 1 for CuspForm.IsNewform.sum_rootMultiplicity_residual_zero_eq_one_of_sq_dvd_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/66b421d0-bc4c-57c7-b72c-e44f8d0b25e7

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Roots
import Theorems.Thm_CuspForm_IsNewform_qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne
import Theorems.Thm_IsDiscreteValuationRing_eq_of_monic_aeval_eq_zero_map_residue_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_sum_rootMultiplicity_residual_zero_eq_one_of_sq_dvd_of_ne
p2m_attr_erase "simp" "CuspForm.coe_heckeULowerLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

open Polynomial IsLocalRing
open scoped TensorProduct IsMulCommutative

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open scoped Classical in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (N : ℕ) [NeZero N] (hN3 : ∀ q : ℕ, q.Prime → ¬ q ^ 3 ∣ N)

    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ)
    (hchigT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg),
      chig (CuspForm.heckeAlgebra.T hℓ hℓMg (Set.notMem_empty ℓ)) = ModularFormClass.qCoeff g ℓ)
    (hchigU : ∀ (q : ℕ) (hq : q.Prime) (hqMg : q ∣ Mg),
      chig (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)) = ModularFormClass.qCoeff g q)
    (ι : chig.range →+* AlgebraicClosure (FractionRing 𝒪))

    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (hqN : q ^ 2 ∣ N) :
    (let P : Polynomial (AlgebraicClosure (FractionRing 𝒪)) :=
      (if hqP : Nat.Prime q then
        (let aq : AlgebraicClosure (FractionRing 𝒪) := if hqMg : q ∣ Mg
            then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U hqP hqMg (Set.notMem_empty q)))
            else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hqP hqMg (Set.notMem_empty q)))
         let e : ℕ := N.factorization q - Mg.factorization q
         if e = 0 then X - C aq
         else X ^ (e - 1) * (X ^ 2 - C aq * X + C (if q ∣ Mg then (0 : AlgebraicClosure (FractionRing 𝒪)) else (q : AlgebraicClosure (FractionRing 𝒪)))))
       else 1)
     ∑ x ∈ P.roots.toFinset,
      if (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (0 : ResidueField 𝒪)) ^ R.natDegree)
      then P.rootMultiplicity x else 0) = 1 := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  have hMg0 : Mg ≠ 0 := NeZero.ne Mg
  have hvN : N.factorization q = 2 := by
    have h2 : 2 ≤ N.factorization q := (Nat.Prime.pow_dvd_iff_le_factorization hq hN0).mp hqN
    have h3 : ¬ 3 ≤ N.factorization q := fun h =>
      hN3 q hq ((Nat.Prime.pow_dvd_iff_le_factorization hq hN0).mpr h)
    omega
  have hvMg : Mg.factorization q ≤ 2 := hvN ▸ (Nat.factorization_le_iff_dvd hMg0 hN0).mpr hMgN q

  obtain ⟨hA, hB, hC⟩ :=
    CuspForm.IsNewform.qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne
      p hp𝒪 Mg g hg chig hchigT ι q hq hqp

  have hRZ0 : ∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (0 : AlgebraicClosure (FractionRing 𝒪)) R = 0 ∧
      R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (0 : ResidueField 𝒪)) ^ R.natDegree :=
    ⟨X, monic_X, by simp, by simp⟩

  have hinj : Function.Injective (algebraMap 𝒪 (AlgebraicClosure (FractionRing 𝒪))) := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (FractionRing 𝒪) (AlgebraicClosure (FractionRing 𝒪))]
    exact (algebraMap (FractionRing 𝒪) (AlgebraicClosure (FractionRing 𝒪))).injective.comp
      (IsFractionRing.injective 𝒪 (FractionRing 𝒪))

  have hpm : ∀ a : ℤ, (a = 1 ∨ a = -1) →
      ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval ((a : ℤ) : AlgebraicClosure (FractionRing 𝒪)) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (0 : ResidueField 𝒪)) ^ R.natDegree) := by
    rintro a ha ⟨R, hRm, hRa, hRr⟩
    have h := IsDiscreteValuationRing.eq_of_monic_aeval_eq_zero_map_residue_eq_pow hinj
      ((a : ℤ) : AlgebraicClosure (FractionRing 𝒪)) 0 (IsLocalRing.residue 𝒪 (a : 𝒪)) R hRm hRa hRr
      (X - C ((a : ℤ) : 𝒪)) (monic_X_sub_C _)
      (by rw [map_sub, aeval_X, aeval_C, map_intCast, sub_self])
      (by rw [Polynomial.map_sub, map_X, map_C, natDegree_X_sub_C, pow_one])
    rw [map_intCast] at h
    rcases ha with rfl | rfl
    · exact zero_ne_one (by exact_mod_cast h)
    · have : (0 : ResidueField 𝒪) = -1 := by exact_mod_cast h
      exact zero_ne_one (neg_eq_zero.mp this.symm).symm

  have key : ∀ Q : Polynomial (AlgebraicClosure (FractionRing 𝒪)), Q.eval 0 ≠ 0 →
      (∀ x ∈ Q.roots, ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (0 : ResidueField 𝒪)) ^ R.natDegree)) →
      ∑ x ∈ (X * Q).roots.toFinset,
        (if (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
              R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (0 : ResidueField 𝒪)) ^ R.natDegree)
          then (X * Q).rootMultiplicity x else 0) = 1 := by
    intro Q hQ0 hQ
    have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h, eval_zero])
    have hXQ : (X : Polynomial (AlgebraicClosure (FractionRing 𝒪))) * Q ≠ 0 := mul_ne_zero X_ne_zero hQne
    have hroots : (X * Q).roots = 0 ::ₘ Q.roots := by
      rw [roots_mul hXQ, roots_X, Multiset.singleton_add]
    rw [Finset.sum_eq_single (0 : AlgebraicClosure (FractionRing 𝒪))]
    · rw [if_pos hRZ0, rootMultiplicity_mul hXQ,
        show (X : Polynomial (AlgebraicClosure (FractionRing 𝒪))) = X - C 0 by rw [C_0, sub_zero],
        rootMultiplicity_X_sub_C_self, rootMultiplicity_eq_zero, add_zero]
      exact fun h => hQ0 h
    · intro b hb hb0
      rw [Multiset.mem_toFinset, hroots, Multiset.mem_cons] at hb
      rw [if_neg (hQ b (hb.resolve_left hb0))]
    · intro h0
      exact absurd (Multiset.mem_toFinset.mpr (by rw [hroots]; exact Multiset.mem_cons_self _ _)) h0

  simp only [dif_pos hq, hvN]
  rcases Nat.lt_or_ge (Mg.factorization q) 1 with hm | hm
  ·
    have hm0 : Mg.factorization q = 0 := by omega
    have hqMg : ¬ q ∣ Mg := fun h => by
      have := (Nat.Prime.dvd_iff_one_le_factorization hq hMg0).mp h; omega
    simp only [hm0, dif_neg hqMg, if_neg hqMg, Nat.sub_zero, show ¬ ((2 : ℕ) = 0) from by decide,
      if_false, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    refine key _ ?_ (hC hqMg)
    simp [hq.ne_zero]
  rcases Nat.lt_or_ge (Mg.factorization q) 2 with hm' | hm'
  ·
    have hm1 : Mg.factorization q = 1 := by omega
    have hqMg : q ∣ Mg := (Nat.Prime.dvd_iff_one_le_factorization hq hMg0).mpr (by omega)
    have hq2Mg : ¬ q ^ 2 ∣ Mg := fun h => by
      have := (Nat.Prime.pow_dvd_iff_le_factorization hq hMg0).mp h; omega
    obtain ⟨a, ha, haq⟩ := hB hqMg hq2Mg
    have hU : chig.rangeRestrict (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)) = (a : chig.range) := by
      apply Subtype.ext
      rw [RingHom.coe_rangeRestrict, hchigU q hq hqMg, haq]
      simp
    simp only [hm1, dif_pos hqMg, if_pos hqMg, show (2 : ℕ) - 1 = 1 from rfl, one_ne_zero, if_false,
      Nat.sub_self, pow_zero, one_mul, hU]
    rw [map_intCast]
    have hfac : (X ^ 2 - C ((a : ℤ) : AlgebraicClosure (FractionRing 𝒪)) * X + C 0 :
        Polynomial (AlgebraicClosure (FractionRing 𝒪))) = X * (X - C ((a : ℤ) : AlgebraicClosure (FractionRing 𝒪))) := by
      rw [C_0, add_zero]; ring
    rw [hfac]
    have ha0 : ((a : ℤ) : AlgebraicClosure (FractionRing 𝒪)) ≠ 0 := by
      rcases ha with rfl | rfl <;> simp
    refine key _ ?_ ?_
    · simp [ha0]
    · intro x hx
      rw [roots_X_sub_C, Multiset.mem_singleton] at hx
      rw [hx]
      exact hpm a ha
  ·
    have hm2 : Mg.factorization q = 2 := le_antisymm hvMg hm'
    have hqMg : q ∣ Mg := (Nat.Prime.dvd_iff_one_le_factorization hq hMg0).mpr (by omega)
    have hq2Mg : q ^ 2 ∣ Mg := (Nat.Prime.pow_dvd_iff_le_factorization hq hMg0).mpr (by omega)
    have hU : chig.rangeRestrict (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)) = 0 := by
      apply Subtype.ext
      rw [RingHom.coe_rangeRestrict, hchigU q hq hqMg, hA hq2Mg]
      rfl
    simp only [hm2, dif_pos hqMg, Nat.sub_self, if_true, hU]
    rw [map_zero ι]
    have hX : (X - C 0 : Polynomial (AlgebraicClosure (FractionRing 𝒪))) = X * 1 := by
      rw [C_0, sub_zero, mul_one]
    rw [hX]
    refine key 1 (by simp) ?_
    intro x hx
    simp at hx

end S_CuspForm_IsNewform_sum_rootMultiplicity_residual_zero_eq_one_of_sq_dvd_of_ne
end P2MW
export P2MW.S_CuspForm_IsNewform_sum_rootMultiplicity_residual_zero_eq_one_of_sq_dvd_of_ne (solution)
