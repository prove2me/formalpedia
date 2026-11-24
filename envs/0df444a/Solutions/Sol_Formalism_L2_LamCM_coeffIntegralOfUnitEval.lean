-- Prove2me | solution 1 for Formalism.L2.LamCM.coeffIntegralOfUnitEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:31.941038+00:00
-- url     : https://prove2.me/submissions/69b8b43d-a685-4fe0-b65d-a899b29f95e0

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Theorems.Thm_Formalism_L2_LamCM_exists_eval_ne_zero_of_totalDegree_lt
import Theorems.Thm_Formalism_L2_LamCM_exists_finset_card_gt
import Theorems.Thm_Formalism_L2_LamCM_totalDegree_det_X_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution : LemmaGCore := by
  intro R K _ _ _ _ _ _ B _ m P hcard hval μ0
  classical
  by_contra hμ0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) P.support (fun μ => coeff μ P)
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hex : ∃ e : ℕ, ∀ μ, algebraMap R K (ϖ ^ e) * coeff μ P ∈ Set.range (algebraMap R K) := by
    refine ⟨n, fun μ => ?_⟩
    by_cases hμ : μ ∈ P.support
    · obtain ⟨r, hr⟩ := hb μ hμ
      refine ⟨(↑u⁻¹ : R) * r, ?_⟩
      rw [map_mul, hr, Algebra.smul_def, hbu, map_mul, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
        one_mul]
    · rw [notMem_support_iff.mp hμ, mul_zero]
      exact ⟨0, map_zero _⟩
  set e := Nat.find hex with he_def
  have he : ∀ μ, algebraMap R K (ϖ ^ e) * coeff μ P ∈ Set.range (algebraMap R K) := Nat.find_spec hex
  have he0 : e ≠ 0 := by
    intro h0
    apply hμ0
    simpa [h0] using he μ0
  have hmin : ¬ ∀ μ, algebraMap R K (ϖ ^ (e - 1)) * coeff μ P ∈ Set.range (algebraMap R K) :=
    Nat.find_min hex (by omega)
  push Not at hmin
  obtain ⟨μ1, hμ1⟩ := hmin

  obtain ⟨Q, hQ⟩ : C (algebraMap R K (ϖ ^ e)) * P ∈ Set.range (map (algebraMap R K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨ν, -, rfl⟩ := mem_coeffs_iff.mp ha
    rw [coeff_C_mul]
    exact he ν
  have hQc : ∀ μ, algebraMap R K (coeff μ Q) = algebraMap R K (ϖ ^ e) * coeff μ P := by
    intro μ
    rw [← coeff_map, hQ, coeff_C_mul]
  have hu1 : IsUnit (coeff μ1 Q) := by
    by_contra hnu
    have hmem : coeff μ1 Q ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
    obtain ⟨t, ht⟩ := hmem
    apply hμ1
    refine ⟨t, ?_⟩
    have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ0
    apply mul_left_cancel₀ hϖK
    rw [← map_mul, mul_comm, ht, hQc, ← mul_assoc, ← map_mul, ← pow_succ', Nat.sub_add_cancel (by omega)]

  set Qb : MvPolynomial (FrVar m) (ResidueField R) := map (residue R) Q with hQb
  let Dt : MvPolynomial (FrVar m) (ResidueField R) :=
    ∏ b, (Matrix.of fun (k i : Fin (m b)) => (X (⟨b, (i, k)⟩ : FrVar m) : MvPolynomial (FrVar m) (ResidueField R))).det
  have hDt : ∀ x : FrVar m → ResidueField R,
      eval x Dt = ∏ b, (Matrix.of fun (k i : Fin (m b)) => x ⟨b, (i, k)⟩).det := by
    intro x
    simp only [Dt, map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext k i
    simp [RingHom.mapMatrix_apply]
  have hQb0 : Qb ≠ 0 := by
    intro h0
    have := congrArg (coeff μ1) h0
    rw [hQb, coeff_map, coeff_zero] at this
    exact (residue_ne_zero_iff_isUnit _).mpr hu1 this
  have hDt0 : Dt ≠ 0 := by
    intro h0
    have := hDt (fun v => if v.2.1 = v.2.2 then 1 else 0)
    rw [h0, map_zero] at this
    have h1 : ∀ b, (Matrix.of fun (k i : Fin (m b)) =>
        (fun v : FrVar m => if v.2.1 = v.2.2 then (1 : ResidueField R) else 0) ⟨b, (i, k)⟩) = 1 := by
      intro b
      ext k i
      simp [Matrix.one_apply, eq_comm]
    simp only [h1, Matrix.det_one, Finset.prod_const_one] at this
    exact zero_ne_one this
  have hdeg : (Qb * Dt).totalDegree ≤ P.totalDegree + ∑ b, m b := by
    refine (totalDegree_mul _ _).trans (add_le_add ?_ ?_)
    · have hsub : Qb.support ⊆ P.support := by
        intro μ hμ
        rw [mem_support_iff] at hμ ⊢
        intro hP0
        apply hμ
        rw [hQb, coeff_map]
        have : coeff μ Q = 0 := hinj (by rw [hQc, hP0, mul_zero, map_zero])
        rw [this, map_zero]
      unfold totalDegree
      exact Finset.sup_mono hsub
    · refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      exact totalDegree_det_X_le (m b) _
  obtain ⟨S, hS⟩ := exists_finset_card_gt (k := ResidueField R) _ hcard
  obtain ⟨x, hx⟩ := exists_eval_ne_zero_of_totalDegree_lt (Qb * Dt) (mul_ne_zero hQb0 hDt0) S (by omega)
  rw [map_mul, hDt, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hx
  obtain ⟨hxQ, hxD⟩ := hx

  choose y hy using fun v => residue_surjective (R := R) (x v)
  let Xf : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R := fun b => Matrix.of fun k i => y ⟨b, (i, k)⟩
  have hdet : ∀ b, IsUnit (Xf b).det := by
    intro b
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det]
    convert hxD b (Finset.mem_univ _) using 2
    ext k i
    simp [Xf, RingHom.mapMatrix_apply, hy]
  have hyx : (residue R) ∘ y = x := funext hy
  have hQy : IsUnit (eval y Q) := by
    rw [← residue_ne_zero_iff_isUnit, map_eval, hyx]
    exact hxQ
  obtain ⟨r, hr⟩ := hval Xf hdet
  have hev : evalFr P (fun b => (Xf b).map (algebraMap R K)) = eval (algebraMap R K ∘ y) P := rfl
  have hyQ : eval y Q = ϖ ^ e * r := by
    apply hinj
    rw [map_eval, hQ, map_mul, eval_C, map_mul, hr, hev]
  rw [hyQ] at hQy
  exact hϖ.not_isUnit ((isUnit_pow_iff he0).mp (isUnit_of_mul_isUnit_left hQy))
end Formalism.L2.LamCM
