-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodMinLeOfProdRatio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:23.860296+00:00
-- url     : https://prove2.me/submissions/54cc2e19-dfec-4b7a-9f78-f7544c5d4b53

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hyperbolicPairRatioLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : SmallTerm := by
  intro ι _ sh₁ ch₁ sh₂ ch₂ T T' g hT hT' hg h₁ h₂ hprod
  have hmin : ∀ x : ℝ, 0 < x → min (T' * x ^ 2) T' = T' * (min 1 x) ^ 2 := by
    intro x hx
    rcases le_total x 1 with h | h
    · have hx2 : x ^ 2 ≤ 1 := by nlinarith
      rw [min_eq_right h, min_eq_left (mul_le_of_le_one_right hT'.le hx2)]
    · have hx2 : 1 ≤ x ^ 2 := by nlinarith
      rw [min_eq_left h, min_eq_right (le_mul_of_one_le_right hT'.le hx2), one_pow, mul_one]
  have hm₁ : ∀ v, 0 < min 1 (sh₁ v) := fun v => lt_min one_pos (h₁ v).1
  have hm₂ : ∀ v, 0 < min 1 (sh₂ v) := fun v => lt_min one_pos (h₂ v).1
  have hPm : 0 < ∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v)) :=
    Finset.prod_pos (fun v _ => mul_pos (hm₁ v) (hm₂ v))
  have hbound : Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι ≤
      4 ^ Fintype.card ι / ∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v)) := by
    refine hprod.trans ?_
    calc ∏ v, (ch₁ v + ch₂ v) / (sh₁ v * sh₂ v)
          ≤ ∏ v, (4 / (min 1 (sh₁ v) * min 1 (sh₂ v))) :=
          Finset.prod_le_prod
            (fun v _ => div_nonneg (add_nonneg (h₁ v).2.1 (h₂ v).2.1)
              (mul_pos (h₁ v).1 (h₂ v).1).le)
            (fun v _ => hyperbolicPairRatioLe _ _ _ _ (h₁ v).1 (h₁ v).2.1 (h₁ v).2.2
              (h₂ v).1 (h₂ v).2.1 (h₂ v).2.2)
      _ = 4 ^ Fintype.card ι / ∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v)) := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hsq : Real.sqrt (T * T' / g ^ 2) ^ 2 = T * T' / g ^ 2 := Real.sq_sqrt (by positivity)
  have hk1 : (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) * Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι ≤
      4 ^ Fintype.card ι := by
    rw [le_div_iff₀ hPm] at hbound; linarith
  have hk2 : (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2 * (T * T' / g ^ 2) ^ Fintype.card ι ≤
      16 ^ Fintype.card ι := by
    have h0 : 0 ≤ (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) *
        Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι := by positivity
    have := pow_le_pow_left₀ h0 hk1 2
    calc (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2 * (T * T' / g ^ 2) ^ Fintype.card ι
          = ((∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) *
              Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι) ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul, hsq]
      _ ≤ (4 ^ Fintype.card ι) ^ 2 := this
      _ = 16 ^ Fintype.card ι := by
          rw [← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul]; norm_num
  have hsq2 : Real.sqrt (T' / T) ^ 2 = T' / T := Real.sq_sqrt (by positivity)
  have hab : (∏ v, min (T' * sh₁ v ^ 2) T') * (∏ v, min (T' * sh₂ v ^ 2) T') ≤
      ((4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι) ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    have e : ∀ v, min (T' * sh₁ v ^ 2) T' * min (T' * sh₂ v ^ 2) T' =
        T' ^ 2 * (min 1 (sh₁ v) * min 1 (sh₂ v)) ^ 2 := by
      intro v; rw [hmin _ (h₁ v).1, hmin _ (h₂ v).1]; ring
    simp only [e]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
    have hc : T * T' / g ^ 2 * (T' / T * g ^ 2) = T' ^ 2 := by
      first | (field_simp; ring) | field_simp
    calc (T' ^ 2) ^ Fintype.card ι * (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2
          = ((∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2 * (T * T' / g ^ 2) ^ Fintype.card ι) *
            (T' / T * g ^ 2) ^ Fintype.card ι := by
          rw [mul_assoc, ← mul_pow, hc]; ring
      _ ≤ 16 ^ Fintype.card ι * (T' / T * g ^ 2) ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ = ((4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι) ^ 2 := by
          rw [← mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul]
          congr 1
          rw [mul_pow, mul_pow, hsq2]; ring
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hc0 : 0 ≤ (4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι := by positivity
  have := mul_lt_mul'' ha hb hc0 hc0
  nlinarith
end Formalism.HermitianLatticeCounting.P
