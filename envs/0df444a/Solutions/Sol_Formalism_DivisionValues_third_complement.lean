-- Prove2me | solution 1 for Formalism.DivisionValues.third_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:27:21.2428+00:00
-- url     : https://prove2.me/submissions/90654f6f-d71b-4671-be5a-a473808f8676

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_sum_top
import Theorems.Thm_Formalism_DivisionValues_phi_sum_difference_cluster
import Theorems.Thm_Formalism_DivisionValues_phi_difference_near_endpoint
import Theorems.Thm_Formalism_DivisionValues_third_complement_final_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution : Complement3 := by
  unfold Complement3
  intro U J Pl _ _ TT _ n hu hP logT hK aT nτ phν nν c mlam logκ cP cT e6 logOm logg cK w fa pr nr
    x eps L b a rd La B0 m f k N S Sc tt η w'' b' Δ C0 Hhu HhP HhK Hmlam Hphν Hnν Hc HSc0 HSc Hnk
    HaT HmΔ Hw HaTw HlogT HcT0 HcT Hnτ Hx Heps HL Hb Ha Hrd Hlogrd Hlogx HLa HB0 HJ HPl Hm Hf Hk
    HN HS Htt Hη Hb' hermFormPi_zeroTorus HlogOm H3 HkN HkS Hmη HNw Hmkb u u'
  have hm0 : 0 ≤ m := by linarith
  have hL1 : 1 ≤ L := by rw [HL]; exact Real.one_le_rpow Hx Heps.le
  have hb0 : 0 < b := by rw [Hb]; exact Real.exp_pos L
  have hx0 : 0 < x := by linarith
  have hapos : 0 < a := by rw [Ha]; exact mul_pos hx0 hb0
  have ha0 : 0 ≤ a := hapos.le
  have hLa_eq : La = Real.log x + L + Real.log rd := by
    rw [HLa, Real.log_mul hapos.ne' (by linarith : (0 : ℝ) < rd).ne', Ha,
      Real.log_mul hx0.ne' hb0.ne', Hb, Real.log_exp]
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg Hx
  have hlrd0 : 0 ≤ Real.log rd := Real.log_nonneg Hrd
  have hLLa : L ≤ La := by rw [hLa_eq]; linarith
  have hLa3 : La ≤ 3 * L := by rw [hLa_eq]; linarith
  have hLa0 : 0 ≤ La := by linarith
  have hB0' : B0 = f * m * b * L := by rw [HB0, HL]
  have hsT : ∑ ρ : Pl, (if ρ ∈ TT then b' else 0) = (TT.card : ℝ) * b' := by
    rw [← sum_top]; simp
  have hsT2 : ∑ ρ : Pl, (if ρ ∈ TT then 2 * (Δ * La) else 0) = (TT.card : ℝ) * (2 * (Δ * La)) := by
    rw [← sum_top]; simp
  have hX : 0 ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) := by
    apply mul_nonneg hermFormPi_zeroTorus
    apply add_nonneg (mul_nonneg (Nat.cast_nonneg _) Hb')
    apply mul_nonneg (Nat.cast_nonneg _)
    have := mul_nonneg hm0 Hη
    linarith
  have hP1gen : ∀ v, |((∑ ρ, (if ρ ∈ TT then aT v ρ else 0)) - ∑ ρ, nτ v ρ) * logT v| ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) * (C0 * m * L) := by
    intro v
    obtain ⟨hl0, hl1⟩ := HlogT v
    have hsum : |∑ ρ, (nτ v ρ - (if ρ ∈ TT then aT v ρ else 0))| ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) := by
      calc _ ≤ ∑ ρ, |nτ v ρ - (if ρ ∈ TT then aT v ρ else 0)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ ρ, C0 * ((if ρ ∈ TT then b' else 0) + S + m * η + N) :=
            Finset.sum_le_sum (fun ρ _ => Hnτ v ρ)
        _ = C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_congr rfl (fun ρ _ => (show (if ρ ∈ TT then b' else 0) + S + m * η + N =
              (if ρ ∈ TT then b' else 0) + (S + m * η + N) by ring)), Finset.sum_add_distrib, hsT]
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have e : ((∑ ρ, (if ρ ∈ TT then aT v ρ else 0)) - ∑ ρ, nτ v ρ) * logT v = -(∑ ρ, (nτ v ρ - (if ρ ∈ TT then aT v ρ else 0))) * logT v := by
      rw [Finset.sum_sub_distrib]; ring
    rw [e, abs_mul, abs_neg, abs_of_nonneg hl0]
    calc _ ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) * logT v := mul_le_mul_of_nonneg_right hsum hl0
      _ ≤ C0 * ((TT.card : ℝ) * b' + (Fintype.card Pl : ℝ) * (S + m * η + N)) * (C0 * m * L) := mul_le_mul_of_nonneg_left hl1 hX
  have hterm : ∀ j ρ, |(phν u j ρ - nν u j ρ * logOm) - (phν u' j ρ - nν u' j ρ * logOm)| ≤
      2 * (k * Sc * La) + (if ρ ∈ TT then 2 * (Δ * La) else 0) := by
    intro j ρ
    rw [Hphν u j ρ, Hphν u' j ρ, Hnν u j ρ, Hnν u' j ρ]
    obtain ⟨hw1, hwA⟩ := Hw j ρ
    have hcl := phi_sum_difference_cluster n (w j ρ) Sc (a * rd) La logOm (c u j ρ) (c u' j ρ) hw1 hwA
      (fun i => Hc u j ρ i) (fun i => Hc u' j ρ i) HLa hLa0 HlogOm
    have hnk : (n : ℝ) * (Sc * La) ≤ k * (Sc * La) :=
      mul_le_mul_of_nonneg_right Hnk (mul_nonneg HSc0 hLa0)
    rw [abs_le] at hcl
    split_ifs with hρ
    · obtain ⟨ha1, ha2⟩ := HaT u ρ hρ
      obtain ⟨hb1, hb2⟩ := HaT u' ρ hρ
      have htop := phi_difference_near_endpoint (w j ρ) a Δ (a * rd) La logOm (aT u ρ) (aT u' ρ) hw1 ha0 ⟨ha1, ha2⟩
        ⟨hb1, hb2⟩ (HaTw u j ρ hρ) (HaTw u' j ρ hρ) HLa hLa0 HlogOm
      rw [abs_le] at htop ⊢
      constructor <;> linarith [hcl.1, hcl.2, htop.1, htop.2]
    · rw [abs_le]
      constructor <;> linarith [hcl.1, hcl.2]
  have hMM : |∑ j, ∑ ρ, ((phν u j ρ - nν u j ρ * logOm) - (phν u' j ρ - nν u' j ρ * logOm))| ≤
      m * ((Fintype.card Pl : ℝ) * (2 * (k * Sc * La)) + (TT.card : ℝ) * (2 * (Δ * La))) := by
    calc _ ≤ ∑ j, |∑ ρ, ((phν u j ρ - nν u j ρ * logOm) - (phν u' j ρ - nν u' j ρ * logOm))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : J, ∑ ρ : Pl, (2 * (k * Sc * La) + (if ρ ∈ TT then 2 * (Δ * La) else 0)) :=
          Finset.sum_le_sum (fun j _ => le_trans (Finset.abs_sum_le_sum_abs _ _)
            (Finset.sum_le_sum (fun ρ _ => hterm j ρ)))
      _ = m * ((Fintype.card Pl : ℝ) * (2 * (k * Sc * La)) + (TT.card : ℝ) * (2 * (Δ * La))) := by
          simp only [Finset.sum_add_distrib, hsT2, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, HJ] <;> ring
  have hT : |m * cT * (logT u - logT u')| ≤ m * (C0 * (f * m ^ 2 * N ^ 2)) * (C0 * m * L) := by
    obtain ⟨a0, a1⟩ := HlogT u
    obtain ⟨b0, b1⟩ := HlogT u'
    have hd : |logT u - logT u'| ≤ C0 * m * L := by
      rw [abs_le]; constructor <;> linarith
    have hmc : 0 ≤ m * cT := mul_nonneg hm0 HcT0
    rw [abs_mul, abs_of_nonneg hmc]
    calc m * cT * |logT u - logT u'| ≤ m * cT * (C0 * m * L) := mul_le_mul_of_nonneg_left hd hmc
      _ ≤ m * (C0 * (f * m ^ 2 * N ^ 2)) * (C0 * m * L) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left HcT hm0
  have hid : (hu u + ∑ t ∈ TT, aT u t * logT u) - (hu u' + ∑ t ∈ TT, aT u' t * logT u') =
      ((∑ ρ, (if ρ ∈ TT then aT u ρ else 0)) - ∑ ρ, nτ u ρ) * logT u - ((∑ ρ, (if ρ ∈ TT then aT u' ρ else 0)) - ∑ ρ, nτ u' ρ) * logT u' + ∑ j, ∑ ρ, ((phν u j ρ - nν u j ρ * logOm) - (phν u' j ρ - nν u' j ρ * logOm)) + m * cT * (logT u - logT u') := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_top TT (aT u), sum_top TT (aT u'), Hhu u, Hhu u',
      HhP u, HhP u']
    simp only [HhK, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, HJ] <;> ring
  rw [hid]
  exact third_complement_final_bound C0 (TT.card : ℝ) a La m B0 f b L S Sc η N k w'' b' Δ tt _ _ _ _
    (Fintype.card Pl : ℝ) hB0' Hf Hm hL1 hb0.le (Nat.cast_nonneg _) ha0 hLLa hLa3 Hk HN HS HSc Htt Hη
    Hb' (Nat.cast_nonneg _) HPl H3 HkN HkS Hmη HNw Hmkb HmΔ (hP1gen u) (hP1gen u') hMM hT
end Formalism.DivisionValues
