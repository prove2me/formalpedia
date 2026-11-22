-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_61
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T09:58:21.671733+00:00
-- url     : https://prove2.me/submissions/22fcaea7-8d45-478f-821f-482fadc4f1a9

import Definitions.Def_GaussLocalMaxColoring_Main_Section5
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_61_branch_0
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_61_branch_1
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_61_branch_2
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_61_branch_3

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace GaussLocalMaxColoring.Certificate.Conclusion
open GaussLocalMaxColoring.Main
noncomputable section

theorem ftilde_monotoneOn : MonotoneOn ftilde (Set.Ici (1968/1000:ℝ)) := by
  intro a ha b hb hab
  change (1968/1000:ℝ) ≤ a at ha
  change (1968/1000:ℝ) ≤ b at hb
  have hfactor : 0 ≤ 52/100 + (246/100:ℝ)*(a+b-4) := by
    linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hab) hfactor
  have heq : ftilde b - ftilde a =
      (b-a) * (52/100 + (246/100:ℝ)*(a+b-4)) := by
    unfold ftilde
    ring
  exact sub_nonneg.mp (heq.symm ▸ hprod)

/-- Property (P1) of the original thresholds, on the paper's full A-range. -/
theorem fA_monotoneOn (ρ : ℝ) :
    MonotoneOn (fun A => fA A ρ) (Set.Ici (1968/1000:ℝ)) := by
  intro a ha b hb hab
  have h := mul_le_mul_of_nonneg_right (ftilde_monotoneOn ha hb hab)
    (Real.sqrt_nonneg (1-ρ^2))
  dsimp only [fA]
  linarith only [h]

def thresholdTailPolynomial (ρ : ℝ) : ℝ :=
  -(8/10)*(ρ-1/50) + 45/100*(ρ-1/50)^2 +
    39/100*(ρ-1/4) + 65/100*(ρ-1/4)^2

theorem thresholdTailPolynomial_monotoneOn :
    MonotoneOn thresholdTailPolynomial (Set.Ici (7/10:ℝ)) := by
  intro a ha b hb hab
  change (7/10:ℝ) ≤ a at ha
  change (7/10:ℝ) ≤ b at hb
  have hfac : 0 ≤ (11/10:ℝ)*(a+b)-753/1000 := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hab) hfac
  have heq : thresholdTailPolynomial b - thresholdTailPolynomial a =
      (b-a)*((11/10:ℝ)*(a+b)-753/1000) := by
    unfold thresholdTailPolynomial
    ring
  exact sub_nonneg.mp (heq.symm ▸ hprod)

/-- Original Lemma 60, proved at the paper's unchanged numerical constants. -/
theorem threshold_tail_public (A ρ : ℝ) (hA : (1968/1000:ℝ) ≤ A)
    (hlo : (7/10:ℝ) ≤ ρ) (hhi : ρ ≤ 1) : qc ρ < fA A ρ := by
  have hz1 : max (-(1/40:ℝ)-ρ) 0 = 0 := max_eq_right (by linarith)
  have hz2 : max (ρ-(1/50:ℝ)) 0 = ρ-1/50 := max_eq_left (by linarith)
  have hz3 : max (ρ-(1/4:ℝ)) 0 = ρ-1/4 := max_eq_left (by linarith)
  have hfa : fA A ρ = ftilde A * Real.sqrt (1-ρ^2) + thresholdTailPolynomial ρ := by
    simp only [fA, hz1, hz2, hz3, thresholdTailPolynomial]
    ring
  have hcap : capacity Da ρ = Da+1 := by
    simp only [capacity, if_neg (show ¬ ρ ≤ 0 by linarith),
      if_neg (show ¬ ρ ≤ 1/4 by linarith)]
  have hbase : 0 ≤ 1-ρ^2 := by nlinarith
  have hqc : qc ρ = Real.sqrt (1-ρ^2) * Real.sqrt (Da+5/4) := by
    rw [qc, hcap, show Da+1+(1/4:ℝ) = Da+5/4 by ring]
    exact Real.sqrt_mul hbase _
  have hF : (49/20:ℝ) ≤ ftilde A := by
    apply (show (49/20:ℝ) ≤ ftilde (1968/1000) by norm_num [ftilde]).trans
    exact ftilde_monotoneOn (by norm_num) hA hA
  have hroot : Real.sqrt (Da+5/4) ≤ (12/5:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · norm_num [Da, D5, beta5, eta5]
  have hgap : (1/20:ℝ) ≤ ftilde A - Real.sqrt (Da+5/4) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hgap (Real.sqrt_nonneg (1-ρ^2))
  rw [hfa, hqc]
  unfold thresholdTailPolynomial
  by_cases hsmall : ρ ≤ (147/200:ℝ)
  · have hP := thresholdTailPolynomial_monotoneOn
      (show (7/10:ℝ) ∈ Set.Ici (7/10:ℝ) by norm_num) hlo hlo
    norm_num [thresholdTailPolynomial] at hP
    have hsqrt : (678/1000:ℝ) ≤ Real.sqrt (1-ρ^2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    nlinarith only [hmul, hP, hsqrt]
  · have hr : (147/200:ℝ) ≤ ρ := (lt_of_not_ge hsmall).le
    have hP := thresholdTailPolynomial_monotoneOn
      (show (147/200:ℝ) ∈ Set.Ici (7/10:ℝ) by norm_num) hlo hr
    norm_num [thresholdTailPolynomial] at hP
    have hsqrt := Real.sqrt_nonneg (1-ρ^2)
    nlinarith only [hmul, hP, hsqrt]

theorem threshold_tail_qA (A ρ : ℝ) (hA : (1968/1000:ℝ) ≤ A)
    (hlo : (7/10:ℝ) ≤ ρ) (hhi : ρ ≤ 1) : qA A ρ = qc ρ :=
  min_eq_left (threshold_tail_public A ρ hA hlo hhi).le

theorem lemma61_of_threshold_branches
    (h0 : ∀ ρ : ℝ, ρ ∈ Set.Icc (-(1/2):ℝ) (-(1/40)) → qc ρ < fA (43/20) ρ)
    (h1 : ∀ ρ : ℝ, ρ ∈ Set.Icc (-(1/40):ℝ) (1/50) → qc ρ < fA (43/20) ρ)
    (h2 : ∀ ρ : ℝ, ρ ∈ Set.Icc (1/50:ℝ) (1/4) → qc ρ < fA (43/20) ρ)
    (h3 : ∀ ρ : ℝ, ρ ∈ Set.Icc (1/4:ℝ) (7/10) → qc ρ < fA (43/20) ρ)
    (A ρ : ℝ) (hA : (43/20:ℝ) ≤ A) (_hA0 : A ≤ A0)
    (hρ : ρ ∈ Set.Icc (-(1/2):ℝ) 1) : qA A ρ = qc ρ := by
  have hstrict : qc ρ < fA A ρ := by
    by_cases hsmall : ρ ≤ (7/10:ℝ)
    · have hfixed : qc ρ < fA (43/20) ρ := by
        by_cases hneg : ρ ≤ (-(1/40):ℝ)
        · exact h0 ρ ⟨hρ.1,hneg⟩
        have hneg' := (lt_of_not_ge hneg).le
        by_cases hcore : ρ ≤ (1/50:ℝ)
        · exact h1 ρ ⟨hneg',hcore⟩
        have hcore' := (lt_of_not_ge hcore).le
        by_cases hpos : ρ ≤ (1/4:ℝ)
        · exact h2 ρ ⟨hcore',hpos⟩
        exact h3 ρ ⟨(lt_of_not_ge hpos).le,hsmall⟩
      exact hfixed.trans_le (fA_monotoneOn ρ (by norm_num)
        (by change (1968/1000:ℝ) ≤ A; linarith) hA)
    · exact threshold_tail_public A ρ (by linarith) (lt_of_not_ge hsmall).le hρ.2
  exact min_eq_left hstrict.le

#print axioms lemma61_of_threshold_branches

end
end GaussLocalMaxColoring.Certificate.Conclusion

open GaussLocalMaxColoring.Main
theorem solution (A ρ : ℝ) (hA : (43/20:ℝ) ≤ A) (hA0 : A ≤ A0)
    (hρ : ρ ∈ Set.Icc (-(1/2):ℝ) 1) : qA A ρ = qc ρ := by
  exact GaussLocalMaxColoring.Certificate.Conclusion.lemma61_of_threshold_branches
    GaussLocalMaxColoring.Main.lemma_61_branch_0
    GaussLocalMaxColoring.Main.lemma_61_branch_1
    GaussLocalMaxColoring.Main.lemma_61_branch_2
    GaussLocalMaxColoring.Main.lemma_61_branch_3 A ρ hA hA0 hρ
#print axioms solution
