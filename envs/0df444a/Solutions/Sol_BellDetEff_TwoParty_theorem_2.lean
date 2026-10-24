-- Prove2me | solution 1 for BellDetEff.TwoParty.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:22:45.299703+00:00
-- url     : https://prove2.me/submissions/f01f9702-d8d8-4698-be5d-3f25230820ba

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_Efficiency
import Theorems.Thm_BellDetEff_TwoParty_eqs_13_14_witness
import Theorems.Thm_BellDetEff_TwoParty_eq_15
import Theorems.Thm_BellDetEff_TwoParty_lhv_bound

namespace BellDetEff.TwoParty.ThresholdProof

open MeasureTheory

noncomputable def noneModel (OA OB : Type) [Fintype OA] [Fintype OB] (MA MB : ℕ) :
    LHVModel (Option OA) (Option OB) MA MB := by
  classical
  exact {
    Λ := Unit
    μ := Measure.dirac ()
    pA := fun _ _ a => if a = none then 1 else 0
    pB := fun _ _ b => if b = none then 1 else 0
    measurable_pA := fun _ _ => measurable_const
    measurable_pB := fun _ _ => measurable_const
    pA_nonneg := by intros; split <;> positivity
    pA_sum := by intros; simp
    pB_nonneg := by intros; split <;> positivity
    pB_sum := by intros; simp }

lemma withEff_zero_simulable {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (p : OA → OB → Fin MA → Fin MB → ℝ) : LHVSimulable (withEff p 0) := by
  classical
  refine ⟨noneModel OA OB MA MB, ?_⟩
  intro a b x y
  change withEff p 0 a b x y =
    ∫ _ : Unit, (if a = none then (1 : ℝ) else 0) *
      (if b = none then (1 : ℝ) else 0) ∂Measure.dirac ()
  cases a <;> cases b <;> simp [withEff]

lemma effThreshold_nonneg {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (p : OA → OB → Fin MA → Fin MB → ℝ) : 0 ≤ effThreshold p := by
  apply le_csSup
  · exact ⟨1, fun _ h => h.2.1⟩
  · exact ⟨le_rfl, zero_le_one, withEff_zero_simulable p⟩

lemma witness_threshold_le (P MA MB : ℕ) [Fact P.Prime]
    (hA : 1 ≤ MA) (hB : 1 ≤ MB) (hAB : 2 ≤ MA * MB) (hAP : MA ≤ P) (hBP : MB ≤ P) :
    effThreshold (witnessBox P MA MB) ≤
      ((MA : ℝ) + MB - 2) / ((MA : ℝ) * MB - 1) := by
  have ha : (1 : ℝ) ≤ MA := by exact_mod_cast hA
  have hb : (1 : ℝ) ≤ MB := by exact_mod_cast hB
  have hab : (2 : ℝ) ≤ (MA : ℝ) * MB := by exact_mod_cast hAB
  have hd : 0 < (MA : ℝ) * MB - 1 := by linarith
  have hn : 0 ≤ (MA : ℝ) + MB - 2 := by linarith
  apply csSup_le
  · exact ⟨0, le_rfl, zero_le_one, withEff_zero_simulable _⟩
  · intro η hη
    have hbell := lhv_bound P MA MB hAP hBP (withEff (witnessBox P MA MB) η) hη.2.2
    rw [eq_15 P MA MB hA hB hAP hBP η] at hbell
    by_cases hz : η = 0
    · subst η
      exact div_nonneg hn hd.le
    · have hp : 0 < η := lt_of_le_of_ne hη.1 (Ne.symm hz)
      apply (le_div_iff₀ hd).mpr
      have hm : η * (η * ((MA : ℝ) * MB - 1) - ((MA : ℝ) + MB - 2)) ≤ 0 := by
        nlinarith [hbell]
      have := nonpos_of_mul_nonpos_right hm hp
      linarith

end BellDetEff.TwoParty.ThresholdProof

open BellDetEff.TwoParty BellDetEff.TwoParty.ThresholdProof

theorem solution (MA MB : ℕ) (hA : 1 ≤ MA) (hB : 1 ≤ MB) (hAB : 2 ≤ MA * MB) :
    etaStarNS MA MB ≤ ((MA : ℝ) + MB - 2) / ((MA : ℝ) * MB - 1) := by
  obtain ⟨P, hPmax, hPprime⟩ := Nat.exists_infinite_primes (max MA MB)
  let : Fact P.Prime := ⟨hPprime⟩
  have hAP : MA ≤ P := (le_max_left _ _).trans hPmax
  have hBP : MB ≤ P := (le_max_right _ _).trans hPmax
  have hprob := eqs_13_14_witness P MA MB
  calc
    etaStarNS MA MB ≤ effThreshold (witnessBox P MA MB) := by
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro e ⟨KA, KB, p, _, _, rfl⟩
        exact effThreshold_nonneg p
      · exact ⟨P, P, witnessBox P MA MB, hprob.1, hprob.2.1, rfl⟩
    _ ≤ _ := witness_threshold_le P MA MB hA hB hAB hAP hBP
