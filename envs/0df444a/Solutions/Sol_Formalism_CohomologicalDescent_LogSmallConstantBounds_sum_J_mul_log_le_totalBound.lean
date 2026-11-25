-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_J_mul_log_le_totalBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:52.893802+00:00
-- url     : https://prove2.me/submissions/fa0c9c30-7a91-4860-b5b5-09ec05145b1f

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLargePrime_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_exceptionalCount_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_prime_nonneg
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_thinSum_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_costBound_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution (rs3 : PrimeCountingBound) {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} [Fintype ι]
    {D : SizeData₂ ι} (I : D.Inputs P) (XC XD : ℝ)
    (hXC : ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ (l : ℝ) ≤ P.lJ) →
      ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ XC)
    (hXD : ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) →
      ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
        XD + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2))
    (Q : Finset ℕ) (hQ : ∀ l ∈ Q, l.Prime) :
    ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤ totalBound P D.T2.card (XC + XD) := by
  have hb' := H.b'_pos
  have hL := G.L_ge
  obtain ⟨A, hAd⟩ : ∃ A : Finset ℕ, A = Q.filter (fun l : ℕ => (l : ℝ) ≤ P.lJ) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : Finset ℕ, B = Q.filter (fun l : ℕ => ¬ (l : ℝ) ≤ P.lJ) := ⟨_, rfl⟩
  obtain ⟨E, hEd⟩ : ∃ E : Finset ℕ, E = B.filter (fun l : ℕ => P.Excl l ∨ l ∈ D.Sp) := ⟨_, rfl⟩
  obtain ⟨W, hWd⟩ : ∃ W : Finset ℕ, W = B.filter (fun l : ℕ => ¬ (P.Excl l ∨ l ∈ D.Sp)) := ⟨_, rfl⟩
  have hQ1 : ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) =
      ∑ l ∈ A, (D.J l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ B, (D.J l : ℝ) * Real.log (l : ℝ) := by
    rw [hAd, hBd, Finset.sum_filter_add_sum_filter_not]
  have hB1 : ∑ l ∈ B, (D.J l : ℝ) * Real.log (l : ℝ) =
      ∑ l ∈ E, (D.J l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (D.J l : ℝ) * Real.log (l : ℝ) := by
    rw [hEd, hWd, Finset.sum_filter_add_sum_filter_not]
  have memA : ∀ l ∈ A, l.Prime ∧ (l : ℝ) ≤ P.lJ := by
    intro l hl
    rw [hAd, Finset.mem_filter] at hl
    exact ⟨hQ l hl.1, hl.2⟩
  have memE : ∀ l ∈ E, l.Prime ∧ P.lJ < (l : ℝ) ∧ (P.Excl l ∨ l ∈ D.Sp) := by
    intro l hl
    rw [hEd, Finset.mem_filter, hBd, Finset.mem_filter] at hl
    exact ⟨hQ l hl.1.1, not_le.1 hl.1.2, hl.2⟩
  have memW : ∀ l ∈ W, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l ∧ l ∉ D.Sp := by
    intro l hl
    rw [hWd, Finset.mem_filter, hBd, Finset.mem_filter] at hl
    push_neg at hl
    exact ⟨hQ l hl.1.1, hl.1.2, hl.2.1, hl.2.2⟩
  have hdisj : Disjoint A W := by
    rw [Finset.disjoint_left]
    intro l ha hw
    have h1 := (memA l ha).2
    have h2 := (memW l hw).2.1
    linarith
  have hfNL : 0 ≤ (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L := mul_nonneg (by positivity) (by linarith)
  have bE : ∑ l ∈ E, (D.J l : ℝ) * Real.log (l : ℝ) ≤ (E.card : ℝ) * ((P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L) := by
    calc ∑ l ∈ E, (D.J l : ℝ) * Real.log (l : ℝ) ≤ ∑ _l ∈ E, (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L := by
          apply Finset.sum_le_sum
          intro l hl
          obtain ⟨hp, _, hES⟩ := memE l hl
          have hJ : (D.J l : ℝ) ≤ ∑ τ, (D.ex τ l : ℝ) := by
            exact_mod_cast I.boundA l hp (Or.inr hES)
          exact (mul_le_mul_of_nonneg_right hJ (log_prime_nonneg hp)).trans
            (costBound_holds P H G ι D I.card_ι I.thinA I.thickA I.widths l hp)
      _ = (E.card : ℝ) * ((P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hEsub : E ⊆ E.filter (fun l : ℕ => P.Excl l) ∪ D.Sp := by
    intro l hl
    rw [Finset.mem_union, Finset.mem_filter]
    rcases (memE l hl).2.2 with h | h
    · exact Or.inl ⟨hl, h⟩
    · exact Or.inr h
  have hEcard : E.card ≤ (E.filter (fun l : ℕ => P.Excl l)).card + D.Sp.card :=
    (Finset.card_le_card hEsub).trans (Finset.card_union_le _ _)
  have hEx := exceptionalCount_holds P H G (E.filter (fun l : ℕ => P.Excl l)) (fun l hl => by
    rw [Finset.mem_filter] at hl
    exact ⟨(memE l hl.1).1, (memE l hl.1).2.1, hl.2⟩)
  have hEcardR : (E.card : ℝ) ≤ P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6 := by
    have h1 : (E.card : ℝ) ≤ ((E.filter (fun l : ℕ => P.Excl l)).card : ℝ) + (D.Sp.card : ℝ) := by
      exact_mod_cast hEcard
    have h2 : (D.Sp.card : ℝ) ≤ 5 := by exact_mod_cast I.card_Sp
    linarith
  have bE' := mul_le_mul_of_nonneg_right hEcardR hfNL
  have hAW : ∑ l ∈ A, (D.J l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (D.J l : ℝ) * Real.log (l : ℝ) ≤
      ∑ τ : ι, (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) := by
    calc ∑ l ∈ A, (D.J l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (D.J l : ℝ) * Real.log (l : ℝ)
        ≤ ∑ l ∈ A, ∑ τ : ι, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, ∑ τ : ι, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ) := by
          apply add_le_add
          · apply Finset.sum_le_sum
            intro l hl
            obtain ⟨hp, hle⟩ := memA l hl
            have hJ : (D.J l : ℝ) ≤ ∑ τ, (D.ex τ l : ℝ) := by
              exact_mod_cast I.boundA l hp (Or.inl hle)
            rw [← Finset.sum_mul]
            exact mul_le_mul_of_nonneg_right hJ (log_prime_nonneg hp)
          · apply Finset.sum_le_sum
            intro l hl
            obtain ⟨hp, hlt, hEx', hSp⟩ := memW l hl
            obtain ⟨_, _, _, h4, _, h6, _, h8⟩ := paramsLargePrime_holds P H G l hlt
            have hJ := I.boundW l hp hlt hEx' hSp h8 h6 h4
            rw [← Finset.sum_mul]
            exact mul_le_mul_of_nonneg_right hJ (log_prime_nonneg hp)
      _ = ∑ τ : ι, ∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ τ : ι, ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ) := by
          congr 1 <;> exact Finset.sum_comm
      _ = ∑ τ : ι, (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) :=
          (Finset.sum_add_distrib).symm
  have top_degree_le_two_b : ∀ τ ∈ D.T2, (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) ≤
      XC + (XD + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)) := by
    intro τ hτ
    have e : ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ) = ∑ l ∈ W, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) :=
      Finset.sum_congr rfl (fun l _ => by rw [if_pos hτ])
    rw [e]
    exact add_le_add (hXC τ hτ A memA)
      (hXD τ hτ W (fun l hl => ⟨(memW l hl).1, (memW l hl).2.1, (memW l hl).2.2.1⟩))
  have bN : ∀ τ, τ ∉ D.T2 → (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) ≤
      1.3 * (P.Nr : ℝ) ^ 2 * P.b' := by
    intro τ hτ
    have e : ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ) = ∑ l ∈ W, (D.ex τ l : ℝ) * Real.log (l : ℝ) :=
      Finset.sum_congr rfl (fun l _ => by rw [if_neg hτ])
    rw [e, ← Finset.sum_union hdisj]
    refine thinSum_holds rs3 P H G ι D I.thinA I.widths τ hτ (A ∪ W) (fun l hl => ?_)
    rcases Finset.mem_union.1 hl with h | h
    · exact (memA l h).1
    · exact (memW l h).1
  have hY0 : 0 ≤ 1.3 * (P.Nr : ℝ) ^ 2 * P.b' := mul_nonneg (by positivity) hb'.le
  have hF : Finset.univ.filter (fun τ => τ ∈ D.T2) = D.T2 := by
    ext τ
    simp
  have hcard2 : (Finset.univ.filter (fun τ => ¬ τ ∈ D.T2)).card ≤ P.f := by
    rw [← I.card_ι]
    exact Finset.card_le_univ _
  have hcard2R : ((Finset.univ.filter (fun τ => ¬ τ ∈ D.T2)).card : ℝ) ≤ P.f := by
    exact_mod_cast hcard2
  have hsumτ : ∑ τ : ι, (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) ≤
      (D.T2.card : ℝ) * (XC + (XD + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)))
        + (P.f : ℝ) * (1.3 * (P.Nr : ℝ) ^ 2 * P.b') := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => τ ∈ D.T2)]
    refine le_trans (add_le_add (Finset.sum_le_sum (fun τ hτ => top_degree_le_two_b τ (Finset.mem_filter.1 hτ).2))
      (Finset.sum_le_sum (fun τ hτ => bN τ (Finset.mem_filter.1 hτ).2))) ?_
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hF]
    nlinarith [mul_le_mul_of_nonneg_right hcard2R hY0]
  rw [hQ1, hB1]
  unfold totalBound
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
