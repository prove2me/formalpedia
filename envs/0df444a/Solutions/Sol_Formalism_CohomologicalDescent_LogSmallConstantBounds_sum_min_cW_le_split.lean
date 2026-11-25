-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_min_cW_le_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:28.433469+00:00
-- url     : https://prove2.me/submissions/e7014666-73a1-41b7-afc2-38793769db4b

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLargePrime_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_prime_nonneg
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_cW_eq_of_eq_zero

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
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hA : D.ThickA P) (hC : D.CloudA P) (hNW : D.NoWindow P) {τ : ι} (hτ : τ ∈ D.T2)
    {Q : Finset ℕ} (hQ : ∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) :
    ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
      ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (P.h + (P.Nr : ℝ)) *
          ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), Real.log (l : ℝ) / ((l : ℝ) - 1)
      + 6 * ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) *
          ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), Real.log (l : ℝ)
      + (P.k : ℝ) * P.S * ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), Real.log (l : ℝ) / (l : ℝ)
      + (P.k : ℝ) * ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h),
          IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ)
      + ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), gatedCoefficientTerm D P τ l * Real.log (l : ℝ)
      + (D.q τ : ℝ) * P.h * ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h),
          (1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ)) := by
  calc ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ)
      ≤ ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h),
            (((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (P.h + (P.Nr : ℝ)) * (Real.log (l : ℝ) / ((l : ℝ) - 1))
              + 6 * ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * Real.log (l : ℝ)
              + (P.k : ℝ) * P.S * (Real.log (l : ℝ) / (l : ℝ))
              + (P.k : ℝ) * (Formalism.CohomologicalDescent.IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ))
              + gatedCoefficientTerm D P τ l * Real.log (l : ℝ)
              + (D.q τ : ℝ) * P.h * ((1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ)))) := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro l hl
        obtain ⟨hp, hlJ, hEx⟩ := hQ l hl
        have hlog0 := log_prime_nonneg hp
        split_ifs with hlh
        · obtain ⟨_, _, _, _, _, _, hSk, _⟩ := paramsLargePrime_holds P H G l hlJ
          have hecl := hC τ hτ l hp hSk
          obtain ⟨hmw, hmwF⟩ := hNW l hp hlJ hEx τ
          have e := cW_eq_of_eq_zero D P τ l hmw hmwF hecl
          calc min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤ D.cW P τ l * Real.log (l : ℝ) :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hlog0
            _ = ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (P.h + (P.Nr : ℝ)) * (Real.log (l : ℝ) / ((l : ℝ) - 1))
              + 6 * ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * Real.log (l : ℝ)
              + (P.k : ℝ) * P.S * (Real.log (l : ℝ) / (l : ℝ))
              + (P.k : ℝ) * (Formalism.CohomologicalDescent.IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ))
              + gatedCoefficientTerm D P τ l * Real.log (l : ℝ)
              + (D.q τ : ℝ) * P.h * ((1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ))) := by
                rw [e]
                ring
        · have hex := (hA τ hτ l hp).1 (not_le.1 hlh)
          rw [hex, Nat.cast_zero]
          nlinarith [min_le_left (0 : ℝ) (D.cW P τ l)]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
end Formalism.CohomologicalDescent.LogSmallConstantBounds
