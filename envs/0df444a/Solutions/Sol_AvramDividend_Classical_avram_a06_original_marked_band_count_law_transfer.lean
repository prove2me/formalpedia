-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_marked_band_count_law_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:22:24.86388+00:00
-- url     : https://prove2.me/submissions/beefbad2-f9e1-4ebf-9e99-cb7b168bf111

import Mathlib.Probability.IdentDistrib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_vector_mark_independent
import Theorems.Thm_AvramDividend_Classical_avram_a06_generic_indep_same_count_law_prefix_sum
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_stationary_increment_law
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_jumpCount_zero_at_origin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Transfer the original stationary count-increment law through
    independence from the original marks and the zero-time endpoint. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.range
        ((LevyFoundations.jumpCount
          (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ)) -
          (LevyFoundations.jumpCount
          (fun j => LevyFoundations.arrival τ j ω) (s : ℝ))), Y j ω)
      (fun ω => ∑ j ∈ Finset.Ico
        (LevyFoundations.jumpCount
          (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ))
        (LevyFoundations.jumpCount
          (fun j => LevyFoundations.arrival τ j ω) (k : ℝ)), Y j ω) P P := by
  let M : ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ → ℝ := fun ω j => Y j ω
  let N (a b : ℝ≥0) : ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ := fun ω =>
    LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (b : ℝ) -
    LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (a : ℝ)
  have hInd (a b : ℝ≥0) : IndepFun (N a b) M P := by
    let t : Fin 2 → ℝ≥0 := fun i => if i = 0 then a else b
    have hvec := AvramDividend.Classical.avram_a06_original_cp_count_vector_mark_independent
      P τ Y hd 2 t
    have h1 : Measurable (fun v : Fin 2 → ℕ => v 1) := measurable_pi_apply 1
    have h0 : Measurable (fun v : Fin 2 → ℕ => v 0) := measurable_pi_apply 0
    have hdiff : Measurable (fun v : Fin 2 → ℕ => v 1 - v 0) := by
      fun_prop
    have hcomp := hvec.comp hdiff measurable_id
    change IndepFun (N a b) M P at hcomp
    change IndepFun (N a b) M P
    exact hcomp
  have hLaw : IdentDistrib (N s (s + k)) (N 0 k) P P :=
    AvramDividend.Classical.avram_a06_original_cp_count_stationary_increment_law
      P τ Y hd s k
  have hM : AEMeasurable M P :=
    (aemeasurable_pi_iff).2 (fun j => (hd.law_mark j).aemeasurable)
  have hPrefix :=
    AvramDividend.Classical.avram_a06_generic_indep_same_count_law_prefix_sum
      P (N s (s + k)) (N 0 k) M
      hLaw.aemeasurable_fst hLaw.aemeasurable_snd hM
      (hInd s (s + k)) (hInd 0 k) hLaw
  have hZero := AvramDividend.Classical.avram_a06_original_cp_jumpCount_zero_at_origin
    P τ Y hd
  have heq : (fun ω => ∑ j ∈ Finset.range (N 0 k ω), Y j ω) =ᵐ[P]
      (fun ω => ∑ j ∈ Finset.Ico
        (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ))
        (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (k : ℝ)),
        Y j ω) := by
    filter_upwards [hZero] with ω hz
    simp [N, hz]
  have hR := IdentDistrib.of_ae_eq hPrefix.aemeasurable_snd heq
  exact hPrefix.trans hR
