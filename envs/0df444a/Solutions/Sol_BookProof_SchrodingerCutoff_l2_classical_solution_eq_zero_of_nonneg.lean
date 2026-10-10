-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.l2_classical_solution_eq_zero_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:57:01.841187+00:00
-- url     : https://prove2.me/submissions/c7d4e755-6737-4d60-8341-ffa440335b0c

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.l2_classical_solution_eq_zero_of_nonneg
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_exists_deriv_chi_bound
import Theorems.Thm_BookProof_SchrodingerCutoff_cutoff_energy_core
import Theorems.Thm_BookProof_SchrodingerCutoff_eq_zero_of_setIntegral_Icc_eq_zero
import Definitions.Def_ChapterParityChirality
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex
open BookProof.ChapterParityChirality

set_option maxHeartbeats 1000000 in
theorem solution
    (V : ℝ → ℝ) (hV : Continuous V) (z : ℂ)
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x + (V x : ℂ) * u x = z * u x)
    (hVz : ∀ x, 0 ≤ V x - z.re)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 := by
    obtain ⟨C, hC0, hC⟩ := exists_deriv_chi_bound
    have hud : Differentiable ℝ u := fun x => (h1 x).differentiableAt
    have hu'd : Differentiable ℝ u' := fun x => (h2 x).differentiableAt
    have hu'cont : Continuous u' := hu'd.continuous
    have hg : Continuous fun x => ‖u' x‖ ^ 2 := by fun_prop
    set A : ℝ := ∫ x, ‖u x‖ ^ 2 with hAdef
    have hA0 : 0 ≤ A := integral_nonneg fun x => by positivity
    have hzero : ∀ n : ℕ, ∫ x in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ‖u' x‖ ^ 2 = 0 := by
      intro n
      set R0 : ℝ := (n : ℝ) + 1 with hR0def
      have hR0pos : (0 : ℝ) < R0 := by positivity
      have hle : ∀ m : ℕ, (∫ x in Set.Icc (-R0) R0, ‖u' x‖ ^ 2)
          ≤ 4 * C ^ 2 / ((m : ℝ) + R0) ^ 2 * A := by
        intro m
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hRpos : (0 : ℝ) < (m : ℝ) + R0 := by linarith
        have hsub : Set.Icc (-R0) R0 ⊆ Set.Icc (-((m : ℝ) + R0)) ((m : ℝ) + R0) :=
          Set.Icc_subset_Icc (by linarith) (by linarith)
        have hstep := setIntegral_mono_set (hg.integrableOn_Icc (μ := volume))
          (Filter.Eventually.of_forall fun x => by positivity) hsub.eventuallyLE
        exact le_trans hstep
          (cutoff_energy_core V hV z u u' u'' h1 h2 heq hVz hL2 hC hRpos).2
      have htend : Tendsto (fun m : ℕ => 4 * C ^ 2 / ((m : ℝ) + R0) ^ 2 * A) atTop (nhds 0) := by
        have hnn : Tendsto (fun m : ℕ => ((m : ℝ) + R0) ^ 2) atTop atTop :=
          (tendsto_pow_atTop (n := 2) (by norm_num)).comp
            (tendsto_atTop_add_const_right _ R0 tendsto_natCast_atTop_atTop)
        have h := (tendsto_const_nhds (x := 4 * C ^ 2 * A) (f := atTop (α := ℕ))).div_atTop hnn
        exact h.congr fun m => by ring
      have hle0 : (∫ x in Set.Icc (-R0) R0, ‖u' x‖ ^ 2) ≤ 0 :=
        ge_of_tendsto htend (Filter.Eventually.of_forall hle)
      have hge0 : (0 : ℝ) ≤ ∫ x in Set.Icc (-R0) R0, ‖u' x‖ ^ 2 :=
        setIntegral_nonneg measurableSet_Icc fun x _ => by positivity
      linarith
    have hu'zero : (fun x => ‖u' x‖ ^ 2) = 0 :=
      eq_zero_of_setIntegral_Icc_eq_zero hg (fun x => by positivity) hzero
    have hu'0 : ∀ x, u' x = 0 := by
      intro x
      have hx : ‖u' x‖ ^ 2 = 0 := congrFun hu'zero x
      have : ‖u' x‖ = 0 := by nlinarith [norm_nonneg (u' x)]
      simpa using this
    have hconst : ∀ x, u x = u 0 :=
      fun x => is_const_of_deriv_eq_zero hud (fun y => by rw [(h1 y).deriv, hu'0 y]) x 0
    have hL2' : Integrable fun _ : ℝ => ‖u 0‖ ^ 2 := by
      refine hL2.congr ?_
      filter_upwards with x using by rw [hconst x]
    have hc : ‖u 0‖ ^ 2 = 0 := by
      rcases integrable_const_iff.mp hL2' with h | h
      · exact h
      · exact absurd h.measure_univ_lt_top (by rw [Real.volume_univ]; exact lt_irrefl _)
    have hu0 : u 0 = 0 := by
      have : ‖u 0‖ = 0 := by nlinarith [norm_nonneg (u 0)]
      simpa using this
    funext x
    simpa [hu0] using hconst x
