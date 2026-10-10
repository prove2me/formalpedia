-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.l2_classical_solution_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:57:46.504455+00:00
-- url     : https://prove2.me/submissions/6f6b194a-03cc-4f63-97ae-7555ade50ae1

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.l2_classical_solution_eq_zero
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_exists_deriv_chi_bound
import Theorems.Thm_BookProof_SchrodingerCutoff_cutoff_energy_estimate
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
    (hVz : ∀ x, 1 ≤ V x - z.re)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 := by
    obtain ⟨C, hC0, hC⟩ := exists_deriv_chi_bound
    have hud : Differentiable ℝ u := fun x => (h1 x).differentiableAt
    have hucont : Continuous u := hud.continuous
    set A : ℝ := ∫ x, ‖u x‖ ^ 2 with hAdef
    have hA0 : 0 ≤ A := integral_nonneg fun x => by positivity
    -- the sets `Icc (-(n+1)) (n+1)` increase to the line
    have hmono : Monotone fun n : ℕ => Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
      intro m n hmn
      have hmn' : ((m : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hmn
      exact Set.Icc_subset_Icc (by linarith) (by linarith)
    have hunion : (⋃ n : ℕ, Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact Set.mem_iUnion.mpr ⟨n, ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩⟩
    have htend : Tendsto (fun n : ℕ => ∫ x in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ‖u x‖ ^ 2)
        atTop (nhds A) := by
      have h := tendsto_setIntegral_of_monotone (fun _ : ℕ => measurableSet_Icc) hmono
        (by rw [hunion]; exact hL2.integrableOn)
      rwa [hunion, setIntegral_univ, ← hAdef] at h
    have hbnd : Tendsto (fun n : ℕ => 2 * C ^ 2 / ((n : ℝ) + 1) ^ 2 * A) atTop (nhds 0) := by
      have hnn : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (n := 2) (by norm_num)).comp
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      have h := (tendsto_const_nhds (x := 2 * C ^ 2 * A) (f := atTop (α := ℕ))).div_atTop hnn
      refine h.congr fun n => ?_
      ring
    have hAle : A ≤ 0 := by
      refine le_of_tendsto_of_tendsto' htend hbnd fun n => ?_
      exact cutoff_energy_estimate V hV z u u' u'' h1 h2 heq hVz hL2 hC
        (by positivity)
    have hAzero : A = 0 := le_antisymm hAle hA0
    have hae : (fun x => ‖u x‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hL2).mp hAzero
    have hu_ae : u =ᵐ[volume] 0 := by
      filter_upwards [hae] with x hx
      have : ‖u x‖ ^ 2 = 0 := hx
      have : ‖u x‖ = 0 := by nlinarith [norm_nonneg (u x)]
      simpa using this
    exact (Continuous.ae_eq_iff_eq volume hucont continuous_const).mp hu_ae
