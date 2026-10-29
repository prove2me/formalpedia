-- Prove2me | solution 1 for AvramDividend.Classical.chat04_alpha_tilted_grid_stopped_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:23:46.793016+00:00
-- url     : https://prove2.me/submissions/fb3c396d-f339-41f7-a6c6-3212b8bd5255

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_first_crossing_martingale_identity

open MeasureTheory Set
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {G : Filtration ℕ mΩ} [SigmaFiniteFiltration P G]
    (Y M : ℕ → Ω → ℝ) (hY : Adapted G Y)
    (hM : Martingale M G P) (hMI : ∀ k, Integrable (M k) P)
    (b a : ℝ) (N : ℕ) :
    (∫ ω, b ^ (hittingBtwn Y (Set.Ioi a) 0 N ω) *
        M (hittingBtwn Y (Set.Ioi a) 0 N ω) ω -
      (b - 1) * (∑ k ∈ Finset.range N,
        if k < hittingBtwn Y (Set.Ioi a) 0 N ω then b ^ k * M k ω else 0) ∂P) =
      ∫ ω, M 0 ω ∂P := by
  set Z : ℕ → Ω → ℝ := fun n ω => b ^ n * M n ω - (b - 1) * ∑ k ∈ Finset.range n, b ^ k * M k ω with hZ
  have hMa : StronglyAdapted G M := hM.1
  have hZad : StronglyAdapted G Z := by
    intro n
    refine ((hMa n).const_mul _).sub (StronglyMeasurable.const_mul ?_ _)
    refine Finset.stronglyMeasurable_fun_sum _ (fun k hk => ?_)
    exact ((hMa k).mono (G.mono (Finset.mem_range.mp hk).le)).const_mul _
  have hZint : ∀ n, Integrable (Z n) P := by
    intro n
    exact ((hMI n).const_mul _).sub ((integrable_finsetSum _ fun k _ => (hMI k).const_mul _).const_mul _)
  have hZm : Martingale Z G P := by
    refine martingale_of_condExp_sub_eq_zero_nat hZad hZint (fun i => ?_)
    have hdiff : Z (i + 1) - Z i = fun ω => b ^ (i + 1) * (M (i + 1) ω - M i ω) := by
      funext ω; simp only [hZ, Pi.sub_apply, Finset.sum_range_succ, pow_succ]; ring
    rw [hdiff]
    have h1 : (fun ω => b ^ (i + 1) * (M (i + 1) ω - M i ω)) = b ^ (i + 1) • (M (i + 1) - M i) := by
      funext ω; simp [smul_eq_mul]
    rw [h1]
    refine (condExp_smul _ _ _).trans ?_
    have h3 : P[M (i + 1) - M i|G i] =ᵐ[P] 0 := by
      filter_upwards [condExp_sub (hMI (i+1)) (hMI i) (G i), hM.2 i (i+1) (Nat.le_succ i)] with ω h1 h2
      rw [h1, Pi.sub_apply, h2, condExp_of_stronglyMeasurable (G.le i) (hMa i) (hMI i)]
      simp
    filter_upwards [h3] with ω hω
    simp [hω]
  have key := AvramDividend.Classical.chat03_bounded_first_crossing_martingale_identity Y Z hY hZm a N
  have hz0 : Z 0 = M 0 := by funext ω; simp [hZ]
  rw [hz0] at key
  rw [← key]
  congr 1
  funext ω
  simp only [hZ]
  congr 2
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨lt_of_lt_of_le h (hittingBtwn_le ω), h⟩
