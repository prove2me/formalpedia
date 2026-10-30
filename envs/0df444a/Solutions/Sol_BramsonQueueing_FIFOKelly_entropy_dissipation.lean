-- Prove2me | solution 1 for BramsonQueueing.FIFOKelly.entropy_dissipation
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T15:13:48.186386+00:00
-- url     : https://prove2.me/submissions/ae848e16-f458-4746-86bb-37d4f9b8a0d4

import Definitions.Def_BramsonQueueing_FIFOKelly_Entropy

namespace S230SH2_d92

open BramsonQueueing.FIFOKelly

noncomputable def dat : ProcessingNetworks.FeedforwardStability.QueueingNetworkData 1 1 where
  p := fun _ => 0
  P := (1/2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
  m := fun _ => 1
  lam := fun _ => 0
  b := fun _ => 1
  lam_nonneg := fun _ => le_refl _
  m_pos := fun _ => one_pos
  b_pos := fun _ => one_pos
  P_nonneg := by
    intro i j
    fin_cases i; fin_cases j; norm_num
  P_rowsum := by
    intro i; fin_cases i; norm_num
  P_transient := by
    intro i j
    fin_cases i; fin_cases j
    simp only [smul_pow, one_pow, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

noncomputable def par : Parameters 1 1 where
  data := dat
  classes_pos := one_pos
  stations_pos := one_pos
  station_onto := by intro j; exact ⟨0, Subsingleton.elim _ _⟩
  unit_capacity := fun _ => rfl

noncomputable def X : SixPaths 1 1 where
  A := fun t _ => min t 2 / 2
  D := fun t _ => min t 2
  T := fun t _ => min t 2
  W := fun t _ => 1 - min t 2 / 2
  Y := fun t _ => t - min t 2
  Z := fun t _ => 1 - min t 2 / 2

lemma hmin : (fun t : ℝ => min t 2) =ᶠ[nhds 1] id := by
  filter_upwards [Iio_mem_nhds (show (1:ℝ) < 2 by norm_num)] with t ht
  simp [min_eq_left (le_of_lt (Set.mem_Iio.mp ht))]

lemma hdmin : HasDerivAt (fun t : ℝ => min t 2) 1 1 :=
  (hasDerivAt_id (1:ℝ)).congr_of_eventuallyEq hmin

lemma hsol : (fifoModel par).Solution X := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht k; simp only [X]; have := le_min ht (show (0:ℝ) ≤ 2 by norm_num); linarith
    · intro t ht k; simp only [X]; exact le_min ht (by norm_num)
    · intro t ht k; simp only [X]; exact le_min ht (by norm_num)
    · intro t ht k; simp only [X]; have := min_le_right t 2; linarith
    · intro t ht k; simp only [X]; have := min_le_left t 2; linarith
    · intro t ht k; simp only [X]; have := min_le_right t 2; linarith
    · intro k a _ b _ hab; simp only [X]; have := min_le_min_right 2 hab; linarith
    · intro k a _ b _ hab; exact min_le_min_right 2 hab
    · intro k a _ b _ hab; exact min_le_min_right 2 hab
    · intro k a _ b _ hab
      simp only [X]
      rcases le_total a 2 with h1 | h1 <;> rcases le_total b 2 with h2 | h2 <;>
        simp [min_eq_left, min_eq_right, h1, h2] <;> linarith
    · funext k; simp [X]
    · funext k; simp [X]
    · funext k; simp [X]
    · funext k; simp [X]
    · intro t ht k; fin_cases k; simp [X, par, dat, fifoModel]; ring
    · intro t ht k; simp [X]; ring
    · intro t ht j; fin_cases j; simp [X, par, dat, fifoModel]; ring
    · intro t ht j; fin_cases j; simp [X, par, dat, fifoModel]
    · intro j a b ha hab hY
      refine ⟨b, ⟨hab, le_refl b⟩, ?_⟩
      simp only [X] at hY ⊢
      have h1 : 2 < b := by
        by_contra hb; push Not at hb
        rw [min_eq_left hb] at hY
        have := min_le_left a 2; linarith
      rw [min_eq_right h1.le]; norm_num
    · intro t ht k; simp [X, par, dat, fifoModel]
  · intro t ht k
    show min (t + (1 - min t 2 / 2)) 2 = (1 - min 0 2 / 2) + min t 2 / 2
    rcases le_total t 2 with h | h
    · rw [min_eq_left h, min_eq_left (by linarith), min_eq_left (by norm_num : (0:ℝ) ≤ 2)]; ring
    · rw [min_eq_right h, min_eq_right (by linarith), min_eq_left (by norm_num : (0:ℝ) ≤ 2)]; ring

end S230SH2_d92

open BramsonQueueing.FIFOKelly in
theorem solution : ¬ (∀ {K J : ℕ} (p : Parameters K J) (hk : KellyType p),
    ∃ c₆ : ℝ, 0 < c₆ ∧ ∀ X : SixPaths K J, (fifoModel p).Solution X →
      ∀ t, Regular X t →
        entropyFlux p X t ≤ queueDerivative X t ∧
        queueDerivative X t + c₆ * workloadDissipation X t ≤ stationEntropyFlux p X t ∧
        rate (entropy p X) t ≤ -c₆ * workloadDissipation X t) := by
  intro H
  have hreg : Regular S230SH2_d92.X 1 := by
    have hd : DifferentiableAt ℝ (fun t : ℝ => min t 2) 1 := S230SH2_d92.hdmin.differentiableAt
    refine ⟨by norm_num, fun k => ⟨?_, ?_, ?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩ <;>
      simp only [S230SH2_d92.X] <;> apply DifferentiableAt.differentiableWithinAt <;> fun_prop
  obtain ⟨c, hc, H⟩ := H S230SH2_d92.par (fun k l _ => rfl)
  have h := (H S230SH2_d92.X S230SH2_d92.hsol 1 hreg).1
  have har : ∀ k, arrivalRate S230SH2_d92.par k = 0 := by
    intro k; simp [arrivalRate, S230SH2_d92.par, S230SH2_d92.dat]
  have hce : ∀ k x, classEntropy S230SH2_d92.par k x = 0 := by
    intro k x; simp [classEntropy, har]
  have hflux : entropyFlux S230SH2_d92.par S230SH2_d92.X 1 = 0 := by
    simp [entropyFlux, hce]
  have hZ : rate (fun r => S230SH2_d92.X.Z r 0) 1 = -1/2 := by
    unfold rate
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds (by norm_num))]
    simp only [S230SH2_d92.X]
    have := (S230SH2_d92.hdmin.div_const 2).const_sub 1
    rw [this.deriv]; norm_num
  have hq : queueDerivative S230SH2_d92.X 1 = -1/2 := by
    simp only [queueDerivative, Fin.sum_univ_one, hZ]
  rw [hflux, hq] at h
  norm_num at h
