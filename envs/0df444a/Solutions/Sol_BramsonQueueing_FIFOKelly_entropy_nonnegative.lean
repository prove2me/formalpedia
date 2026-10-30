-- Prove2me | solution 1 for BramsonQueueing.FIFOKelly.entropy_nonnegative
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T15:14:14.065445+00:00
-- url     : https://prove2.me/submissions/7c831d9c-4353-471a-9769-30a41c938465

import Definitions.Def_BramsonQueueing_FIFOKelly_Entropy

namespace S230SH2_73f

open BramsonQueueing.FIFOKelly

noncomputable def dat : ProcessingNetworks.FeedforwardStability.QueueingNetworkData 2 1 where
  p := fun _ => 0
  P := 0
  m := fun _ => 1
  lam := ![0, 1/2]
  b := fun _ => 1
  lam_nonneg := by intro i; fin_cases i <;> norm_num
  m_pos := fun _ => one_pos
  b_pos := fun _ => one_pos
  P_nonneg := by intro i j; simp
  P_rowsum := by intro i; simp
  P_transient := by
    intro i j
    apply tendsto_const_nhds.congr'
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨1, fun n hn => by simp [zero_pow (show n ≠ 0 by omega)]⟩

noncomputable def par : Parameters 2 1 where
  data := dat
  classes_pos := by norm_num
  stations_pos := one_pos
  station_onto := by intro j; exact ⟨0, Subsingleton.elim _ _⟩
  unit_capacity := fun _ => rfl

noncomputable def d1 (t : ℝ) : ℝ := min (3 * t / 4) 3
noncomputable def y (t : ℝ) : ℝ := max 0 (t / 2 - 4)
noncomputable def d2 (t : ℝ) : ℝ := t - d1 t - y t

noncomputable def X : SixPaths 2 1 where
  A := fun t k => ![0, t / 2] k
  D := fun t k => ![d1 t, d2 t] k
  T := fun t k => ![d1 t, d2 t] k
  W := fun t _ => 4 + t / 2 - t + y t
  Y := fun t _ => y t
  Z := fun t k => ![3 - d1 t, 1 + t / 2 - d2 t] k

lemma d1_nn (t : ℝ) (ht : 0 ≤ t) : 0 ≤ d1 t := by unfold d1; exact le_min (by linarith) (by norm_num)
lemma d1_le (t : ℝ) : d1 t ≤ 3 := min_le_right _ _
lemma y_nn (t : ℝ) : 0 ≤ y t := le_max_left _ _
lemma d2_nn (t : ℝ) (ht : 0 ≤ t) : 0 ≤ d2 t := by
  unfold d2 d1 y; simp only [min_def, max_def]; split_ifs <;> linarith
lemma z2_nn (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 1 + t / 2 - d2 t := by
  unfold d2 d1 y; simp only [min_def, max_def]; split_ifs <;> linarith
lemma d1_mono (a b : ℝ) (h : a ≤ b) : d1 a ≤ d1 b := by
  unfold d1; simp only [min_def]; split_ifs <;> linarith
lemma d2_mono (a b : ℝ) (h : a ≤ b) : d2 a ≤ d2 b := by
  unfold d2 d1 y; simp only [min_def, max_def]; split_ifs <;> linarith
lemma y_mono (a b : ℝ) (h : a ≤ b) : y a ≤ y b := by
  unfold y; simp only [max_def]; split_ifs <;> linarith
lemma w_nn (t : ℝ) : 0 ≤ 4 + t / 2 - t + y t := by
  unfold y; simp only [max_def]; split_ifs <;> linarith
@[simp] lemma d1_0 : d1 0 = 0 := by norm_num [d1]
@[simp] lemma y_0 : y 0 = 0 := by norm_num [y]
@[simp] lemma d2_0 : d2 0 = 0 := by simp [d2]

lemma hsol : (fifoModel par).Solution X := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht k; fin_cases k <;> simp [X] <;> linarith
    · intro t ht k; fin_cases k <;> simp [X, d1_nn t ht, d2_nn t ht]
    · intro t ht k; fin_cases k <;> simp [X, d1_nn t ht, d2_nn t ht]
    · intro t ht k; exact w_nn t
    · intro t ht k; exact y_nn t
    · intro t ht k; fin_cases k <;> simp [X, z2_nn t ht] <;> linarith [d1_le t]
    · intro k a _ b _ hab; fin_cases k <;> simp [X] <;> linarith
    · intro k a _ b _ hab; fin_cases k <;> simp [X, d1_mono a b hab, d2_mono a b hab]
    · intro k a _ b _ hab; fin_cases k <;> simp [X, d1_mono a b hab, d2_mono a b hab]
    · intro k a _ b _ hab; exact y_mono a b hab
    · funext k; fin_cases k <;> simp [X]
    · funext k; fin_cases k <;> simp [X]
    · funext k; fin_cases k <;> simp [X]
    · funext k; simp [X]
    · intro t ht k; fin_cases k <;> simp [X, par, dat, fifoModel] <;> ring
    · intro t ht k; fin_cases k <;> simp [X] <;> ring
    · intro t ht j; fin_cases j; simp [X, par, dat, fifoModel, Fin.sum_univ_two, d2]; ring
    · intro t ht j; fin_cases j; simp [X, par, dat, fifoModel, Fin.sum_univ_two, d2]; ring
    · intro j a b ha hab hY
      refine ⟨b, ⟨hab, le_refl b⟩, ?_⟩
      simp only [X] at hY ⊢
      have h1 : 8 < b := by
        by_contra hb; push Not at hb
        have : y b = 0 := by unfold y; simp only [max_def]; split_ifs <;> linarith
        linarith [y_nn a]
      unfold y; simp only [max_def]; split_ifs <;> linarith
    · intro t ht k; fin_cases k <;> simp [X, par, dat, fifoModel]
  · intro t ht k
    fin_cases k
    · simp only [X]; simp; unfold d1 y; simp only [min_def, max_def]; split_ifs <;> linarith
    · simp only [X]; simp; unfold d2 d1 y; simp only [min_def, max_def]; split_ifs <;> linarith

end S230SH2_73f

open BramsonQueueing.FIFOKelly in
theorem solution : ¬ (∀ {K J : ℕ} (p : Parameters K J)
    (hk : KellyType p) (hr : ∀ j, load p j ≤ 1)
    (X : SixPaths K J) (hX : (fifoModel p).Solution X),
    ∀ t, 0 ≤ t → 0 ≤ entropy p X t) := by
  intro H
  have hfund : ∀ k l, fundamental S230SH2_73f.par k l = (1 : Matrix (Fin 2) (Fin 2) ℝ) k l := by
    intro k l
    unfold fundamental
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [S230SH2_73f.par, S230SH2_73f.dat, zero_pow hn]
  have har : ∀ k, arrivalRate S230SH2_73f.par k = S230SH2_73f.par.data.lam k := by
    intro k
    simp only [arrivalRate, hfund]
    simp [Matrix.one_apply]
  have hr : ∀ j, load S230SH2_73f.par j ≤ 1 := by
    intro j
    simp only [load, har, Fin.sum_univ_two]
    simp [S230SH2_73f.par, S230SH2_73f.dat]; split_ifs <;> norm_num
  have h := H S230SH2_73f.par (fun k l _ => rfl) hr S230SH2_73f.X S230SH2_73f.hsol 0 le_rfl
  have hce0 : ∀ x, classEntropy S230SH2_73f.par 0 x = 0 := by
    intro x; simp only [classEntropy, har]; simp [S230SH2_73f.par, S230SH2_73f.dat]
  have hW : S230SH2_73f.X.W 0 0 = 4 := by simp [S230SH2_73f.X]
  have hrate : ∀ r ∈ Set.Ioo (0:ℝ) 4, rate (fun s => S230SH2_73f.X.D s 1) r = 1/4 := by
    intro r hr
    unfold rate
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds hr.1)]
    have hev : (fun s => S230SH2_73f.X.D s 1) =ᶠ[nhds r] fun s => s / 4 := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
      simp only [S230SH2_73f.X]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      unfold S230SH2_73f.d2 S230SH2_73f.d1 S230SH2_73f.y
      have h1 : 3 * s / 4 ≤ 3 := by linarith [hs.2]
      have h2 : s / 2 - 4 ≤ 0 := by linarith [hs.2]
      rw [min_eq_left h1, max_eq_left h2]; ring
    rw [hev.deriv_eq]
    have := (hasDerivAt_id r).div_const 4
    simpa using this.deriv
  have hint : (∫ r in (0:ℝ)..(0 + S230SH2_73f.X.W 0 (S230SH2_73f.par.data.p 1)),
      classEntropy S230SH2_73f.par 1 (rate (fun s => S230SH2_73f.X.D s 1) r)) =
      4 * (1/4 * Real.log (1/2)) := by
    have hp : S230SH2_73f.par.data.p 1 = 0 := rfl
    rw [hp, hW, zero_add]
    rw [intervalIntegral.integral_congr_ae (g := fun _ => 1/4 * Real.log (1/2))]
    · simp
    · filter_upwards [(Set.countable_singleton (4:ℝ)).ae_notMem MeasureTheory.volume] with x hx hx'
      rw [Set.uIoc_of_le (by norm_num)] at hx'
      have hx4 : x ≠ 4 := hx
      have hmem : x ∈ Set.Ioo (0:ℝ) 4 := ⟨hx'.1, lt_of_le_of_ne hx'.2 hx4⟩
      rw [hrate x hmem]
      simp only [classEntropy, har]
      simp [S230SH2_73f.par, S230SH2_73f.dat]
      have : Real.log (1/2) = - Real.log 2 := by rw [one_div, Real.log_inv]
      linarith
  have hent : entropy S230SH2_73f.par S230SH2_73f.X 0 = 4 * (1/4 * Real.log (1/2)) := by
    unfold entropy
    rw [Fin.sum_univ_two, hint]
    simp [hce0]
  have hl : Real.log (1/2) < 0 := Real.log_neg (by norm_num) (by norm_num)
  rw [hent] at h
  linarith
