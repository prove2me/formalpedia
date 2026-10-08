-- Prove2me | solution 1 for BesbesZeevi.SingleParam.fact1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:45:57.077168+00:00
-- url     : https://prove2.me/submissions/68545472-2287-497d-b6e9-e0a44d1bd032

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_Model

open MeasureTheory

open BesbesZeevi.SingleParam Pointwise in
theorem solution (D : Market) (M KLo KHi m : ℝ) (hM : 0 < M) (hKLo : 0 < KLo)
    (hK : KLo ≤ KHi) (hm : 0 < m) :
    0 < m * min D.T (D.x / M) ∧
    ∀ f : ℝ → ℝ, InClass D M KLo KHi m f →
      (∀ n : ℕ, 1 ≤ n → detValueScaled D f n = (n : ℝ) * detValue D f D.x) ∧
      m * min D.T (D.x / M) ≤ detValue D f D.x := by
  have hT := D.T_pos
  have hx := D.x_pos
  have hT'pos : 0 < min D.T (D.x / M) := lt_min hT (div_pos hx hM)
  refine ⟨mul_pos hm hT'pos, ?_⟩
  intro f hf
  obtain ⟨hoff, hnn, -, -, -, hbd, -, -, ps, hps, hrev⟩ := hf
  refine ⟨?_, ?_⟩
  · intro n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hu : IsUnit (n:ℝ) := (ne_of_gt hnpos).isUnit
    unfold detValueScaled detValue
    rw [show ∀ S : Set ℝ, (n:ℝ) * sSup S = sSup ((n:ℝ) • S) from
      fun S => by rw [Real.sSup_smul_of_nonneg hnpos.le, smul_eq_mul]]
    congr 1
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    have hfe : ∀ p : ℝ → ℝ, Feasible D (fun p => (n:ℝ) * f p) ((n:ℝ) * D.x) p ↔ Feasible D f D.x p := by
      intro p
      simp only [Feasible]
      have e1 : (fun s => p s * ((n:ℝ) * f (p s))) = fun s => (n:ℝ) * (p s * f (p s)) := by
        funext s; ring
      rw [e1, integral_const_mul]
      simp only [IntegrableOn]
      rw [integrable_const_mul_iff hu, integrable_const_mul_iff hu]
      constructor
      · rintro ⟨a, b, c, d, e⟩
        exact ⟨a, b, c, d, le_of_mul_le_mul_left e hnpos⟩
      · rintro ⟨a, b, c, d, e⟩
        exact ⟨a, b, c, d, mul_le_mul_of_nonneg_left e hnpos.le⟩
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨∫ s in Set.Icc (0:ℝ) D.T, p s * f (p s), ⟨p, (hfe p).1 hp, rfl⟩, ?_⟩
      rw [← integral_const_mul]
      congr 1; funext s; ring
    · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨p, (hfe p).2 hp, ?_⟩
      rw [← integral_const_mul]
      congr 1; funext s; ring
  · set T' := min D.T (D.x / M) with hT'def
    have hT'le : T' ≤ D.T := min_le_left _ _
    let q : ℝ → ℝ := fun s => if s ≤ T' then ps else D.pOff
    have hfq : (fun s => f (q s)) = Set.indicator (Set.Iic T') (fun _ => f ps) := by
      funext s
      simp only [q, Set.indicator, Set.mem_Iic]
      split_ifs <;> simp [hoff]
    have hrq : (fun s => q s * f (q s)) = Set.indicator (Set.Iic T') (fun _ => ps * f ps) := by
      funext s
      simp only [q, Set.indicator, Set.mem_Iic]
      split_ifs <;> simp [hoff]
    have hvol : volume.real (Set.Icc (0:ℝ) D.T ∩ Set.Iic T') = T' := by
      have : Set.Icc (0:ℝ) D.T ∩ Set.Iic T' = Set.Icc 0 T' := by
        ext s; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
        constructor
        · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
        · rintro ⟨a, c⟩; exact ⟨⟨a, c.trans hT'le⟩, c⟩
      rw [this, Real.volume_real_Icc]
      simp [hT'pos.le]
    have hint : ∀ c : ℝ, (∫ s in Set.Icc (0:ℝ) D.T, Set.indicator (Set.Iic T') (fun _ => c) s) = T' * c := by
      intro c
      rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        setIntegral_const, smul_eq_mul, Set.inter_comm, hvol]
    have hfM : f ps ≤ M := (le_abs_self _).trans (hbd ps hps)
    have hfeas : Feasible D f D.x q := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact Measurable.ite measurableSet_Iic measurable_const measurable_const
      · intro s _
        by_cases h : s ≤ T'
        · left; simp [q, h, hps]
        · right; simp [q, h]
      · rw [hfq]
        exact ((integrable_const (f ps)).indicator measurableSet_Iic)
      · rw [hrq]
        exact ((integrable_const (ps * f ps)).indicator measurableSet_Iic)
      · rw [hfq, hint]
        calc T' * f ps ≤ (D.x / M) * M := by
              apply mul_le_mul (min_le_right _ _) hfM (hnn ps hps) (div_pos hx hM).le
          _ = D.x := by field_simp
    have hpHi : 0 < D.pHi := D.pLo_pos.trans D.pLo_lt_pHi
    have hbdd : BddAbove {v : ℝ | ∃ p : ℝ → ℝ, Feasible D f D.x p ∧
        v = ∫ s in Set.Icc (0 : ℝ) D.T, p s * f (p s)} := by
      refine ⟨D.pHi * M * volume.real (Set.Icc (0:ℝ) D.T), ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      apply norm_setIntegral_le_of_norm_le_const (by simp)
      intro s hs
      rcases hp.2.1 s hs with h | h
      · rw [Real.norm_eq_abs, abs_mul]
        have h1 : |p s| ≤ D.pHi := by
          rw [abs_of_pos (lt_of_lt_of_le D.pLo_pos h.1)]; exact h.2
        exact mul_le_mul h1 (hbd _ h) (abs_nonneg _) hpHi.le
      · rw [h, hoff]; simp
        exact mul_nonneg hpHi.le hM.le
    have hmem : (∫ s in Set.Icc (0 : ℝ) D.T, q s * f (q s)) ∈ {v : ℝ | ∃ p : ℝ → ℝ, Feasible D f D.x p ∧
        v = ∫ s in Set.Icc (0 : ℝ) D.T, p s * f (p s)} := ⟨q, hfeas, rfl⟩
    have hval : (∫ s in Set.Icc (0 : ℝ) D.T, q s * f (q s)) = T' * (ps * f ps) := by
      rw [hrq, hint]
    unfold detValue
    calc m * T' ≤ T' * (ps * f ps) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hrev hT'pos.le
      _ = _ := hval.symm
      _ ≤ _ := le_csSup hbdd hmem
