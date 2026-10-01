-- Prove2me | solution 1 for CalibratedCE.Forecast.regret_sandwich_fractional_calibration
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T09:01:13.197948+00:00
-- url     : https://prove2.me/submissions/9da78fce-10b3-4704-91d1-466d03bc9e1b

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_CalibratedCE_Forecast_Regret
import Definitions.Def_CalibratedCE_Forecast_FracCalib

set_option autoImplicit false

namespace CalibratedCE.Forecast

lemma rsfc_ind_nonneg {n : ℕ} (X : ℕ → Fin n) (t : ℕ) (m : Fin n) : 0 ≤ ind X t m := by
  unfold ind; split_ifs <;> norm_num

lemma rsfc_ind_le_one {n : ℕ} (X : ℕ → Fin n) (t : ℕ) (m : Fin n) : ind X t m ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma rsfc_ind_sum {n : ℕ} (X : ℕ → Fin n) (t : ℕ) : ∑ m, ind X t m = 1 := by
  unfold ind; simp

lemma rsfc_Nw_nonneg {k : ℕ} (w : ℕ → Fin k → ℝ) (hw : ∀ t, IsDist (w t)) (T : ℕ)
    (i : Fin k) : 0 ≤ Nw w T i :=
  Finset.sum_nonneg (fun t _ => (hw t).1 i)

lemma rsfc_A_eq {k n : ℕ} (w : ℕ → Fin k → ℝ) (hw : ∀ t, IsDist (w t)) (X : ℕ → Fin n)
    (T : ℕ) (i : Fin k) (m : Fin n) :
    ∑ t ∈ Finset.range T, w t i * ind X t m = Nw w T i * rhoW w X T i m := by
  unfold rhoW
  split_ifs with h
  · rw [mul_zero]
    apply le_antisymm
    · calc ∑ t ∈ Finset.range T, w t i * ind X t m ≤ ∑ t ∈ Finset.range T, w t i :=
            Finset.sum_le_sum (fun t _ => by
              have h1 := (hw t).1 i
              have h2 := rsfc_ind_le_one X t m
              nlinarith)
        _ = 0 := h
    · exact Finset.sum_nonneg (fun t _ => mul_nonneg ((hw t).1 i) (rsfc_ind_nonneg X t m))
  · field_simp

lemma rsfc_S_eq {k n : ℕ} (p : Fin k → Fin n → ℝ) (w : ℕ → Fin k → ℝ)
    (hw : ∀ t, IsDist (w t)) (X : ℕ → Fin n) (T : ℕ) (i j : Fin k) :
    S (sqLoss p X) w T i j = Nw w T i *
      ∑ m, ((rhoW w X T i m - p i m) ^ 2 - (rhoW w X T i m - p j m) ^ 2) := by
  have step1 : S (sqLoss p X) w T i j = ∑ t ∈ Finset.range T, ∑ m,
      (-2 * (p i m - p j m) * (w t i * ind X t m) + (p i m ^ 2 - p j m ^ 2) * w t i) := by
    unfold S sqLoss
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [step1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, rsfc_A_eq w hw X T i m]
  unfold Nw
  ring

end CalibratedCE.Forecast

open CalibratedCE.Forecast in
theorem solution {k n : ℕ} (hk : 0 < k) (ε : ℝ)
    (p : Fin k → Fin n → ℝ) (hp : ∀ i, IsDist (p i))
    (hgrid : ∀ q : Fin n → ℝ, IsDist q → ∃ i, ∑ j, (q j - p i j) ^ 2 ≤ ε)
    (X : ℕ → Fin n) (w : ℕ → Fin k → ℝ) (hw : ∀ t, IsDist (w t)) (T : ℕ) :
    ∑ i : Fin k, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
        fun j => Rg (sqLoss p X) w T i j) / (T : ℝ) ≤ C2w p w X T ∧
    C2w p w X T ≤ ε + ∑ i : Fin k, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
        fun j => Rg (sqLoss p X) w T i j) / (T : ℝ) := by
  have hC : C2w p w X T =
      ∑ i, (Nw w T i * ∑ m, (rhoW w X T i m - p i m) ^ 2) / (T : ℝ) := by
    unfold C2w
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  have hle : ∀ i j, Rg (sqLoss p X) w T i j ≤
      Nw w T i * ∑ m, (rhoW w X T i m - p i m) ^ 2 := by
    intro i j
    have hN := rsfc_Nw_nonneg w hw T i
    have hS := rsfc_S_eq p w hw X T i j
    have h1 : 0 ≤ ∑ m, (rhoW w X T i m - p j m) ^ 2 :=
      Finset.sum_nonneg (fun m _ => sq_nonneg _)
    have h2 : 0 ≤ ∑ m, (rhoW w X T i m - p i m) ^ 2 :=
      Finset.sum_nonneg (fun m _ => sq_nonneg _)
    rw [Finset.sum_sub_distrib, mul_sub] at hS
    unfold Rg
    apply max_le (mul_nonneg hN h2)
    rw [hS]
    linarith [mul_nonneg hN h1]
  have hε : 0 ≤ ε := by
    obtain ⟨i, hi⟩ := hgrid (p ⟨0, hk⟩) (hp _)
    exact le_trans (Finset.sum_nonneg (fun m _ => sq_nonneg _)) hi
  have hge : ∀ i, Nw w T i * ∑ m, (rhoW w X T i m - p i m) ^ 2 ≤
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
        (fun j => Rg (sqLoss p X) w T i j) + Nw w T i * ε := by
    intro i
    have hN := rsfc_Nw_nonneg w hw T i
    have hsup : ∀ j, Rg (sqLoss p X) w T i j ≤
        Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
          (fun j => Rg (sqLoss p X) w T i j) :=
      fun j => Finset.le_sup' (fun j => Rg (sqLoss p X) w T i j) (Finset.mem_univ j)
    by_cases h0 : Nw w T i = 0
    · rw [h0, zero_mul, zero_mul, add_zero]
      have h00 : (0:ℝ) ≤ Rg (sqLoss p X) w T i ⟨0, hk⟩ := le_max_left _ _
      exact le_trans h00 (hsup ⟨0, hk⟩)
    · have hdist : IsDist (fun m => rhoW w X T i m) := by
        constructor
        · intro m
          show 0 ≤ rhoW w X T i m
          unfold rhoW
          rw [if_neg h0]
          exact div_nonneg (Finset.sum_nonneg (fun t _ =>
            mul_nonneg ((hw t).1 i) (rsfc_ind_nonneg X t m))) hN
        · show ∑ m, rhoW w X T i m = 1
          unfold rhoW
          simp only [if_neg h0]
          rw [← Finset.sum_div, Finset.sum_comm]
          have hA : ∑ t ∈ Finset.range T, ∑ m, w t i * ind X t m = Nw w T i := by
            unfold Nw
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [← Finset.mul_sum, rsfc_ind_sum, mul_one]
          rw [hA, div_self h0]
      obtain ⟨j, hj⟩ := hgrid _ hdist
      have hS := rsfc_S_eq p w hw X T i j
      rw [Finset.sum_sub_distrib, mul_sub] at hS
      have hR : S (sqLoss p X) w T i j ≤ Rg (sqLoss p X) w T i j := le_max_right _ _
      have h4 := hsup j
      have h3 : Nw w T i * ∑ m, (rhoW w X T i m - p j m) ^ 2 ≤ Nw w T i * ε :=
        mul_le_mul_of_nonneg_left hj hN
      linarith
  constructor
  · rw [hC]
    apply Finset.sum_le_sum
    intro i _
    gcongr
    exact Finset.sup'_le _ _ (fun j _ => hle i j)
  · rw [hC]
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp [hε]
    · have hTpos : (0:ℝ) < T := Nat.cast_pos.mpr hT
      have hsumN : ∑ i, Nw w T i = (T : ℝ) := by
        unfold Nw
        rw [Finset.sum_comm, Finset.sum_congr rfl (fun t _ => (hw t).2)]
        simp
      have key : ∑ i, (Nw w T i * ∑ m, (rhoW w X T i m - p i m) ^ 2) / (T : ℝ) ≤
          ∑ i, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
            (fun j => Rg (sqLoss p X) w T i j) + Nw w T i * ε) / (T : ℝ) :=
        Finset.sum_le_sum (fun i _ => by gcongr; exact hge i)
      have heq : ∑ i, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
            (fun j => Rg (sqLoss p X) w T i j) + Nw w T i * ε) / (T : ℝ) =
          ε + ∑ i : Fin k, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
            fun j => Rg (sqLoss p X) w T i j) / (T : ℝ) := by
        simp only [add_div, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        rw [← Finset.sum_div, ← Finset.sum_mul, hsumN]
        field_simp
      linarith
