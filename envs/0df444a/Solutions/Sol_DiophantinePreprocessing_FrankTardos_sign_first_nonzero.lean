-- Prove2me | solution 1 for DiophantinePreprocessing.FrankTardos.sign_first_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:20:52.963293+00:00
-- url     : https://prove2.me/submissions/9ace08bd-6a11-4ac6-9359-aeed7a617838

import Mathlib
import Definitions.Def_DiophantinePreprocessing_FrankTardos_CondIII

namespace DiophantinePreprocessing.FrankTardos

theorem aux_sfn_supNorm_ge {n : ℕ} (u : Fin n → ℤ) (l : Fin n) : |u l| ≤ (supNorm u : ℤ) := by
  have h : (u l).natAbs ≤ supNorm u :=
    Finset.le_sup (f := fun j => (u j).natAbs) (Finset.mem_univ l)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h

theorem aux_sfn_supNorm_pos {n : ℕ} (u : Fin n → ℤ) (hu : u ≠ 0) : 1 ≤ (supNorm u : ℤ) := by
  obtain ⟨l, hl⟩ : ∃ l, u l ≠ 0 := by
    by_contra h
    exact hu (funext fun l => by_contra fun hl => h ⟨l, hl⟩)
  have h1 := aux_sfn_supNorm_ge u l
  have h2 : 0 < |u l| := abs_pos.mpr hl
  omega

theorem aux_sfn_dot_bound {n : ℕ} (N : ℕ) (b u : Fin n → ℤ) (hb : ∑ l, |b l| ≤ (N : ℤ) - 1) :
    |∑ l, b l * u l| ≤ ((N:ℤ) - 1) * (supNorm u : ℤ) := by
  calc |∑ l, b l * u l| ≤ ∑ l, |b l * u l| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, |b l| * |u l| := by simp [abs_mul]
    _ ≤ ∑ l, |b l| * (supNorm u : ℤ) := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_left (aux_sfn_supNorm_ge u l) (abs_nonneg _)
    _ = (∑ l, |b l|) * (supNorm u : ℤ) := by rw [Finset.sum_mul]
    _ ≤ ((N:ℤ) - 1) * (supNorm u : ℤ) := mul_le_mul_of_nonneg_right hb (by positivity)

end DiophantinePreprocessing.FrankTardos

open DiophantinePreprocessing.FrankTardos

theorem solution (n N k : ℕ) (hN : 1 ≤ N) (w : Fin n → ℝ)
    (v : ℕ → Fin n → ℤ) (lam : ℕ → ℝ)
    (hlam : ∀ i ∈ Finset.Icc 1 k, 0 < lam i)
    (hw : ∀ l, w l = ∑ i ∈ Finset.Icc 1 k, lam i * (v i l : ℝ))
    (hIII : CondIII N k lam v)
    (b : Fin n → ℤ) (hb : ∑ l, |b l| ≤ (N : ℤ) - 1) :
    (∀ j ∈ Finset.Icc 1 k,
        (∀ i ∈ Finset.Ico 1 j, ∑ l, b l * v i l = 0) → ∑ l, b l * v j l ≠ 0 →
        SignType.sign (∑ l, (b l : ℝ) * w l) = SignType.sign ((∑ l, b l * v j l : ℤ) : ℝ)) ∧
    ((∀ i ∈ Finset.Icc 1 k, ∑ l, b l * v i l = 0) → ∑ l, (b l : ℝ) * w l = 0) := by
  set c : ℕ → ℤ := fun i => ∑ l, b l * v i l with hc
  have hcdef : ∀ i, (∑ l, b l * v i l) = c i := fun i => rfl
  simp only [hcdef]
  have hdot : ∑ l, (b l : ℝ) * w l = ∑ i ∈ Finset.Icc 1 k, lam i * (c i : ℝ) := by
    simp_rw [hw, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hc]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hstep : ∀ i ∈ Finset.Icc 2 k, lam i * (|(c i : ℝ)| + 1) ≤ lam (i - 1) := by
    intro i hi
    obtain ⟨hv, hl⟩ := hIII i hi
    have h1 : |c i| ≤ ((N:ℤ) - 1) * (supNorm (v i) : ℤ) := aux_sfn_dot_bound N b (v i) hb
    have h2 := aux_sfn_supNorm_pos (v i) hv
    have h3 : |c i| + 1 ≤ (N : ℤ) * (supNorm (v i) : ℤ) := by nlinarith
    have h4 : (|(c i : ℝ)| + 1) ≤ (N : ℝ) * (supNorm (v i) : ℝ) := by
      have : ((|c i| + 1 : ℤ) : ℝ) ≤ (((N : ℤ) * (supNorm (v i) : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast h3
      push_cast at this
      exact this
    have hi1 : i ∈ Finset.Icc 1 k := by
      simp only [Finset.mem_Icc] at hi ⊢; omega
    have hpos := hlam i hi1
    calc lam i * (|(c i : ℝ)| + 1) ≤ lam i * ((N : ℝ) * (supNorm (v i) : ℝ)) :=
          mul_le_mul_of_nonneg_left h4 hpos.le
      _ ≤ lam (i - 1) := hl
  constructor
  · intro j hj hprev hcj
    have hj' := Finset.mem_Icc.mp hj
    have htail : ∀ e, j ≤ e → e ≤ k →
        (∑ i ∈ Finset.Ico (j+1) (e+1), lam i * |(c i : ℝ)|) + lam e ≤ lam j := by
      intro e hje
      induction e, hje using Nat.le_induction with
      | base => intro _; simp
      | succ e hje ih =>
        intro hek
        rw [Finset.sum_Ico_succ_top (by omega)]
        have h1 := ih (by omega)
        have hs := hstep (e+1) (Finset.mem_Icc.mpr ⟨by omega, hek⟩)
        simp only [Nat.add_sub_cancel] at hs
        nlinarith
    have hT := htail k hj'.2 le_rfl
    have hlamk := hlam k (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    have hsplit : ∑ i ∈ Finset.Icc 1 k, lam i * (c i : ℝ)
        = lam j * (c j : ℝ) + ∑ i ∈ Finset.Ico (j+1) (k+1), lam i * (c i : ℝ) := by
      rw [← Finset.Ico_add_one_right_eq_Icc,
        ← Finset.sum_Ico_consecutive _ (show 1 ≤ j by omega) (show j ≤ k+1 by omega),
        Finset.sum_eq_sum_Ico_succ_bot (show j < k+1 by omega)]
      have : ∑ i ∈ Finset.Ico 1 j, lam i * (c i : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [hprev i hi]
      rw [this, zero_add]
    have hR : |∑ i ∈ Finset.Ico (j+1) (k+1), lam i * (c i : ℝ)| < lam j := by
      calc |∑ i ∈ Finset.Ico (j+1) (k+1), lam i * (c i : ℝ)|
          ≤ ∑ i ∈ Finset.Ico (j+1) (k+1), |lam i * (c i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ Finset.Ico (j+1) (k+1), lam i * |(c i : ℝ)| := by
            apply Finset.sum_congr rfl
            intro i hi
            have hi' := Finset.mem_Ico.mp hi
            rw [abs_mul, abs_of_pos (hlam i (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))]
        _ < lam j := by linarith
    rw [hdot, hsplit]
    have hlj := hlam j hj
    have hR' := abs_lt.mp hR
    rcases lt_or_gt_of_ne hcj with hneg | hpos
    · have hc1 : (c j : ℝ) ≤ -1 := by
        have : c j ≤ -1 := by omega
        exact_mod_cast this
      have hxneg : lam j * (c j : ℝ) + ∑ i ∈ Finset.Ico (j+1) (k+1), lam i * (c i : ℝ) < 0 := by
        nlinarith
      rw [sign_neg hxneg, sign_neg]
      exact_mod_cast hneg
    · have hc1 : (1 : ℝ) ≤ (c j : ℝ) := by
        have : 1 ≤ c j := by omega
        exact_mod_cast this
      have hxpos : 0 < lam j * (c j : ℝ) + ∑ i ∈ Finset.Ico (j+1) (k+1), lam i * (c i : ℝ) := by
        nlinarith
      rw [sign_pos hxpos, sign_pos]
      exact_mod_cast hpos
  · intro hall
    rw [hdot]
    apply Finset.sum_eq_zero
    intro i hi
    simp [hall i hi]
