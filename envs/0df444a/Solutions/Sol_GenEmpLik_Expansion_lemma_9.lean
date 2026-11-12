-- Prove2me | solution 1 for GenEmpLik.Expansion.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:58:11.309389+00:00
-- url     : https://prove2.me/submissions/d84fe26e-43cd-47bd-9ff5-53f520600be7

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_reparamSets
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar

open VarianceRegularization.Expansion

private lemma sum_mul_le_sqrt_mul_sqrt {n : ℕ} (a b : Fin n → ℝ) :
    ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  have hA_nonneg : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
    rcases eq_or_lt_of_le hA_nonneg with hA0 | hA_pos
    · have ha0 : ∀ i : Fin n, a i = 0 := by
        intro i
        have hi : a i ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (a j))).mp hA0.symm i
            (Finset.mem_univ i)
        exact sq_eq_zero_iff.mp hi
      simp [ha0]
    · let t : ℝ := (∑ i, a i * b i) / (∑ i, a i ^ 2)
      have hquad : 0 ≤ ∑ i, (t * a i - b i) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have hexp : ∑ i, (t * a i - b i) ^ 2 =
          t ^ 2 * (∑ i, a i ^ 2) - 2 * t * (∑ i, a i * b i) + ∑ i, b i ^ 2 := by
        calc ∑ i, (t * a i - b i) ^ 2
            = ∑ i, (t ^ 2 * a i ^ 2 - 2 * t * (a i * b i) + b i ^ 2) :=
              Finset.sum_congr rfl fun i _ => by ring
          _ = ∑ i, (t ^ 2 * a i ^ 2 - 2 * t * (a i * b i)) + ∑ i, b i ^ 2 :=
              Finset.sum_add_distrib
          _ = t ^ 2 * (∑ i, a i ^ 2) - 2 * t * (∑ i, a i * b i) + ∑ i, b i ^ 2 := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hexp] at hquad
      have hmul := mul_le_mul_of_nonneg_left hquad (le_of_lt hA_pos)
      have hsimpl : (∑ i, a i ^ 2) *
          (t ^ 2 * (∑ i, a i ^ 2) - 2 * t * (∑ i, a i * b i) + ∑ i, b i ^ 2) =
          (∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2 := by
        dsimp [t]
        field_simp [ne_of_gt hA_pos]
        ring
      linarith
  calc ∑ i, a i * b i
      ≤ |∑ i, a i * b i| := le_abs_self _
    _ = Real.sqrt ((∑ i, a i * b i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, a i ^ 2) * (∑ i, b i ^ 2)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := Real.sqrt_mul hA_nonneg _

private lemma huber_decomp {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ x y : ℝ, t = x + y ∧ GenEmpLik.Expansion.huber ε t = x ^ 2 / 2 + ε * |y| := by
  unfold GenEmpLik.Expansion.huber
  by_cases h : |t| ≤ ε
  · refine ⟨t, 0, by ring, ?_⟩
    rw [if_pos h, abs_zero, mul_zero, add_zero]
  · rw [if_neg h]
    rcases lt_abs.mp (not_le.mp h) with ht_pos | ht_neg
    · refine ⟨ε, t - ε, by ring, ?_⟩
      rw [abs_of_pos (lt_trans hε ht_pos), abs_of_pos (by linarith)]
      ring
    · refine ⟨-ε, t + ε, by ring, ?_⟩
      have ht_lt : t < 0 := by linarith
      rw [abs_of_neg ht_lt, abs_of_neg (by linarith)]
      ring

open GenEmpLik.Expansion in
theorem solution {n : ℕ} (hn : 0 < n) {ρ ε C : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hC : 0 ≤ C)
    (hCε : C * ε < 1) (z : Fin n → ℝ)
    (hz : (⨆ i, |z i - empMean z|) / Real.sqrt n ≤
      ε * Real.sqrt (empVar z) * Real.sqrt ((1 - C * ε) / ρ)) :
    sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Ubig n ε C ρ) ≤
      Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 - C * ε)) := by
  have _ := hC
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h1Cε_pos : 0 < 1 - C * ε := by linarith
  let w : Fin n → ℝ := fun i => z i - empMean z
  have hw_sq : ∑ i, w i ^ 2 = (n : ℝ) * empVar z := by
    dsimp [w, empVar]
    have hsum_z : ∑ i, z i = (n : ℝ) * empMean z := by
      dsimp [empMean]
      field_simp
    calc ∑ i, (z i - empMean z) ^ 2
        = ∑ i, (z i ^ 2 - 2 * empMean z * z i + empMean z ^ 2) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, (z i ^ 2 - 2 * empMean z * z i) + ∑ i : Fin n, empMean z ^ 2 :=
          Finset.sum_add_distrib
      _ = ∑ i, z i ^ 2 - 2 * empMean z * ∑ i, z i + (n : ℝ) * empMean z ^ 2 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ = (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i, z i ^ 2 - empMean z ^ 2) := by
          rw [hsum_z]
          field_simp
          ring
  let sn : ℝ := Real.sqrt (empVar z)
  have h0_mem : (0 : Fin n → ℝ) ∈ Ubig n ε C ρ := by
    refine ⟨by simp, ?_⟩
    have hhub0 : huber ε 0 = 0 := by
      unfold huber
      rw [if_pos (by simp [hε.le])]
      ring
    simp only [Pi.zero_apply, mul_zero, hhub0, Finset.sum_const_zero]
    positivity
  refine csSup_le ⟨0, 0, h0_mem, by simp⟩ ?_
  rintro _ ⟨u, ⟨hu_sum, hu_hub⟩, rfl⟩
  have huz : ∑ i, u i * z i = (n : ℝ)⁻¹ * ∑ i, ((n : ℝ) * u i) * w i := by
    have h1 : ∑ i, u i * z i = ∑ i, u i * w i := by
      calc ∑ i, u i * z i
          = ∑ i, (u i * w i + u i * empMean z) :=
            Finset.sum_congr rfl fun i _ => by dsimp [w]; ring
        _ = ∑ i, u i * w i + (∑ i, u i) * empMean z := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        _ = ∑ i, u i * w i := by rw [hu_sum, zero_mul, add_zero]
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by field_simp
  choose x y hxy hhub_xy using fun i : Fin n => huber_decomp hε ((n : ℝ) * u i)
  have hsplit : (n : ℝ)⁻¹ * ∑ i, ((n : ℝ) * u i) * w i =
      (n : ℝ)⁻¹ * ∑ i, x i * w i + (n : ℝ)⁻¹ * ∑ i, y i * w i := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by rw [hxy i]; ring
  have hw_inf : ∀ i : Fin n,
      |w i| ≤ Real.sqrt n * ε * sn * (Real.sqrt (1 - C * ε) / Real.sqrt ρ) := by
    intro i
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hb_range : BddAbove (Set.range fun j : Fin n => |w j|) := Set.toFinite _ |>.bddAbove
    have hi_le : |w i| ≤ ⨆ j : Fin n, |w j| := le_ciSup hb_range i
    have h1 : |w i| / Real.sqrt n ≤
        ε * sn * (Real.sqrt (1 - C * ε) / Real.sqrt ρ) := by
      calc |w i| / Real.sqrt n
          ≤ (⨆ j : Fin n, |w j|) / Real.sqrt n :=
            div_le_div_of_nonneg_right hi_le (Real.sqrt_nonneg _)
        _ ≤ ε * sn * Real.sqrt ((1 - C * ε) / ρ) := hz
        _ = ε * sn * (Real.sqrt (1 - C * ε) / Real.sqrt ρ) := by
            rw [Real.sqrt_div h1Cε_pos.le]
    have hmul := (div_le_iff₀' (Real.sqrt_pos.mpr hn_pos)).mp h1
    linarith
  have hterm_x : (n : ℝ)⁻¹ * ∑ i, x i * w i ≤
      (sn / Real.sqrt n) * Real.sqrt (∑ i, x i ^ 2) := by
    have hcs := sum_mul_le_sqrt_mul_sqrt x w
    rw [hw_sq, Real.sqrt_mul hn_pos.le] at hcs
    have hmul := mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hn_pos.le)
    calc (n : ℝ)⁻¹ * ∑ i, x i * w i
        ≤ (n : ℝ)⁻¹ * (Real.sqrt (∑ i, x i ^ 2) * (Real.sqrt n * sn)) := hmul
      _ = (sn / Real.sqrt n) * Real.sqrt (∑ i, x i ^ 2) := by
          field_simp [ne_of_gt (Real.sqrt_pos.mpr hn_pos)]
          rw [Real.sq_sqrt hn_pos.le]
          ring
  have hterm_y : (n : ℝ)⁻¹ * ∑ i, y i * w i ≤
      (sn / Real.sqrt n) * (Real.sqrt (1 - C * ε) / Real.sqrt ρ) * (ε * ∑ i, |y i|) := by
    calc (n : ℝ)⁻¹ * ∑ i, y i * w i
        ≤ (n : ℝ)⁻¹ * ∑ i, |y i * w i| :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => le_abs_self _)
            (inv_nonneg.mpr hn_pos.le)
      _ = (n : ℝ)⁻¹ * ∑ i, |y i| * |w i| := by simp_rw [abs_mul]
      _ ≤ (n : ℝ)⁻¹ * ∑ i, |y i| *
            (Real.sqrt n * ε * sn * (Real.sqrt (1 - C * ε) / Real.sqrt ρ)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hw_inf i) (abs_nonneg _))
            (inv_nonneg.mpr hn_pos.le)
      _ = (n : ℝ)⁻¹ * ((∑ i, |y i|) *
            (Real.sqrt n * ε * sn * (Real.sqrt (1 - C * ε) / Real.sqrt ρ))) := by
          rw [← Finset.sum_mul]
      _ = (sn / Real.sqrt n) * (Real.sqrt (1 - C * ε) / Real.sqrt ρ) * (ε * ∑ i, |y i|) := by
          field_simp [ne_of_gt (Real.sqrt_pos.mpr hn_pos), ne_of_gt (Real.sqrt_pos.mpr hρ)]
          rw [Real.sq_sqrt hn_pos.le]
          ring
  let A : ℝ := Real.sqrt (∑ i, x i ^ 2)
  let lam : ℝ := Real.sqrt ρ / Real.sqrt (1 - C * ε)
  have hlam_pos : 0 < lam := by positivity
  have hamgm : A ≤ (Real.sqrt (1 - C * ε) / Real.sqrt ρ) * ((∑ i, x i ^ 2) / 2) + lam / 2 := by
    have hA_sq : A ^ 2 = ∑ i, x i ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hsq_nonneg : 0 ≤ (A - lam) ^ 2 := sq_nonneg _
    have h1 : 2 * lam * A ≤ A ^ 2 + lam ^ 2 := by nlinarith
    have h2 : A ≤ (A ^ 2 + lam ^ 2) / (2 * lam) := (le_div_iff₀' (by positivity)).mpr h1
    have h3 : (A ^ 2 + lam ^ 2) / (2 * lam) =
        (Real.sqrt (1 - C * ε) / Real.sqrt ρ) * ((∑ i, x i ^ 2) / 2) + lam / 2 := by
      rw [← hA_sq]
      dsimp [lam]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hρ), ne_of_gt (Real.sqrt_pos.mpr h1Cε_pos)]
    linarith
  have hsum_xy : (∑ i, x i ^ 2) / 2 + ε * ∑ i, |y i| = ∑ i, huber ε ((n : ℝ) * u i) := by
    calc (∑ i, x i ^ 2) / 2 + ε * ∑ i, |y i|
        = ∑ i, (x i ^ 2 / 2 + ε * |y i|) := by
          rw [Finset.sum_add_distrib, Finset.sum_div, ← Finset.mul_sum]
      _ = ∑ i, huber ε ((n : ℝ) * u i) :=
          Finset.sum_congr rfl fun i _ => (hhub_xy i).symm
  dsimp only
  rw [huz, hsplit]
  have hsn_div_nonneg : 0 ≤ sn / Real.sqrt n := by positivity
  calc (n : ℝ)⁻¹ * ∑ i, x i * w i + (n : ℝ)⁻¹ * ∑ i, y i * w i
      ≤ (sn / Real.sqrt n) * A +
          (sn / Real.sqrt n) * (Real.sqrt (1 - C * ε) / Real.sqrt ρ) * (ε * ∑ i, |y i|) :=
        add_le_add hterm_x hterm_y
    _ ≤ (sn / Real.sqrt n) *
          ((Real.sqrt (1 - C * ε) / Real.sqrt ρ) * ((∑ i, x i ^ 2) / 2) + lam / 2) +
          (sn / Real.sqrt n) * (Real.sqrt (1 - C * ε) / Real.sqrt ρ) * (ε * ∑ i, |y i|) :=
        add_le_add_left (mul_le_mul_of_nonneg_left hamgm hsn_div_nonneg) _
    _ = (sn / Real.sqrt n) *
          ((Real.sqrt (1 - C * ε) / Real.sqrt ρ) * ∑ i, huber ε ((n : ℝ) * u i) + lam / 2) := by
        rw [← hsum_xy]
        ring
    _ ≤ (sn / Real.sqrt n) *
          ((Real.sqrt (1 - C * ε) / Real.sqrt ρ) * (ρ / (2 * (1 - C * ε))) + lam / 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) hsn_div_nonneg
        exact mul_le_mul_of_nonneg_left hu_hub (by positivity)
    _ = Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 - C * ε)) := by
        dsimp [sn, lam]
        rw [Real.sqrt_mul (div_nonneg hρ.le hn_pos.le), Real.sqrt_div hρ.le]
        have hsqρ : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ.le
        have hsq1 : Real.sqrt (1 - C * ε) ^ 2 = 1 - C * ε := Real.sq_sqrt h1Cε_pos.le
        field_simp [ne_of_gt (Real.sqrt_pos.mpr hn_pos), ne_of_gt (Real.sqrt_pos.mpr hρ),
          ne_of_gt (Real.sqrt_pos.mpr h1Cε_pos), ne_of_gt h1Cε_pos]
        rw [hsqρ, hsq1]
        ring
