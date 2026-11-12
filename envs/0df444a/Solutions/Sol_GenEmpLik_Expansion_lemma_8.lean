-- Prove2me | solution 1 for GenEmpLik.Expansion.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:56:50.317266+00:00
-- url     : https://prove2.me/submissions/85817f85-780b-4c4c-a90d-f17aa8c7da3c

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_reparamSets
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar

open VarianceRegularization.Expansion

private lemma sum_mul_le_sqrt_mul_sqrt {n : ℕ} (a b : Fin n → ℝ) :
    ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  have hA_nonneg : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB_nonneg : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
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

open GenEmpLik.Expansion in
theorem solution {n : ℕ} (hn : 0 < n) {ρ ε C : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hC : 0 ≤ C)
    (z : Fin n → ℝ)
    (hz : (⨆ i, |z i - empMean z|) / Real.sqrt n ≤
      ε * Real.sqrt (empVar z) * Real.sqrt ((1 + C * ε) / ρ)) :
    sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Usm n ε C ρ) =
      Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 + C * ε)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h1Cε_pos : 0 < 1 + C * ε := by nlinarith
  let w : Fin n → ℝ := fun i => z i - empMean z
  have hw_sum : ∑ i, w i = 0 := by
    dsimp [w, empMean]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
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
  have hvar_nonneg : 0 ≤ empVar z := by
    have : 0 ≤ (n : ℝ) * empVar z := by
      rw [← hw_sq]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    exact nonneg_of_mul_nonneg_right this hn_pos
  let RHS : ℝ := Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 + C * ε))
  have h0_mem : (0 : Fin n → ℝ) ∈ Usm n ε C ρ := by
    refine ⟨by simp, fun _ => by simp [le_of_lt hε], ?_⟩
    simp [le_of_lt hρ]
  have hub_all : ∀ u ∈ Usm n ε C ρ, ∑ i, u i * z i ≤ RHS := by
    intro u ⟨hu_sum, _, hu_quad⟩
    have huz : ∑ i, u i * z i = ∑ i, u i * w i := by
      calc ∑ i, u i * z i
          = ∑ i, (u i * w i + u i * empMean z) :=
            Finset.sum_congr rfl fun i _ => by dsimp [w]; ring
        _ = ∑ i, u i * w i + (∑ i, u i) * empMean z := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        _ = ∑ i, u i * w i := by rw [hu_sum, zero_mul, add_zero]
    have hu_sq : ∑ i, u i ^ 2 ≤ ρ / ((n : ℝ) ^ 2 * (1 + C * ε)) := by
      have h1 : (n : ℝ) ^ 2 * (1 + C * ε) * ∑ i, u i ^ 2 ≤ ρ := by
        have heq : (1 + C * ε) * ∑ i, ((n : ℝ) * u i) ^ 2 =
            (n : ℝ) ^ 2 * (1 + C * ε) * ∑ i, u i ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
        linarith
      exact (le_div_iff₀' (by positivity)).mpr h1
    rw [huz]
    calc ∑ i, u i * w i
        ≤ Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, w i ^ 2) := sum_mul_le_sqrt_mul_sqrt u w
      _ ≤ Real.sqrt (ρ / ((n : ℝ) ^ 2 * (1 + C * ε))) * Real.sqrt ((n : ℝ) * empVar z) := by
          rw [hw_sq]
          exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hu_sq) (Real.sqrt_nonneg _)
      _ = RHS := by
          dsimp [RHS]
          rw [Real.sqrt_div (le_of_lt hρ), Real.sqrt_mul (sq_nonneg (n : ℝ)),
            Real.sqrt_sq (le_of_lt hn_pos), Real.sqrt_mul hn_pos.le,
            Real.sqrt_mul (div_nonneg hρ.le hn_pos.le), Real.sqrt_div hρ.le]
          have hsqn : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn_pos)
          have hsq1 : Real.sqrt (1 + C * ε) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1Cε_pos)
          field_simp
          rw [Real.sq_sqrt hn_pos.le]
  have hbdd : BddAbove ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Usm n ε C ρ) := by
    refine ⟨RHS, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hub_all u hu
  have hle_rhs : sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Usm n ε C ρ) ≤ RHS := by
    refine csSup_le ⟨0, 0, h0_mem, by simp⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hub_all u hu
  apply le_antisymm hle_rhs
  rcases eq_or_lt_of_le hvar_nonneg with hvar0 | hvar_pos
  · have hrhs0 : RHS = 0 := by simp [RHS, ← hvar0]
    rw [hrhs0]
    exact le_csSup hbdd ⟨0, h0_mem, by simp⟩
  · let sn : ℝ := Real.sqrt (empVar z)
    have hsn_pos : 0 < sn := Real.sqrt_pos.mpr hvar_pos
    let α : ℝ := Real.sqrt ρ / ((n : ℝ) * Real.sqrt n * sn * Real.sqrt (1 + C * ε))
    let uStar : Fin n → ℝ := fun i => α * w i
    have huStar_mem : uStar ∈ Usm n ε C ρ := by
      refine ⟨?_, ?_, ?_⟩
      · dsimp [uStar]
        rw [← Finset.mul_sum, hw_sum, mul_zero]
      · intro i
        have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        have hb_range : BddAbove (Set.range fun j : Fin n => |w j|) := Set.toFinite _ |>.bddAbove
        have hi_le : |w i| ≤ ⨆ j : Fin n, |w j| := le_ciSup hb_range i
        have hi_div : |w i| / Real.sqrt n ≤
            ε * sn * (Real.sqrt (1 + C * ε) / Real.sqrt ρ) := by
          calc |w i| / Real.sqrt n
              ≤ (⨆ j : Fin n, |w j|) / Real.sqrt n :=
                div_le_div_of_nonneg_right hi_le (Real.sqrt_nonneg _)
            _ ≤ ε * sn * Real.sqrt ((1 + C * ε) / ρ) := hz
            _ = ε * sn * (Real.sqrt (1 + C * ε) / Real.sqrt ρ) := by
                rw [Real.sqrt_div h1Cε_pos.le]
        have hα_pos : 0 < α := by positivity
        have hcalc : |(n : ℝ) * uStar i| =
            (|w i| / Real.sqrt n) * (Real.sqrt ρ / (sn * Real.sqrt (1 + C * ε))) := by
          change |(n : ℝ) * (α * w i)| = _
          rw [abs_mul, abs_mul, abs_of_pos hn_pos, abs_of_pos hα_pos]
          dsimp [α]
          field_simp [hn_ne, ne_of_gt (Real.sqrt_pos.mpr hn_pos), ne_of_gt hsn_pos,
            ne_of_gt (Real.sqrt_pos.mpr h1Cε_pos)]
        rw [hcalc]
        calc (|w i| / Real.sqrt n) * (Real.sqrt ρ / (sn * Real.sqrt (1 + C * ε)))
            ≤ (ε * sn * (Real.sqrt (1 + C * ε) / Real.sqrt ρ)) *
                (Real.sqrt ρ / (sn * Real.sqrt (1 + C * ε))) :=
              mul_le_mul_of_nonneg_right hi_div (by positivity)
          _ = ε := by
              field_simp [ne_of_gt (Real.sqrt_pos.mpr hρ), ne_of_gt hsn_pos,
                ne_of_gt (Real.sqrt_pos.mpr h1Cε_pos)]
      · have heq : (1 + C * ε) * ∑ i, ((n : ℝ) * uStar i) ^ 2 = ρ := by
          have h1 : ∑ i, ((n : ℝ) * uStar i) ^ 2 = (n : ℝ) ^ 2 * α ^ 2 * ∑ i, w i ^ 2 := by
            dsimp [uStar]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
          rw [h1, hw_sq]
          dsimp [α]
          field_simp [hn_ne, ne_of_gt (Real.sqrt_pos.mpr hn_pos), ne_of_gt hsn_pos,
            ne_of_gt (Real.sqrt_pos.mpr h1Cε_pos)]
          rw [Real.sq_sqrt hρ.le, Real.sq_sqrt hn_pos.le, Real.sq_sqrt h1Cε_pos.le]
          have hsn_sq : sn ^ 2 = empVar z := Real.sq_sqrt hvar_pos.le
          rw [hsn_sq]
          ring
        linarith
    have huStar_val : ∑ i, uStar i * z i = RHS := by
      have huz : ∑ i, uStar i * z i = α * ∑ i, w i ^ 2 := by
        calc ∑ i, uStar i * z i
            = ∑ i, (α * w i ^ 2 + α * empMean z * w i) :=
              Finset.sum_congr rfl fun i _ => by dsimp [uStar, w]; ring
          _ = α * ∑ i, w i ^ 2 + α * empMean z * ∑ i, w i := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = α * ∑ i, w i ^ 2 := by rw [hw_sum, mul_zero, add_zero]
      rw [huz, hw_sq]
      dsimp [α, RHS]
      rw [Real.sqrt_mul (div_nonneg hρ.le hn_pos.le), Real.sqrt_div hρ.le]
      change Real.sqrt ρ / (↑n * Real.sqrt ↑n * sn * Real.sqrt (1 + C * ε)) * (↑n * empVar z) =
        Real.sqrt ρ / Real.sqrt ↑n * sn * (1 / Real.sqrt (1 + C * ε))
      have hsn_sq : empVar z = sn ^ 2 := (Real.sq_sqrt hvar_pos.le).symm
      rw [hsn_sq]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hn_pos), ne_of_gt hsn_pos,
        ne_of_gt (Real.sqrt_pos.mpr h1Cε_pos)]
    rw [← huStar_val]
    exact le_csSup hbdd ⟨uStar, huStar_mem, rfl⟩
