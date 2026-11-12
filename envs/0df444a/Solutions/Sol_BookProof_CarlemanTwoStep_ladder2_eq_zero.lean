-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.ladder2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-11T06:13:59.441127+00:00
-- url     : https://prove2.me/submissions/f8f3785d-e7cc-4d42-942a-bc9abc591a75

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.ladder2_eq_zero
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_CarlemanTwoStep_mem_faceK
import Theorems.Thm_BookProof_CarlemanTwoStep_rc2_nonneg
import Theorems.Thm_BookProof_CarlemanTwoStep_rc1_nonneg
import Theorems.Thm_BookProof_CarlemanTwoStep_flux_identity2
import Theorems.Thm_BookProof_CarlemanTwoStep_flux_boundG
import Theorems.Thm_BookProof_CarlemanTwoStep_facesK_le
import Theorems.Thm_BookProof_CarlemanTwoStep_shifted_facesK_le
import Theorems.Thm_BookProof_CarlemanTwoStep_not_summable_inv_natCast_succ
import Theorems.Thm_BookProof_HermiteCarleman_mem_cube_inc
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {B : ℝ} (hz : z.im ≠ 0)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (hrec : LadderRec2 u lam w1 w2 z) : ∀ a, u a = 0 := by

  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨a₀, ha₀⟩ := hcon
  -- the boundary mass functional
  set mass : ℕ → Fin d → ℕ → ℝ := fun N i k =>
    (∑ a ∈ faceK d N i k, (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2)) / 2 with hmass
  set A : ℕ → ℝ := fun N =>
    (∑ i, ‖w1 i‖ * mass N i 1) + ∑ i, ‖w2 i‖ * mass N i 2 with hAdef
  have hmass_nonneg : ∀ N i k, 0 ≤ mass N i k := by
    intro N i k
    have hs : 0 ≤ ∑ a ∈ faceK d N i k, (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) :=
      Finset.sum_nonneg fun a _ => by positivity
    rw [hmass]
    positivity
  have hAnn : ∀ N, 0 ≤ A N := by
    intro N
    have h1 : 0 ≤ ∑ i, ‖w1 i‖ * mass N i 1 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hmass_nonneg N i 1)
    have h2 : 0 ≤ ∑ i, ‖w2 i‖ * mass N i 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hmass_nonneg N i 2)
    rw [hAdef]
    linarith
  -- the total boundary mass is finite
  have hmass_sum : ∀ (i : Fin d) (k M : ℕ),
      ∑ N ∈ Finset.range M, mass N i k ≤ (k : ℝ) * B := by
    intro i k M
    have h1 := facesK_le hbes i k M
    have h2 := shifted_facesK_le hbes i k M
    have hpt : ∀ N : ℕ, mass N i k
        = ((∑ a ∈ faceK d N i k, ‖u a‖ ^ 2)
            + ∑ a ∈ faceK d N i k, ‖u (a + Finsupp.single i k)‖ ^ 2) / 2 := by
      intro N; simp only [hmass]; rw [Finset.sum_add_distrib]
    simp_rw [hpt]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  have hApart : ∀ M, ∑ N ∈ Finset.range M, A N
      ≤ ((∑ i, ‖w1 i‖) * (1 * B)) + (∑ i, ‖w2 i‖) * (2 * B) := by
    intro M
    have hsplit : ∑ N ∈ Finset.range M, A N
        = (∑ N ∈ Finset.range M, ∑ i, ‖w1 i‖ * mass N i 1)
          + ∑ N ∈ Finset.range M, ∑ i, ‖w2 i‖ * mass N i 2 := by
      rw [hAdef, ← Finset.sum_add_distrib]
    have hb : ∀ (k : ℕ) (W : Fin d → ℂ),
        ∑ N ∈ Finset.range M, ∑ i, ‖W i‖ * mass N i k
          ≤ (∑ i, ‖W i‖) * ((k : ℝ) * B) := by
      intro k W
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      calc ∑ N ∈ Finset.range M, ‖W i‖ * mass N i k
          = ‖W i‖ * ∑ N ∈ Finset.range M, mass N i k := by rw [Finset.mul_sum]
        _ ≤ ‖W i‖ * ((k : ℝ) * B) :=
            mul_le_mul_of_nonneg_left (hmass_sum i k M) (norm_nonneg _)
    have h1 := hb 1 w1
    have h2 := hb 2 w2
    rw [hsplit]
    push_cast at h1 h2
    linarith
  have hsummable : Summable A := summable_of_sum_range_le hAnn hApart
  -- the flux bound, with the uniform amplitude bound `2(N+1)`
  have hCn : ∀ N : ℕ, (0 : ℝ) ≤ 2 * ((N : ℝ) + 1) := by intro N; positivity
  have hC1 : ∀ (N : ℕ) (i : Fin d), ∀ a ∈ faceK d N i 1, |rc1 a i| ≤ 2 * ((N : ℝ) + 1) := by
    intro N i a ha
    rw [mem_faceK] at ha
    have hai : ((a i : ℝ)) ≤ (N : ℝ) := by exact_mod_cast ha.1 i
    have h1 : rc1 a i ≤ (N : ℝ) + 1 := by
      rw [rc1]
      have : Real.sqrt ((a i : ℝ) + 1) ≤ Real.sqrt (((N : ℝ) + 1) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      rwa [Real.sqrt_sq (by positivity)] at this
    rw [abs_of_nonneg (rc1_nonneg a i)]
    linarith
  have hC2 : ∀ (N : ℕ) (i : Fin d), ∀ a ∈ faceK d N i 2, |rc2 a i| ≤ 2 * ((N : ℝ) + 1) := by
    intro N i a ha
    rw [mem_faceK] at ha
    have hai : ((a i : ℝ)) ≤ (N : ℝ) := by exact_mod_cast ha.1 i
    have h1 : rc2 a i ≤ (N : ℝ) + 2 := by
      rw [rc2]
      have : Real.sqrt (((a i : ℝ) + 1) * ((a i : ℝ) + 2)) ≤ Real.sqrt (((N : ℝ) + 2) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [Nat.cast_nonneg (α := ℝ) (a i)]
      rwa [Real.sqrt_sq (by positivity)] at this
    rw [abs_of_nonneg (rc2_nonneg a i)]
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hkey : ∀ N : ℕ,
      |z.im| * (∑ a ∈ cube d N, ‖u a‖ ^ 2) ≤ (2 * ((N : ℝ) + 1)) * A N := by
    intro N
    have hS : 0 ≤ ∑ a ∈ cube d N, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    have h1 : |z.im| * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
        = |(∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im)
            + ∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im| := by
      rw [← flux_identity2 hrec N, abs_mul, abs_of_nonneg hS]
    rw [h1]
    have hb1 : |∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im|
        ≤ (2 * ((N : ℝ) + 1)) * ∑ i, ‖w1 i‖ * mass N i 1 := by
      calc |∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im|
          ≤ ∑ i, |(∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (2 * ((N : ℝ) + 1)) * (‖w1 i‖ * mass N i 1) :=
            Finset.sum_le_sum fun i _ => flux_boundG N i 1 (hCn N) (hC1 N i)
        _ = (2 * ((N : ℝ) + 1)) * ∑ i, ‖w1 i‖ * mass N i 1 := by rw [Finset.mul_sum]
    have hb2 : |∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im|
        ≤ (2 * ((N : ℝ) + 1)) * ∑ i, ‖w2 i‖ * mass N i 2 := by
      calc |∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im|
          ≤ ∑ i, |(∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (2 * ((N : ℝ) + 1)) * (‖w2 i‖ * mass N i 2) :=
            Finset.sum_le_sum fun i _ => flux_boundG N i 2 (hCn N) (hC2 N i)
        _ = (2 * ((N : ℝ) + 1)) * ∑ i, ‖w2 i‖ * mass N i 2 := by rw [Finset.mul_sum]
    have habs := abs_add_le (∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im)
      (∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im)
    rw [hAdef]
    simp only
    rw [mul_add]
    linarith
  -- the cube mass is bounded below
  set N₀ : ℕ := Finset.univ.sup (fun i : Fin d => a₀ i) with hN₀
  have hlow : ∀ N : ℕ, N₀ ≤ N → ‖u a₀‖ ^ 2 ≤ ∑ a ∈ cube d N, ‖u a‖ ^ 2 := by
    intro N hN
    refine Finset.single_le_sum (f := fun a => ‖u a‖ ^ 2) (fun a _ => by positivity) ?_
    rw [mem_cube_inc]
    intro i
    exact le_trans (Finset.le_sup (f := fun i : Fin d => a₀ i) (Finset.mem_univ i)) hN
  have hcpos : 0 < |z.im| * ‖u a₀‖ ^ 2 := by
    have h1 : 0 < |z.im| := abs_pos.mpr hz
    have h2 : 0 < ‖u a₀‖ ^ 2 := by
      have : 0 < ‖u a₀‖ := norm_pos_iff.mpr ha₀
      positivity
    positivity
  have hAlow : ∀ N : ℕ, N₀ ≤ N →
      ((|z.im| * ‖u a₀‖ ^ 2) / 2) * ((N : ℝ) + 1)⁻¹ ≤ A N := by
    intro N hN
    have hpos : (0 : ℝ) < 2 * ((N : ℝ) + 1) := by positivity
    have h1 := hkey N
    have h2 := hlow N hN
    have h3 : |z.im| * ‖u a₀‖ ^ 2 ≤ (2 * ((N : ℝ) + 1)) * A N := by
      have := mul_le_mul_of_nonneg_left h2 (abs_nonneg z.im)
      linarith
    have h5 : ((|z.im| * ‖u a₀‖ ^ 2) / 2) * ((N : ℝ) + 1)⁻¹
        = (|z.im| * ‖u a₀‖ ^ 2) / (2 * ((N : ℝ) + 1)) := by
      field_simp
    rw [h5, div_le_iff₀ hpos]
    linarith [h3, mul_comm (2 * ((N : ℝ) + 1)) (A N)]
  have hshift : Summable (fun N : ℕ => A (N + N₀)) := (summable_nat_add_iff N₀).mpr hsummable
  have hcomp : Summable (fun N : ℕ =>
      ((|z.im| * ‖u a₀‖ ^ 2) / 2) * (((N + N₀ : ℕ) : ℝ) + 1)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hshift
    exact hAlow (N + N₀) (Nat.le_add_left _ _)
  have h4 : Summable (fun N : ℕ => (((N + N₀ : ℕ) : ℝ) + 1)⁻¹) := by
    have h5 := hcomp.mul_left ((|z.im| * ‖u a₀‖ ^ 2) / 2)⁻¹
    refine h5.congr fun N => ?_
    field_simp
  exact not_summable_inv_natCast_succ ((summable_nat_add_iff N₀).mp h4)
