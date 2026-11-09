-- Prove2me | solution 1 for BookProof.CarlemanSimplex.ladderQ_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T08:10:58.033192+00:00
-- url     : https://prove2.me/submissions/a0f9b27f-6251-4464-acee-7ea91d1dc586
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.ladderQ_eq_zero
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_apply_le_deg
import Theorems.Thm_BookProof_CarlemanSimplex_deg_single
import Theorems.Thm_BookProof_CarlemanSimplex_mem_simplexF
import Theorems.Thm_BookProof_CarlemanSimplex_mem_sBd
import Theorems.Thm_BookProof_CarlemanSimplex_deg_pvec
import Theorems.Thm_BookProof_CarlemanSimplex_rcp_nonneg
import Theorems.Thm_BookProof_CarlemanSimplex_flux_identityQ
import Theorems.Thm_BookProof_CarlemanSimplex_flux_bound_on
import Theorems.Thm_BookProof_CarlemanSimplex_sBd_mass_le
import Theorems.Thm_BookProof_CarlemanSimplex_not_summable_inv_natCast_add_two
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_shifted_sBd_mass_le
import Theorems.Thm_BookProof_CarlemanTwoStep_rc1_nonneg
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {B : ℝ} (hz : z.im ≠ 0)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j))
    (hrec : LadderRecQ u lam w W M z) : ∀ a, u a = 0 := by

  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨a₀, ha₀⟩ := hcon
  set mass : ℕ → (Fin d →₀ ℕ) → ℝ := fun N P =>
    (∑ a ∈ sBd d N (deg P), (‖u a‖ ^ 2 + ‖u (a + P)‖ ^ 2)) / 2 with hmass
  set A : ℕ → ℝ := fun N =>
    (∑ i, ‖w i‖ * mass N (Finsupp.single i 1)) + ∑ i, ∑ j, ‖W i j‖ * mass N (pvec i j)
    with hAdef
  have hmass_nonneg : ∀ N P, 0 ≤ mass N P := by
    intro N P
    have hs : 0 ≤ ∑ a ∈ sBd d N (deg P), (‖u a‖ ^ 2 + ‖u (a + P)‖ ^ 2) :=
      Finset.sum_nonneg fun a _ => by positivity
    rw [hmass]
    positivity
  have hAnn : ∀ N, 0 ≤ A N := by
    intro N
    have h1 : 0 ≤ ∑ i, ‖w i‖ * mass N (Finsupp.single i 1) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hmass_nonneg N _)
    have h2 : 0 ≤ ∑ i, ∑ j, ‖W i j‖ * mass N (pvec i j) :=
      Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hmass_nonneg N _)
    rw [hAdef]
    linarith
  -- the total boundary mass is finite
  have hmass_sum : ∀ (P : Fin d →₀ ℕ) (Mx : ℕ),
      ∑ N ∈ Finset.range Mx, mass N P ≤ ((deg P : ℕ) : ℝ) * B := by
    intro P Mx
    have h1 := sBd_mass_le hbes (deg P) Mx
    have h2 := shifted_sBd_mass_le hbes P Mx
    have hpt : ∀ N : ℕ, mass N P
        = ((∑ a ∈ sBd d N (deg P), ‖u a‖ ^ 2)
            + ∑ a ∈ sBd d N (deg P), ‖u (a + P)‖ ^ 2) / 2 := by
      intro N; simp only [hmass]; rw [Finset.sum_add_distrib]
    simp_rw [hpt]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  have hApart : ∀ Mx, ∑ N ∈ Finset.range Mx, A N
      ≤ ((∑ i, ‖w i‖) * (1 * B)) + (∑ i, ∑ j, ‖W i j‖) * (2 * B) := by
    intro Mx
    have hsplit : ∑ N ∈ Finset.range Mx, A N
        = (∑ N ∈ Finset.range Mx, ∑ i, ‖w i‖ * mass N (Finsupp.single i 1))
          + ∑ N ∈ Finset.range Mx, ∑ i, ∑ j, ‖W i j‖ * mass N (pvec i j) := by
      rw [hAdef, ← Finset.sum_add_distrib]
    have hb1 : ∑ N ∈ Finset.range Mx, ∑ i, ‖w i‖ * mass N (Finsupp.single i 1)
        ≤ (∑ i, ‖w i‖) * (1 * B) := by
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      calc ∑ N ∈ Finset.range Mx, ‖w i‖ * mass N (Finsupp.single i 1)
          = ‖w i‖ * ∑ N ∈ Finset.range Mx, mass N (Finsupp.single i 1) := by rw [Finset.mul_sum]
        _ ≤ ‖w i‖ * (1 * B) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            have := hmass_sum (Finsupp.single i 1) Mx
            rw [deg_single] at this
            simpa using this
    have hb2 : ∑ N ∈ Finset.range Mx, ∑ i, ∑ j, ‖W i j‖ * mass N (pvec i j)
        ≤ (∑ i, ∑ j, ‖W i j‖) * (2 * B) := by
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      calc ∑ N ∈ Finset.range Mx, ‖W i j‖ * mass N (pvec i j)
          = ‖W i j‖ * ∑ N ∈ Finset.range Mx, mass N (pvec i j) := by rw [Finset.mul_sum]
        _ ≤ ‖W i j‖ * (2 * B) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            have := hmass_sum (pvec i j) Mx
            rw [deg_pvec] at this
            simpa using this
    rw [hsplit]
    push_cast at hb1 hb2
    linarith
  have hsummable : Summable A := summable_of_sum_range_le hAnn hApart
  -- the amplitude bound on the boundary
  have hC1 : ∀ (N : ℕ) (i : Fin d), ∀ a ∈ sBd d N 1, |rc1 a i| ≤ (N : ℝ) + 2 := by
    intro N i a ha
    rw [mem_sBd] at ha
    have hai : ((a i : ℝ)) ≤ (N : ℝ) := by
      exact_mod_cast le_trans (apply_le_deg a i) ha.1
    have h1 : rc1 a i ≤ (N : ℝ) + 2 := by
      rw [rc1]
      have : Real.sqrt ((a i : ℝ) + 1) ≤ Real.sqrt (((N : ℝ) + 2) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      rwa [Real.sqrt_sq (by positivity)] at this
    rw [abs_of_nonneg (rc1_nonneg a i)]
    exact h1
  have hC2 : ∀ (N : ℕ) (i j : Fin d), ∀ a ∈ sBd d N 2, |rcp a i j| ≤ (N : ℝ) + 2 := by
    intro N i j a ha
    rw [mem_sBd] at ha
    have haj : ((a j : ℝ)) ≤ (N : ℝ) := by
      exact_mod_cast le_trans (apply_le_deg a j) ha.1
    have hai : (((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
      have : ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) ≤ a i + 1 := by
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        by_cases h : j = i <;> simp [h]
      have h2 : (a i : ℕ) ≤ N := le_trans (apply_le_deg a i) ha.1
      have : ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) ≤ N + 1 := by omega
      exact_mod_cast this
    have hs1 : Real.sqrt ((a j : ℝ) + 1) ≤ Real.sqrt (((N : ℝ) + 2)) := by
      refine Real.sqrt_le_sqrt ?_
      linarith
    have hs2 : Real.sqrt ((((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℝ) + 1)
        ≤ Real.sqrt (((N : ℝ) + 2)) := by
      refine Real.sqrt_le_sqrt ?_
      linarith
    have hnn : (0 : ℝ) ≤ Real.sqrt ((N : ℝ) + 2) := Real.sqrt_nonneg _
    have hprod : rcp a i j ≤ Real.sqrt ((N : ℝ) + 2) * Real.sqrt ((N : ℝ) + 2) := by
      rw [rcp]
      exact mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) hnn
    have hsq : Real.sqrt ((N : ℝ) + 2) * Real.sqrt ((N : ℝ) + 2) = (N : ℝ) + 2 :=
      Real.mul_self_sqrt (by positivity)
    rw [abs_of_nonneg (rcp_nonneg a i j)]
    linarith [hprod, hsq]
  have hkey : ∀ N : ℕ,
      |z.im| * (∑ a ∈ simplexF d N, ‖u a‖ ^ 2) ≤ ((N : ℝ) + 2) * A N := by
    intro N
    have hS : 0 ≤ ∑ a ∈ simplexF d N, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    have h1 : |z.im| * (∑ a ∈ simplexF d N, ‖u a‖ ^ 2)
        = |(∑ i, (∑ a ∈ sBd d N 1,
                rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a).im)
            + ∑ i, ∑ j, (∑ a ∈ sBd d N 2,
                rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im| := by
      rw [← flux_identityQ hM hrec N, abs_mul, abs_of_nonneg hS]
    rw [h1]
    have hb1 : |∑ i, (∑ a ∈ sBd d N 1,
          rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a).im|
        ≤ ((N : ℝ) + 2) * ∑ i, ‖w i‖ * mass N (Finsupp.single i 1) := by
      calc |∑ i, (∑ a ∈ sBd d N 1,
              rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a).im|
          ≤ ∑ i, |(∑ a ∈ sBd d N 1,
              rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a).im| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ((N : ℝ) + 2) * (‖w i‖ * mass N (Finsupp.single i 1)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h := flux_bound_on (u := u) (w := w i) (rc := fun b => rc1 b i)
              (sBd d N 1) (Finsupp.single i 1) (Cn := (N : ℝ) + 2) (hC1 N i)
            have hd : deg (Finsupp.single i 1 : Fin d →₀ ℕ) = 1 := deg_single i 1
            simpa [hmass, hd] using h
        _ = ((N : ℝ) + 2) * ∑ i, ‖w i‖ * mass N (Finsupp.single i 1) := by rw [Finset.mul_sum]
    have hb2 : |∑ i, ∑ j, (∑ a ∈ sBd d N 2,
          rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im|
        ≤ ((N : ℝ) + 2) * ∑ i, ∑ j, ‖W i j‖ * mass N (pvec i j) := by
      calc |∑ i, ∑ j, (∑ a ∈ sBd d N 2,
              rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im|
          ≤ ∑ i, |∑ j, (∑ a ∈ sBd d N 2,
              rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ((N : ℝ) + 2) * ∑ j, (‖W i j‖ * mass N (pvec i j)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc |∑ j, (∑ a ∈ sBd d N 2,
                    rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im|
                ≤ ∑ j, |(∑ a ∈ sBd d N 2,
                    rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ j, ((N : ℝ) + 2) * (‖W i j‖ * mass N (pvec i j)) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  have h := flux_bound_on (u := u) (w := W i j) (rc := fun b => rcp b i j)
                    (sBd d N 2) (pvec i j) (Cn := (N : ℝ) + 2) (hC2 N i j)
                  have hd : deg (pvec (d := d) i j) = 2 := deg_pvec i j
                  simpa [hmass, hd] using h
              _ = ((N : ℝ) + 2) * ∑ j, (‖W i j‖ * mass N (pvec i j)) := by rw [Finset.mul_sum]
        _ = ((N : ℝ) + 2) * ∑ i, ∑ j, ‖W i j‖ * mass N (pvec i j) := by rw [Finset.mul_sum]
    have habs := abs_add_le
      (∑ i, (∑ a ∈ sBd d N 1,
        rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a).im)
      (∑ i, ∑ j, (∑ a ∈ sBd d N 2,
        rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im)
    rw [hAdef]
    simp only
    rw [mul_add]
    linarith
  -- the shell mass is bounded below
  set N₀ : ℕ := deg a₀ with hN₀
  have hlow : ∀ N : ℕ, N₀ ≤ N → ‖u a₀‖ ^ 2 ≤ ∑ a ∈ simplexF d N, ‖u a‖ ^ 2 := by
    intro N hN
    refine Finset.single_le_sum (f := fun a => ‖u a‖ ^ 2) (fun a _ => by positivity) ?_
    rw [mem_simplexF]
    exact hN
  have hcpos : 0 < |z.im| * ‖u a₀‖ ^ 2 := by
    have h1 : 0 < |z.im| := abs_pos.mpr hz
    have h2 : 0 < ‖u a₀‖ ^ 2 := by
      have : 0 < ‖u a₀‖ := norm_pos_iff.mpr ha₀
      positivity
    positivity
  have hAlow : ∀ N : ℕ, N₀ ≤ N →
      (|z.im| * ‖u a₀‖ ^ 2) * ((N : ℝ) + 2)⁻¹ ≤ A N := by
    intro N hN
    have hpos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have h1 := hkey N
    have h2 := hlow N hN
    have h3 : |z.im| * ‖u a₀‖ ^ 2 ≤ ((N : ℝ) + 2) * A N := by
      have := mul_le_mul_of_nonneg_left h2 (abs_nonneg z.im)
      linarith
    have h5 : (|z.im| * ‖u a₀‖ ^ 2) * ((N : ℝ) + 2)⁻¹
        = (|z.im| * ‖u a₀‖ ^ 2) / ((N : ℝ) + 2) := by
      field_simp
    rw [h5, div_le_iff₀ hpos]
    linarith [h3, mul_comm ((N : ℝ) + 2) (A N)]
  have hshift : Summable (fun N : ℕ => A (N + N₀)) := (summable_nat_add_iff N₀).mpr hsummable
  have hcomp : Summable (fun N : ℕ =>
      (|z.im| * ‖u a₀‖ ^ 2) * (((N + N₀ : ℕ) : ℝ) + 2)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hshift
    exact hAlow (N + N₀) (Nat.le_add_left _ _)
  have h4 : Summable (fun N : ℕ => (((N + N₀ : ℕ) : ℝ) + 2)⁻¹) := by
    have h5 := hcomp.mul_left (|z.im| * ‖u a₀‖ ^ 2)⁻¹
    refine h5.congr fun N => ?_
    field_simp
  exact not_summable_inv_natCast_add_two ((summable_nat_add_iff N₀).mp h4)
