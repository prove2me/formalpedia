-- Prove2me | solution 1 for FastCLO.LowerBound.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:01:29.7417+00:00
-- url     : https://prove2.me/submissions/de31ce13-d635-4005-869d-5f1915c93059

import Mathlib
import Definitions.Def_FastCLO_LowerBound_Model
import Definitions.Def_FastCLO_LowerBound_Rho

open scoped InnerProductSpace

open FastCLO.LowerBound in
theorem solution {d : ℕ} (P : Polytope d) (hnt : P.ext.Nontrivial) (z : Vec d) (hz : z ∈ P.ext)
    (zbar : Vec d) (hzbar : zbar ∈ convexHull ℝ (P.ext \ {z}))
    (hproj : ∀ y ∈ convexHull ℝ (P.ext \ {z}), ‖z - zbar‖ ≤ ‖z - y‖) :
    let w : Vec d := (rho P / ‖zbar - z‖ ^ 2) • (zbar - z)
    ‖w‖ ≤ 1 ∧ (∀ z' ∈ P.ext \ {z}, rho P ≤ ⟪w, z' - z⟫_ℝ) ∧
      ∃ z' ∈ P.ext \ {z}, ⟪w, z' - z⟫_ℝ = rho P := by
  intro w
  set C := convexHull ℝ (P.ext \ {z}) with hC
  -- variational inequality
  have hVI : ∀ y ∈ C, ⟪z - zbar, y - zbar⟫_ℝ ≤ 0 := by
    intro y hy
    by_contra hpos
    push_neg at hpos
    set c := ⟪z - zbar, y - zbar⟫_ℝ with hc
    set N := ‖y - zbar‖ ^ 2 with hN
    have hN0 : 0 ≤ N := sq_nonneg _
    set t := c / (N + c) with ht
    have ht0 : 0 < t := div_pos hpos (by linarith)
    have ht1 : t ≤ 1 := by rw [ht, div_le_one (by linarith)]; linarith
    have hmem : zbar + t • (y - zbar) ∈ C :=
      (convex_convexHull ℝ _).add_smul_sub_mem hzbar hy ⟨ht0.le, ht1⟩
    have h1 := hproj _ hmem
    have h2 : ‖z - (zbar + t • (y - zbar))‖ ^ 2 = ‖z - zbar‖ ^ 2 - 2 * t * c + t ^ 2 * N := by
      rw [show z - (zbar + t • (y - zbar)) = (z - zbar) - t • (y - zbar) by abel,
        norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have h3 : ‖z - zbar‖ ^ 2 ≤ ‖z - (zbar + t • (y - zbar))‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [h2] at h3
    have h4 : 2 * c ≤ t * N := by nlinarith
    have h5 : t * N = c * N / (N + c) := by rw [ht]; ring
    rw [h5, le_div_iff₀ (by linarith)] at h4
    nlinarith
  have hρ0 : 0 ≤ rho P := by
    unfold rho
    apply Real.sInf_nonneg
    rintro r ⟨_, _, _, _, rfl⟩
    exact norm_nonneg _
  have hρle : rho P ≤ ‖z - zbar‖ := by
    unfold rho
    apply csInf_le
    · exact ⟨0, by rintro r ⟨_, _, _, _, rfl⟩; exact norm_nonneg _⟩
    · exact ⟨z, hz, zbar, hzbar, rfl⟩
  have hDsym : ‖zbar - z‖ = ‖z - zbar‖ := norm_sub_rev _ _
  set D := ‖zbar - z‖ with hD
  rcases (norm_nonneg (zbar - z)).lt_or_eq with hDpos | hD0
  · have hD2 : 0 < D ^ 2 := by positivity
    -- inner product formula
    have hinner : ∀ y, ⟪w, y - z⟫_ℝ = rho P / D ^ 2 * (D ^ 2 - ⟪z - zbar, y - zbar⟫_ℝ) := by
      intro y
      simp only [w]
      rw [real_inner_smul_left]
      congr 1
      have : y - z = (y - zbar) + (zbar - z) := by abel
      rw [this, inner_add_right, real_inner_self_eq_norm_sq, ← hD]
      have : ⟪zbar - z, y - zbar⟫_ℝ = -⟪z - zbar, y - zbar⟫_ℝ := by
        rw [← inner_neg_left, neg_sub]
      rw [this]; ring
    refine ⟨?_, ?_, ?_⟩
    · simp only [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← hD]
      rw [show rho P / D ^ 2 * D = rho P / D by field_simp]
      rw [div_le_one hDpos]
      calc rho P ≤ ‖z - zbar‖ := hρle
        _ = ‖zbar - z‖ := norm_sub_rev _ _
    · intro z' hz'
      rw [hinner]
      have h1 := hVI z' (subset_convexHull ℝ _ hz')
      have : rho P / D ^ 2 * (D ^ 2 - ⟪z - zbar, z' - zbar⟫_ℝ) ≥ rho P / D ^ 2 * D ^ 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      rw [div_mul_cancel₀ _ hD2.ne'] at this
      linarith
    · obtain ⟨ι, _, lw, sp, hlw0, hlw1, hsp, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hzbar
      have hterms : ∀ i, lw i * ⟪z - zbar, sp i - zbar⟫_ℝ ≤ 0 := fun i =>
        mul_nonpos_of_nonneg_of_nonpos (hlw0 i) (hVI _ (subset_convexHull ℝ _ (hsp i)))
      have htot : ∑ i, lw i * ⟪z - zbar, sp i - zbar⟫_ℝ = 0 := by
        have : ∑ i, lw i * ⟪z - zbar, sp i - zbar⟫_ℝ =
            ⟪z - zbar, ∑ i, lw i • sp i - zbar⟫_ℝ := by
          rw [inner_sub_right, inner_sum]
          simp only [real_inner_smul_right, inner_sub_right, mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hlw1, one_mul]
        rw [this, hsum, sub_self, inner_zero_right]
      have hzero := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hterms i)).mp htot
      obtain ⟨i, hi⟩ : ∃ i, lw i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        rw [Finset.sum_eq_zero (fun i _ => hcon i)] at hlw1
        exact zero_ne_one hlw1
      have hi0 := hzero i (Finset.mem_univ i)
      have hin0 : ⟪z - zbar, sp i - zbar⟫_ℝ = 0 := by
        rcases mul_eq_zero.mp hi0 with h | h
        · exact absurd h hi
        · exact h
      refine ⟨sp i, hsp i, ?_⟩
      rw [hinner, hin0, sub_zero, div_mul_cancel₀ _ hD2.ne']
  · have hzz : zbar = z := sub_eq_zero.mp (norm_eq_zero.mp hD0.symm)
    have hρ : rho P = 0 := by
      have : ‖z - zbar‖ = 0 := by rw [← hDsym]; exact hD0.symm
      linarith
    have hw0 : w = 0 := by simp only [w]; rw [hzz, sub_self, smul_zero]
    refine ⟨by rw [hw0, norm_zero]; exact zero_le_one, ?_, ?_⟩
    · intro z' _; rw [hw0, inner_zero_left, hρ]
    · obtain ⟨z', hz', hne⟩ := hnt.exists_ne z
      exact ⟨z', ⟨hz', hne⟩, by rw [hw0, inner_zero_left, hρ]⟩
