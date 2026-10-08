-- Prove2me | solution 1 for BoydADMM.L1.group_lasso_z_update
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T08:01:49.80342+00:00
-- url     : https://prove2.me/submissions/7796226d-be66-478b-af12-8e23d07858a9

import Definitions.Def_BoydADMM_L1_Basic
set_option autoImplicit false
section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.L1
 theorem block_subgradient {n : ℕ} (lam ρ : ℝ) (hlam : 0≤lam) (hρ : 0<ρ)
    (a z : EuclideanSpace ℝ (Fin n)) :
    lam*‖blockSoftThreshold (lam/ρ) a‖+
      ρ*inner ℝ (a-blockSoftThreshold (lam/ρ) a) (z-blockSoftThreshold (lam/ρ) a) ≤ lam*‖z‖ := by
  have hk : 0≤lam/ρ := div_nonneg hlam (le_of_lt hρ)
  have hmul : ρ*(lam/ρ)=lam := by field_simp
  by_cases ha : a=0
  · simp [blockSoftThreshold, ha]
    positivity
  · have hr : 0<‖a‖ := norm_pos_iff.mpr ha
    by_cases hs : ‖a‖ ≤ lam/ρ
    · have hscale : 1-(lam/ρ)/‖a‖ ≤ 0 := by
        apply sub_nonpos.mpr
        exact (le_div_iff₀ hr).mpr (by simpa using hs)
      have hT : blockSoftThreshold (lam/ρ) a=0 := by
        simp [blockSoftThreshold, ha, max_eq_right hscale]
      rw [hT]
      simp only [norm_zero, mul_zero, zero_add, sub_zero]
      have hρa : ρ*‖a‖ ≤ lam := by
        have := mul_le_mul_of_nonneg_left hs (le_of_lt hρ)
        nlinarith [hmul]
      calc
        ρ*inner ℝ a z ≤ ρ*(‖a‖*‖z‖) := mul_le_mul_of_nonneg_left (real_inner_le_norm a z) (le_of_lt hρ)
        _ ≤ lam*‖z‖ := by nlinarith [mul_le_mul_of_nonneg_right hρa (norm_nonneg z)]
    · have hbig : lam/ρ < ‖a‖ := lt_of_not_ge hs
      have hscale : 0<1-(lam/ρ)/‖a‖ := by
        apply sub_pos.mpr
        exact (div_lt_one hr).mpr hbig
      have hT : blockSoftThreshold (lam/ρ) a=(1-(lam/ρ)/‖a‖) • a := by
        simp [blockSoftThreshold, ha, max_eq_left (le_of_lt hscale)]
      rw [hT]
      have hn : ‖(1-(lam/ρ)/‖a‖) • a‖=(1-(lam/ρ)/‖a‖)*‖a‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
      have hres : ρ • (a-(1-(lam/ρ)/‖a‖) • a)=(lam/‖a‖) • a := by
        have hd : a-(1-(lam/ρ)/‖a‖) • a = (1-(1-(lam/ρ)/‖a‖)) • a := by
          simpa only [one_smul] using (sub_smul (1 : ℝ) (1-(lam/ρ)/‖a‖) a).symm
        rw [hd,smul_smul]
        congr 1
        field_simp [ne_of_gt hρ, ne_of_gt hr] <;> ring
      have hip : inner ℝ a ((1-(lam/ρ)/‖a‖) • a)=‖a‖*‖(1-(lam/ρ)/‖a‖) • a‖ := by
        rw [inner_smul_right, real_inner_self_eq_norm_sq, hn]
        ring
      have hcoef : 0≤lam/‖a‖ := div_nonneg hlam (le_of_lt hr)
      have hcancel : (lam/‖a‖)*‖a‖=lam := by field_simp
      calc
        _ = lam*‖(1-(lam/ρ)/‖a‖) • a‖ +
            (lam/‖a‖)*(inner ℝ a z-‖a‖*‖(1-(lam/ρ)/‖a‖) • a‖) := by
          rw [← real_inner_smul_left, hres, real_inner_smul_left, inner_sub_right, hip]
        _ = (lam/‖a‖)*inner ℝ a z := by rw [mul_sub, ← mul_assoc, hcancel];ring
        _ ≤ (lam/‖a‖)*(‖a‖*‖z‖) := mul_le_mul_of_nonneg_left (real_inner_le_norm a z) hcoef
        _ = lam*‖z‖ := by rw [← mul_assoc, hcancel]
 theorem block_gap {n : ℕ} (lam ρ : ℝ) (hlam : 0≤lam) (hρ : 0<ρ)
    (a z : EuclideanSpace ℝ (Fin n)) :
    (ρ/2)*‖z-blockSoftThreshold (lam/ρ) a‖^2 ≤
      (lam*‖z‖+(ρ/2)*‖a-z‖^2)-
        (lam*‖blockSoftThreshold (lam/ρ) a‖+(ρ/2)*‖a-blockSoftThreshold (lam/ρ) a‖^2) := by
  let T := blockSoftThreshold (lam/ρ) a
  have h := block_subgradient lam ρ hlam hρ a z
  have he : a-z=(a-T)-(z-T) := by abel
  change (ρ/2)*‖z-T‖^2 ≤ (lam*‖z‖+(ρ/2)*‖a-z‖^2)-(lam*‖T‖+(ρ/2)*‖a-T‖^2)
  change lam*‖T‖+ρ*inner ℝ (a-T) (z-T) ≤ lam*‖z‖ at h
  rw [he, norm_sub_sq_real (a-T) (z-T)]
  nlinarith
end ADMMCodex

end

section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.L1
 theorem group_threshold {N : ℕ} (nb : Fin N → ℕ) (lam ρ : ℝ) (hlam : 0≤lam) (hρ : 0<ρ)
    (x u : (i : Fin N) → EuclideanSpace ℝ (Fin (nb i))) :
    IsUniqueMinimizerOn
      (fun z : (i : Fin N) → EuclideanSpace ℝ (Fin (nb i)) =>
        lam*∑ i, ‖z i‖+(ρ/2)*∑ i, ‖x i-z i+u i‖^2) Set.univ
      (fun i => blockSoftThreshold (lam/ρ) (x i+u i)) := by
  let T := fun i => blockSoftThreshold (lam/ρ) (x i+u i)
  have gap (z : (i : Fin N) → EuclideanSpace ℝ (Fin (nb i))) :
      (ρ/2)*(∑ i, ‖z i-T i‖^2) ≤
        (lam*(∑ i, ‖z i‖)+(ρ/2)*(∑ i, ‖x i-z i+u i‖^2)) -
          (lam*(∑ i, ‖T i‖)+(ρ/2)*(∑ i, ‖x i-T i+u i‖^2)) := by
    have he (i : Fin N) (w : EuclideanSpace ℝ (Fin (nb i))) : x i-w+u i=(x i+u i)-w := by abel
    have hg := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => block_gap lam ρ hlam hρ (x i+u i) (z i))
    simpa only [T, he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] using hg
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · intro z _
    have hg := gap z
    have hn : 0≤∑ i, ‖z i-T i‖^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hp := mul_nonneg (le_of_lt (half_pos hρ)) hn
    linarith
  · intro z _ hm
    change lam*(∑ i, ‖z i‖)+(ρ/2)*(∑ i, ‖x i-z i+u i‖^2) ≤
      lam*(∑ i, ‖T i‖)+(ρ/2)*(∑ i, ‖x i-T i+u i‖^2) at hm
    have hle : (ρ/2)*(∑ i, ‖z i-T i‖^2) ≤ 0 := le_trans (gap z) (sub_nonpos.mpr hm)
    have hs : (∑ i, ‖z i-T i‖^2) ≤ 0 := by
      by_contra h
      have := mul_pos (half_pos hρ) (lt_of_not_ge h)
      linarith
    funext i
    have hi : ‖z i-T i‖^2 ≤ ∑ j, ‖z j-T j‖^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖z j-T j‖) (Finset.mem_univ i)
    have hz : ‖z i-T i‖=0 := by nlinarith [norm_nonneg (z i-T i)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
end ADMMCodex

end

set_option autoImplicit false
open Matrix BoydADMM.L1
theorem solution {N : ℕ} (nb : Fin N → ℕ) (lam ρ : ℝ) (hlam : 0 ≤ lam) (hρ : 0 < ρ)
    (x u : (i : Fin N) → EuclideanSpace ℝ (Fin (nb i))) :
    IsUniqueMinimizerOn
      (fun z : (i : Fin N) → EuclideanSpace ℝ (Fin (nb i)) =>
        lam * ∑ i, ‖z i‖ + (ρ / 2) * ∑ i, ‖x i - z i + u i‖ ^ 2) Set.univ
      (fun i => blockSoftThreshold (lam / ρ) (x i + u i)) := by
  exact ADMMCodex.group_threshold nb lam ρ hlam hρ x u



#print axioms solution
