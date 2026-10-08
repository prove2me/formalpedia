-- Prove2me | solution 1 for BoydADMM.L1.huber_z_update
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T08:01:51.26477+00:00
-- url     : https://prove2.me/submissions/ab22329a-c41e-4f45-8216-908a6a0233ca

import Definitions.Def_BoydADMM_L1_Basic
set_option autoImplicit false
section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.L1
 theorem huber_lower_pos (z : ℝ) : z-1/2 ≤ huber z := by
  unfold huber
  split_ifs with h
  · nlinarith [sq_nonneg (z-1)]
  · linarith [le_abs_self z]
 theorem huber_lower_neg (z : ℝ) : -z-1/2 ≤ huber z := by
  unfold huber
  split_ifs with h
  · nlinarith [sq_nonneg (z+1)]
  · linarith [neg_le_abs z]
 theorem huber_support_middle (t z : ℝ) (ht : |t|≤1) : huber t+t*(z-t) ≤ huber z := by
  have htu : t≤1 := (abs_le.mp ht).2
  have htl : -1≤t := (abs_le.mp ht).1
  rw [huber, if_pos ht]
  unfold huber
  split_ifs with hz
  · nlinarith [sq_nonneg (z-t)]
  · by_cases hzp : 0≤z
    · rw [abs_of_nonneg hzp]
      have hbig : 1≤z := by rw [abs_of_nonneg hzp] at hz;linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr htu) (sub_nonneg.mpr hbig), sq_nonneg (1-t)]
    · rw [abs_of_neg (lt_of_not_ge hzp)]
      have hbig : 1≤ -z := by rw [abs_of_neg (lt_of_not_ge hzp)] at hz;linarith
      nlinarith [mul_nonneg (by linarith : 0≤1+t) (sub_nonneg.mpr hbig), sq_nonneg (1+t)]
 theorem huber_support_upper (t z : ℝ) (ht : 1<t) : huber t+(z-t) ≤ huber z := by
  have htn : 0<t := by linarith
  have hh : ¬|t|≤1 := by rw [abs_of_pos htn];linarith
  rw [huber, if_neg hh, abs_of_pos htn]
  linarith [huber_lower_pos z]
 theorem huber_support_lower (t z : ℝ) (ht : t< -1) : huber t-(z-t) ≤ huber z := by
  have htn : t<0 := by linarith
  have hh : ¬|t|≤1 := by rw [abs_of_neg htn];linarith
  rw [huber, if_neg hh, abs_of_neg htn]
  linarith [huber_lower_neg z]
end ADMMCodex

end

section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.L1 BoydADMM.Prox
noncomputable def huberCandidate (ρ a : ℝ) : ℝ :=
  ρ/(1+ρ)*a + 1/(1+ρ)*softThreshold (1+1/ρ) a
 theorem huber_subgradient (ρ a z : ℝ) (hρ : 0<ρ) :
    huber (huberCandidate ρ a)+ρ*(a-huberCandidate ρ a)*(z-huberCandidate ρ a) ≤ huber z := by
  let t := huberCandidate ρ a
  have hden : 0<1+ρ := by linarith
  have hmul : ρ*(1/ρ)=1 := by field_simp
  by_cases hp : 1+1/ρ<a
  · have ht : t=a-1/ρ := by
      dsimp [t,huberCandidate]
      rw [softThreshold,if_pos hp]
      field_simp [ne_of_gt hρ, ne_of_gt hden] <;> ring
    have hbig : 1<t := by rw [ht];linarith
    have hr : ρ*(a-t)=1 := by rw [ht];nlinarith [hmul]
    change huber t+ρ*(a-t)*(z-t) ≤ huber z
    rw [hr,one_mul]
    exact huber_support_upper t z hbig
  · by_cases hn : a< -(1+1/ρ)
    · have ht : t=a+1/ρ := by
        dsimp [t,huberCandidate]
        rw [softThreshold,if_neg hp,if_pos hn]
        field_simp [ne_of_gt hρ, ne_of_gt hden] <;> ring
      have hbig : t< -1 := by rw [ht];linarith
      have hr : ρ*(a-t)= -1 := by rw [ht];nlinarith [hmul]
      change huber t+ρ*(a-t)*(z-t) ≤ huber z
      rw [hr]
      simpa only [neg_one_mul,sub_eq_add_neg] using huber_support_lower t z hbig
    · have ht : t=ρ*a/(1+ρ) := by
        dsimp [t,huberCandidate]
        rw [softThreshold,if_neg hp,if_neg hn]
        ring
      have hu : ρ*a ≤ 1+ρ := by
        have := mul_le_mul_of_nonneg_left (le_of_not_gt hp) (le_of_lt hρ)
        nlinarith [hmul]
      have hl : -(1+ρ) ≤ ρ*a := by
        have := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (le_of_lt hρ)
        nlinarith [hmul]
      have htbound : |t|≤1 := by
        rw [ht,abs_le]
        constructor
        · apply (le_div_iff₀ hden).mpr
          linarith
        · apply (div_le_iff₀ hden).mpr
          linarith
      have hr : ρ*(a-t)=t := by rw [ht];field_simp [ne_of_gt hden] <;> ring
      change huber t+ρ*(a-t)*(z-t) ≤ huber z
      rw [hr]
      exact huber_support_middle t z htbound
 theorem huber_gap (ρ a z : ℝ) (hρ : 0<ρ) : (ρ/2)*(z-huberCandidate ρ a)^2 ≤
    (huber z+(ρ/2)*(a-z)^2)-(huber (huberCandidate ρ a)+(ρ/2)*(a-huberCandidate ρ a)^2) := by
  have h := huber_subgradient ρ a z hρ
  nlinarith
end ADMMCodex

end

section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.L1
 theorem huber_vector {n : ℕ} (ρ : ℝ) (hρ : 0<ρ) (v : EuclideanSpace ℝ (Fin n)) :
    IsUniqueMinimizerOn (fun z : EuclideanSpace ℝ (Fin n) => huberVec z+(ρ/2)*‖v-z‖^2)
      Set.univ (WithLp.toLp 2 fun i => huberCandidate ρ (v i)) := by
  let T : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => huberCandidate ρ (v i)
  have gap (z : EuclideanSpace ℝ (Fin n)) : (ρ/2)*‖z-T‖^2 ≤
      (huberVec z+(ρ/2)*‖v-z‖^2)-(huberVec T+(ρ/2)*‖v-T‖^2) := by
    have hg := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => huber_gap ρ (v i) (z i) hρ)
    simpa only [huberVec, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] using hg
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · intro z _
    have hg := gap z
    have hn := mul_nonneg (le_of_lt (half_pos hρ)) (sq_nonneg ‖z-T‖)
    linarith
  · intro z _ hm
    change huberVec z+(ρ/2)*‖v-z‖^2 ≤ huberVec T+(ρ/2)*‖v-T‖^2 at hm
    have hle : (ρ/2)*‖z-T‖^2 ≤ 0 := le_trans (gap z) (sub_nonpos.mpr hm)
    have hs : ‖z-T‖^2 ≤ 0 := by
      by_contra h
      have := mul_pos (half_pos hρ) (lt_of_not_ge h)
      linarith
    have hz : ‖z-T‖=0 := by nlinarith [norm_nonneg (z-T)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
end ADMMCodex

end

set_option autoImplicit false
open Matrix BoydADMM.L1
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b u : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ) :
    IsUniqueMinimizerOn
      (fun z : EuclideanSpace ℝ (Fin m) =>
        huberVec z + (ρ / 2) * ‖Matrix.toEuclideanLin A x - z - b + u‖ ^ 2) Set.univ
      (WithLp.toLp 2 fun i =>
        ρ / (1 + ρ) * (Matrix.toEuclideanLin A x - b + u) i +
          1 / (1 + ρ) * BoydADMM.Prox.softThreshold (1 + 1 / ρ) ((Matrix.toEuclideanLin A x - b + u) i)) := by
  have he (z : EuclideanSpace ℝ (Fin m)) : Matrix.toEuclideanLin A x-z-b+u=(Matrix.toEuclideanLin A x-b+u)-z := by abel
  simpa only [he, ADMMCodex.huberCandidate] using ADMMCodex.huber_vector ρ hρ (Matrix.toEuclideanLin A x-b+u)



#print axioms solution
