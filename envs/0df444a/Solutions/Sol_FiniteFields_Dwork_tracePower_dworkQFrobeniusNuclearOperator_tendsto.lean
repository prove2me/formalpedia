-- Prove2me | solution 1 for FiniteFields.Dwork.tracePower_dworkQFrobeniusNuclearOperator_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:48:22.551624+00:00
-- url     : https://prove2.me/submissions/e705d941-04a5-458f-b3eb-ce20ddd485fd

import Mathlib
import Definitions.Def_FiniteFields_Dwork_NuclearOperator
section
noncomputable section
open Filter Set Topology
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem nuclear_sum_nestedWeightedCutoff {smaller larger : ℕ} (h : smaller ≤ larger)
    (f : WeightedCutoff w smaller → K) :
    (∑ v : WeightedCutoff w larger,
        if hv : monomialWeight w v.1 ≤ smaller then
          f (nuclearWeightedCutoffOfLE w v hv) else 0) =
      ∑ v : WeightedCutoff w smaller, f v := by
  classical
  let s : Set (WeightedCutoff w larger) :=
    {v | monomialWeight w v.1 ≤ smaller}
  calc
    _ = ∑ v : s, f (nuclearWeightedCutoffOfLE w v.1 v.2) := by
      apply Finset.sum_congr_set s
      · intro v hv
        change monomialWeight w v.1 ≤ smaller at hv
        rw [dif_pos hv]
      · intro v hv
        change ¬monomialWeight w v.1 ≤ smaller at hv
        rw [dif_neg hv]
    _ = _ := by
      symm
      apply Fintype.sum_equiv (nuclearNestedWeightedCutoffEquiv w h)
      intro v
      rfl
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem nuclearPaddedCutoffKernel_pow_apply_of_mem
    (kernel : InfiniteWeightedKernel (K := K) (d := d))
    {smaller larger : ℕ} (h : smaller ≤ larger) (power : ℕ)
    (u v : WeightedCutoff w larger)
    (hu : monomialWeight w u.1 ≤ smaller) (hv : monomialWeight w v.1 ≤ smaller) :
    (nuclearPaddedCutoffKernel w kernel smaller larger ^ (power + 1)) u v =
      (cutoffKernel w kernel smaller ^ (power + 1))
        (nuclearWeightedCutoffOfLE w u hu) (nuclearWeightedCutoffOfLE w v hv) := by
  classical
  induction power generalizing u v with
  | zero =>
      simp only [zero_add, pow_one]
      simp [nuclearPaddedCutoffKernel, cutoffKernel, hu, hv,
        nuclearWeightedCutoffOfLE]
  | succ power ih =>
      change
        ((nuclearPaddedCutoffKernel w kernel smaller larger ^ (power + 1)) *
            nuclearPaddedCutoffKernel w kernel smaller larger) u v =
          ((cutoffKernel w kernel smaller ^ (power + 1)) *
            cutoffKernel w kernel smaller)
            (nuclearWeightedCutoffOfLE w u hu) (nuclearWeightedCutoffOfLE w v hv)
      rw [Matrix.mul_apply, Matrix.mul_apply]
      calc
        _ = ∑ x : WeightedCutoff w larger,
            if hx : monomialWeight w x.1 ≤ smaller then
              (cutoffKernel w kernel smaller ^ (power + 1))
                  (nuclearWeightedCutoffOfLE w u hu)
                  (nuclearWeightedCutoffOfLE w x hx) *
                kernel x.1 v.1
            else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : monomialWeight w x.1 ≤ smaller
              · rw [dif_pos hx, ih u x hu hx]
                simp [nuclearPaddedCutoffKernel, hx, hv]
              · rw [dif_neg hx]
                simp [nuclearPaddedCutoffKernel, hx]
        _ = ∑ x : WeightedCutoff w smaller,
            (cutoffKernel w kernel smaller ^ (power + 1))
                (nuclearWeightedCutoffOfLE w u hu) x *
              kernel x.1 v.1 :=
          by
            simpa [nuclearWeightedCutoffOfLE] using
              nuclear_sum_nestedWeightedCutoff w h
                (fun x : WeightedCutoff w smaller ↦
                  (cutoffKernel w kernel smaller ^ (power + 1))
                      (nuclearWeightedCutoffOfLE w u hu) x * kernel x.1 v.1)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rfl
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem nuclearPaddedCutoffKernel_pow_apply_of_row_not_mem
    (kernel : InfiniteWeightedKernel (K := K) (d := d))
    (smaller larger power : ℕ) (hpower : 0 < power)
    (u v : WeightedCutoff w larger) (hu : ¬monomialWeight w u.1 ≤ smaller) :
    (nuclearPaddedCutoffKernel w kernel smaller larger ^ power) u v = 0 := by
  classical
  obtain ⟨power, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpower)
  rw [pow_succ']
  simp [Matrix.mul_apply, nuclearPaddedCutoffKernel, hu]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem trace_nuclearPaddedCutoffKernel_pow
    (kernel : InfiniteWeightedKernel (K := K) (d := d))
    {smaller larger power : ℕ} (h : smaller ≤ larger) (hpower : 0 < power) :
    Matrix.trace (nuclearPaddedCutoffKernel w kernel smaller larger ^ power) =
      finiteKernelPowerTrace w kernel power smaller := by
  classical
  unfold Matrix.trace finiteKernelPowerTrace
  calc
    _ = ∑ u : WeightedCutoff w larger,
        if hu : monomialWeight w u.1 ≤ smaller then
          (cutoffKernel w kernel smaller ^ power)
            (nuclearWeightedCutoffOfLE w u hu) (nuclearWeightedCutoffOfLE w u hu)
        else 0 := by
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : monomialWeight w u.1 ≤ smaller
          · rw [dif_pos hu]
            obtain ⟨power, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpower)
            simpa [Nat.succ_eq_add_one] using
              nuclearPaddedCutoffKernel_pow_apply_of_mem
                w kernel h power u u hu hu
          · rw [dif_neg hu]
            exact nuclearPaddedCutoffKernel_pow_apply_of_row_not_mem
              w kernel smaller larger power hpower u u hu
    _ = ∑ u : WeightedCutoff w smaller,
        (cutoffKernel w kernel smaller ^ power) u u :=
      by
        simpa [nuclearWeightedCutoffOfLE] using
          nuclear_sum_nestedWeightedCutoff w h
            (fun u : WeightedCutoff w smaller ↦
              (cutoffKernel w kernel smaller ^ power) u u)
omit [CompleteSpace K] in
private theorem nuclear_matrix_mul_entry_norm_le
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι K) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i j, ‖A i j‖ ≤ C) (hB : ∀ i j, ‖B i j‖ ≤ D)
    (i j : ι) :
    ‖(A * B) i j‖ ≤ C * D := by
  classical
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hC hD) ?_
  intro x _
  rw [norm_mul]
  exact mul_le_mul (hA i x) (hB x j) (norm_nonneg _) hC
omit [CompleteSpace K] in
private theorem nuclear_matrix_pow_entry_norm_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (power : ℕ) (i j : ι) :
    ‖(A ^ power) i j‖ ≤ 1 := by
  classical
  induction power generalizing i j with
  | zero =>
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
  | succ power ih =>
      rw [pow_succ]
      simpa using nuclear_matrix_mul_entry_norm_le
        (K := K) (A ^ power) A zero_le_one zero_le_one ih hA i j
omit [CompleteSpace K] in
private theorem nuclear_matrix_pow_sub_entry_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι K) {tail : ℝ} (htail : 0 ≤ tail)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1)
    (hsub : ∀ i j, ‖(A - B) i j‖ ≤ tail)
    {power : ℕ} (hpower : 0 < power) (i j : ι) :
    ‖(A ^ power - B ^ power) i j‖ ≤ tail := by
  classical
  obtain ⟨power, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpower)
  clear hpower
  induction power generalizing i j with
  | zero =>
      simpa using hsub i j
  | succ power ih =>
      have hpow :
          A ^ (power + 1 + 1) - B ^ (power + 1 + 1) =
            (A ^ (power + 1) - B ^ (power + 1)) * A +
              B ^ (power + 1) * (A - B) := by
        rw [pow_succ, pow_succ]
        simp only [sub_mul, mul_sub]
        abel
      rw [show Nat.succ (Nat.succ power) = power + 1 + 1 by omega, hpow,
        Matrix.add_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa [mul_one] using nuclear_matrix_mul_entry_norm_le
          (K := K) (A ^ (power + 1) - B ^ (power + 1)) A htail zero_le_one
          ih hA i j
      · simpa [one_mul] using nuclear_matrix_mul_entry_norm_le
          (K := K) (B ^ (power + 1)) (A - B) zero_le_one htail
          (nuclear_matrix_pow_entry_norm_le_one (K := K) B hB (power + 1)) hsub i j
omit [CompleteSpace K] in
private theorem nuclear_norm_trace_le_of_entry
    {ι : Type*} [Fintype ι] (A : Matrix ι ι K) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, ‖A i j‖ ≤ C) :
    ‖Matrix.trace A‖ ≤ C := by
  classical
  rw [Matrix.trace]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ ↦ hA i i
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem nuclearPaddedCutoffKernel_global_bound
    (kernel : InfiniteWeightedKernel (K := K) (d := d)) (tailBound : ℕ → ℝ)
    (hnuclear : NuclearKernelDecay w kernel tailBound)
    (smaller larger : ℕ) (u v : WeightedCutoff w larger) :
    ‖nuclearPaddedCutoffKernel w kernel smaller larger u v‖ ≤ 1 := by
  by_cases hu : monomialWeight w u.1 ≤ smaller
  · by_cases hv : monomialWeight w v.1 ≤ smaller
    · simpa [nuclearPaddedCutoffKernel, hu, hv] using hnuclear.2 u.1 v.1
    · simp [nuclearPaddedCutoffKernel, hu, hv]
  · simp [nuclearPaddedCutoffKernel, hu]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem cutoffKernel_sub_nuclearPaddedCutoffKernel_tail_bound
    (kernel : InfiniteWeightedKernel (K := K) (d := d)) (tailBound : ℕ → ℝ)
    (hnuclear : NuclearKernelDecay w kernel tailBound)
    (smaller larger : ℕ) (u v : WeightedCutoff w larger) :
    ‖(cutoffKernel w kernel larger -
        nuclearPaddedCutoffKernel w kernel smaller larger) u v‖ ≤ tailBound smaller := by
  by_cases hu : monomialWeight w u.1 ≤ smaller
  · by_cases hv : monomialWeight w v.1 ≤ smaller
    · simpa [cutoffKernel, nuclearPaddedCutoffKernel, hu, hv] using hnuclear.1.1 smaller
    · simpa [cutoffKernel, nuclearPaddedCutoffKernel, hu, hv] using
        hnuclear.1.2.2 smaller u.1 v.1 (Or.inr (Nat.lt_of_not_ge hv))
  · simpa [cutoffKernel, nuclearPaddedCutoffKernel, hu] using
      hnuclear.1.2.2 smaller u.1 v.1 (Or.inl (Nat.lt_of_not_ge hu))
omit [CompleteSpace K] in
theorem finiteKernelPowerTrace_sub_bound
    (kernel : InfiniteWeightedKernel (K := K) (d := d)) (tailBound : ℕ → ℝ)
    (hnuclear : NuclearKernelDecay w kernel tailBound)
    {power : ℕ} (hpower : 0 < power) {smaller larger : ℕ} (h : smaller ≤ larger) :
    ‖finiteKernelPowerTrace w kernel power larger -
        finiteKernelPowerTrace w kernel power smaller‖ ≤ tailBound smaller := by
  classical
  let A := cutoffKernel w kernel larger
  let B := nuclearPaddedCutoffKernel w kernel smaller larger
  have htraceB : Matrix.trace (B ^ power) = finiteKernelPowerTrace w kernel power smaller :=
    trace_nuclearPaddedCutoffKernel_pow w kernel h hpower
  rw [finiteKernelPowerTrace, ← htraceB, ← Matrix.trace_sub]
  apply nuclear_norm_trace_le_of_entry (K := K) _ (hnuclear.1.1 smaller)
  exact nuclear_matrix_pow_sub_entry_norm_le (K := K) A B (hnuclear.1.1 smaller)
    (fun i j ↦ hnuclear.2 i.1 j.1)
    (nuclearPaddedCutoffKernel_global_bound w kernel tailBound hnuclear smaller larger)
    (cutoffKernel_sub_nuclearPaddedCutoffKernel_tail_bound
      w kernel tailBound hnuclear smaller larger)
    hpower
omit [CompleteSpace K] in
theorem cauchy_finiteKernelPowerTrace
    (kernel : InfiniteWeightedKernel (K := K) (d := d)) (tailBound : ℕ → ℝ)
    (hnuclear : NuclearKernelDecay w kernel tailBound)
    {power : ℕ} (hpower : 0 < power) :
    CauchySeq (fun bound ↦ finiteKernelPowerTrace w kernel power bound) := by
  apply cauchySeq_of_le_tendsto_0' tailBound
  · intro smaller larger h
    rw [dist_eq_norm, norm_sub_rev]
    exact finiteKernelPowerTrace_sub_bound w kernel tailBound hnuclear hpower h
  · exact hnuclear.1.2.1
theorem tendsto_finiteKernelPowerTrace
    (kernel : InfiniteWeightedKernel (K := K) (d := d)) (tailBound : ℕ → ℝ)
    (hnuclear : NuclearKernelDecay w kernel tailBound)
    {power : ℕ} (hpower : 0 < power) :
    Tendsto (fun bound ↦ finiteKernelPowerTrace w kernel power bound) atTop
      (nhds (nuclearTracePower w kernel tailBound hnuclear power hpower)) :=
  (cauchy_finiteKernelPowerTrace w kernel tailBound hnuclear hpower).tendsto_limUnder
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Set Topology
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
namespace NuclearOperator
theorem tracePower_tendsto (T : NuclearOperator (K := K) w) (power : ℕ+) :
    Tendsto (fun bound ↦ finiteKernelPowerTrace w T.kernel (power : ℕ) bound) atTop
      (nhds (tracePower w T power)) :=
  tendsto_finiteKernelPowerTrace w T.kernel T.tailBound T.decay power.2
end NuclearOperator
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
variable {d : ℕ} (w : PositiveMonomialWeight d)
theorem cutoffKernel_conjugateKernel_pow (c : DworkCyclotomicField k p) (hc : c ≠ 0)
    (n : MonomialIndex d → ℕ)
    (kernel : InfiniteWeightedKernel (K := DworkCyclotomicField k p) (d := d))
    (bound power : ℕ) (u v : WeightedCutoff w bound) :
    ((cutoffKernel w (conjugateKernel k p c n kernel) bound) ^ power) u v
      = c ^ n v.1 * (c ^ n u.1)⁻¹ * ((cutoffKernel w kernel bound) ^ power) u v := by
  classical
  induction power generalizing u v with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      by_cases huv : u = v
      · subst huv
        rw [if_pos rfl, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hc)]
      · rw [if_neg huv, mul_zero]
  | succ power ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx : c ^ n x.1 * (c ^ n x.1)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hc)
      rw [ih u x, cutoffKernel_apply, conjugateKernel, cutoffKernel_apply]
      calc c ^ n x.1 * (c ^ n u.1)⁻¹ * ((cutoffKernel w kernel bound ^ power) u x) *
            (c ^ n v.1 * (c ^ n x.1)⁻¹ * kernel x.1 v.1)
          = (c ^ n x.1 * (c ^ n x.1)⁻¹) *
              (c ^ n v.1 * (c ^ n u.1)⁻¹ *
                ((cutoffKernel w kernel bound ^ power) u x * kernel x.1 v.1)) := by ring
        _ = c ^ n v.1 * (c ^ n u.1)⁻¹ *
              ((cutoffKernel w kernel bound ^ power) u x * kernel x.1 v.1) := by
            rw [hx, one_mul]
theorem cutoffKernel_dworkQFrobeniusNormalizedKernel_pow (f : MonomialIndex d →₀ k)
    (bound power : ℕ) (u v : WeightedCutoff w bound) :
    ((cutoffKernel w (dworkQFrobeniusNormalizedKernel k p w f) bound) ^ power) u v
      = dworkRamificationParameter k p ^ dworkQDiagonalExponent k p w f v.1 *
          (dworkRamificationParameter k p ^ dworkQDiagonalExponent k p w f u.1)⁻¹ *
          ((cutoffKernel w (dworkQFrobeniusKernel k p w f) bound) ^ power) u v :=
  cutoffKernel_conjugateKernel_pow k p w _ (dworkRamificationParameter_ne_zero k p) _ _
    bound power u v
theorem cutoffKernel_dworkQFrobeniusNormalizedKernel_pow_diagonal (f : MonomialIndex d →₀ k)
    (bound power : ℕ) (u : WeightedCutoff w bound) :
    ((cutoffKernel w (dworkQFrobeniusNormalizedKernel k p w f) bound) ^ power) u u
      = ((cutoffKernel w (dworkQFrobeniusKernel k p w f) bound) ^ power) u u := by
  rw [cutoffKernel_dworkQFrobeniusNormalizedKernel_pow,
    mul_inv_cancel₀ (pow_ne_zero _ (dworkRamificationParameter_ne_zero k p)), one_mul]
theorem finiteKernelPowerTrace_dworkQFrobeniusNormalizedKernel (f : MonomialIndex d →₀ k)
    (power bound : ℕ) :
    finiteKernelPowerTrace w (dworkQFrobeniusNormalizedKernel k p w f) power bound
      = finiteKernelPowerTrace w (dworkQFrobeniusKernel k p w f) power bound := by
  rw [finiteKernelPowerTrace, finiteKernelPowerTrace, Matrix.trace, Matrix.trace]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact cutoffKernel_dworkQFrobeniusNormalizedKernel_pow_diagonal k p w f bound power u
end FiniteFields.Dwork
end
end
open Filter Topology
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
variable {d : ℕ} (w : PositiveMonomialWeight d)
theorem solution (f : MonomialIndex d →₀ k)
    (power : ℕ+) :
    Tendsto (fun bound =>
        finiteKernelPowerTrace w (dworkQFrobeniusKernel k p w f) (power : ℕ) bound) atTop
      (nhds (NuclearOperator.tracePower w (dworkQFrobeniusNuclearOperator k p w f) power)) := by
  have h := NuclearOperator.tracePower_tendsto w (dworkQFrobeniusNuclearOperator k p w f) power
  simpa only [dworkQFrobeniusNuclearOperator_kernel,
    finiteKernelPowerTrace_dworkQFrobeniusNormalizedKernel] using h
