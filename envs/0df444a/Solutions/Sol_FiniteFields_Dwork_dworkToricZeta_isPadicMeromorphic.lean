-- Prove2me | solution 1 for FiniteFields.Dwork.dworkToricZeta_isPadicMeromorphic
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T07:02:01.404281+00:00
-- url     : https://prove2.me/submissions/7aff93ea-63c4-4849-921a-db370a90a6d1

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Meromorphy
import Theorems.Thm_FiniteFields_Dwork_dworkToricTraceFormula
import Theorems.Thm_FiniteFields_LinearAlgebra_logDerivative_fredholmDeterminant
import Theorems.Thm_FiniteFields_LinearAlgebra_finiteRankFredholmDeterminant_swap
section
noncomputable section
namespace FiniteFields
open PowerSeries
@[simp]
theorem coeff_countingSeries (N : ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (countingSeries N) = (N n : ℚ) := by
  simp [countingSeries]
end FiniteFields
end
end
section
namespace FiniteFields.Dwork
noncomputable section
@[simp]
theorem mem_monomialCutoff {d : ℕ} {w : PositiveMonomialWeight d} {bound : ℕ}
    {u : MonomialIndex d} :
    u ∈ MonomialCutoff w bound ↔ monomialWeight w u ≤ bound :=
  Iff.rfl
end
end FiniteFields.Dwork
end
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
open Module Polynomial PowerSeries
namespace FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
theorem fredholmDeterminant_eq_det (u : Module.End R M) {ι : Type w}
    [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    fredholmDeterminant u =
      Matrix.det (1 - (X : R[X]) • (LinearMap.toMatrix b b u).map Polynomial.C) := by
  rw [fredholmDeterminant, ← LinearMap.charpoly_toMatrix u b,
    Matrix.reverse_charpoly, Matrix.charpolyRev]
@[simp]
theorem fredholmDeterminant_coeff_zero (u : Module.End R M) :
    (fredholmDeterminant u).coeff 0 = 1 := by
  let b := Module.Free.chooseBasis R M
  rw [fredholmDeterminant_eq_det u b, coeff_zero_eq_eval_zero]
  exact Matrix.eval_charpolyRev
section FiniteRank
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
end FiniteRank
end FiniteFields.LinearAlgebra
end
end
section
noncomputable section
open Filter Set Topology Polynomial PowerSeries Finset
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
namespace NuclearOperator
omit [IsUltrametricDist K] [CompleteSpace K] in
theorem cutoffFredholmPolynomial_eq_charpolyRev
    (T : NuclearOperator (K := K) w) (bound : ℕ) :
    cutoffFredholmPolynomial w T bound = (cutoffKernel w T.kernel bound).charpolyRev := by
  rw [cutoffFredholmPolynomial, FiniteFields.LinearAlgebra.fredholmDeterminant,
    ← LinearMap.charpoly_toMatrix (Matrix.toLin' (cutoffKernel w T.kernel bound))
      (Pi.basisFun K (WeightedCutoff w bound)),
    Matrix.reverse_charpoly, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem fredholmCutoffRestriction_comp_zeroExtension
    {smaller larger : ℕ} (h : smaller ≤ larger) :
    (fredholmCutoffRestriction (K := K) w h).comp
        (fredholmCutoffZeroExtension (K := K) w smaller larger) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext u
  change (if hv : monomialWeight w (weightedCutoffInclusion w h u).1 ≤ smaller then
    f (fredholmWeightedCutoffOfLE w (weightedCutoffInclusion w h u) hv) else 0) = f u
  have hu : monomialWeight w (weightedCutoffInclusion w h u).1 ≤ smaller := by
    change monomialWeight w u.1 ≤ smaller
    exact u.2
  rw [dif_pos hu]
  rfl
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem fredholmPaddedCutoffKernel_toLin'
    (T : NuclearOperator (K := K) w) {smaller larger : ℕ} (h : smaller ≤ larger) :
    Matrix.toLin' (fredholmPaddedCutoffKernel w T smaller larger) =
      (fredholmCutoffZeroExtension (K := K) w smaller larger).comp
        ((Matrix.toLin' (cutoffKernel w T.kernel smaller)).comp
          (fredholmCutoffRestriction (K := K) w h)) := by
  classical
  apply LinearMap.ext
  intro f
  funext u
  change (∑ v : WeightedCutoff w larger,
      fredholmPaddedCutoffKernel w T smaller larger u v * f v) =
    if hu' : monomialWeight w u.1 ≤ smaller then
      ∑ v : WeightedCutoff w smaller, T.kernel u.1 v.1 *
        f (weightedCutoffInclusion w h v)
    else 0
  by_cases hu : monomialWeight w u.1 ≤ smaller
  · rw [dif_pos hu]
    let s : Set (WeightedCutoff w larger) :=
      {v | monomialWeight w v.1 ≤ smaller}
    calc
      _ = ∑ v : s, T.kernel u.1 v.1 * f v.1 := by
        apply Finset.sum_congr_set s
        · intro v hv
          change monomialWeight w v.1 ≤ smaller at hv
          simp [fredholmPaddedCutoffKernel, hu, hv]
        · intro v hv
          change ¬monomialWeight w v.1 ≤ smaller at hv
          simp [fredholmPaddedCutoffKernel, hu, hv]
      _ = _ := by
        let e : WeightedCutoff w smaller ≃ s := {
          toFun v := ⟨weightedCutoffInclusion w h v, v.2⟩
          invFun v := fredholmWeightedCutoffOfLE w v.1 v.2
          left_inv _ := rfl
          right_inv _ := rfl }
        symm
        apply Fintype.sum_equiv e
        intro v
        rfl
  · rw [dif_neg hu]
    apply Finset.sum_eq_zero
    intro v _
    simp [fredholmPaddedCutoffKernel, hu]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem fredholmPaddedCutoffPolynomial_eq
    (T : NuclearOperator (K := K) w) {smaller larger : ℕ} (h : smaller ≤ larger) :
    FiniteFields.LinearAlgebra.fredholmDeterminant
        (Matrix.toLin' (fredholmPaddedCutoffKernel w T smaller larger)) =
      cutoffFredholmPolynomial w T smaller := by
  let a := fredholmCutoffRestriction (K := K) w h
  let z := fredholmCutoffZeroExtension (K := K) w smaller larger
  let m := Matrix.toLin' (cutoffKernel w T.kernel smaller)
  have hpadded : Matrix.toLin' (fredholmPaddedCutoffKernel w T smaller larger) =
      (z.comp m).comp a := by
    simpa [a, z, m, LinearMap.comp_assoc] using
      fredholmPaddedCutoffKernel_toLin' (K := K) w T h
  have hsmall : a.comp (z.comp m) = m := by
    rw [← LinearMap.comp_assoc, fredholmCutoffRestriction_comp_zeroExtension (K := K) w h,
      LinearMap.id_comp]
  rw [hpadded, cutoffFredholmPolynomial,
    ← FiniteFields.LinearAlgebra.finiteRankFredholmDeterminant]
  rw [FiniteFields.LinearAlgebra.finiteRankFredholmDeterminant_swap]
  rw [FiniteFields.LinearAlgebra.finiteRankFredholmDeterminant, hsmall]
omit [CompleteSpace K] in
private theorem fredholm_norm_prod_sub_prod_le
    {ι : Type*} (s : Finset ι) (a b : ι → K) {tail : ℝ} (htail : 0 ≤ tail)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1)
    (hsub : ∀ i ∈ s, ‖a i - b i‖ ≤ tail) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ tail := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using htail
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have hrewrite :
          a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
            (a i - b i) * ∏ j ∈ s, a j +
              b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) := by ring
      rw [hrewrite]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        have hprodA : ‖∏ j ∈ s, a j‖ ≤ 1 := by
          calc
            ‖∏ j ∈ s, a j‖ ≤ ∏ j ∈ s, ‖a j‖ := Finset.norm_prod_le _ _
            _ ≤ ∏ _j ∈ s, (1 : ℝ) := Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
              (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
            _ = 1 := by simp
        refine (mul_le_mul (hsub i (Finset.mem_insert_self i s))
          hprodA
          (norm_nonneg _) htail).trans ?_
        simp
      · rw [norm_mul]
        refine (mul_le_mul (hb i (Finset.mem_insert_self i s))
          (ih (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
            (fun j hj ↦ hb j (Finset.mem_insert_of_mem hj))
            (fun j hj ↦ hsub j (Finset.mem_insert_of_mem hj)))
          (norm_nonneg _) zero_le_one).trans ?_
        simp
omit [CompleteSpace K] in
private theorem fredholm_det_sub_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι K) {tail : ℝ} (htail : 0 ≤ tail)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1)
    (hsub : ∀ i j, ‖A i j - B i j‖ ≤ tail) :
    ‖A.det - B.det‖ ≤ tail := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (M := K) htail ?_
  intro σ _
  rw [← mul_sub, norm_mul]
  have hprod := fredholm_norm_prod_sub_prod_le (K := K) Finset.univ
    (fun i ↦ A (σ i) i) (fun i ↦ B (σ i) i) htail
    (fun i _ ↦ hA (σ i) i) (fun i _ ↦ hB (σ i) i)
    (fun i _ ↦ hsub (σ i) i)
  have hsign : ‖((↑(Equiv.Perm.sign σ) : ℤ) : K)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  rw [hsign, one_mul]
  exact hprod
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem fredholmPaddedCutoffKernel_global_bound
    (T : NuclearOperator (K := K) w) (smaller larger : ℕ)
    (u v : WeightedCutoff w larger) :
    ‖fredholmPaddedCutoffKernel w T smaller larger u v‖ ≤ 1 := by
  by_cases hu : monomialWeight w u.1 ≤ smaller
  · by_cases hv : monomialWeight w v.1 ≤ smaller
    · simpa [fredholmPaddedCutoffKernel, hu, hv] using T.decay.2 u.1 v.1
    · simp [fredholmPaddedCutoffKernel, hu, hv]
  · simp [fredholmPaddedCutoffKernel, hu]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem cutoffKernel_sub_fredholmPaddedCutoffKernel_tail_bound
    (T : NuclearOperator (K := K) w) (smaller larger : ℕ)
    (u v : WeightedCutoff w larger) :
    ‖cutoffKernel w T.kernel larger u v -
        fredholmPaddedCutoffKernel w T smaller larger u v‖ ≤ T.tailBound smaller := by
  by_cases hu : monomialWeight w u.1 ≤ smaller
  · by_cases hv : monomialWeight w v.1 ≤ smaller
    · simp [cutoffKernel, fredholmPaddedCutoffKernel, hu, hv, T.decay.1.1 smaller]
    · simpa [cutoffKernel, fredholmPaddedCutoffKernel, hu, hv] using
        T.decay.1.2.2 smaller u.1 v.1 (Or.inr (Nat.lt_of_not_ge hv))
  · simpa [cutoffKernel, fredholmPaddedCutoffKernel, hu] using
      T.decay.1.2.2 smaller u.1 v.1 (Or.inl (Nat.lt_of_not_ge hu))
omit [CompleteSpace K] in
theorem fredholm_charpolyRev_coeff_sub_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι K) {tail : ℝ} (htail : 0 ≤ tail)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1)
    (hsub : ∀ i j, ‖A i j - B i j‖ ≤ tail) (degree : ℕ) :
    ‖A.charpolyRev.coeff degree - B.charpolyRev.coeff degree‖ ≤ tail := by
  classical
  have hcoeff (M : Matrix ι ι K) :
      M.charpolyRev.coeff degree =
        (-1 : K) ^ degree * ∑ s ∈ Finset.univ.powersetCard degree,
          (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det := by
    rw [Matrix.charpolyRev]
    have hmatrix :
        -((Polynomial.X : K[X]) • M.map Polynomial.C) =
          (Polynomial.X : K[X]) • (-M).map Polynomial.C := by
      ext i j
      simp
    rw [sub_eq_add_neg, hmatrix]
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    simp only [Matrix.submatrix_neg, Pi.neg_apply, Matrix.det_neg, Fintype.card_coe,
      mul_sum]
    exact Finset.sum_congr rfl fun s hs ↦ by rw [(Finset.mem_powersetCard.mp hs).2]
  rw [hcoeff A, hcoeff B, ← mul_sub, norm_mul]
  have hsign : ‖(-1 : K) ^ degree‖ = 1 := by simp
  rw [hsign, one_mul]
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (M := K) (s := Finset.univ.powersetCard degree)
    (f := fun s : Finset ι ↦
      (A.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det -
        (B.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det) htail ?_
  intro s hs
  exact fredholm_det_sub_norm_le (K := K)
    (A.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι))
    (B.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) htail
    (fun i j ↦ hA i.1 j.1) (fun i j ↦ hB i.1 j.1) (fun i j ↦ hsub i.1 j.1)
omit [CompleteSpace K] in
theorem cutoffFredholmCoefficient_sub_norm_le
    (T : NuclearOperator (K := K) w) (degree : ℕ)
    {smaller larger : ℕ} (h : smaller ≤ larger) :
    ‖cutoffFredholmCoefficient w T degree larger -
        cutoffFredholmCoefficient w T degree smaller‖ ≤ T.tailBound smaller := by
  rw [cutoffFredholmCoefficient, cutoffFredholmCoefficient,
    cutoffFredholmPolynomial_eq_charpolyRev,
    ← fredholmPaddedCutoffPolynomial_eq (K := K) w T h,
    FiniteFields.LinearAlgebra.fredholmDeterminant,
    ← LinearMap.charpoly_toMatrix
      (Matrix.toLin' (fredholmPaddedCutoffKernel w T smaller larger))
      (Pi.basisFun K (WeightedCutoff w larger)),
    Matrix.reverse_charpoly, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  exact fredholm_charpolyRev_coeff_sub_norm_le (K := K)
    (cutoffKernel w T.kernel larger)
    (fredholmPaddedCutoffKernel w T smaller larger) (T.decay.1.1 smaller)
    (fun i j ↦ T.decay.2 i.1 j.1)
    (fredholmPaddedCutoffKernel_global_bound w T smaller larger)
    (cutoffKernel_sub_fredholmPaddedCutoffKernel_tail_bound w T smaller larger) degree
omit [CompleteSpace K] in
theorem cauchy_cutoffFredholmCoefficient
    (T : NuclearOperator (K := K) w) (degree : ℕ) :
    CauchySeq (fun bound ↦ cutoffFredholmCoefficient w T degree bound) := by
  apply cauchySeq_of_le_tendsto_0' T.tailBound
  · intro smaller larger h
    rw [dist_eq_norm, norm_sub_rev]
    exact cutoffFredholmCoefficient_sub_norm_le w T degree h
  · exact T.decay.1.2.1
theorem tendsto_cutoffFredholmCoefficient
    (T : NuclearOperator (K := K) w) (degree : ℕ) :
    Tendsto (fun bound ↦ cutoffFredholmCoefficient w T degree bound) atTop
      (nhds (weightedFredholmCoefficient w T degree)) :=
  (cauchy_cutoffFredholmCoefficient w T degree).tendsto_limUnder
omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp]
theorem weightedFredholmSeries_coeff
    (T : NuclearOperator (K := K) w) (degree : ℕ) :
    PowerSeries.coeff degree (weightedFredholmSeries w T) =
      weightedFredholmCoefficient w T degree := by
  simp [weightedFredholmSeries]
@[simp]
theorem weightedFredholmCoefficient_zero (T : NuclearOperator (K := K) w) :
    weightedFredholmCoefficient w T 0 = 1 := by
  apply tendsto_nhds_unique (tendsto_cutoffFredholmCoefficient w T 0)
  have hseq : (fun bound ↦ cutoffFredholmCoefficient w T 0 bound) =
      (fun _ : ℕ ↦ (1 : K)) := by
    funext bound
    rw [cutoffFredholmCoefficient, cutoffFredholmPolynomial,
      FiniteFields.LinearAlgebra.fredholmDeterminant_coeff_zero]
  rw [hseq]
  exact tendsto_const_nhds
end NuclearOperator
end FiniteFields.Dwork
end
end
section
noncomputable section
open Module Polynomial PowerSeries
namespace FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
omit [Module.Free R M] [Module.Finite R M] in
@[simp]
theorem coeff_tracePowerSeries (u : Module.End R M) (n : ℕ) :
    PowerSeries.coeff n (tracePowerSeries u) = LinearMap.trace R M (u ^ (n + 1)) := by
  simp [tracePowerSeries]
@[simp]
private theorem coeff_matrixGeometricSeries {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (i j : ι) (n : ℕ) :
    PowerSeries.coeff n (matrixGeometricSeries A i j) = (A ^ n) i j := by
  simp [matrixGeometricSeries]
@[simp]
private theorem constantCoeff_matrixGeometricSeries {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (i j : ι) :
    PowerSeries.constantCoeff (matrixGeometricSeries A i j) = (A ^ 0) i j := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_matrixGeometricSeries A i j 0
private theorem one_sub_X_mul_matrixGeometricSeries {ι : Type w} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι R) :
    (1 - (PowerSeries.X : R⟦X⟧) • A.map PowerSeries.C) * matrixGeometricSeries A = 1 := by
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [Matrix.mul_apply, Matrix.one_apply]
  | succ n =>
      simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
        Matrix.map_apply, smul_eq_mul]
      rw [map_sum]
      simp_rw [sub_mul, map_sub]
      simp_rw [mul_assoc]
      simp_rw [PowerSeries.coeff_succ_X_mul]
      simp only [ite_mul, one_mul, zero_mul, apply_ite, map_zero,
        coeff_matrixGeometricSeries, PowerSeries.coeff_C_mul]
      rw [Finset.sum_sub_distrib]
      rw [Fintype.sum_ite_eq]
      rw [← Matrix.mul_apply]
      rw [← pow_succ']
      simp
private theorem coeff_trace_matrixGeometricSeries_mul {ι : Type w} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι R) (n : ℕ) :
    PowerSeries.coeff n
        (Matrix.trace (matrixGeometricSeries A * A.map PowerSeries.C)) =
      Matrix.trace (A ^ (n + 1)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum,
    PowerSeries.coeff_mul_C, coeff_matrixGeometricSeries,
    Matrix.map_apply]
  simp_rw [← Matrix.mul_apply]
  rw [← pow_succ]
private theorem map_matrix_C {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    Polynomial.coeToPowerSeries.ringHom.mapMatrix (A.map Polynomial.C) =
      A.map PowerSeries.C := by
  ext i j n
  simp
private theorem map_one_sub_X_smul {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    Polynomial.coeToPowerSeries.ringHom.mapMatrix
        (1 - (Polynomial.X : R[X]) • A.map Polynomial.C) =
      1 - (PowerSeries.X : R⟦X⟧) • A.map PowerSeries.C := by
  ext i j n
  simp [Matrix.one_apply]
  rw [mul_comm (A i j)]
  by_cases hij : i = j
  · simpa [hij] using (Polynomial.coeff_one (R := R) (n := n))
  · simp [hij]
private theorem invOfUnit_smul_adjugate_eq_matrixGeometricSeries
    {ι : Type w} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) :
    PowerSeries.invOfUnit
          ((Matrix.det
            (1 - (Polynomial.X : R[X]) • A.map Polynomial.C) : R[X]) : R⟦X⟧) 1 •
        Matrix.adjugate (1 - (PowerSeries.X : R⟦X⟧) • A.map PowerSeries.C) =
      matrixGeometricSeries A := by
  let Bp : Matrix ι ι R[X] :=
    1 - (Polynomial.X : R[X]) • A.map Polynomial.C
  let B : Matrix ι ι R⟦X⟧ :=
    1 - (PowerSeries.X : R⟦X⟧) • A.map PowerSeries.C
  let P : R⟦X⟧ := (Bp.det : R⟦X⟧)
  let Q : R⟦X⟧ := PowerSeries.invOfUnit P 1
  have hmap : Polynomial.coeToPowerSeries.ringHom.mapMatrix Bp = B := by
    exact map_one_sub_X_smul A
  have hdet : B.det = P := by
    calc
      B.det = (Polynomial.coeToPowerSeries.ringHom.mapMatrix Bp).det :=
        congrArg Matrix.det hmap.symm
      _ = Polynomial.coeToPowerSeries.ringHom Bp.det :=
        (RingHom.map_det Polynomial.coeToPowerSeries.ringHom Bp).symm
      _ = P := rfl
  have hconst : PowerSeries.constantCoeff P = 1 := by
    dsimp [P, Bp]
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact Matrix.eval_charpolyRev
  have hleft : (Q • B.adjugate) * B = 1 := by
    calc
      (Q • B.adjugate) * B = Q • (B.adjugate * B) := by rw [Matrix.smul_mul]
      _ = Q • (B.det • (1 : Matrix ι ι R⟦X⟧)) := by rw [Matrix.adjugate_mul]
      _ = (Q * B.det) • (1 : Matrix ι ι R⟦X⟧) := by rw [smul_smul]
      _ = 1 := by
        rw [hdet]
        change (PowerSeries.invOfUnit P 1 * P) • (1 : Matrix ι ι R⟦X⟧) = 1
        rw [PowerSeries.invOfUnit_mul P 1 hconst]
        simp
  have hright : B * matrixGeometricSeries A = 1 := by
    exact one_sub_X_mul_matrixGeometricSeries A
  change Q • B.adjugate = matrixGeometricSeries A
  calc
    Q • B.adjugate = (Q • B.adjugate) * 1 := by rw [Matrix.mul_one]
    _ = (Q • B.adjugate) * (B * matrixGeometricSeries A) := by rw [hright]
    _ = ((Q • B.adjugate) * B) * matrixGeometricSeries A := by rw [Matrix.mul_assoc]
    _ = matrixGeometricSeries A := by rw [hleft, Matrix.one_mul]
theorem coeff_fredholmLogDerivative (u : Module.End R M) (n : ℕ) :
    PowerSeries.coeff n (fredholmLogDerivative u) = LinearMap.trace R M (u ^ (n + 1)) := by
  let b := Module.Free.chooseBasis R M
  let A := LinearMap.toMatrix b b u
  have hlog :
      fredholmLogDerivative u =
        Matrix.trace (matrixGeometricSeries A * A.map PowerSeries.C) := by
    rw [logDerivative_fredholmDeterminant u b]
    rw [fredholmDeterminant_eq_det u b]
    let Bp : Matrix _ _ R[X] :=
      1 - (Polynomial.X : R[X]) • A.map Polynomial.C
    let B : Matrix _ _ R⟦X⟧ :=
      1 - (PowerSeries.X : R⟦X⟧) • A.map PowerSeries.C
    let Q : R⟦X⟧ := PowerSeries.invOfUnit (Bp.det : R⟦X⟧) 1
    have hnum :
        ((Matrix.trace (Bp.adjugate * A.map Polynomial.C) : R[X]) : R⟦X⟧) =
          Matrix.trace (B.adjugate * A.map PowerSeries.C) := by
      calc
        ((Matrix.trace (Bp.adjugate * A.map Polynomial.C) : R[X]) : R⟦X⟧) =
            Polynomial.coeToPowerSeries.ringHom
              (Matrix.trace (Bp.adjugate * A.map Polynomial.C)) := rfl
        _ = Matrix.trace
              (Polynomial.coeToPowerSeries.ringHom.mapMatrix
                (Bp.adjugate * A.map Polynomial.C)) :=
              AddMonoidHom.map_trace Polynomial.coeToPowerSeries.ringHom _
        _ = Matrix.trace (B.adjugate * A.map PowerSeries.C) := by
              rw [map_mul, RingHom.map_adjugate, map_matrix_C]
              change Matrix.trace
                ((Polynomial.coeToPowerSeries.ringHom.mapMatrix Bp).adjugate *
                  A.map PowerSeries.C) = _
              rw [show Polynomial.coeToPowerSeries.ringHom.mapMatrix Bp = B by
                exact map_one_sub_X_smul A]
    have hres : Q • B.adjugate = matrixGeometricSeries A := by
      exact invOfUnit_smul_adjugate_eq_matrixGeometricSeries A
    change ((Matrix.trace (Bp.adjugate * A.map Polynomial.C) : R[X]) : R⟦X⟧) * Q = _
    rw [hnum]
    calc
      Matrix.trace (B.adjugate * A.map PowerSeries.C) * Q =
          Q * Matrix.trace (B.adjugate * A.map PowerSeries.C) := by rw [mul_comm]
      _ = Matrix.trace (Q • (B.adjugate * A.map PowerSeries.C)) := by
        rw [Matrix.trace_smul]
        rfl
      _ = Matrix.trace ((Q • B.adjugate) * A.map PowerSeries.C) := by
        rw [Matrix.smul_mul]
      _ = Matrix.trace (matrixGeometricSeries A * A.map PowerSeries.C) := by rw [hres]
  rw [hlog, coeff_trace_matrixGeometricSeries_mul]
  rw [LinearMap.trace_eq_matrix_trace R b, LinearMap.toMatrix_pow]
theorem fredholmLogDerivative_eq_tracePowerSeries (u : Module.End R M) :
    fredholmLogDerivative u = tracePowerSeries u := by
  ext n
  rw [coeff_fredholmLogDerivative, coeff_tracePowerSeries]
end FiniteFields.LinearAlgebra
end
end
section
noncomputable section
open Filter Set Topology Polynomial PowerSeries Finset
namespace FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
namespace NuclearOperator
omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp]
theorem fredholmDeterminant_coeff (T : NuclearOperator (K := K) w) (degree : ℕ) :
    PowerSeries.coeff degree (fredholmDeterminant w T) =
      weightedFredholmCoefficient w T degree := by
  simp [fredholmDeterminant]
@[simp]
theorem fredholmDeterminant_constantCoeff (T : NuclearOperator (K := K) w) :
    PowerSeries.constantCoeff (fredholmDeterminant w T) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp
omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp]
theorem coeff_tracePowerSeries (T : NuclearOperator (K := K) w) (n : ℕ) :
    PowerSeries.coeff n (tracePowerSeries w T) =
      tracePower w T ⟨n + 1, Nat.succ_pos n⟩ := by
  simp [tracePowerSeries]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem trace_cutoffEndomorphism_pow
    (T : NuclearOperator (K := K) w) (bound power : ℕ) :
    LinearMap.trace K (WeightedCutoff w bound → K) ((cutoffEndomorphism w T bound) ^ power) =
      finiteKernelPowerTrace w T.kernel power bound := by
  simp [cutoffEndomorphism, finiteKernelPowerTrace, ← Matrix.toLin'_pow]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem cutoff_neg_derivative_eq_mul_tracePowerSeries
    (T : NuclearOperator (K := K) w) (bound : ℕ) :
    -(PowerSeries.derivative K (cutoffFredholmPolynomial w T bound : K⟦X⟧)) =
      (cutoffFredholmPolynomial w T bound : K⟦X⟧) *
        FiniteFields.LinearAlgebra.tracePowerSeries (cutoffEndomorphism w T bound) := by
  let u := cutoffEndomorphism w T bound
  let P : K⟦X⟧ := (cutoffFredholmPolynomial w T bound : K⟦X⟧)
  have hP : P =
      (FiniteFields.LinearAlgebra.fredholmDeterminant u : K[X]) := rfl
  have hconst : PowerSeries.constantCoeff P = (1 : Kˣ) := by
    rw [hP, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp
  have hlog :=
    FiniteFields.LinearAlgebra.fredholmLogDerivative_eq_tracePowerSeries u
  change -(PowerSeries.derivative K P) =
    P * FiniteFields.LinearAlgebra.tracePowerSeries u
  calc
    -(PowerSeries.derivative K P) = -(PowerSeries.derivative K P) * 1 := by rw [mul_one]
    _ = -(PowerSeries.derivative K P) * (PowerSeries.invOfUnit P 1 * P) := by
      rw [PowerSeries.invOfUnit_mul P 1 hconst]
    _ = (-(PowerSeries.derivative K P) * PowerSeries.invOfUnit P 1) * P := by
      rw [mul_assoc]
    _ = FiniteFields.LinearAlgebra.fredholmLogDerivative u * P := by
      rw [FiniteFields.LinearAlgebra.fredholmLogDerivative, hP]
    _ = FiniteFields.LinearAlgebra.tracePowerSeries u * P := by rw [hlog]
    _ = P * FiniteFields.LinearAlgebra.tracePowerSeries u := by rw [mul_comm]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem cutoff_coefficient_trace_identity
    (T : NuclearOperator (K := K) w) (n bound : ℕ) :
    -(cutoffFredholmCoefficient w T (n + 1) bound * (n + 1 : K)) =
      ∑ p ∈ antidiagonal n,
        cutoffFredholmCoefficient w T p.1 bound *
          finiteKernelPowerTrace w T.kernel (p.2 + 1) bound := by
  have h := congrArg (PowerSeries.coeff n)
    (cutoff_neg_derivative_eq_mul_tracePowerSeries w T bound)
  simpa [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    cutoffFredholmCoefficient, trace_cutoffEndomorphism_pow] using h
private theorem weightedFredholmCoefficient_trace_identity
    (T : NuclearOperator (K := K) w) (n : ℕ) :
    -(weightedFredholmCoefficient w T (n + 1) * (n + 1 : K)) =
      ∑ p ∈ antidiagonal n,
        weightedFredholmCoefficient w T p.1 *
          tracePower w T ⟨p.2 + 1, Nat.succ_pos p.2⟩ := by
  have hleft : Tendsto
      (fun bound ↦ -(cutoffFredholmCoefficient w T (n + 1) bound * (n + 1 : K))) atTop
      (nhds (-(weightedFredholmCoefficient w T (n + 1) * (n + 1 : K)))) :=
    ((tendsto_cutoffFredholmCoefficient w T (n + 1)).mul tendsto_const_nhds).neg
  have hright : Tendsto
      (fun bound ↦ ∑ p ∈ antidiagonal n,
        cutoffFredholmCoefficient w T p.1 bound *
          finiteKernelPowerTrace w T.kernel (p.2 + 1) bound) atTop
      (nhds (∑ p ∈ antidiagonal n,
        weightedFredholmCoefficient w T p.1 *
          tracePower w T ⟨p.2 + 1, Nat.succ_pos p.2⟩)) := by
    apply tendsto_finsetSum
    intro p hp
    exact (tendsto_cutoffFredholmCoefficient w T p.1).mul
      (T.tracePower_tendsto (w := w) ⟨p.2 + 1, Nat.succ_pos p.2⟩)
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun bound ↦
      (cutoff_coefficient_trace_identity w T n bound).symm))
private theorem neg_derivative_fredholmDeterminant_eq_mul_tracePowerSeries
    (T : NuclearOperator (K := K) w) :
    -(PowerSeries.derivative K (fredholmDeterminant w T)) =
      fredholmDeterminant w T * tracePowerSeries w T := by
  ext n
  simpa [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] using
    weightedFredholmCoefficient_trace_identity w T n
theorem coeff_fredholmLogDerivative
    (T : NuclearOperator (K := K) w) (n : ℕ) :
    PowerSeries.coeff n (fredholmLogDerivative w T) =
      tracePower w T ⟨n + 1, Nat.succ_pos n⟩ := by
  have hconst : PowerSeries.constantCoeff (fredholmDeterminant w T) = (1 : Kˣ) := by
    change PowerSeries.constantCoeff (fredholmDeterminant w T) = (1 : K)
    exact fredholmDeterminant_constantCoeff w T
  rw [fredholmLogDerivative,
    neg_derivative_fredholmDeterminant_eq_mul_tracePowerSeries]
  have hseries :
      (fredholmDeterminant w T * tracePowerSeries w T) *
          PowerSeries.invOfUnit (fredholmDeterminant w T) 1 =
        tracePowerSeries w T := by
    calc
      _ = tracePowerSeries w T *
          (fredholmDeterminant w T *
            PowerSeries.invOfUnit (fredholmDeterminant w T) 1) := by ac_rfl
      _ = tracePowerSeries w T * 1 := by
        rw [PowerSeries.mul_invOfUnit (fredholmDeterminant w T) 1 hconst]
      _ = tracePowerSeries w T := by rw [mul_one]
  rw [hseries, coeff_tracePowerSeries]
theorem fredholmLogDerivative_eq_tracePowerSeries (T : NuclearOperator (K := K) w) :
    fredholmLogDerivative w T = tracePowerSeries w T := by
  ext n
  rw [coeff_fredholmLogDerivative, coeff_tracePowerSeries]
end NuclearOperator
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section PadicGrowth
variable {K : Type*} [NontriviallyNormedField K]
theorem isPadicEntire_iff_exists_bound (F : K⟦X⟧) :
    IsPadicEntire F ↔
      ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ n : ℕ, ‖PowerSeries.coeff n F‖ * R ^ n ≤ C := by
  constructor
  · intro hF R hR
    obtain ⟨C, hC⟩ := (hF R hR).bddAbove_range
    exact ⟨C, fun n ↦ hC (Set.mem_range_self n)⟩
  · intro hF R hR
    obtain ⟨C, hC⟩ := hF (2 * R + 1) (by linarith)
    have hR' : (0 : ℝ) < 2 * R + 1 := by linarith
    set ρ : ℝ := R / (2 * R + 1) with hρdef
    have hρ0 : 0 ≤ ρ := div_nonneg hR hR'.le
    have hρ1 : ρ < 1 := by
      rw [hρdef, div_lt_one hR']
      linarith
    have hfactor : (2 * R + 1) * ρ = R := by
      rw [hρdef]
      field_simp
    refine squeeze_zero (g := fun n ↦ C * ρ ^ n) (fun n ↦ by positivity) (fun n ↦ ?_) ?_
    · have hsplit : R ^ n = (2 * R + 1) ^ n * ρ ^ n := by
        rw [← mul_pow, hfactor]
      calc ‖PowerSeries.coeff n F‖ * R ^ n
          = (‖PowerSeries.coeff n F‖ * (2 * R + 1) ^ n) * ρ ^ n := by
            rw [hsplit]; ring
        _ ≤ C * ρ ^ n := mul_le_mul_of_nonneg_right (hC n) (by positivity)
    · simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
theorem IsPadicEntire.exists_nonneg_bound {F : K⟦X⟧} (hF : IsPadicEntire F)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖PowerSeries.coeff n F‖ * R ^ n ≤ C := by
  obtain ⟨C, hC⟩ := (isPadicEntire_iff_exists_bound F).1 hF R hR
  refine ⟨C, ?_, hC⟩
  have h0 := hC 0
  simpa using le_trans (norm_nonneg (PowerSeries.coeff 0 F)) (by simpa using h0)
theorem isPadicEntire_of_eventually_zero {F : K⟦X⟧} {N : ℕ}
    (h : ∀ n, N ≤ n → PowerSeries.coeff n F = 0) : IsPadicEntire F := by
  intro R _
  refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop))
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [h n hn, norm_zero, zero_mul]
theorem isPadicEntire_one : IsPadicEntire (1 : K⟦X⟧) :=
  isPadicEntire_of_eventually_zero (N := 1) fun n hn ↦ by
    rw [PowerSeries.coeff_one, if_neg (by omega)]
theorem isPadicEntire_one_sub_C_mul_X (c : K) :
    IsPadicEntire (1 - PowerSeries.C c * (PowerSeries.X : K⟦X⟧)) :=
  isPadicEntire_of_eventually_zero (N := 2) fun n hn ↦ by
    rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X, if_neg (by omega), mul_zero, sub_zero]
theorem IsPadicEntire.rescale {F : K⟦X⟧} (hF : IsPadicEntire F) (c : K) :
    IsPadicEntire (PowerSeries.rescale c F) := by
  intro R hR
  have hcR : (0 : ℝ) ≤ ‖c‖ * R := by positivity
  refine (hF (‖c‖ * R) hcR).congr fun n ↦ ?_
  rw [PowerSeries.coeff_rescale, norm_mul, norm_pow, mul_pow]
  ring
end PadicGrowth
section PadicGrowthUltra
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
theorem norm_sum_mul_le_of_forall {ι : Type*} (s : Finset ι) (f : ι → K) {r C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C) (h : ∀ i ∈ s, ‖f i‖ * r ≤ C) :
    ‖∑ i ∈ s, f i‖ * r ≤ C := by
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · rw [← hr0, mul_zero]
    exact hC
  · rw [← le_div_iff₀ hr0]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (M := K) (by positivity) ?_
    intro i hi
    rw [le_div_iff₀ hr0]
    exact h i hi
theorem IsPadicEntire.mul {F G : K⟦X⟧} (hF : IsPadicEntire F) (hG : IsPadicEntire G) :
    IsPadicEntire (F * G) := by
  rw [isPadicEntire_iff_exists_bound]
  intro R hR
  obtain ⟨CF, hCF0, hCF⟩ := hF.exists_nonneg_bound R hR
  obtain ⟨CG, hCG0, hCG⟩ := hG.exists_nonneg_bound R hR
  refine ⟨CF * CG, fun n ↦ ?_⟩
  rw [PowerSeries.coeff_mul]
  refine norm_sum_mul_le_of_forall _ _ (by positivity) (by positivity) ?_
  intro ij hij
  have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [norm_mul]
  calc ‖PowerSeries.coeff ij.1 F‖ * ‖PowerSeries.coeff ij.2 G‖ * R ^ n
      = (‖PowerSeries.coeff ij.1 F‖ * R ^ ij.1) *
          (‖PowerSeries.coeff ij.2 G‖ * R ^ ij.2) := by
        rw [← hsum, pow_add]; ring
    _ ≤ CF * CG :=
        mul_le_mul (hCF ij.1) (hCG ij.2) (by positivity) hCF0
theorem IsPadicEntire.pow {F : K⟦X⟧} (hF : IsPadicEntire F) : ∀ m : ℕ, IsPadicEntire (F ^ m)
  | 0 => by simpa using isPadicEntire_one
  | m + 1 => by
      rw [pow_succ]
      exact (hF.pow m).mul hF
theorem isPadicEntire_prod {ι : Type*} (s : Finset ι) (F : ι → K⟦X⟧)
    (hF : ∀ i ∈ s, IsPadicEntire (F i)) : IsPadicEntire (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPadicEntire_one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hF i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hF j (Finset.mem_insert_of_mem hj))
end PadicGrowthUltra
section PadicGrowthComplete
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
end PadicGrowthComplete
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section FredholmEntire
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
namespace NuclearOperator
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem escapeBound_nonneg (T : NuclearOperator (K := K) w) (m : ℕ)
    (u : MonomialIndex d) : 0 ≤ escapeBound w T m u := by
  rw [escapeBound]
  split
  · exact zero_le_one
  · exact T.decay.1.1 m
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem norm_kernel_le_escapeBound (T : NuclearOperator (K := K) w) (m : ℕ)
    (u v : MonomialIndex d) : ‖T.kernel u v‖ ≤ escapeBound w T m u := by
  rw [escapeBound]
  split
  · exact T.decay.2 u v
  · rename_i hu
    exact T.decay.1.2.2 m u v (Or.inl (Nat.lt_of_not_ge hu))
omit [CompleteSpace K] in
private theorem norm_det_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hA : ∀ i j, ‖A i j‖ ≤ b i) :
    ‖A.det‖ ≤ ∏ i, b i := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (M := K)
    (Finset.prod_nonneg fun i _ ↦ hb i) ?_
  intro σ _
  rw [norm_mul]
  have hsign : ‖((↑(Equiv.Perm.sign σ) : ℤ) : K)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  rw [hsign, one_mul]
  calc ‖∏ i, A (σ i) i‖
      ≤ ∏ i, ‖A (σ i) i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i, b (σ i) :=
        Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hA (σ i) i)
    _ = ∏ i, b i := Equiv.prod_comp σ b
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem coeff_charpolyRev_eq_sum_minors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (degree : ℕ) :
    M.charpolyRev.coeff degree =
      (-1 : K) ^ degree * ∑ s ∈ Finset.univ.powersetCard degree,
        (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det := by
  rw [Matrix.charpolyRev]
  have hmatrix :
      -((Polynomial.X : Polynomial K) • M.map Polynomial.C) =
        (Polynomial.X : Polynomial K) • (-M).map Polynomial.C := by
    ext i j
    simp
  rw [sub_eq_add_neg, hmatrix, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  simp only [Matrix.submatrix_neg, Pi.neg_apply, Matrix.det_neg, Fintype.card_coe,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun s hs ↦ by rw [(Finset.mem_powersetCard.mp hs).2]
omit [CompleteSpace K] in
private theorem norm_cutoffFredholmCoefficient_le (T : NuclearOperator (K := K) w)
    (m n bound : ℕ) (ht1 : T.tailBound m ≤ 1) :
    ‖cutoffFredholmCoefficient w T n bound‖ ≤ T.tailBound m ^ (n - cutoffCard w m) := by
  classical
  have ht0 : 0 ≤ T.tailBound m := T.decay.1.1 m
  rw [cutoffFredholmCoefficient, cutoffFredholmPolynomial_eq_charpolyRev,
    coeff_charpolyRev_eq_sum_minors, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (M := K) (by positivity) ?_
  intro s hs
  have hcard : s.card = n := (Finset.mem_powersetCard.mp hs).2
  have hdet := norm_det_le_prod
    ((cutoffKernel w T.kernel bound).submatrix
      (Subtype.val : s → WeightedCutoff w bound) (Subtype.val : s → WeightedCutoff w bound))
    (fun i : s ↦ escapeBound w T m (i : WeightedCutoff w bound).1)
    (fun i ↦ escapeBound_nonneg w T m _)
    (fun i j ↦ norm_kernel_le_escapeBound w T m _ _)
  refine hdet.trans ?_
  rw [Finset.prod_coe_sort s (fun i ↦ escapeBound w T m i.1)]
  have hprod : ∏ i ∈ s, escapeBound w T m i.1 =
      T.tailBound m ^ (s.filter fun i ↦ ¬ monomialWeight w i.1 ≤ m).card := by
    simp only [escapeBound]
    rw [Finset.prod_ite (fun _ ↦ (1 : ℝ)) (fun _ ↦ T.tailBound m)]
    simp
  rw [hprod]
  refine pow_le_pow_of_le_one ht0 ht1 ?_
  have hsmall : (s.filter fun i ↦ monomialWeight w i.1 ≤ m).card
      ≤ (finite_monomialCutoff w m).toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun i ↦ (i.1 : MonomialIndex d)) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter,
        Set.Finite.coe_toFinset, mem_monomialCutoff] at hi ⊢
      exact hi.2
    · intro i _ j _ hij
      exact Subtype.ext hij
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s) (p := fun i ↦ monomialWeight w i.1 ≤ m)
  simp only [cutoffCard]
  omega
private theorem norm_weightedFredholmCoefficient_le (T : NuclearOperator (K := K) w)
    (m n : ℕ) (ht1 : T.tailBound m ≤ 1) :
    ‖weightedFredholmCoefficient w T n‖ ≤ T.tailBound m ^ (n - cutoffCard w m) :=
  le_of_tendsto (tendsto_cutoffFredholmCoefficient w T n).norm
    (Eventually.of_forall fun bound ↦ norm_cutoffFredholmCoefficient_le w T m n bound ht1)
theorem isPadicEntire_fredholmDeterminant (T : NuclearOperator (K := K) w) :
    IsPadicEntire (fredholmDeterminant w T) := by
  intro R hR
  have hpos : (0 : ℝ) < R + 1 := by linarith
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp T.decay.1.2.1 (R + 1)⁻¹ (by positivity)
  have ht0 : 0 ≤ T.tailBound m := T.decay.1.1 m
  have htlt : T.tailBound m < (R + 1)⁻¹ := by
    have := hm m le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg ht0] at this
  have hinv : (R + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have ht1 : T.tailBound m ≤ 1 := (htlt.trans_le hinv).le
  have hprod : T.tailBound m * R < 1 := by
    calc T.tailBound m * R ≤ T.tailBound m * (R + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) ht0
      _ < (R + 1)⁻¹ * (R + 1) := mul_lt_mul_of_pos_right htlt hpos
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  set c := cutoffCard w m with hc
  set t := T.tailBound m with hT
  set Cst : ℝ := max 1 (R ^ c) with hCst
  have hCst1 : (1 : ℝ) ≤ Cst := le_max_left _ _
  have hCstR : R ^ c ≤ Cst := le_max_right _ _
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_)
    (g := fun n ↦ Cst * (t * R) ^ (n - c)) ?_
  · rw [fredholmDeterminant_coeff]
    rcases le_or_gt c n with hcn | hcn
    · have hR' : R ^ n = R ^ c * R ^ (n - c) := by
        rw [← pow_add]
        congr 1
        omega
      calc ‖weightedFredholmCoefficient w T n‖ * R ^ n
          ≤ t ^ (n - c) * R ^ n :=
            mul_le_mul_of_nonneg_right
              (norm_weightedFredholmCoefficient_le w T m n ht1) (by positivity)
        _ = R ^ c * (t * R) ^ (n - c) := by
            rw [hR', mul_pow]; ring
        _ ≤ Cst * (t * R) ^ (n - c) :=
            mul_le_mul_of_nonneg_right hCstR (by positivity)
    · have hzero : n - c = 0 := by omega
      rw [hzero, pow_zero, mul_one]
      calc ‖weightedFredholmCoefficient w T n‖ * R ^ n
          ≤ 1 * R ^ n := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have := norm_weightedFredholmCoefficient_le w T m n ht1
            rwa [hzero, pow_zero] at this
        _ = R ^ n := one_mul _
        _ ≤ Cst := by
            rcases le_or_gt R 1 with hR1 | hR1
            · exact le_trans (pow_le_one₀ hR hR1) hCst1
            · exact le_trans (pow_le_pow_right₀ hR1.le (by omega : n ≤ c)) hCstR
  · have hsub : Tendsto (fun n : ℕ ↦ n - c) atTop atTop :=
      tendsto_atTop_atTop.2 fun b ↦ ⟨b + c, fun a ha ↦ by omega⟩
    have hgeom : Tendsto (fun j : ℕ ↦ (t * R) ^ j) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hprod
    simpa using ((hgeom.comp hsub).const_mul Cst)
end NuclearOperator
end FredholmEntire
section DworkEntire
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
variable {d : ℕ} (w : PositiveMonomialWeight d)
theorem dworkFredholmDeterminant_isPadicEntire (f : MonomialIndex d →₀ k) :
    IsPadicEntire
      (NuclearOperator.fredholmDeterminant w (dworkQFrobeniusNuclearOperator k p w f)) :=
  NuclearOperator.isPadicEntire_fredholmDeterminant w _
end DworkEntire
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section ZetaSeries
private theorem constantCoeff_countingZetaLog (N : ℕ → ℕ) :
    PowerSeries.constantCoeff (countingZetaLog N) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, countingZetaLog, PowerSeries.coeff_mk]
  simp
private theorem derivative_countingZetaLog (N : ℕ → ℕ) :
    PowerSeries.derivative ℚ (countingZetaLog N) = countingSeries N := by
  ext n
  rw [PowerSeries.coeff_derivative, countingZetaLog, PowerSeries.coeff_mk, coeff_countingSeries]
  have hne : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  field_simp
  push_cast
  ring
private theorem constantCoeff_countingZetaSeries (N : ℕ → ℕ) :
    PowerSeries.constantCoeff (countingZetaSeries N) = 1 := by
  rw [countingZetaSeries, ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero'
      (constantCoeff_countingZetaLog N)), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [he, constantCoeff_countingZetaLog]
private theorem derivative_countingZetaSeries (N : ℕ → ℕ) :
    PowerSeries.derivative ℚ (countingZetaSeries N) = countingSeries N * countingZetaSeries N := by
  rw [countingZetaSeries, PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_countingZetaLog N)),
    PowerSeries.derivative_exp, derivative_countingZetaLog, mul_comm]
private theorem countingZetaSeries_isZetaSeries (N : ℕ → ℕ) :
    IsZetaSeries N (countingZetaSeries N) :=
  ⟨constantCoeff_countingZetaSeries N, derivative_countingZetaSeries N⟩
variable (k₀ : Type) (p : ℕ) [Fact p.Prime] [Field k₀] [CharP k₀ p] [Finite k₀]
variable {d : ℕ}
theorem toricHypersurfaceZetaSeries_isZetaSeries (f : MonomialIndex d →₀ k₀) :
    IsZetaSeries (toricHypersurfacePointCount k₀ p f) (toricHypersurfaceZetaSeries k₀ p f) :=
  countingZetaSeries_isZetaSeries _
end ZetaSeries
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section LogDerivative
variable {R : Type*} [CommRing R]
private theorem neg_derivative_rescale {F L : R⟦X⟧} (c : R)
    (h : -(PowerSeries.derivative R F) = L * F) :
    -(PowerSeries.derivative R (PowerSeries.rescale c F))
      = (PowerSeries.C c * PowerSeries.rescale c L) * PowerSeries.rescale c F := by
  have hr : PowerSeries.rescale c (-(PowerSeries.derivative R F))
      = PowerSeries.rescale c (L * F) := by rw [h]
  rw [map_neg, map_mul] at hr
  rw [derivative_rescale]
  calc -(PowerSeries.C c * PowerSeries.rescale c (PowerSeries.derivative R F))
      = PowerSeries.C c * -(PowerSeries.rescale c (PowerSeries.derivative R F)) := by ring
    _ = PowerSeries.C c * (PowerSeries.rescale c L * PowerSeries.rescale c F) := by rw [hr]
    _ = PowerSeries.C c * PowerSeries.rescale c L * PowerSeries.rescale c F := by ring
private theorem neg_derivative_mul {F G LF LG : R⟦X⟧}
    (hF : -(PowerSeries.derivative R F) = LF * F)
    (hG : -(PowerSeries.derivative R G) = LG * G) :
    -(PowerSeries.derivative R (F * G)) = (LF + LG) * (F * G) := by
  rw [(PowerSeries.derivative R).leibniz F G, smul_eq_mul, smul_eq_mul, neg_add]
  have h1 : -(F * PowerSeries.derivative R G) = F * (LG * G) := by rw [← hG]; ring
  have h2 : -(G * PowerSeries.derivative R F) = G * (LF * F) := by rw [← hF]; ring
  rw [h1, h2]
  ring
private theorem neg_derivative_pow {F L : R⟦X⟧} (h : -(PowerSeries.derivative R F) = L * F) :
    ∀ m : ℕ, -(PowerSeries.derivative R (F ^ m)) = (m • L) * F ^ m
  | 0 => by simp
  | m + 1 => by
      have := neg_derivative_mul (neg_derivative_pow h m) h
      rw [← pow_succ] at this
      rw [this, succ_nsmul]
private theorem neg_derivative_prod {ι : Type*} (s : Finset ι) (F L : ι → R⟦X⟧)
    (h : ∀ i ∈ s, -(PowerSeries.derivative R (F i)) = L i * F i) :
    -(PowerSeries.derivative R (∏ i ∈ s, F i)) = (∑ i ∈ s, L i) * ∏ i ∈ s, F i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact neg_derivative_mul (h i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
@[simp]
private theorem coeff_geometricLogSeries (c : R) (n : ℕ) :
    PowerSeries.coeff n (geometricLogSeries c) = c ^ (n + 1) := by
  simp [geometricLogSeries]
private theorem neg_derivative_linearFactor (c : R) :
    -(PowerSeries.derivative R (1 - PowerSeries.C c * (PowerSeries.X : R⟦X⟧)))
      = geometricLogSeries c * (1 - PowerSeries.C c * (PowerSeries.X : R⟦X⟧)) := by
  have hderiv : PowerSeries.derivative R (1 - PowerSeries.C c * (PowerSeries.X : R⟦X⟧))
      = -(PowerSeries.C c) := by
    ext n
    rw [PowerSeries.coeff_derivative]
    rcases n with _ | n <;> simp
  rw [hderiv, neg_neg]
  ext n
  rw [PowerSeries.coeff_C, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rcases n with _ | n
  · simp
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hzero : ∀ i ∈ Finset.range n,
        PowerSeries.coeff i (geometricLogSeries c) *
          PowerSeries.coeff (n + 1 - i) (1 - PowerSeries.C c * (PowerSeries.X : R⟦X⟧)) = 0 := by
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      have : PowerSeries.coeff (n + 1 - i) (1 - PowerSeries.C c * (PowerSeries.X : R⟦X⟧)) = 0 := by
        rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_C_mul,
          PowerSeries.coeff_X, if_neg (by omega), mul_zero, sub_zero]
      rw [this, mul_zero]
    rw [Finset.sum_eq_zero hzero, zero_add]
    have hP0 : PowerSeries.coeff 0 (1 - PowerSeries.C c * (PowerSeries.X : R⟦X⟧)) = 1 := by
      rw [map_sub, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X, if_neg (by omega), mul_zero, sub_zero]
    have hP1 : PowerSeries.coeff 1 (1 - PowerSeries.C c * (PowerSeries.X : R⟦X⟧)) = -c := by
      rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X, if_pos rfl, mul_one, zero_sub]
    have h1 : n + 1 - n = 1 := by omega
    have h2 : n + 1 - (n + 1) = 0 := by omega
    rw [h1, h2, hP0, hP1, coeff_geometricLogSeries, coeff_geometricLogSeries, if_neg (by omega)]
    ring
end LogDerivative
section OdeUniqueness
variable {K : Type*} [Field K] [CharZero K]
private theorem powerSeries_eq_of_derivative_eq {B Y W : K⟦X⟧}
    (h0 : PowerSeries.constantCoeff Y = PowerSeries.constantCoeff W)
    (hY : PowerSeries.derivative K Y = B * Y)
    (hW : PowerSeries.derivative K W = B * W) : Y = W := by
  exact PowerSeries.eq_of_derivative_eq_mul (a := B)
    (by simpa only [mul_comm] using hY) (by simpa only [mul_comm] using hW) h0
end OdeUniqueness
section FredholmLogDerivative
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
theorem neg_derivative_fredholmDeterminant (T : NuclearOperator (K := K) w) :
    -(PowerSeries.derivative K (NuclearOperator.fredholmDeterminant w T))
      = NuclearOperator.tracePowerSeries w T * NuclearOperator.fredholmDeterminant w T := by
  have hconst : PowerSeries.constantCoeff (NuclearOperator.fredholmDeterminant w T) = (1 : Kˣ) := by
    change PowerSeries.constantCoeff (NuclearOperator.fredholmDeterminant w T) = (1 : K)
    exact NuclearOperator.fredholmDeterminant_constantCoeff w T
  have hlog := NuclearOperator.fredholmLogDerivative_eq_tracePowerSeries w T
  rw [NuclearOperator.fredholmLogDerivative] at hlog
  calc -(PowerSeries.derivative K (NuclearOperator.fredholmDeterminant w T))
      = -(PowerSeries.derivative K (NuclearOperator.fredholmDeterminant w T)) *
          (PowerSeries.invOfUnit (NuclearOperator.fredholmDeterminant w T) 1 *
            NuclearOperator.fredholmDeterminant w T) := by
        rw [PowerSeries.invOfUnit_mul _ 1 hconst, mul_one]
    _ = (-(PowerSeries.derivative K (NuclearOperator.fredholmDeterminant w T)) *
          PowerSeries.invOfUnit (NuclearOperator.fredholmDeterminant w T) 1) *
          NuclearOperator.fredholmDeterminant w T := by rw [mul_assoc]
    _ = _ := by rw [hlog]
end FredholmLogDerivative
section SignedSplit
variable {R : Type*} [CommRing R]
private theorem sum_signed_choose (x : R) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (-1 : R) ^ (m + i) * (m.choose i : R) * x ^ i = (x - 1) ^ m := by
  rw [sub_eq_add_neg, add_pow]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsign : (-1 : R) ^ (m + i) = (-1 : R) ^ (m - i) := by
    have hexp : m + i = (m - i) + 2 * i := by omega
    rw [hexp, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  rw [hsign]
  ring
private theorem sum_signed_split {ι : Type*} (s : Finset ι) (par : ι → Prop)
    [DecidablePred par] (sgn : ι → R) (c : ι → ℕ) (L : ι → R)
    (hpos : ∀ i ∈ s, par i → sgn i = 1) (hneg : ∀ i ∈ s, ¬ par i → sgn i = -1) :
    ∑ i ∈ s, sgn i * (c i : R) * L i
      = (∑ i ∈ s.filter par, c i • L i) - ∑ i ∈ s.filter (fun i ↦ ¬ par i), c i • L i := by
  have h1 : ∑ i ∈ s.filter par, sgn i * (c i : R) * L i
      = ∑ i ∈ s.filter par, c i • L i := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
    rw [hpos i his hip, one_mul, nsmul_eq_mul]
  have h2 : ∑ i ∈ s.filter (fun i ↦ ¬ par i), sgn i * (c i : R) * L i
      = -∑ i ∈ s.filter (fun i ↦ ¬ par i), c i • L i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
    rw [hneg i his hip, nsmul_eq_mul]
    ring
  rw [← Finset.sum_filter_add_sum_filter_not s par, h1, h2, ← sub_eq_add_neg]
end SignedSplit
section CharZeroInstance
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
end CharZeroInstance
section ZetaFredholm
variable (k₀ : Type) (p : ℕ) [Fact p.Prime] [Field k₀] [CharP k₀ p] [Finite k₀]
variable {d : ℕ}
private theorem natCard_ne_zero : (Nat.card k₀ : DworkCyclotomicField k₀ p) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.card_pos (α := k₀)).ne'
private theorem natCard_pow_mul_toricZetaScale_pow (i n : ℕ) :
    (Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1) * toricZetaScale k₀ p i ^ (n + 1)
      = ((Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1)) ^ i := by
  have hq := natCard_ne_zero k₀ p
  rw [toricZetaScale, mul_pow, inv_pow, ← pow_mul, mul_comm i (n + 1), pow_mul]
  field_simp
variable (w' : PositiveMonomialWeight (d + 1))
private theorem coeff_toricZetaLinearLog (i n : ℕ) :
    PowerSeries.coeff n (toricZetaLinearLog k₀ p i) = toricZetaScale k₀ p i ^ (n + 1) := by
  rw [toricZetaLinearLog, coeff_geometricLogSeries]
private theorem coeff_toricZetaFredholmLog (f : MonomialIndex d →₀ k₀) (j n : ℕ) :
    PowerSeries.coeff n (toricZetaFredholmLog k₀ p w' f j)
      = toricZetaScale k₀ p j ^ (n + 1) *
          NuclearOperator.tracePower w' (dworkToricOperator k₀ p w' f)
            ⟨n + 1, Nat.succ_pos n⟩ := by
  rw [toricZetaFredholmLog, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
    NuclearOperator.coeff_tracePowerSeries]
  ring
private theorem toricZetaLog_sub (f : MonomialIndex d →₀ k₀) :
    toricZetaDenominatorLog k₀ p w' f - toricZetaNumeratorLog k₀ p w' f
      = toricZetaSignedLog k₀ p w' f := by
  have hsign : ∀ m : ℕ, Even m →
      PowerSeries.C ((-1 : DworkCyclotomicField k₀ p) ^ m) = 1 := by
    intro m hm
    rw [hm.neg_one_pow, map_one]
  have hsign' : ∀ m : ℕ, ¬ Even m →
      PowerSeries.C ((-1 : DworkCyclotomicField k₀ p) ^ m) = -1 := by
    intro m hm
    rw [(Nat.not_even_iff_odd.mp hm).neg_one_pow, map_neg, map_one]
  rw [toricZetaSignedLog,
    sum_signed_split (Finset.range (d + 1)) (fun i ↦ Even (d + i))
      (fun i ↦ PowerSeries.C ((-1 : DworkCyclotomicField k₀ p) ^ (d + i)))
      (fun i ↦ d.choose i) (toricZetaLinearLog k₀ p)
      (fun i _ hi ↦ hsign _ hi) (fun i _ hi ↦ hsign' _ hi),
    sum_signed_split (Finset.range (d + 2)) (fun j ↦ Even (d + 1 + j))
      (fun j ↦ PowerSeries.C ((-1 : DworkCyclotomicField k₀ p) ^ (d + 1 + j)))
      (fun j ↦ (d + 1).choose j) (toricZetaFredholmLog k₀ p w' f)
      (fun j _ hj ↦ hsign _ hj) (fun j _ hj ↦ hsign' _ hj),
    toricZetaDenominatorLog, toricZetaNumeratorLog]
  ring
private theorem toricPointCount_cast_eq (f : MonomialIndex d →₀ k₀) (n : ℕ) :
    ((toricHypersurfacePointCount k₀ p f n : ℕ) : DworkCyclotomicField k₀ p)
      = (∑ i ∈ Finset.range (d + 1),
          (-1 : DworkCyclotomicField k₀ p) ^ (d + i) * (d.choose i : DworkCyclotomicField k₀ p) *
            toricZetaScale k₀ p i ^ (n + 1))
        + (∑ j ∈ Finset.range (d + 2),
            (-1 : DworkCyclotomicField k₀ p) ^ (d + 1 + j) *
              ((d + 1).choose j : DworkCyclotomicField k₀ p) *
                toricZetaScale k₀ p j ^ (n + 1))
          * NuclearOperator.tracePower w' (dworkToricOperator k₀ p w' f)
              ⟨n + 1, Nat.succ_pos n⟩ := by
  have hq := natCard_ne_zero k₀ p
  have hQs : (Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1) ≠ 0 := pow_ne_zero _ hq
  have hone : 1 ≤ Nat.card k₀ ^ (n + 1) :=
    Nat.one_le_pow _ _ (Nat.card_pos (α := k₀))
  have hcastsub : ((Nat.card k₀ ^ (n + 1) - 1 : ℕ) : DworkCyclotomicField k₀ p)
      = (Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1) - 1 := by
    rw [Nat.cast_sub hone, Nat.cast_pow, Nat.cast_one]
  have hDW := dworkToricTraceFormula p k₀ f w' n
  rw [hcastsub, Nat.cast_pow] at hDW
  refine mul_left_cancel₀ hQs ?_
  have hgeom : ∀ (m : ℕ) (c : ℕ → ℕ),
      (Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1) *
          ∑ i ∈ Finset.range (m + 1),
            (-1 : DworkCyclotomicField k₀ p) ^ (m + i) * (c i : DworkCyclotomicField k₀ p) *
              toricZetaScale k₀ p i ^ (n + 1)
        = ∑ i ∈ Finset.range (m + 1),
            (-1 : DworkCyclotomicField k₀ p) ^ (m + i) * (c i : DworkCyclotomicField k₀ p) *
              ((Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1)) ^ i := by
    intro m c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    calc (Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1) *
          ((-1 : DworkCyclotomicField k₀ p) ^ (m + i) * (c i : DworkCyclotomicField k₀ p) *
            toricZetaScale k₀ p i ^ (n + 1))
        = ((-1 : DworkCyclotomicField k₀ p) ^ (m + i) * (c i : DworkCyclotomicField k₀ p)) *
            ((Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1) *
              toricZetaScale k₀ p i ^ (n + 1)) := by ring
      _ = _ := by rw [natCard_pow_mul_toricZetaScale_pow]
  rw [mul_add, hgeom d (fun i ↦ d.choose i), sum_signed_choose,
    show (Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1) *
        ((∑ j ∈ Finset.range (d + 2),
            (-1 : DworkCyclotomicField k₀ p) ^ (d + 1 + j) *
              ((d + 1).choose j : DworkCyclotomicField k₀ p) *
                toricZetaScale k₀ p j ^ (n + 1)) *
          NuclearOperator.tracePower w' (dworkToricOperator k₀ p w' f) ⟨n + 1, Nat.succ_pos n⟩)
      = ((Nat.card k₀ : DworkCyclotomicField k₀ p) ^ (n + 1) *
          ∑ j ∈ Finset.range (d + 2),
            (-1 : DworkCyclotomicField k₀ p) ^ (d + 1 + j) *
              ((d + 1).choose j : DworkCyclotomicField k₀ p) *
                toricZetaScale k₀ p j ^ (n + 1)) *
          NuclearOperator.tracePower w' (dworkToricOperator k₀ p w' f)
            ⟨n + 1, Nat.succ_pos n⟩ by ring,
    hgeom (d + 1) (fun j ↦ (d + 1).choose j), sum_signed_choose]
  simp only [dworkToricOperator]
  rw [hDW]
  ring
private theorem map_countingSeries_eq_signedLog (f : MonomialIndex d →₀ k₀) :
    PowerSeries.map (algebraMap ℚ (DworkCyclotomicField k₀ p))
        (countingSeries (toricHypersurfacePointCount k₀ p f))
      = toricZetaSignedLog k₀ p w' f := by
  ext n
  rw [PowerSeries.coeff_map, coeff_countingSeries, map_natCast, toricZetaSignedLog, map_add,
    map_sum, map_sum]
  have hlin : ∀ i ∈ Finset.range (d + 1),
      PowerSeries.coeff n (PowerSeries.C ((-1 : DworkCyclotomicField k₀ p) ^ (d + i)) *
          (d.choose i : (DworkCyclotomicField k₀ p)⟦X⟧) * toricZetaLinearLog k₀ p i)
        = (-1 : DworkCyclotomicField k₀ p) ^ (d + i) *
            (d.choose i : DworkCyclotomicField k₀ p) * toricZetaScale k₀ p i ^ (n + 1) := by
    intro i _
    rw [show (d.choose i : (DworkCyclotomicField k₀ p)⟦X⟧)
        = PowerSeries.C ((d.choose i : DworkCyclotomicField k₀ p)) by rw [map_natCast],
      ← map_mul, PowerSeries.coeff_C_mul, coeff_toricZetaLinearLog, mul_assoc]
  have hfred : ∀ j ∈ Finset.range (d + 2),
      PowerSeries.coeff n (PowerSeries.C ((-1 : DworkCyclotomicField k₀ p) ^ (d + 1 + j)) *
          ((d + 1).choose j : (DworkCyclotomicField k₀ p)⟦X⟧) * toricZetaFredholmLog k₀ p w' f j)
        = (-1 : DworkCyclotomicField k₀ p) ^ (d + 1 + j) *
            ((d + 1).choose j : DworkCyclotomicField k₀ p) *
              toricZetaScale k₀ p j ^ (n + 1) *
              NuclearOperator.tracePower w' (dworkToricOperator k₀ p w' f)
                ⟨n + 1, Nat.succ_pos n⟩ := by
    intro j _
    rw [show ((d + 1).choose j : (DworkCyclotomicField k₀ p)⟦X⟧)
        = PowerSeries.C (((d + 1).choose j : DworkCyclotomicField k₀ p)) by rw [map_natCast],
      ← map_mul, PowerSeries.coeff_C_mul, coeff_toricZetaFredholmLog]
    ring
  rw [Finset.sum_congr rfl hlin, Finset.sum_congr rfl hfred, ← Finset.sum_mul]
  exact toricPointCount_cast_eq k₀ p w' f n
private theorem neg_derivative_toricZetaLinearFactor (i : ℕ) :
    -(PowerSeries.derivative (DworkCyclotomicField k₀ p) (toricZetaLinearFactor k₀ p i))
      = toricZetaLinearLog k₀ p i * toricZetaLinearFactor k₀ p i :=
  neg_derivative_linearFactor _
private theorem neg_derivative_toricZetaFredholmFactor (f : MonomialIndex d →₀ k₀) (j : ℕ) :
    -(PowerSeries.derivative (DworkCyclotomicField k₀ p) (toricZetaFredholmFactor k₀ p w' f j))
      = toricZetaFredholmLog k₀ p w' f j * toricZetaFredholmFactor k₀ p w' f j :=
  neg_derivative_rescale _ (neg_derivative_fredholmDeterminant w' (dworkToricOperator k₀ p w' f))
private theorem neg_derivative_toricZetaFredholmDenominator (f : MonomialIndex d →₀ k₀) :
    -(PowerSeries.derivative (DworkCyclotomicField k₀ p)
        (toricZetaFredholmDenominator k₀ p w' f))
      = toricZetaDenominatorLog k₀ p w' f * toricZetaFredholmDenominator k₀ p w' f := by
  rw [toricZetaFredholmDenominator, toricZetaDenominatorLog]
  exact neg_derivative_mul
    (neg_derivative_prod _ _ _ fun i _ ↦
      neg_derivative_pow (neg_derivative_toricZetaLinearFactor k₀ p i) _)
    (neg_derivative_prod _ _ _ fun j _ ↦
      neg_derivative_pow (neg_derivative_toricZetaFredholmFactor k₀ p w' f j) _)
private theorem neg_derivative_toricZetaFredholmNumerator (f : MonomialIndex d →₀ k₀) :
    -(PowerSeries.derivative (DworkCyclotomicField k₀ p)
        (toricZetaFredholmNumerator k₀ p w' f))
      = toricZetaNumeratorLog k₀ p w' f * toricZetaFredholmNumerator k₀ p w' f := by
  rw [toricZetaFredholmNumerator, toricZetaNumeratorLog]
  exact neg_derivative_mul
    (neg_derivative_prod _ _ _ fun i _ ↦
      neg_derivative_pow (neg_derivative_toricZetaLinearFactor k₀ p i) _)
    (neg_derivative_prod _ _ _ fun j _ ↦
      neg_derivative_pow (neg_derivative_toricZetaFredholmFactor k₀ p w' f j) _)
theorem constantCoeff_toricZetaLinearFactor (i : ℕ) :
    PowerSeries.constantCoeff (toricZetaLinearFactor k₀ p i) = 1 := by
  rw [toricZetaLinearFactor, map_sub, map_one, map_mul, PowerSeries.constantCoeff_X, mul_zero,
    sub_zero]
theorem constantCoeff_toricZetaFredholmFactor (f : MonomialIndex d →₀ k₀) (j : ℕ) :
    PowerSeries.constantCoeff (toricZetaFredholmFactor k₀ p w' f j) = 1 := by
  rw [toricZetaFredholmFactor, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    NuclearOperator.fredholmDeterminant_constantCoeff]
theorem constantCoeff_toricZetaFredholmDenominator (f : MonomialIndex d →₀ k₀) :
    PowerSeries.constantCoeff (toricZetaFredholmDenominator k₀ p w' f) = 1 := by
  rw [toricZetaFredholmDenominator, map_mul, map_prod, map_prod]
  simp only [map_pow, constantCoeff_toricZetaLinearFactor, constantCoeff_toricZetaFredholmFactor,
    one_pow, Finset.prod_const_one, mul_one]
theorem constantCoeff_toricZetaFredholmNumerator (f : MonomialIndex d →₀ k₀) :
    PowerSeries.constantCoeff (toricZetaFredholmNumerator k₀ p w' f) = 1 := by
  rw [toricZetaFredholmNumerator, map_mul, map_prod, map_prod]
  simp only [map_pow, constantCoeff_toricZetaLinearFactor, constantCoeff_toricZetaFredholmFactor,
    one_pow, Finset.prod_const_one, mul_one]
theorem isPadicEntire_toricZetaFredholmDenominator (f : MonomialIndex d →₀ k₀) :
    IsPadicEntire (toricZetaFredholmDenominator k₀ p w' f) := by
  rw [toricZetaFredholmDenominator]
  refine IsPadicEntire.mul (isPadicEntire_prod _ _ fun i _ ↦ ?_)
    (isPadicEntire_prod _ _ fun j _ ↦ ?_)
  · exact IsPadicEntire.pow (isPadicEntire_one_sub_C_mul_X _) _
  · exact IsPadicEntire.pow
      (IsPadicEntire.rescale
        (dworkFredholmDeterminant_isPadicEntire k₀ p w' (dworkAuxiliaryPolynomial (k := k₀) f)) _) _
theorem isPadicEntire_toricZetaFredholmNumerator (f : MonomialIndex d →₀ k₀) :
    IsPadicEntire (toricZetaFredholmNumerator k₀ p w' f) := by
  rw [toricZetaFredholmNumerator]
  refine IsPadicEntire.mul (isPadicEntire_prod _ _ fun i _ ↦ ?_)
    (isPadicEntire_prod _ _ fun j _ ↦ ?_)
  · exact IsPadicEntire.pow (isPadicEntire_one_sub_C_mul_X _) _
  · exact IsPadicEntire.pow
      (IsPadicEntire.rescale
        (dworkFredholmDeterminant_isPadicEntire k₀ p w' (dworkAuxiliaryPolynomial (k := k₀) f)) _) _
theorem toricHypersurfaceZeta_fredholmIdentity (f : MonomialIndex d →₀ k₀) :
    toricZetaFredholmDenominator k₀ p w' f * toricHypersurfaceZetaSeriesPadic k₀ p f
      = toricZetaFredholmNumerator k₀ p w' f := by
  have hZ := toricHypersurfaceZetaSeries_isZetaSeries k₀ p f
  have hZ0 : PowerSeries.constantCoeff (toricHypersurfaceZetaSeriesPadic k₀ p f) = 1 := by
    rw [toricHypersurfaceZetaSeriesPadic, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hZ.1, map_one]
  have hZ' : PowerSeries.derivative (DworkCyclotomicField k₀ p)
        (toricHypersurfaceZetaSeriesPadic k₀ p f)
      = toricZetaSignedLog k₀ p w' f * toricHypersurfaceZetaSeriesPadic k₀ p f := by
    rw [toricHypersurfaceZetaSeriesPadic, ← map_derivative, hZ.2, map_mul,
      map_countingSeries_eq_signedLog k₀ p w' f]
  have hkey : toricZetaSignedLog k₀ p w' f
      = toricZetaDenominatorLog k₀ p w' f - toricZetaNumeratorLog k₀ p w' f :=
    (toricZetaLog_sub k₀ p w' f).symm
  have hD : PowerSeries.derivative (DworkCyclotomicField k₀ p)
        (toricZetaFredholmDenominator k₀ p w' f)
      = -(toricZetaDenominatorLog k₀ p w' f * toricZetaFredholmDenominator k₀ p w' f) := by
    rw [← neg_derivative_toricZetaFredholmDenominator k₀ p w' f, neg_neg]
  have hLHS : PowerSeries.derivative (DworkCyclotomicField k₀ p)
        (toricZetaFredholmDenominator k₀ p w' f * toricHypersurfaceZetaSeriesPadic k₀ p f)
      = -(toricZetaNumeratorLog k₀ p w' f) *
          (toricZetaFredholmDenominator k₀ p w' f * toricHypersurfaceZetaSeriesPadic k₀ p f) := by
    rw [(PowerSeries.derivative (DworkCyclotomicField k₀ p)).leibniz _ _, smul_eq_mul, smul_eq_mul,
      hZ', hD, hkey]
    ring
  have hRHS : PowerSeries.derivative (DworkCyclotomicField k₀ p)
        (toricZetaFredholmNumerator k₀ p w' f)
      = -(toricZetaNumeratorLog k₀ p w' f) * toricZetaFredholmNumerator k₀ p w' f := by
    rw [neg_mul, ← neg_derivative_toricZetaFredholmNumerator k₀ p w' f, neg_neg]
  refine powerSeries_eq_of_derivative_eq ?_ hLHS hRHS
  rw [map_mul, hZ0, mul_one, constantCoeff_toricZetaFredholmDenominator,
    constantCoeff_toricZetaFredholmNumerator]
theorem toricHypersurfaceZeta_isPadicMeromorphic (weight : PositiveMonomialWeight (d + 1))
    (f : MonomialIndex d →₀ k₀) :
    IsPadicMeromorphic (toricHypersurfaceZetaSeriesPadic k₀ p f) :=
  ⟨toricZetaFredholmNumerator k₀ p weight f, toricZetaFredholmDenominator k₀ p weight f,
    isPadicEntire_toricZetaFredholmNumerator k₀ p weight f,
    isPadicEntire_toricZetaFredholmDenominator k₀ p weight f,
    constantCoeff_toricZetaFredholmDenominator k₀ p weight f,
    toricHypersurfaceZeta_fredholmIdentity k₀ p weight f⟩
end ZetaFredholm
end FiniteFields.Dwork
end
end
open PowerSeries
open FiniteFields.Dwork
variable (k₀ : Type) (p : ℕ) [Fact p.Prime] [Field k₀] [CharP k₀ p] [Finite k₀]
variable {d : ℕ}
theorem solution (f : MonomialIndex d →₀ k₀)
    (w' : PositiveMonomialWeight (d + 1)) :
    IsPadicMeromorphic
      (PowerSeries.map (algebraMap ℚ (DworkCyclotomicField k₀ p))
        (toricHypersurfaceZetaSeries k₀ p f)) :=
  toricHypersurfaceZeta_isPadicMeromorphic k₀ p w' f
