-- Prove2me | solution 1 for GRH.centered_moebius_bound_iff_square_mertens_residual
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:09:02.474689+00:00
-- url     : https://prove2.me/submissions/3e284fcd-e204-4ab6-8174-1de68321ba16

import Theorems.Thm_GRH_centered_moebius_mertens_remainder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Finset
open scoped BigOperators

private theorem cutoff_bound (N : ℕ) (σ : ℝ) (hhalf : (1 / 2 : ℝ) ≤ σ) :
    (N.sqrt : ℝ) ≤ ((N : ℝ) + 1) ^ σ := by
  calc
    _ ≤ Real.sqrt ((N : ℝ) + 1) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      have h : (N.sqrt : ℝ) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
      linarith
    _ ≤ _ := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by simp) hhalf

private noncomputable def residueSum {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n+1), if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0

private theorem prefix_increment {q : ℕ} (a : ZMod q) (s j : ℕ) :
    |residueSum a (s+j) - residueSum a s| ≤ (j:ℝ) := by
  unfold residueSum
  rw [show s+j+1=s+1+j by omega, sum_range_add, add_sub_cancel_left]
  calc
    _ ≤ ∑ k ∈ range j, |if ((s+1+k:ℕ):ZMod q) = a then
        (ArithmeticFunction.moebius (s+1+k) : ℝ) else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range j, (1:ℝ) := by
      apply sum_le_sum
      intro k _
      split_ifs
      · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := s+1+k))
      · norm_num
    _ = _ := by simp

private theorem prefix_size {q : ℕ} (a : ZMod q) (s : ℕ) : |residueSum a s| ≤ (s:ℝ) := by
  have hz : residueSum a 0 = 0 := by simp [residueSum]
  simpa only [Nat.zero_add, hz, sub_zero] using prefix_increment a 0 s

private theorem interpolate_affine (s j m v c : ℝ) (hs : 0 < s) (hj : 0 ≤ j)
    (hjs : j ≤ 2*s) (hm : |m| ≤ s) (hv : |v-m| ≤ j) :
    |v+(s+j)*c| ≤ 3*|m+s*c| + 2*j := by
  let r := j/s
  have hr : 0 ≤ r := div_nonneg hj hs.le
  have hr2 : r ≤ 2 := (div_le_iff₀ hs).2 hjs
  have hrs : r*s = j := by dsimp [r]; field_simp
  have hcoef : |1+r| ≤ 3 := by rw [abs_of_nonneg (show 0 ≤ 1+r by linarith)]; linarith
  have hlast : |r*m| ≤ j := by
    rw [abs_mul, abs_of_nonneg hr, ← hrs]
    exact mul_le_mul_of_nonneg_left hm hr
  have hi : v+(s+j)*c = (v-m)+(1+r)*(m+s*c)-r*m := by
    conv_lhs => rw [← hrs]
    ring
  rw [hi]
  calc
    _ ≤ |(v-m)+(1+r)*(m+s*c)| + |r*m| := abs_sub _ _
    _ ≤ (|v-m|+|(1+r)*(m+s*c)|) + |r*m| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (j+3*|m+s*c|) + j := by
      rw [abs_mul (1+r)]
      exact add_le_add (add_le_add hv (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))) hlast
    _ = _ := by ring

set_option maxHeartbeats 900000 in
theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (σ : ℝ) (hhalf : (1/2 : ℝ) ≤ σ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ) ↔
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) +
        (u : ℝ) ^ 2 * ((1 / (q : ℝ)) * (GRH.reducedMoebiusHarmonic q u) ^ 2)| ≤
      D * ((u : ℝ) ^ 2 + 1) ^ σ := by
  let B := GRH.centeredMoebiusBilinear q a
  let c := fun u : ℕ => (1/(q:ℝ)) * (GRH.reducedMoebiusHarmonic q u)^2
  have err (N : ℕ) :
      |B N + (residueSum a N + (N:ℝ)*c N.sqrt)| ≤ 2*(N.sqrt:ℝ) := by
    have h := (GRH.centered_moebius_mertens_remainder q a N).2
    dsimp only at h
    simpa only [B,c,residueSum,mul_comm,mul_left_comm,mul_assoc] using h
  have square_err (u : ℕ) :
      |B (u^2) + (residueSum a (u^2)+(u:ℝ)^2*c u)| ≤ 2*(u:ℝ) := by
    have h := err (u^2)
    rw [Nat.sqrt_eq' u, Nat.cast_pow] at h
    exact h
  constructor
  · rintro ⟨C,hC,H⟩
    refine ⟨2+C, by positivity, fun u => ?_⟩
    let R := residueSum a (u^2)+(u:ℝ)^2*c u
    let P := ((u:ℝ)^2+1)^σ
    have hu : (u:ℝ) ≤ P := by
      have h := cutoff_bound (u^2) σ hhalf
      rw [Nat.sqrt_eq' u, Nat.cast_pow] at h
      exact h
    have hb : |B (u^2)| ≤ C*P := by
      have h := H (u^2)
      rw [Nat.cast_pow] at h
      exact h
    change |R| ≤ (2+C)*P
    calc
      |R| = |(B (u^2)+R)-B (u^2)| := by congr 1; ring
      _ ≤ |B (u^2)+R|+|B (u^2)| := abs_sub _ _
      _ ≤ 2*(u:ℝ)+C*P := add_le_add (square_err u) hb
      _ ≤ (2+C)*P := by linarith
  · rintro ⟨D,hD,H⟩
    refine ⟨3*D+6, by positivity, fun N => ?_⟩
    by_cases hN : N=0
    · subst N
      simp [GRH.centeredMoebiusBilinear]
      positivity
    let u := N.sqrt
    let j := N - u^2
    let P := ((N:ℝ)+1)^σ
    have hs : u^2 ≤ N := Nat.sqrt_le' N
    have he : u^2+j=N := Nat.add_sub_of_le hs
    have huadd : N ≤ u^2+2*u := by
      simpa [u, pow_two,two_mul,add_assoc] using Nat.sqrt_le_add N
    have hj : j ≤ 2*u := by omega
    have hu : 0 < u := by
      by_contra! hu
      have hn := Nat.lt_succ_sqrt' N
      change N < (u+1)^2 at hn
      have hz : u=0 := by omega
      rw [hz] at hn
      norm_num at hn
      omega
    have hu1 : (1:ℝ) ≤ u := by exact_mod_cast hu
    have hju : (j:ℝ) ≤ 2*(u:ℝ) := by exact_mod_cast hj
    have hjs : (j:ℝ) ≤ 2*(u:ℝ)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (Nat.cast_nonneg (α:=ℝ) u)]
    have hm : |residueSum a (u^2)| ≤ (u:ℝ)^2 := by
      have h := prefix_size a (u^2)
      rw [Nat.cast_pow] at h
      exact h
    have hv : |residueSum a N - residueSum a (u^2)| ≤ (j:ℝ) := by
      have h := prefix_increment a (u^2) j
      rw [he] at h
      exact h
    have hr := interpolate_affine ((u:ℝ)^2) j (residueSum a (u^2)) (residueSum a N)
      (c u) (by positivity) (Nat.cast_nonneg j) hjs hm hv
    have heR : (u:ℝ)^2 + j = (N:ℝ) := by exact_mod_cast he
    rw [heR] at hr
    have hsqR : (u:ℝ)^2 ≤ N := by exact_mod_cast hs
    have hscale : ((u:ℝ)^2+1)^σ ≤ P :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have hbase : |residueSum a (u^2)+(u:ℝ)^2*c u| ≤ D*P :=
      (H u).trans (mul_le_mul_of_nonneg_left hscale hD)
    have huP : (u:ℝ) ≤ P := cutoff_bound N σ hhalf
    let R := residueSum a N+(N:ℝ)*c u
    have hR : |R| ≤ (3*D+4)*P := by dsimp only [R]; linarith only [hr,hbase,hju,huP]
    have hB := err N
    change |B N+R| ≤ 2*(u:ℝ) at hB
    change |B N| ≤ (3*D+6)*P
    calc
      |B N| = |(B N+R)-R| := by rw [add_sub_cancel_right]
      _ ≤ |B N+R|+|R| := abs_sub _ _
      _ ≤ 2*(u:ℝ)+(3*D+4)*P := add_le_add hB hR
      _ ≤ (3*D+6)*P := by linarith
