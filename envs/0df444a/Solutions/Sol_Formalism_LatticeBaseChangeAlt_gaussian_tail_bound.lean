-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.gaussian_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:35:24.818287+00:00
-- url     : https://prove2.me/submissions/82498750-dc4f-47d1-9a50-34791d66a8c8

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_TransvectionIsometry
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_IntegralMulExpNegSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Finset MeasureTheory Filter Topology Set
private theorem pow_le_pow_left_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    x ^ n ≤ y ^ n := by
  exact pow_le_pow_left₀ hx hxy n
private theorem exp_neg_sq_div_sixteen_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.exp (-t ^ 2 / 16) ≤ Real.exp (-s ^ 2 / 16) :=
  Real.exp_le_exp.mpr (by nlinarith)
private theorem gaussian_tail_pow_mul_exp_le {g : ℕ} {R0 s t : ℝ} (hR0 : 0 < R0)
    (hg : 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2) (hs : R0 ≤ s) (hst : s ≤ t) :
    (2 * (3 * t / R0) ^ (2 * g) - (3 * s / R0) ^ (2 * g)) * Real.exp (-t ^ 2 / 16) ≤
      (3 * s / R0) ^ (2 * g) * Real.exp (-s ^ 2 / 16) := by
  have hs0 : 0 < s := lt_of_lt_of_le hR0 hs
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (t ^ 2 - s ^ 2) / 16 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; nlinarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (u / 2) := ⟨_, rfl⟩
  have hE2 : E ^ 2 = Real.exp u := by
    rw [show E ^ 2 = E * E by ring, hE, ← Real.exp_add]
    congr 1
    ring
  have hfs : Real.exp (-s ^ 2 / 16) = Real.exp (-t ^ 2 / 16) * E ^ 2 := by
    rw [hE2, ← Real.exp_add]
    congr 1
    rw [hu]
    ring
  have hK : 0 < 2 * (g : ℝ) + 1 := by positivity
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u / (2 * (g : ℝ) + 1) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; exact div_nonneg hu0 hK.le
  have hvK : v * (2 * (g : ℝ) + 1) = u := by rw [hv]; field_simp
  have hR2 : R0 ^ 2 ≤ s ^ 2 := by nlinarith
  have ht2 : t ^ 2 ≤ s ^ 2 * (1 + v) := by
    have h16 : 16 * (2 * (g : ℝ) + 1) ≤ s ^ 2 := le_trans hg hR2
    have htu : t ^ 2 = s ^ 2 + 16 * u := by rw [hu]; ring
    nlinarith [mul_le_mul_of_nonneg_left h16 hv0]
  have hP : ∀ x : ℝ, (3 * x / R0) ^ (2 * g) = ((3 / R0) ^ 2 * x ^ 2) ^ g := by
    intro x
    rw [pow_mul]
    congr 1
    ring
  have hBt : (3 * t / R0) ^ (2 * g) ≤ (3 * s / R0) ^ (2 * g) * E := by
    rw [hP t, hP s]
    have h1 : (3 / R0) ^ 2 * t ^ 2 ≤ ((3 / R0) ^ 2 * s ^ 2) * (1 + v) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ht2 (sq_nonneg _)
    have h2 : ((3 / R0) ^ 2 * t ^ 2) ^ g ≤ (((3 / R0) ^ 2 * s ^ 2) * (1 + v)) ^ g :=
      pow_le_pow_left_of_nonneg (by positivity) h1 g
    have h3 : (1 + v) ^ g ≤ E := by
      have hexp : (1 + v) ^ g ≤ (Real.exp v) ^ g :=
        pow_le_pow_left_of_nonneg (by linarith) (by linarith [Real.add_one_le_exp v]) g
      have hnat : (Real.exp v) ^ g = Real.exp (g * v) := by
        exact (Real.exp_nat_mul v g).symm
      have hle : Real.exp (g * v) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.mpr
        nlinarith
      linarith
    calc ((3 / R0) ^ 2 * t ^ 2) ^ g ≤ (((3 / R0) ^ 2 * s ^ 2) * (1 + v)) ^ g := h2
      _ = ((3 / R0) ^ 2 * s ^ 2) ^ g * (1 + v) ^ g := mul_pow _ _ _
      _ ≤ ((3 / R0) ^ 2 * s ^ 2) ^ g * E := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hft : 0 ≤ Real.exp (-t ^ 2 / 16) := (Real.exp_pos _).le
  have hBs : 0 ≤ (3 * s / R0) ^ (2 * g) := by rw [hP s]; positivity
  rw [hfs]
  nlinarith [mul_le_mul_of_nonneg_right hBt hft, mul_nonneg (mul_nonneg hBs hft) (sq_nonneg (E - 1))]
end Formalism.LatticeBaseChangeAlt
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset MeasureTheory Filter Topology Set
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : GaussianTailBound := by
  intro ι h g R0 hR0 hg hlow hcount
  classical
  have claim : ∀ S : Finset ι, ∀ M : ℝ, R0 ≤ M → (∀ i ∈ S, h i ≤ M) →
      ∑ i ∈ S, Real.exp (-(h i) ^ 2 / 16) ≤
        2 * (3 * R0 / R0) ^ (2 * g) * Real.exp (-R0 ^ 2 / 16)
          - 2 * (3 * M / R0) ^ (2 * g) * Real.exp (-M ^ 2 / 16)
          + (S.card : ℝ) * Real.exp (-M ^ 2 / 16) := by
    intro S
    refine Finset.induction_on_max_value h S ?_ ?_
    · intro M hM _
      have k := gaussian_tail_pow_mul_exp_le hR0 hg le_rfl hM
      have hfa : Real.exp (-M ^ 2 / 16) ≤ Real.exp (-R0 ^ 2 / 16) :=
        exp_neg_sq_div_sixteen_antitone hR0.le hM
      have hB0 : 0 ≤ (3 * R0 / R0) ^ (2 * g) :=
        pow_nonneg (div_nonneg (by linarith) hR0.le) _
      simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left hfa hB0]
    · intro a S haS hmax ih M hM hSM
      have hxR : R0 ≤ h a := hlow a
      have hxM : h a ≤ M := hSM a (Finset.mem_insert_self a S)
      have ih' := ih (h a) hxR hmax
      have hins : ∀ i ∈ insert a S, h i ≤ h a := by
        intro i hi
        rcases Finset.mem_insert.mp hi with hia | hi'
        · rw [hia]
        · exact hmax i hi'
      have hcard := hcount (h a) hxR (insert a S) hins
      have hc : (insert a S).card = S.card + 1 := by
        first
          | exact Finset.card_insert_of_notMem haS
          | exact Finset.card_insert_of_not_mem haS
          | simp [haS]
      rw [hc] at hcard
      rw [Finset.sum_insert haS, hc]
      push_cast at hcard ⊢
      have k := gaussian_tail_pow_mul_exp_le hR0 hg hxR hxM
      have hfa : Real.exp (-M ^ 2 / 16) ≤ Real.exp (-(h a) ^ 2 / 16) :=
        exp_neg_sq_div_sixteen_antitone (hR0.le.trans hxR) hxM
      nlinarith [mul_le_mul_of_nonneg_right hcard (sub_nonneg.mpr hfa)]
  have hG0 : (3 * R0 / R0) ^ (2 * g) = (9 : ℝ) ^ g := by
    rw [show 3 * R0 / R0 = (3 : ℝ) by field_simp, pow_mul]
    norm_num
  have hpos : ∀ i, 0 ≤ h i := fun i => hR0.le.trans (hlow i)
  have hsum : ∀ S : Finset ι, ∑ i ∈ S, Real.exp (-(h i) ^ 2 / 16) ≤
      2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16) := by
    intro S
    have hM0 : R0 ≤ R0 + ∑ j ∈ S, h j :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hpos j)
    have hMi : ∀ i ∈ S, h i ≤ R0 + ∑ j ∈ S, h j := fun i hi =>
      (Finset.single_le_sum (fun j _ => hpos j) hi).trans (le_add_of_nonneg_left hR0.le)
    have c1 := claim S _ hM0 hMi
    have c2 := hcount _ hM0 S hMi
    have hBM : 0 ≤ (3 * (R0 + ∑ j ∈ S, h j) / R0) ^ (2 * g) :=
      pow_nonneg (div_nonneg (by linarith) hR0.le) _
    have hfM := (Real.exp_pos (-(R0 + ∑ j ∈ S, h j) ^ 2 / 16)).le
    rw [hG0] at c1
    nlinarith [mul_le_mul_of_nonneg_right c2 hfM, mul_nonneg hBM hfM]
  have hnn : ∀ i, 0 ≤ Real.exp (-(h i) ^ 2 / 16) := fun i => (Real.exp_pos _).le
  have hsm : Summable (fun i => Real.exp (-(h i) ^ 2 / 16)) := summable_of_sum_le hnn hsum
  refine ⟨hsm, ?_⟩
  exact Real.tsum_le_of_sum_le hnn hsum
end Formalism.LatticeBaseChangeAlt
