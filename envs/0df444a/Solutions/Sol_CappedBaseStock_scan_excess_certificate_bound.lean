-- Prove2me | solution 1 for CappedBaseStock.scan_excess_certificate_bound
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:46:00.836717+00:00
-- url     : https://prove2.me/submissions/1d774bc9-d921-413c-8225-98228064aeec

import Definitions.Def_CappedBaseStock_BaseStockAnalysis

-- Proven component: Solutions/Sol_CappedBaseStock_scan_excess_certificate_bound.lean
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace CappedBaseStock

private def reverseIndex (N i : ℕ) : ℕ := if i < N then N - 1 - i else i

private lemma reverseIndex_injective (N : ℕ) : Function.Injective (reverseIndex N) := by
  intro i j h
  unfold reverseIndex at h
  split_ifs at h <;> omega

private lemma reverse_path_preserving (P : DemandLaw) (N : ℕ) :
    MeasurePreserving (fun d : DemandPath => fun i => d (reverseIndex N i))
      (demandPathLaw P) (demandPathLaw P) := by
  constructor
  · fun_prop
  · exact Measure.map_infinitePi_infinitePi_of_inj (reverseIndex_injective N)

private lemma measurable_certificate (r z : ℝ) (m : ℕ) :
    Measurable (fun d => certificateExcess d r z m) := by
  unfold certificateExcess
  apply Measurable.ennreal_ofReal
  apply Measurable.sub_const
  apply Measurable.add
  · unfold finiteInventory
    convert (Finset.measurable_sup' (s := Finset.range (m + 1)) (by simp)
        (f := fun (k : ℕ) (d : DemandPath) => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
        (by intro k hk; fun_prop)) using 1
    funext d
    exact (Finset.sup'_apply (by simp : (Finset.range (m + 1)).Nonempty)
      (fun (k : ℕ) (d : DemandPath) => ∑ i ∈ Finset.range k, (r - (d i : ℝ))) d).symm
  · fun_prop

private lemma suffix_le_certificate_real (d : DemandPath) (r : ℝ) (m k : ℕ)
    (hk : k ≤ m) :
    (∑ i ∈ Finset.range (m - k), ((d (k + i) : ℝ) - r)) ≤
      finiteInventory d r m + ∑ i ∈ Finset.range m, ((d i : ℝ) - r) := by
  have h := Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
    (show k ∈ Finset.range (m + 1) by simp; omega)
  change (∑ i ∈ Finset.range k, (r - (d i : ℝ))) ≤ finiteInventory d r m at h
  have heq := Finset.sum_range_add (fun i => (d i : ℝ) - r) k (m - k)
  rw [Nat.add_sub_of_le hk] at heq
  have hneg : (∑ i ∈ Finset.range k, (r - (d i : ℝ))) =
      -(∑ i ∈ Finset.range k, ((d i : ℝ) - r)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hneg] at h
  linarith

private lemma reverse_suffix (d : DemandPath) (r : ℝ) (L j : ℕ) (hj : j ≤ L) :
    (∑ i ∈ Finset.range (L + 1 - (L - j)),
      ((d (reverseIndex (2 * L + 1) (L - j + i)) : ℝ) - r)) =
      ∑ i ∈ Finset.range (j + 1), ((d (L + i) : ℝ) - r) := by
  have hlen : L + 1 - (L - j) = j + 1 := by omega
  rw [hlen]
  calc
    _ = ∑ i ∈ Finset.range (j + 1),
        ((d (L + ((j + 1) - 1 - i)) : ℝ) - r) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < j + 1 := Finset.mem_range.mp hi
      congr 3
      unfold reverseIndex
      split_ifs <;> omega
    _ = _ := Finset.sum_range_reflect (fun i => (d (L + i) : ℝ) - r) (j + 1)

private lemma window_deviation_split (d : DemandPath) (r : ℝ) (L j : ℕ) (hj : j ≤ L) :
    (∑ i ∈ Finset.range (L + 1), ((d (j + i) : ℝ) - r)) =
      (∑ i ∈ Finset.range (L - j), ((d (j + i) : ℝ) - r)) +
      ∑ i ∈ Finset.range (j + 1), ((d (L + i) : ℝ) - r) := by
  have hlen : L + 1 = (L - j) + (j + 1) := by omega
  conv_lhs => rw [hlen, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 3
  omega

private lemma scan_pointwise (d : DemandPath) (r z : ℝ) (L : ℕ) :
    scanExcess d L (((L : ℝ) + 1) * r + 2 * z) ≤
      certificateExcess d r z L +
      certificateExcess (fun i => d (reverseIndex (2 * L + 1) i)) r z (L + 1) := by
  let e : DemandPath := fun i => d (reverseIndex (2 * L + 1) i)
  let A := finiteInventory d r L + ∑ i ∈ Finset.range L, ((d i : ℝ) - r)
  let B := finiteInventory e r (L + 1) + ∑ i ∈ Finset.range (L + 1), ((e i : ℝ) - r)
  have hscan : scanDemand d L - ((L : ℝ) + 1) * r ≤ A + B := by
    apply sub_le_iff_le_add.mpr
    unfold scanDemand
    apply Finset.sup'_le
    intro j hj
    have hj' : j ≤ L := by simpa using hj
    have hA := suffix_le_certificate_real d r L j hj'
    have hB := suffix_le_certificate_real e r (L + 1) (L - j) (by omega)
    change (∑ i ∈ Finset.range (L + 1 - (L - j)),
      ((d (reverseIndex (2 * L + 1) (L - j + i)) : ℝ) - r)) ≤ B at hB
    rw [reverse_suffix d r L j hj'] at hB
    have hsum := window_deviation_split d r L j hj'
    have hconst : (∑ i ∈ Finset.range (L + 1), ((d (j + i) : ℝ) - r)) =
        (∑ i ∈ Finset.range (L + 1), (d (j + i) : ℝ)) - ((L : ℝ) + 1) * r := by
      simp [Finset.sum_sub_distrib]
    change _ ≤ A at hA
    rw [hconst] at hsum
    linarith
  change ENNReal.ofReal _ ≤ ENNReal.ofReal (A - z) + ENNReal.ofReal (B - z)
  calc
    _ ≤ ENNReal.ofReal ((A - z) + (B - z)) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ _ := ENNReal.ofReal_add_le

end CappedBaseStock

open CappedBaseStock

theorem solution (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    (∫⁻ d, scanExcess d c.L (((c.L : ℝ) + 1) * r + 2 * z) ∂demandPathLaw P) ≤
      ENNReal.ofReal ((2 * (c.L : ℝ) + 1) * (mean P - r)) := by
  rcases feasible with ⟨hr, hrmean, hz, hL, hL1⟩
  calc
    _ ≤ ∫⁻ d, certificateExcess d r z c.L +
        certificateExcess (fun i => d (reverseIndex (2 * c.L + 1) i)) r z (c.L + 1)
        ∂demandPathLaw P := lintegral_mono (fun d => scan_pointwise d r z c.L)
    _ = (∫⁻ d, certificateExcess d r z c.L ∂demandPathLaw P) +
        (∫⁻ d, certificateExcess d r z (c.L + 1) ∂demandPathLaw P) := by
      rw [lintegral_add_left (measurable_certificate r z c.L)]
      rw [(reverse_path_preserving P (2 * c.L + 1)).lintegral_comp
        (measurable_certificate r z (c.L + 1))]
    _ ≤ ENNReal.ofReal ((c.L : ℝ) * (mean P - r)) +
        ENNReal.ofReal (((c.L : ℝ) + 1) * (mean P - r)) := add_le_add hL hL1
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hrmean))
        (mul_nonneg (by positivity) (sub_nonneg.mpr hrmean))]
      congr 1
      ring
