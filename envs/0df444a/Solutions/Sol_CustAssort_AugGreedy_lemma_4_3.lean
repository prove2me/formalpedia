-- Prove2me | solution 1 for CustAssort.AugGreedy.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T19:38:22.933397+00:00
-- url     : https://prove2.me/submissions/615085d9-4882-4bfa-8625-fa022a665e80

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

set_option autoImplicit false

namespace ThresholdBound
open ChoiceCDLP.MNL

theorem sum_threshold {ι : Type*} [DecidableEq ι] (U A : Finset ι)
    (w r : ι → ℝ) (z : ℝ) (hA : A ⊆ U) (hw : ∀ i ∈ U, 0 ≤ w i) :
    (∑ i ∈ A, (r i - z) * w i) ≤
      ∑ i ∈ U.filter (fun i => z ≤ r i), (r i - z) * w i := by
  classical
  have hterm : ∀ i ∈ U, (r i - z) * w i ≤
      if z ≤ r i then (r i - z) * w i else 0 := by
    intro i hi
    split_ifs with h
    · rfl
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge h)) (hw i hi)
  have hnonneg : ∀ i ∈ U, 0 ≤
      if z ≤ r i then (r i - z) * w i else 0 := by
    intro i hi
    split_ifs with h
    · exact mul_nonneg (sub_nonneg.mpr h) (hw i hi)
    · rfl
  rw [Finset.sum_filter]
  exact (Finset.sum_le_sum (fun i hi => hterm i (hA hi))).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hA (fun i hi _ => hnonneg i hi))

theorem threshold_optimal {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (w r : ι → ℝ) (hw : ∀ i ∈ U, 0 ≤ w i) :
    let z := U.powerset.sup' (Finset.powerset_nonempty U) (mnlObjective w r 1)
    mnlObjective w r 1 (U.filter (fun i => z ≤ r i)) = z := by
  classical
  intro z
  have hden (T : Finset ι) (hT : T ⊆ U) : 0 < (∑ i ∈ T, w i) + 1 := by
    have := Finset.sum_nonneg (fun i hi => hw i (hT hi))
    linarith
  have hupper (T : Finset ι) (hT : T ⊆ U) : mnlObjective w r 1 T ≤ z :=
    Finset.le_sup' _ (Finset.mem_powerset.mpr hT)
  obtain ⟨A, hAU, hAz⟩ := Finset.exists_mem_eq_sup'
    (Finset.powerset_nonempty U) (mnlObjective w r 1)
  have hA := Finset.mem_powerset.mp hAU
  change z = mnlObjective w r 1 A at hAz
  have heq : (∑ i ∈ A, r i * w i) = z * ((∑ i ∈ A, w i) + 1) := by
    exact (div_eq_iff (ne_of_gt (hden A hA))).mp hAz.symm
  have hgap : (∑ i ∈ A, (r i - z) * w i) = z := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    nlinarith [heq]
  have hs := sum_threshold U A w r z hA hw
  rw [hgap] at hs
  have hb : U.filter (fun i => z ≤ r i) ⊆ U := Finset.filter_subset _ _
  apply le_antisymm (hupper _ hb)
  unfold mnlObjective
  apply (le_div_iff₀ (hden _ hb)).2
  simp_rw [sub_mul] at hs
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  nlinarith

theorem monotone_value {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (j : Fin m) (A B : Finset (Fin n)) (hAB : A ⊆ B) :
    CustAssort.AugGreedy.fj v r j A ≤ CustAssort.AugGreedy.fj v r j B := by
  apply Finset.sup'_le
  intro T hT
  exact Finset.le_sup' _ (Finset.mem_powerset.mpr
    (Finset.Subset.trans (Finset.mem_powerset.mp hT) hAB))

end ThresholdBound

theorem threshold_solution {ι : Type*} [DecidableEq ι] (U : Finset ι) (w r : ι → ℝ)
    (hw : ∀ i ∈ U, 0 ≤ w i) :
    let zstar := U.powerset.sup' (Finset.powerset_nonempty U)
      (ChoiceCDLP.MNL.mnlObjective w r 1)
    ChoiceCDLP.MNL.mnlObjective w r 1 (U.filter (fun i => zstar ≤ r i)) = zstar := by
  exact ThresholdBound.threshold_optimal U w r hw

#print axioms threshold_solution

namespace TruncatedRevenue
open CustAssort.AugGreedy

theorem denom_pos {n m : ℕ} (v : Fin n → Fin m → ℝ)
    (hv : ∀ p j, 0 ≤ v p j) (j : Fin m) (S : Finset (Fin n)) :
    0 < (∑ p ∈ S, v p j) + 1 := by
  have := Finset.sum_nonneg (fun p (_ : p ∈ S) => hv p j)
  linarith

theorem full_of_le {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hv : ∀ p j, 0 ≤ v p j) (j : Fin m) (S : Finset (Fin n))
    (h : ∀ p ∈ S, fj v r j S ≤ r p) : rev v r j S = fj v r j S := by
  have ht := ThresholdBound.threshold_optimal S (fun p => v p j) r (fun p _ => hv p j)
  have hf : S.filter (fun p => fj v r j S ≤ r p) = S :=
    Finset.filter_eq_self.mpr h
  change rev v r j (S.filter (fun p => fj v r j S ≤ r p)) = fj v r j S at ht
  rwa [hf] at ht

theorem clipped_le_full {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hv : ∀ p j, 0 ≤ v p j) (j : Fin m) (S : Finset (Fin n))
    (c : ℝ) (hc : ∀ p ∈ S, c ≤ r p) :
    min (fj v r j S) c ≤ rev v r j S := by
  by_cases hz : fj v r j S ≤ c
  · rw [min_eq_left hz, full_of_le v r hv j S (fun p hp => hz.trans (hc p hp))]
  · have hcz : c ≤ fj v r j S := le_of_not_ge hz
    obtain ⟨A, hA, heq⟩ := Finset.exists_mem_eq_sup' (Finset.powerset_nonempty S) (rev v r j)
    have hAS := Finset.mem_powerset.mp hA
    change fj v r j S = rev v r j A at heq
    rw [min_eq_right hcz]
    rw [heq] at hcz
    unfold rev ChoiceCDLP.MNL.mnlObjective at hcz ⊢
    have ha := (le_div_iff₀ (denom_pos v hv j A)).mp hcz
    have hs : (∑ p ∈ A, (r p - c) * v p j) ≤ ∑ p ∈ S, (r p - c) * v p j :=
      Finset.sum_le_sum_of_subset_of_nonneg hAS
        (fun p hp _ => mul_nonneg (sub_nonneg.mpr (hc p hp)) (hv p j))
    simp_rw [sub_mul] at hs
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum] at hs
    apply (le_div_iff₀ (denom_pos v hv j S)).2
    nlinarith

theorem marginal_formula {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hv : ∀ p j, 0 ≤ v p j) (j : Fin m) (S : Finset (Fin n))
    (p : Fin n) (hp : p ∉ S) :
    rev v r j (insert p S) - rev v r j S =
      (v p j / ((∑ q ∈ S, v q j) + 1 + v p j)) * (r p - rev v r j S) := by
  have hd := denom_pos v hv j S
  have hd' : (∑ q ∈ S, v q j) + 1 + v p j ≠ 0 := by linarith [hv p j]
  unfold rev ChoiceCDLP.MNL.mnlObjective
  rw [Finset.sum_insert hp, Finset.sum_insert hp]
  have he : v p j + (∑ q ∈ S, v q j) + 1 = (∑ q ∈ S, v q j) + 1 + v p j := by ring
  rw [he]
  field_simp
  <;> ring

theorem marginal_le {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hv : ∀ p j, 0 ≤ v p j) (j : Fin m) (A B : Finset (Fin n))
    (hAB : A ⊆ B) (p : Fin n) (hp : p ∉ B)
    (hval : rev v r j A ≤ rev v r j B) (hr : rev v r j B ≤ r p) :
    rev v r j (insert p B) - rev v r j B ≤ rev v r j (insert p A) - rev v r j A := by
  have hpA : p ∉ A := fun h => hp (hAB h)
  rw [marginal_formula v r hv j B p hp, marginal_formula v r hv j A p hpA]
  have hsum : (∑ q ∈ A, v q j) ≤ ∑ q ∈ B, v q j :=
    Finset.sum_le_sum_of_subset_of_nonneg hAB (fun q _ _ => hv q j)
  have hda : 0 < (∑ q ∈ A, v q j) + 1 + v p j := by linarith [denom_pos v hv j A, hv p j]
  have hfrac : v p j / ((∑ q ∈ B, v q j) + 1 + v p j) ≤
      v p j / ((∑ q ∈ A, v q j) + 1 + v p j) :=
    div_le_div_of_nonneg_left (hv p j) hda (by linarith)
  exact mul_le_mul hfrac (sub_le_sub_left hval _) (sub_nonneg.mpr hr)
    (div_nonneg (hv p j) hda.le)

end TruncatedRevenue

open CustAssort.AugGreedy
theorem solution {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (hr : ∀ p, 0 < r p) (hv : ∀ p j, 0 ≤ v p j) (hanti : Antitone r)
    (j : Fin m) (i : Fin n) :
    SubmodularOn (fun S => min (fj v r j S) (r i)) (Vset i) := by
  intro A B hAB hBV p hp
  dsimp only
  have hpB := (Finset.mem_sdiff.mp hp).2
  have hpV := (Finset.mem_sdiff.mp hp).1
  have hAV := Finset.Subset.trans hAB hBV
  have hAiV : insert p A ⊆ Vset i := Finset.insert_subset hpV hAV
  have hBiV : insert p B ⊆ Vset i := Finset.insert_subset hpV hBV
  have hlevel : ∀ S : Finset (Fin n), S ⊆ Vset i → ∀ q ∈ S, r i ≤ r q := by
    intro S hS q hq
    exact hanti (Finset.mem_filter.mp (hS hq)).2
  have hmAB := ThresholdBound.monotone_value v r j A B hAB
  have hmAi := ThresholdBound.monotone_value v r j A (insert p A) (Finset.subset_insert p A)
  have hmBi := ThresholdBound.monotone_value v r j B (insert p B) (Finset.subset_insert p B)
  by_cases hb : r i ≤ fj v r j B
  · rw [min_eq_right hb, min_eq_right (hb.trans hmBi)]
    have := min_le_min_right (r i) hmAi
    linarith
  · have hb' : fj v r j B ≤ r i := le_of_not_ge hb
    have ha' := hmAB.trans hb'
    rw [min_eq_left hb', min_eq_left ha']
    by_cases hai : r i ≤ fj v r j (insert p A)
    · rw [min_eq_right hai]
      have := min_le_right (fj v r j (insert p B)) (r i)
      linarith
    · have hai' : fj v r j (insert p A) ≤ r i := le_of_not_ge hai
      rw [min_eq_left hai']
      have hA := TruncatedRevenue.full_of_le v r hv j A (fun q hq => ha'.trans (hlevel A hAV q hq))
      have hB := TruncatedRevenue.full_of_le v r hv j B (fun q hq => hb'.trans (hlevel B hBV q hq))
      have hAi := TruncatedRevenue.full_of_le v r hv j (insert p A)
        (fun q hq => hai'.trans (hlevel (insert p A) hAiV q hq))
      have hclip := TruncatedRevenue.clipped_le_full v r hv j (insert p B) (r i)
        (hlevel (insert p B) hBiV)
      have hmar := TruncatedRevenue.marginal_le v r hv j A B hAB p hpB
        (by rwa [hA,hB]) (by rw [hB]; exact hb'.trans (hlevel (Vset i) (Finset.Subset.refl _) p hpV))
      rw [hA, hB, hAi] at hmar
      linarith

#print axioms solution
