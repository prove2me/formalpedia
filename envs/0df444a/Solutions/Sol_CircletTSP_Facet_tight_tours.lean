-- Prove2me | solution 1 for CircletTSP.Facet.tight_tours
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:22:35.705835+00:00
-- url     : https://prove2.me/submissions/cb07da9b-156b-4063-98d6-1ff89144ba46

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

/-! Explicit tight circlet tours. The first-family independence proof uses unit-edge
evaluations J-I, repairing the paper's inaccurate diameter-edge uniqueness claim. -/


/- From C4_TourCountsSupport. -/
set_option autoImplicit false

open scoped BigOperators

namespace CircletTSP.Facet.TourCounts

lemma rotate_ne_self {n : ℕ} (hn : 1 < n) (i : Fin n) : finRotate n i ≠ i := by
  cases n with
  | zero => omega
  | succ n =>
    intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    by_cases hi : i = Fin.last n
    · subst i
      simp at hv
      omega
    · simp [hi] at hv

lemma tourVec_nonneg {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    0 ≤ MetricTSP.tourVec π u v := by
  unfold MetricTSP.tourVec
  positivity

lemma tourVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = MetricTSP.tourVec π v u := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps, or_comm]

lemma tourVec_eq_step_sum {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = ∑ k : Fin n,
      if (π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u)
      then (1 : ℝ) else 0 := by
  unfold MetricTSP.tourVec MetricTSP.tourSteps
  exact Finset.natCast_card_filter _ _

lemma single_edge_mass_of_lt {n : ℕ} (a b : Fin n) (hab : a < b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then (1 : ℝ) else 0) = 1 := by
  have heq (u v : Fin n) :
      (u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ↔ u = a ∧ v = b := by
    constructor
    · rintro ⟨huv, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨rfl, rfl⟩
      · exact (lt_asymm hab huv).elim
    · rintro ⟨rfl, rfl⟩
      exact ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
  simp_rw [heq]
  simp [ite_and]

lemma single_edge_mass {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then (1 : ℝ) else 0) = 1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact single_edge_mass_of_lt a b h
  · simpa [or_comm, and_comm] using single_edge_mass_of_lt b a h

lemma tour_unordered_mass {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) :
    (∑ u : Fin n, ∑ v : Fin n, if u < v then MetricTSP.tourVec π u v else 0) = n := by
  have hexpand (u v : Fin n) :
      (if u < v then MetricTSP.tourVec π u v else 0) =
      ∑ k : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by
    rw [tourVec_eq_step_sum]
    by_cases huv : u < v <;> simp [huv]
  simp_rw [hexpand]
  calc
    _ = ∑ u : Fin n, ∑ k : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ u : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by rw [Finset.sum_comm]
    _ = ∑ _k : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      apply single_edge_mass
      intro h
      exact rotate_ne_self hn k (π.injective h).symm
    _ = n := by simp

lemma cycLen_mem_range_of_lt {n : ℕ} (u v : Fin n) (huv : u < v) :
    cycLen n u v ∈ Finset.Icc 1 (n / 2) := by
  have hu := u.isLt
  have hv := v.isLt
  have huv' : u.val < v.val := huv
  simp only [Finset.mem_Icc, cycLen,
    Int.natAbs_natCast_sub_natCast_of_le (Nat.le_of_lt huv')]
  omega

lemma sum_lenCount_eq_mass (n : ℕ) (x : Fin n → Fin n → ℝ) :
    (∑ i ∈ Finset.Icc 1 (n / 2), lenCount n i x) =
      ∑ u : Fin n, ∑ v : Fin n, if u < v then x u v else 0 := by
  unfold lenCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u < v
  · have hmem := cycLen_mem_range_of_lt u v huv
    simp [huv, hmem]
  · simp [huv]

lemma sum_lenCount_tour {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) :
    (∑ i ∈ Finset.Icc 1 (n / 2), lenCount n i (MetricTSP.tourVec π)) = n := by
  rw [sum_lenCount_eq_mass]
  exact tour_unordered_mass hn π

lemma lenCount_nonneg {n : ℕ} (π : Equiv.Perm (Fin n)) (i : ℕ) :
    0 ≤ lenCount n i (MetricTSP.tourVec π) := by
  unfold lenCount
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact tourVec_nonneg π u v
  · exact le_rfl

end CircletTSP.Facet.TourCounts


/- From C4_Successors. -/
namespace CircletTSP.Facet.TourCounts

lemma tourVec_eq_successors {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) (huv : u ≠ v) :
    MetricTSP.tourVec π u v =
      (if π (finRotate n (π.symm u)) = v then 1 else 0) +
      (if π (finRotate n (π.symm v)) = u then 1 else 0) := by
  rw [tourVec_eq_step_sum]
  have hsplit (k : Fin n) :
      (if (π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u)
        then (1 : ℝ) else 0) =
      (if k = π.symm u then if π (finRotate n k) = v then 1 else 0 else 0) +
      (if k = π.symm v then if π (finRotate n k) = u then 1 else 0 else 0) := by
    have hku : π k = u ↔ k = π.symm u := π.eq_symm_apply.symm
    have hkv : π k = v ↔ k = π.symm v := π.eq_symm_apply.symm
    simp only [hku, hkv]
    by_cases hu : k = π.symm u
    · by_cases hv : k = π.symm v
      · exact (huv (π.symm.injective (hu.symm.trans hv))).elim
      · simp [hu, huv]
    · by_cases hv : k = π.symm v
      · simp [hv, Ne.symm huv]
      · simp [hu, hv]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp

lemma tourVec_diagonal_zero {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    MetricTSP.tourVec π u u = 0 := by
  rw [tourVec_eq_step_sum]
  apply Finset.sum_eq_zero
  intro k _
  have hnot : ¬ (π k = u ∧ π (finRotate n k) = u) := by
    rintro ⟨ha, hb⟩
    exact rotate_ne_self hn k (π.injective (hb.trans ha.symm))
  simp only [or_self, if_neg hnot]

def successorPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  π.symm.trans ((finRotate n).trans π)

lemma successor_ne_self {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    successorPerm π u ≠ u := by
  intro h
  have h' : finRotate n (π.symm u) = π.symm u := by
    apply π.injective
    simpa [successorPerm] using h
  exact rotate_ne_self hn (π.symm u) h'

lemma tourVec_eq_successors_all {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v =
      (if successorPerm π u = v then 1 else 0) +
      (if successorPerm π v = u then 1 else 0) := by
  by_cases huv : u = v
  · subst v
    simp [tourVec_diagonal_zero hn, successor_ne_self hn]
  · exact tourVec_eq_successors π u v huv

lemma tourVec_row_sum {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    (∑ v : Fin n, MetricTSP.tourVec π u v) = 2 := by
  simp_rw [tourVec_eq_successors_all hn]
  rw [Finset.sum_add_distrib]
  have hleft : (∑ v : Fin n, if successorPerm π u = v then (1 : ℝ) else 0) = 1 := by simp
  have hright : (∑ v : Fin n, if successorPerm π v = u then (1 : ℝ) else 0) = 1 := by
    simp_rw [← (successorPerm π).eq_symm_apply]
    simp
  rw [hleft, hright]
  norm_num

lemma tourVec_trans {n : ℕ} (π σ : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec (π.trans σ) (σ u) (σ v) = MetricTSP.tourVec π u v := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps]

end CircletTSP.Facet.TourCounts


/- From C4_TourCost. -/
namespace CircletTSP.Facet.TightProof

noncomputable section

theorem cycLen_symm {n : ℕ} (u v : Fin n) : cycLen n u v = cycLen n v u := by
  have h : (u.val : ℤ) - v.val = -((v.val : ℤ) - u.val) := by omega
  simp only [cycLen, h, Int.natAbs_neg]

theorem circletForm_eq_weighted_edges (n : ℕ) (x : Fin n → Fin n → ℝ) :
    circletForm n x = ∑ u : Fin n, ∑ v : Fin n,
      if u < v then (coeff n (cycLen n u v) : ℝ) * x u v else 0 := by
  unfold circletForm lenCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u < v
  · have hmem := TourCounts.cycLen_mem_range_of_lt u v huv
    simp [huv, hmem, eq_comm]
  · simp [huv]

private theorem single_edge_weight_of_lt {n : ℕ} (w : Fin n → Fin n → ℝ)
    (a b : Fin n) (hab : a < b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then w u v else 0) = w a b := by
  have heq (u v : Fin n) :
      (u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ↔ u = a ∧ v = b := by
    constructor
    · rintro ⟨huv, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨rfl, rfl⟩
      · exact (lt_asymm hab huv).elim
    · rintro ⟨rfl, rfl⟩
      exact ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
  simp_rw [heq]
  simp [ite_and]

private theorem single_edge_weight {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hw : ∀ u v, w u v = w v u) (a b : Fin n) (hab : a ≠ b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then w u v else 0) = w a b := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact single_edge_weight_of_lt w a b h
  · simpa [or_comm, and_comm, hw b a] using single_edge_weight_of_lt w b a h

theorem weighted_tour_eq_step_sum {n : ℕ} (hn : 1 < n)
    (w : Fin n → Fin n → ℝ) (hw : ∀ u v, w u v = w v u)
    (π : Equiv.Perm (Fin n)) :
    (∑ u : Fin n, ∑ v : Fin n, if u < v then w u v * MetricTSP.tourVec π u v else 0) =
      ∑ k : Fin n, w (π k) (π (finRotate n k)) := by
  have hexpand (u v : Fin n) :
      (if u < v then w u v * MetricTSP.tourVec π u v else 0) =
      ∑ k : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then w u v else 0 := by
    rw [TourCounts.tourVec_eq_step_sum]
    by_cases huv : u < v
    · simp only [huv, if_true, true_and, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    · simp only [huv, if_false, false_and, Finset.sum_const_zero]
  simp_rw [hexpand]
  calc
    _ = ∑ u : Fin n, ∑ k : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then w u v else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ u : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then w u v else 0 := by rw [Finset.sum_comm]
    _ = ∑ k : Fin n, w (π k) (π (finRotate n k)) := by
      apply Finset.sum_congr rfl
      intro k _
      apply single_edge_weight w hw
      intro h
      exact TourCounts.rotate_ne_self hn k (π.injective h).symm

theorem circletForm_tour_eq_step_sum {n : ℕ} (hn : 1 < n)
    (π : Equiv.Perm (Fin n)) :
    circletForm n (MetricTSP.tourVec π) =
      ∑ k : Fin n, (coeff n (cycLen n (π k) (π (finRotate n k))) : ℝ) := by
  rw [circletForm_eq_weighted_edges]
  apply weighted_tour_eq_step_sum hn
  intro u v
  rw [cycLen_symm]

end

end CircletTSP.Facet.TightProof


/- From C4_Rotation. -/
namespace CircletTSP.Facet.TightProof

noncomputable section

theorem cycLen_eq_min_sub {n : ℕ} (u v : Fin n) :
    cycLen n u v = min (u - v).val (v - u).val := by
  have hsub := Fin.intCast_val_sub_eq_sub_add_ite u v
  have hsub' := Fin.intCast_val_sub_eq_sub_add_ite v u
  by_cases h : u.val ≤ v.val
  · simp only [cycLen, Int.natAbs_natCast_sub_natCast_of_le h]
    simp only [Fin.le_def] at hsub hsub'
    split_ifs at hsub hsub' <;> omega
  · have h' : v.val ≤ u.val := by omega
    rw [cycLen_symm]
    simp only [cycLen, Int.natAbs_natCast_sub_natCast_of_le h']
    simp only [Fin.le_def] at hsub hsub'
    split_ifs at hsub hsub'; omega

theorem cycLen_add_right {n : ℕ} [NeZero n] (u v m : Fin n) :
    cycLen n (u + m) (v + m) = cycLen n u v := by
  rw [cycLen_eq_min_sub, cycLen_eq_min_sub]
  simp only [add_sub_add_right_eq_sub]

theorem tourVec_relabel {n : ℕ} (π ρ : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec (π.trans ρ) (ρ u) (ρ v) = MetricTSP.tourVec π u v := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps]

def rotateTour {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n)) (m : Fin n) :
    Equiv.Perm (Fin n) := π.trans (Equiv.addRight m)

theorem rotateTour_apply {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n)) (m i : Fin n) :
    rotateTour π m i = π i + m := rfl

theorem tourVec_rotate {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n)) (m u v : Fin n) :
    MetricTSP.tourVec (rotateTour π m) u v = MetricTSP.tourVec π (u - m) (v - m) := by
  have h := tourVec_relabel π (Equiv.addRight m) (u - m) (v - m)
  simpa [rotateTour] using h

theorem circletForm_rotate {n : ℕ} [NeZero n] (hn : 1 < n)
    (π : Equiv.Perm (Fin n)) (m : Fin n) :
    circletForm n (MetricTSP.tourVec (rotateTour π m)) = circletForm n (MetricTSP.tourVec π) := by
  rw [circletForm_tour_eq_step_sum hn, circletForm_tour_eq_step_sum hn]
  simp only [rotateTour_apply, cycLen_add_right]

end

end CircletTSP.Facet.TightProof


/- From C4_BaseTours. -/
namespace CircletTSP.Facet.TightProof

noncomputable section

/-- Reverse the second half of the cyclic ordering. -/
def baseVertex (d : ℕ) (i : Fin (2 * d)) : Fin (2 * d) :=
  ⟨if i.val < d then i.val else 3 * d - 1 - i.val, by
    have hi := i.isLt
    split_ifs <;> omega⟩

theorem baseVertex_involutive (d : ℕ) : Function.Involutive (baseVertex d) := by
  intro i
  apply Fin.ext
  have hi := i.isLt
  dsimp [baseVertex]
  split_ifs <;> omega

/-- The first paper tour visits `0,...,d-1,2d-1,...,d`. -/
def baseTour (d : ℕ) : Equiv.Perm (Fin (2 * d)) :=
  { toFun := baseVertex d
    invFun := baseVertex d
    left_inv := baseVertex_involutive d
    right_inv := baseVertex_involutive d }

theorem baseTour_apply_val (d : ℕ) (i : Fin (2 * d)) :
    (baseTour d i).val = if i.val < d then i.val else 3 * d - 1 - i.val := rfl

theorem baseTour_symm_apply_val (d : ℕ) (i : Fin (2 * d)) :
    ((baseTour d).symm i).val = if i.val < d then i.val else 3 * d - 1 - i.val := rfl

theorem baseTour_successor_val (d : ℕ) (hd : 0 < d) (i : Fin (2 * d)) :
    (baseTour d (finRotate (2 * d) ((baseTour d).symm i))).val =
      if i.val + 1 < d then i.val + 1
      else if i.val < d then 2 * d - 1
      else if d < i.val then i.val - 1 else 0 := by
  let _ : NeZero (2 * d) := ⟨by omega⟩
  have hi := i.isLt
  rw [baseTour_apply_val]
  rw [finRotate_apply]
  have hone : (1 : Fin (2 * d)).val = 1 := by
    change 1 % (2 * d) = 1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_add_eq_ite, hone]
  rw [baseTour_symm_apply_val]
  split_ifs <;> omega

end

end CircletTSP.Facet.TightProof


/- From C4_BaseProperties. -/
namespace CircletTSP.Facet.TightProof

noncomputable section

theorem fin_pred_val {n : ℕ} [NeZero n] (hn : 1 < n) (j : Fin n) :
    (j - 1).val = if j.val = 0 then n - 1 else j.val - 1 := by
  have hj := j.isLt
  have h := Fin.intCast_val_sub_eq_sub_add_ite j (1 : Fin n)
  have hone : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt hn
  simp only [Fin.le_def, hone] at h
  split_ifs at h ⊢ <;> omega

theorem baseTour_unit_edge (d : ℕ) (hd : 2 ≤ d) (j : Fin (2 * d)) :
    letI : NeZero (2 * d) := ⟨by omega⟩
    MetricTSP.tourVec (baseTour d) (j - 1) j =
      if j.val = 0 ∨ j.val = d then 0 else 1 := by
  let : NeZero (2 * d) := ⟨by omega⟩
  have hj := j.isLt
  have hs₁ : baseTour d (finRotate (2*d) ((baseTour d).symm (j - 1))) = j ↔
      0 < j.val ∧ j.val < d := by
    rw [Fin.ext_iff, baseTour_successor_val d (by omega), fin_pred_val (by omega)]
    split_ifs <;> omega
  have hs₂ : baseTour d (finRotate (2*d) ((baseTour d).symm j)) = j - 1 ↔
      d < j.val := by
    rw [Fin.ext_iff, baseTour_successor_val d (by omega), fin_pred_val (by omega)]
    split_ifs <;> omega
  rw [TourCounts.tourVec_eq_successors_all (by omega)]
  change (if baseTour d (finRotate (2*d) ((baseTour d).symm (j-1)))=j then (1:ℝ) else 0) +
    (if baseTour d (finRotate (2*d) ((baseTour d).symm j))=j-1 then 1 else 0) = _
  simp only [hs₁, hs₂]
  split_ifs <;> norm_num <;> omega

theorem baseTour_successor_length (d : ℕ) (hd : 2 ≤ d) (j : Fin (2*d)) :
    cycLen (2*d) j (baseTour d (finRotate (2*d) ((baseTour d).symm j))) =
      if j.val = d-1 ∨ j.val = d then d else 1 := by
  have hj := j.isLt
  let v := baseTour d (finRotate (2*d) ((baseTour d).symm j))
  have hv := v.isLt
  have hs : v.val = if j.val+1<d then j.val+1 else if j.val<d then 2*d-1
      else if d<j.val then j.val-1 else 0 := baseTour_successor_val d (by omega) j
  change cycLen (2*d) j v = _
  by_cases h : j.val ≤ v.val
  · simp only [cycLen, Int.natAbs_natCast_sub_natCast_of_le h]
    split_ifs at hs ⊢ <;> omega
  · have h' : v.val ≤ j.val := by omega
    rw [cycLen_symm]
    simp only [cycLen, Int.natAbs_natCast_sub_natCast_of_le h']
    split_ifs at hs ⊢ <;> omega

theorem circletForm_tour_eq_successor_sum {n : ℕ} (hn : 1 < n)
    (π : Equiv.Perm (Fin n)) :
    circletForm n (MetricTSP.tourVec π) =
      ∑ u, (coeff n (cycLen n u (π (finRotate n (π.symm u)))) : ℝ) := by
  rw [circletForm_tour_eq_step_sum hn]
  simpa using (Equiv.sum_comp π
    (fun u => (coeff n (cycLen n u (π (finRotate n (π.symm u)))) : ℝ)))

theorem baseTour_tight (d : ℕ) (hd : 2 ≤ d) (heven : Even d) :
    circletForm (2*d) (MetricTSP.tourVec (baseTour d)) = (2*d:ℕ)-2 := by
  rw [circletForm_tour_eq_successor_sum (by omega)]
  have hmod : d % 2 = 0 := Nat.mod_eq_zero_of_dvd heven.two_dvd
  have hddiv : 2*d/2=d := by omega
  have hterm (j : Fin (2*d)) :
      (coeff (2*d) (cycLen (2*d) j (baseTour d (finRotate (2*d) ((baseTour d).symm j)))) : ℝ) =
        if j.val=d-1 ∨ j.val=d then 0 else 1 := by
    rw [baseTour_successor_length d hd j]
    split_ifs <;> simp [coeff, hmod, hddiv]
  simp_rw [hterm]
  let a : Fin (2*d) := ⟨d-1, by omega⟩
  let b : Fin (2*d) := ⟨d, by omega⟩
  have hab : a ≠ b := by simp only [ne_eq, Fin.ext_iff]; dsimp [a,b]; omega
  have hexpand (j : Fin (2*d)) :
      (if j.val=d-1 ∨ j.val=d then (0:ℝ) else 1) =
        1 - (if j=a then 1 else 0) - (if j=b then 1 else 0) := by
    have ha : j.val=d-1 ↔ j=a := by simp [Fin.ext_iff,a]
    have hb : j.val=d ↔ j=b := by simp [Fin.ext_iff,b]
    simp only [ha,hb]
    by_cases hja : j=a <;> by_cases hjb : j=b <;> simp_all
  simp_rw [hexpand]
  simp only [Finset.sum_sub_distrib]
  simp
  ring

end
end CircletTSP.Facet.TightProof


/- From C4_Independence. -/
namespace CircletTSP.Facet.TightProof

noncomputable section

/-- The matrix of these evaluations is `J - I`, which is nonsingular whenever
the number of columns is different from one. -/
theorem linearIndependent_of_complement_evaluations
    {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℝ M]
    (v : I → M) (eval : I → M →ₗ[ℝ] ℝ) (hcard : Fintype.card I ≠ 1)
    (hval : ∀ i j, eval j (v i) = if i = j then 0 else 1) :
    LinearIndependent ℝ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  let S : ℝ := ∑ i, a i
  have heq (j : I) : S = a j := by
    have hc := congrArg (eval j) ha
    simp only [map_sum, map_smul, map_zero, smul_eq_mul, hval] at hc
    have hsum : (∑ i, a i * (if i = j then 0 else 1)) = S - a j := by
      calc
        (∑ i, a i * (if i = j then 0 else 1)) =
            ∑ i, (a i - if i = j then a i else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> simp
        _ = S - a j := by simp [S, Finset.sum_sub_distrib]
    rw [hsum] at hc
    linarith
  have htotal : S = (Fintype.card I : ℝ) * S := by
    calc
      S = ∑ _ : I, S := Finset.sum_congr rfl (fun i _ => (heq i).symm)
      _ = (Fintype.card I : ℝ) * S := by simp
  have hcardR : (Fintype.card I : ℝ) ≠ 1 := by exact_mod_cast hcard
  have hS : S = 0 := by
    have hm : ((Fintype.card I : ℝ) - 1) * S = 0 := by nlinarith [htotal]
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hcardR)
  intro i
  exact (heq i).symm.trans hS

/-- Distinguished coordinates eliminate the second family; `J - I` evaluations
then eliminate the first family. This repairs the independence argument in the paper. -/
theorem linearIndependent_sum_of_unique_and_complement_evaluations
    {I J M : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [AddCommGroup M] [Module ℝ M]
    (v : I ⊕ J → M) (baseEval : I → M →ₗ[ℝ] ℝ)
    (extraEval : J → M →ₗ[ℝ] ℝ) (hcard : Fintype.card I ≠ 1)
    (hbase : ∀ i j, baseEval j (v (Sum.inl i)) = if i = j then 0 else 1)
    (hextra : ∀ i j, extraEval j (v i) = if i = Sum.inr j then 1 else 0) :
    LinearIndependent ℝ v := by
  classical
  have hleft := linearIndependent_of_complement_evaluations
    (fun i => v (Sum.inl i)) baseEval hcard hbase
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hright (j : J) : a (Sum.inr j) = 0 := by
    have hc := congrArg (extraEval j) ha
    simpa only [map_sum, map_smul, map_zero, smul_eq_mul, hextra,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hc
  have hbasezero : (∑ i : I, a (Sum.inl i) • v (Sum.inl i)) = 0 := by
    simpa only [Fintype.sum_sum_type, hright, zero_smul, Finset.sum_const_zero,
      add_zero] using ha
  intro i
  cases i with
  | inl i => exact Fintype.linearIndependent_iff.mp hleft _ hbasezero i
  | inr j => exact hright j

end

end CircletTSP.Facet.TightProof


/- From C4_BaseFamily. -/
namespace CircletTSP.Facet.TightProof

noncomputable section

def halfLift {d : ℕ} (j : Fin d) : Fin (2*d) := ⟨j.val, by have := j.isLt; omega⟩

@[simp] theorem halfLift_val {d : ℕ} (j : Fin d) : (halfLift j).val=j.val := rfl

def baseFamily (d : ℕ) (hd : 2 ≤ d) (j : Fin d) : Equiv.Perm (Fin (2*d)) :=
  letI : NeZero (2*d) := ⟨by omega⟩
  rotateTour (baseTour d) (halfLift j)

theorem baseFamily_tight (d : ℕ) (hd : 2 ≤ d) (heven : Even d) (j : Fin d) :
    circletForm (2*d) (MetricTSP.tourVec (baseFamily d hd j)) = (2*d:ℕ)-2 := by
  let : NeZero (2*d) := ⟨by omega⟩
  rw [baseFamily, circletForm_rotate (by omega), baseTour_tight d hd heven]

theorem baseFamily_unit_evaluation (d : ℕ) (hd : 2 ≤ d) (i j : Fin d) :
    letI : NeZero (2*d) := ⟨by omega⟩
    MetricTSP.tourVec (baseFamily d hd i) (halfLift j - 1) (halfLift j) =
      if i=j then 0 else 1 := by
  let : NeZero (2*d) := ⟨by omega⟩
  rw [baseFamily, tourVec_rotate]
  have hreorder : halfLift j - 1 - halfLift i = (halfLift j - halfLift i) - 1 := by abel
  rw [hreorder, baseTour_unit_edge d hd]
  have hbad : (halfLift j - halfLift i).val=0 ∨ (halfLift j-halfLift i).val=d ↔ i=j := by
    have h := Fin.intCast_val_sub_eq_sub_add_ite (halfLift j) (halfLift i)
    have hi := i.isLt
    have hj := j.isLt
    simp only [Fin.le_def,halfLift_val] at h
    rw [Fin.ext_iff]
    split_ifs at h <;> omega
  simp only [hbad]

def edgeEval {n : ℕ} (u v : Fin n) : (Fin n → Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x u v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem baseFamily_linearIndependent (d : ℕ) (hd : 2 ≤ d) :
    LinearIndependent ℝ (fun j => MetricTSP.tourVec (baseFamily d hd j)) := by
  let : NeZero (2*d) := ⟨by omega⟩
  apply linearIndependent_of_complement_evaluations _
    (fun j => edgeEval (halfLift j-1) (halfLift j))
  · simp only [Fintype.card_fin]; omega
  · intro i j
    exact baseFamily_unit_evaluation d hd i j

theorem baseTour_zero_of_length_ne (d : ℕ) (hd : 2 ≤ d) (u v : Fin (2*d))
    (hunit : cycLen (2*d) u v ≠ 1) (hdiam : cycLen (2*d) u v ≠ d) :
    MetricTSP.tourVec (baseTour d) u v = 0 := by
  have hs₁ : ¬ baseTour d (finRotate (2*d) ((baseTour d).symm u))=v := by
    intro h
    have hl := baseTour_successor_length d hd u
    rw [h] at hl
    split_ifs at hl <;> contradiction
  have hs₂ : ¬ baseTour d (finRotate (2*d) ((baseTour d).symm v))=u := by
    intro h
    have hl := baseTour_successor_length d hd v
    rw [h,cycLen_symm] at hl
    split_ifs at hl <;> contradiction
  rw [TourCounts.tourVec_eq_successors_all (by omega)]
  change (if baseTour d (finRotate (2*d) ((baseTour d).symm u))=v then (1:ℝ) else 0)+
    (if baseTour d (finRotate (2*d) ((baseTour d).symm v))=u then 1 else 0)=0
  simp only [hs₁,hs₂,if_false,zero_add]

theorem cycLen_sub_right {n : ℕ} [NeZero n] (u v m : Fin n) :
    cycLen n (u-m) (v-m) = cycLen n u v := by
  have h := cycLen_add_right (u-m) (v-m) m
  simpa using h.symm

theorem baseFamily_zero_of_length_ne (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (u v : Fin (2*d))
    (hunit : cycLen (2*d) u v ≠ 1) (hdiam : cycLen (2*d) u v ≠ d) :
    MetricTSP.tourVec (baseFamily d hd i) u v = 0 := by
  let : NeZero (2*d) := ⟨by omega⟩
  rw [baseFamily,tourVec_rotate]
  apply baseTour_zero_of_length_ne d hd
  · simpa only [cycLen_sub_right] using hunit
  · simpa only [cycLen_sub_right] using hdiam

end
end CircletTSP.Facet.TightProof


/- From C4_LongFamilies. -/
namespace CircletTSP.Facet.TightProof

noncomputable section

theorem rotated_pair_injective (d : ℕ) (hd : 2 ≤ d) (u v m m' : Fin (2*d))
    (hlen : cycLen (2*d) u v ≠ d) :
    letI : NeZero (2*d) := ⟨by omega⟩
    ((u+m=u+m' ∧ v+m=v+m') ∨ (u+m=v+m' ∧ v+m=u+m')) → m=m' := by
  let : NeZero (2*d) := ⟨by omega⟩
  rintro (⟨h,_⟩ | ⟨h₁,h₂⟩)
  · exact add_left_cancel h
  · by_contra hm
    have hu := u.isLt
    have hv := v.isLt
    have hmv := m.isLt
    have hm'v := m'.isLt
    have hmne : m.val ≠ m'.val := fun h => hm (Fin.ext h)
    have h₁v := congrArg Fin.val h₁
    have h₂v := congrArg Fin.val h₂
    simp only [Fin.val_add_eq_ite] at h₁v h₂v
    have hgap : u.val+d=v.val ∨ v.val+d=u.val := by
      split_ifs at h₁v h₂v <;> omega
    apply hlen
    rcases hgap with h | h
    · rw [cycLen,Int.natAbs_natCast_sub_natCast_of_le (by omega : u.val ≤ v.val)]
      omega
    · rw [cycLen,Int.natAbs_natCast_sub_natCast_of_ge (by omega : v.val ≤ u.val)]
      omega

/-- Data for one tour at each distinct long-edge cost. -/
structure TightLongTours (d : ℕ) (K : Type*) where
  tour : K → Equiv.Perm (Fin (2*d))
  tail : K → Fin (2*d)
  head : K → Fin (2*d)
  cost : K → ℕ
  cost_injective : Function.Injective cost
  cost_ge_two : ∀ k, 2 ≤ cost k
  long_cost : ∀ k, coeff (2*d) (cycLen (2*d) (tail k) (head k)) = cost k
  support : ∀ k u v, MetricTSP.tourVec (tour k) u v ≠ 0 →
    cycLen (2*d) u v = 1 ∨ cycLen (2*d) u v = d ∨
    (u=tail k ∧ v=head k) ∨ (v=tail k ∧ u=head k)
  long_entry : ∀ k, MetricTSP.tourVec (tour k) (tail k) (head k) = 1
  tight : ∀ k, circletForm (2*d) (MetricTSP.tourVec (tour k)) = (2*d:ℕ)-2

theorem TightLongTours.long_ne_unit {d : ℕ} {K : Type*} (H : TightLongTours d K) (k : K) :
    cycLen (2*d) (H.tail k) (H.head k) ≠ 1 := by
  intro h
  have hc := H.long_cost k
  rw [h] at hc
  norm_num [coeff] at hc
  have := H.cost_ge_two k
  omega

theorem TightLongTours.long_ne_diameter {d : ℕ} {K : Type*} (H : TightLongTours d K)
    (heven : Even d) (k : K) :
    cycLen (2*d) (H.tail k) (H.head k) ≠ d := by
  intro h
  have hc := H.long_cost k
  rw [h] at hc
  have he := Nat.even_iff.mp heven
  have hdiv : 2*d/2=d := by omega
  simp [coeff,he,hdiv] at hc
  have := H.cost_ge_two k
  omega

def TightLongTours.rotation {d : ℕ} {K : Type*} (H : TightLongTours d K)
    (hd : 2 ≤ d) (j : K × Fin (2*d)) : Equiv.Perm (Fin (2*d)) :=
  letI : NeZero (2*d) := ⟨by omega⟩
  rotateTour (H.tour j.1) j.2

theorem TightLongTours.rotation_tight {d : ℕ} {K : Type*} (H : TightLongTours d K)
    (hd : 2 ≤ d) (j : K × Fin (2*d)) :
    circletForm (2*d) (MetricTSP.tourVec (H.rotation hd j)) = (2*d:ℕ)-2 := by
  let : NeZero (2*d) := ⟨by omega⟩
  rw [TightLongTours.rotation,circletForm_rotate (by omega),H.tight]

theorem TightLongTours.rotation_unique_evaluation {d : ℕ} {K : Type*} [DecidableEq K]
    (H : TightLongTours d K) (hd : 2 ≤ d) (heven : Even d) (i j : K × Fin (2*d)) :
    letI : NeZero (2*d) := ⟨by omega⟩
    MetricTSP.tourVec (H.rotation hd i) (H.tail j.1+j.2) (H.head j.1+j.2) =
      if i=j then 1 else 0 := by
  let : NeZero (2*d) := ⟨by omega⟩
  by_cases hij : i=j
  · subst j
    simp only [TightLongTours.rotation]
    exact (tourVec_relabel (H.tour i.1) (Equiv.addRight i.2) _ _).trans (H.long_entry i.1)
  · rw [if_neg hij]
    by_contra hnonzero
    rw [TightLongTours.rotation,tourVec_rotate] at hnonzero
    have hlen : cycLen (2*d) (H.tail j.1+j.2-i.2) (H.head j.1+j.2-i.2) =
        cycLen (2*d) (H.tail j.1) (H.head j.1) := by
      rw [cycLen_sub_right,cycLen_add_right]
    have hsupport := H.support i.1 _ _ hnonzero
    rcases hsupport with h | h | h | h
    · exact H.long_ne_unit j.1 (hlen.symm.trans h)
    · exact H.long_ne_diameter heven j.1 (hlen.symm.trans h)
    · have hc : H.cost i.1=H.cost j.1 := by
        rw [← H.long_cost i.1,← h.1,← h.2,hlen,H.long_cost]
      have hk : i.1=j.1 := H.cost_injective hc
      have hm : i.2=j.2 := by
        have hh := congrArg (fun z : Fin (2*d) => z+i.2) h.1
        simp only [sub_add_cancel,hk] at hh
        exact (add_left_cancel hh).symm
      exact hij (Prod.ext hk hm)
    · have hc : H.cost i.1=H.cost j.1 := by
        rw [← H.long_cost i.1,← h.1,← h.2,cycLen_symm,hlen,H.long_cost]
      have hk : i.1=j.1 := H.cost_injective hc
      have hm : j.2=i.2 := by
        apply rotated_pair_injective d hd (H.tail j.1) (H.head j.1) j.2 i.2
          (H.long_ne_diameter heven j.1)
        apply Or.inr
        have h₁ := congrArg (fun z : Fin (2*d) => z+i.2) h.1
        have h₂ := congrArg (fun z : Fin (2*d) => z+i.2) h.2
        simp only [sub_add_cancel,hk] at h₁ h₂
        exact ⟨h₂,h₁⟩
      exact hij (Prod.ext hk hm.symm)

end
end CircletTSP.Facet.TightProof


/- From C4_ZigzagSupport. -/
set_option autoImplicit false

namespace CircletTSP.Facet.Zigzag

/-- The first top row, alternating two-vertex columns, then the remaining bottom row in reverse. -/
def zigzagIndex (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) (p : Fin (2 * d)) : Fin (2 * d) :=
  ⟨if (p : ℕ) < d - k + 1 then p
    else if (p : ℕ) < d + k - 1 then
      if (((p : ℕ) - (d - k + 1)) / 2 + ((p : ℕ) - (d - k + 1)) % 2) % 2 = 0
      then d - k + 1 + ((p : ℕ) - (d - k + 1)) / 2
      else d + (d - k + 1) + ((p : ℕ) - (d - k + 1)) / 2
    else 3 * d - 1 - p,
    by split_ifs <;> have hp := p.isLt <;> omega⟩

lemma zigzagIndex_injective (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) :
    Function.Injective (zigzagIndex d k hk hkd) := by
  intro p q hpq
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  have h := congrArg Fin.val hpq
  dsimp [zigzagIndex] at h
  split_ifs at h <;> omega

noncomputable def zigzagTour (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) :
    Equiv.Perm (Fin (2 * d)) :=
  Equiv.ofBijective (zigzagIndex d k hk hkd)
    ⟨zigzagIndex_injective d k hk hkd,
      Finite.surjective_of_injective (zigzagIndex_injective d k hk hkd)⟩

@[simp] lemma zigzagTour_apply (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d)
    (p : Fin (2 * d)) : zigzagTour d k hk hkd p = zigzagIndex d k hk hkd p := rfl


lemma rotate_val {n : ℕ} (p : Fin n) :
    (finRotate n p).val = if p.val + 1 < n then p.val + 1 else 0 := by
  cases n with
  | zero => exact Fin.elim0 p
  | succ m =>
    rw [coe_finRotate]
    by_cases hp : p = Fin.last m
    · subst p
      simp
    · have hlt := Fin.val_lt_last hp
      simp [hp, show p.val + 1 < m + 1 by omega]

def longPosition (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) : Fin (2 * d) :=
  ⟨d + k - 2, by omega⟩

def longTail (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) : Fin (2 * d) :=
  ⟨if k % 2 = 0 then 2 * d - 1 else d - 1, by split_ifs <;> omega⟩

def longHead (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) : Fin (2 * d) :=
  ⟨2 * d - k, by omega⟩

lemma long_tail_image (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) :
    zigzagTour d k hk hkd (longPosition d k hk hkd) = longTail d k hk hkd := by
  apply Fin.ext
  simp only [zigzagTour_apply, zigzagIndex, longPosition, longTail]
  split_ifs <;> omega

lemma long_head_image (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) :
    zigzagTour d k hk hkd (finRotate (2 * d) (longPosition d k hk hkd)) =
      longHead d k hk hkd := by
  have hr : (finRotate (2 * d) (longPosition d k hk hkd)).val = d + k - 1 := by
    rw [rotate_val, if_pos (by dsimp [longPosition]; omega)]
    dsimp [longPosition]
    omega
  apply Fin.ext
  simp only [zigzagTour_apply, zigzagIndex, longHead, hr]
  split_ifs <;> omega

lemma long_endpoints_ne (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) :
    longTail d k hk hkd ≠ longHead d k hk hkd := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [longTail, longHead] at hv
  split_ifs at hv <;> omega


def diameterPosition (d k : ℕ) (p : Fin (2 * d)) : Prop :=
  p.val = 2 * d - 1 ∨
    (d - k + 1 ≤ p.val ∧ p.val < d + k - 1 ∧ (p.val - (d - k + 1)) % 2 = 0)

instance (d k : ℕ) (p : Fin (2 * d)) : Decidable (diameterPosition d k p) := by
  unfold diameterPosition
  infer_instance

lemma diameter_step_gap (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d)
    (p : Fin (2 * d)) (hd : diameterPosition d k p) :
    (zigzagTour d k hk hkd p).val + d =
        (zigzagTour d k hk hkd (finRotate (2 * d) p)).val ∨
      (zigzagTour d k hk hkd (finRotate (2 * d) p)).val + d =
        (zigzagTour d k hk hkd p).val := by
  have hp := p.isLt
  dsimp [diameterPosition] at hd
  simp only [zigzagTour_apply, zigzagIndex, rotate_val]
  split_ifs <;> omega

lemma unit_step_gap (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d)
    (p : Fin (2 * d)) (hd : ¬ diameterPosition d k p)
    (hl : p.val ≠ d + k - 2) :
    (zigzagTour d k hk hkd p).val + 1 =
        (zigzagTour d k hk hkd (finRotate (2 * d) p)).val ∨
      (zigzagTour d k hk hkd (finRotate (2 * d) p)).val + 1 =
        (zigzagTour d k hk hkd p).val := by
  have hp := p.isLt
  dsimp [diameterPosition] at hd
  simp only [zigzagTour_apply, zigzagIndex, rotate_val]
  split_ifs <;> omega

lemma cycLen_of_unit_gap (d : ℕ) (_hd : 1 < d) (u v : Fin (2 * d))
    (h : u.val + 1 = v.val ∨ v.val + 1 = u.val) : cycLen (2 * d) u v = 1 := by
  rcases h with h | h
  · rw [cycLen, Int.natAbs_natCast_sub_natCast_of_le (by omega : u.val ≤ v.val)]
    omega
  · rw [cycLen, Int.natAbs_natCast_sub_natCast_of_ge (by omega : v.val ≤ u.val)]
    omega

lemma cycLen_of_diameter_gap (d : ℕ) (u v : Fin (2 * d))
    (h : u.val + d = v.val ∨ v.val + d = u.val) : cycLen (2 * d) u v = d := by
  rcases h with h | h
  · rw [cycLen, Int.natAbs_natCast_sub_natCast_of_le (by omega : u.val ≤ v.val)]
    omega
  · rw [cycLen, Int.natAbs_natCast_sub_natCast_of_ge (by omega : v.val ≤ u.val)]
    omega

lemma diameter_step_length (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d)
    (p : Fin (2 * d)) (hd : diameterPosition d k p) :
    cycLen (2 * d) (zigzagTour d k hk hkd p)
      (zigzagTour d k hk hkd (finRotate (2 * d) p)) = d :=
  cycLen_of_diameter_gap d _ _ (diameter_step_gap d k hk hkd p hd)

lemma unit_step_length (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d)
    (p : Fin (2 * d)) (hd : ¬ diameterPosition d k p)
    (hl : p.val ≠ d + k - 2) :
    cycLen (2 * d) (zigzagTour d k hk hkd p)
      (zigzagTour d k hk hkd (finRotate (2 * d) p)) = 1 :=
  cycLen_of_unit_gap d (by omega) _ _ (unit_step_gap d k hk hkd p hd hl)

lemma long_length (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) :
    cycLen (2 * d) (longTail d k hk hkd) (longHead d k hk hkd) =
      if k % 2 = 0 then k - 1 else d - k + 1 := by
  unfold cycLen longTail longHead
  by_cases he : k % 2 = 0
  · simp only [he, if_true]
    rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega : 2 * d - k ≤ 2 * d - 1)]
    omega
  · simp only [he, if_false]
    rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : d - 1 ≤ 2 * d - k)]
    omega

lemma long_cost (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) (hd : Even d) :
    coeff (2 * d) (cycLen (2 * d) (longTail d k hk hkd) (longHead d k hk hkd)) =
      k - 1 := by
  rw [long_length]
  have hde : d % 2 = 0 := Nat.even_iff.mp hd
  unfold coeff
  split_ifs <;> omega

lemma long_not_diameter (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) :
    ¬ diameterPosition d k (longPosition d k hk hkd) := by
  change ¬ (d + k - 2 = 2 * d - 1 ∨
    (d - k + 1 ≤ d + k - 2 ∧ d + k - 2 < d + k - 1 ∧
      (d + k - 2 - (d - k + 1)) % 2 = 0))
  omega

lemma step_support (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) (p : Fin (2 * d)) :
    cycLen (2 * d) (zigzagTour d k hk hkd p)
      (zigzagTour d k hk hkd (finRotate (2 * d) p)) = 1 ∨
    cycLen (2 * d) (zigzagTour d k hk hkd p)
      (zigzagTour d k hk hkd (finRotate (2 * d) p)) = d ∨
    (zigzagTour d k hk hkd p = longTail d k hk hkd ∧
      zigzagTour d k hk hkd (finRotate (2 * d) p) = longHead d k hk hkd) := by
  by_cases hl : p.val = d + k - 2
  · have hp : p = longPosition d k hk hkd := Fin.ext hl
    subst p
    exact Or.inr (Or.inr ⟨long_tail_image d k hk hkd, long_head_image d k hk hkd⟩)
  · by_cases hd : diameterPosition d k p
    · exact Or.inr (Or.inl (diameter_step_length d k hk hkd p hd))
    · exact Or.inl (unit_step_length d k hk hkd p hd hl)

lemma cycLen_symm {n : ℕ} (u v : Fin n) : cycLen n u v = cycLen n v u := by
  have h : (u.val : ℤ) - v.val = -((v.val : ℤ) - u.val) := by omega
  simp only [cycLen, h, Int.natAbs_neg]

lemma support (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) (u v : Fin (2 * d))
    (huv : MetricTSP.tourVec (zigzagTour d k hk hkd) u v ≠ 0) :
    cycLen (2 * d) u v = 1 ∨ cycLen (2 * d) u v = d ∨
      (u = longTail d k hk hkd ∧ v = longHead d k hk hkd) ∨
      (v = longTail d k hk hkd ∧ u = longHead d k hk hkd) := by
  have hc : 0 < (MetricTSP.tourSteps (zigzagTour d k hk hkd) u v).card := by
    by_contra hn
    have hz := Nat.eq_zero_of_not_pos hn
    exact huv (by simp [MetricTSP.tourVec, hz])
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hc
  simp only [MetricTSP.tourSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases step_support d k hk hkd p with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases step_support d k hk hkd p with h | h | h
    · exact Or.inl ((cycLen_symm _ _).trans h)
    · exact Or.inr (Or.inl ((cycLen_symm _ _).trans h))
    · exact Or.inr (Or.inr (Or.inr h))

lemma diameter_count (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) :
    (Finset.univ.filter (diameterPosition d k)).card = k := by
  have hc : (Finset.univ.filter (diameterPosition d k)).card =
      (Finset.univ : Finset (Fin k)).card := by
    refine Finset.card_bij (fun p hp => (⟨if p.val = 2 * d - 1 then 0
        else (p.val - (d - k + 1)) / 2 + 1, ?_⟩ : Fin k)) (by simp) ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      dsimp [diameterPosition] at hp
      split_ifs <;> omega
    · intro p hp q hq he
      have heval := congrArg Fin.val he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      dsimp [diameterPosition] at hp hq
      apply Fin.ext
      dsimp at heval
      split_ifs at heval <;> omega
    · intro j _
      have hj := j.isLt
      by_cases hj0 : j.val = 0
      · refine ⟨⟨2 * d - 1, by omega⟩, ?_, ?_⟩
        · simp [diameterPosition]
        · apply Fin.ext
          dsimp
          split_ifs <;> omega
      · let p : Fin (2 * d) := ⟨d - k + 1 + 2 * (j.val - 1), by omega⟩
        have hp : p ∈ Finset.univ.filter (diameterPosition d k) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp [diameterPosition, p]
          omega
        refine ⟨p, hp, ?_⟩
        apply Fin.ext
        dsimp [p]
        split_ifs <;> omega
  simpa using hc

lemma rotate_twice_ne_self {n : ℕ} (hn : 2 < n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  let : NeZero n := ⟨by omega⟩
  intro h
  have hv := congrArg Fin.val h
  simp only [finRotate_apply, Fin.val_add, Fin.val_one'] at hv
  rw [Nat.mod_eq_of_lt (show 1 < n by omega)] at hv
  have hi := i.isLt
  by_cases h₁ : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h₁] at hv
    by_cases h₂ : i.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt h₂] at hv
      omega
    · have heq : i.val + 1 + 1 = n := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (show 1 < n by omega)] at hv
    omega

lemma tourVec_zero_or_one {n : ℕ} (hn : 2 < n) (π : Equiv.Perm (Fin n))
    (u v : Fin n) : MetricTSP.tourVec π u v = 0 ∨ MetricTSP.tourVec π u v = 1 := by
  have hc : (MetricTSP.tourSteps π u v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    simp only [MetricTSP.tourSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rcases hi with ⟨hiu, hiv⟩ | ⟨hiv, hiu⟩ <;>
      rcases hj with ⟨hju, hjv⟩ | ⟨hjv, hju⟩
    · exact π.injective (hiu.trans hju.symm)
    · have h₁ : finRotate n i = j := π.injective (hiv.trans hjv.symm)
      have h₂ : finRotate n j = i := π.injective (hju.trans hiu.symm)
      exact (rotate_twice_ne_self hn i (by rw [h₁, h₂])).elim
    · have h₁ : finRotate n i = j := π.injective (hiu.trans hju.symm)
      have h₂ : finRotate n j = i := π.injective (hjv.trans hiv.symm)
      exact (rotate_twice_ne_self hn i (by rw [h₁, h₂])).elim
    · exact π.injective (hiv.trans hjv.symm)
  have heq : (MetricTSP.tourSteps π u v).card = 0 ∨
      (MetricTSP.tourSteps π u v).card = 1 := by omega
  simpa only [MetricTSP.tourVec, Nat.cast_eq_zero, Nat.cast_eq_one] using heq


lemma long_entry (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) :
    MetricTSP.tourVec (zigzagTour d k hk hkd)
      (longTail d k hk hkd) (longHead d k hk hkd) = 1 := by
  have hp : longPosition d k hk hkd ∈ MetricTSP.tourSteps (zigzagTour d k hk hkd)
      (longTail d k hk hkd) (longHead d k hk hkd) := by
    simp only [MetricTSP.tourSteps, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨long_tail_image d k hk hkd, long_head_image d k hk hkd⟩
  have hc := Finset.card_pos.mpr ⟨_, hp⟩
  rcases tourVec_zero_or_one (by omega : 2 < 2 * d) (zigzagTour d k hk hkd)
      (longTail d k hk hkd) (longHead d k hk hkd) with hz | ho
  · have hcz : (MetricTSP.tourSteps (zigzagTour d k hk hkd)
        (longTail d k hk hkd) (longHead d k hk hkd)).card = 0 := by
      simpa only [MetricTSP.tourVec, Nat.cast_eq_zero] using hz
    omega
  · exact ho

lemma step_cost (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) (hd : Even d)
    (p : Fin (2 * d)) :
    (coeff (2 * d) (cycLen (2 * d) (zigzagTour d k hk hkd p)
      (zigzagTour d k hk hkd (finRotate (2 * d) p))) : ℝ) =
      1 - (if diameterPosition d k p then 1 else 0) +
        (if p = longPosition d k hk hkd then (k : ℝ) - 2 else 0) := by
  by_cases hl : p = longPosition d k hk hkd
  · subst p
    rw [long_tail_image, long_head_image, long_cost d k hk hkd hd]
    simp only [long_not_diameter d k hk hkd, ↓reduceIte,
      Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    ring
  · by_cases hdiam : diameterPosition d k p
    · rw [diameter_step_length d k hk hkd p hdiam]
      have hde : d % 2 = 0 := Nat.even_iff.mp hd
      simp [coeff, hde, hl, hdiam]
    · rw [unit_step_length d k hk hkd p hdiam (by
        intro h
        exact hl (Fin.ext h))]
      simp [coeff, hl, hdiam]

lemma tight (d k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d) (hd : Even d) :
    circletForm (2 * d) (MetricTSP.tourVec (zigzagTour d k hk hkd)) =
      (2 * d : ℕ) - (2 : ℝ) := by
  rw [TightProof.circletForm_tour_eq_step_sum (by omega)]
  simp_rw [step_cost d k hk hkd hd]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.natCast_card_filter, diameter_count d k hk hkd]
  simp

end CircletTSP.Facet.Zigzag


/- From C4_Assemble. -/
namespace CircletTSP.Facet.TightProof

noncomputable section

def TightLongTours.assembled {d : ℕ} {K : Type*} (H : TightLongTours d K) (hd : 2 ≤ d) :
    Fin d ⊕ (K × Fin (2*d)) → Equiv.Perm (Fin (2*d)) :=
  Sum.elim (baseFamily d hd) (H.rotation hd)

theorem TightLongTours.assembled_tight {d : ℕ} {K : Type*} (H : TightLongTours d K)
    (hd : 2 ≤ d) (heven : Even d) (i : Fin d ⊕ (K × Fin (2*d))) :
    circletForm (2*d) (MetricTSP.tourVec (H.assembled hd i)) = (2*d:ℕ)-2 := by
  cases i with
  | inl i => exact baseFamily_tight d hd heven i
  | inr i => exact H.rotation_tight hd i

theorem TightLongTours.assembled_linearIndependent {d : ℕ} {K : Type*}
    [Fintype K] [DecidableEq K] (H : TightLongTours d K) (hd : 2 ≤ d) (heven : Even d) :
    LinearIndependent ℝ (fun i => MetricTSP.tourVec (H.assembled hd i)) := by
  let : NeZero (2*d) := ⟨by omega⟩
  apply linearIndependent_sum_of_unique_and_complement_evaluations _
    (fun j => edgeEval (halfLift j-1) (halfLift j))
    (fun j => edgeEval (H.tail j.1+j.2) (H.head j.1+j.2))
  · simp only [Fintype.card_fin]; omega
  · intro i j
    exact baseFamily_unit_evaluation d hd i j
  · intro i j
    cases i with
    | inl i =>
      simp only [TightLongTours.assembled,Sum.elim_inl,edgeEval,LinearMap.coe_mk,
        AddHom.coe_mk,Sum.inl_ne_inr,if_false]
      apply baseFamily_zero_of_length_ne d hd i
      · simpa only [cycLen_add_right] using H.long_ne_unit j.1
      · simpa only [cycLen_add_right] using H.long_ne_diameter heven j.1
    | inr i =>
      simpa only [TightLongTours.assembled,Sum.elim_inr,edgeEval,LinearMap.coe_mk,
        AddHom.coe_mk,Sum.inr.injEq] using H.rotation_unique_evaluation hd heven i j

def zigzagData (d : ℕ) (_hd : 2 ≤ d) (heven : Even d) : TightLongTours d (Fin (d-2)) where
  tour i := Zigzag.zigzagTour d (i.val+3) (by omega) (by have := i.isLt; omega)
  tail i := Zigzag.longTail d (i.val+3) (by omega) (by have := i.isLt; omega)
  head i := Zigzag.longHead d (i.val+3) (by omega) (by have := i.isLt; omega)
  cost i := i.val+2
  cost_injective := by intro i j h; apply Fin.ext; dsimp at h; omega
  cost_ge_two := by intro i; omega
  long_cost := by
    intro i
    have h := Zigzag.long_cost d (i.val+3) (by omega) (by have := i.isLt; omega) heven
    simpa using h
  support := by intro i; exact Zigzag.support d (i.val+3) (by omega) (by have := i.isLt; omega)
  long_entry := by intro i; exact Zigzag.long_entry d (i.val+3) (by omega) (by have := i.isLt; omega)
  tight := by intro i; exact Zigzag.tight d (i.val+3) (by omega) (by have := i.isLt; omega) heven

theorem tight_family_card (d : ℕ) (hd : 2 ≤ d) :
    d + (d-2)*(2*d) = (2*d)*(2*d-3)/2 := by
  have hsub : 2*d-3=2*(d-2)+1 := by omega
  have hprod : 2*d*(2*(d-2)+1) = (d+(d-2)*(2*d))*2 := by ring
  rw [hsub,hprod]
  omega

theorem tight_tours_of_even_half (d : ℕ) (hd : 2 ≤ d) (heven : Even d) :
    ∃ τ : Fin ((2*d)*(2*d-3)/2) → Equiv.Perm (Fin (2*d)),
      (∀ i, circletForm (2*d) (MetricTSP.tourVec (τ i)) = (2*d:ℕ)-2) ∧
      LinearIndependent ℝ (fun i => MetricTSP.tourVec (τ i)) := by
  let H := zigzagData d hd heven
  let e : Fin ((2*d)*(2*d-3)/2) ≃ Fin d ⊕ (Fin (d-2) × Fin (2*d)) :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin,Fintype.card_sum,Fintype.card_prod]
      exact (tight_family_card d hd).symm)
  refine ⟨fun i => H.assembled hd (e i), ?_, ?_⟩
  · intro i
    exact H.assembled_tight hd heven (e i)
  · exact (H.assembled_linearIndependent hd heven).comp e e.injective

end
end CircletTSP.Facet.TightProof

open CircletTSP.Facet

theorem solution (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) :
    ∃ τ : Fin (n * (n - 3) / 2) → Equiv.Perm (Fin n),
      (∀ i, circletForm n (MetricTSP.tourVec (τ i)) = (n : ℝ) - 2) ∧
      LinearIndependent ℝ (fun i => MetricTSP.tourVec (τ i)) := by
  obtain ⟨k,hk⟩ := h4
  have hnk : n=2*(2*k) := by omega
  rw [hnk]
  exact TightProof.tight_tours_of_even_half (2*k) (by omega) (even_two_mul k)
