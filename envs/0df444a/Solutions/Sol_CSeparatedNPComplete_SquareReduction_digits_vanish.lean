-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.digits_vanish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:44.029804+00:00
-- url     : https://prove2.me/submissions/d276c08a-44fa-448d-978a-1df753eb6e53

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hlarge : (n : ℝ) + C < K ^ 2) (d : Fin n → ℝ)
    (hd : ∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) (e : ℝ)
    (he : |e| ≤ C * K ^ (2 * n))
    (hzero : (∑ i, d i * K ^ (2 * n + 2 * i.val + 2)) + e = 0) :
    ∀ i, d i = 0 := by
  classical
  by_contra h
  have hn : (Finset.univ.filter fun i => d i ≠ 0).Nonempty := by
    simpa only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and, not_forall] using h
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image _ (fun i : Fin n => i.val) hn
  have hjne : d j ≠ 0 := (Finset.mem_filter.mp hj).2
  let T := K ^ (2 * n + 2 * j.val)
  have hT : 0 < T := by dsimp [T]; positivity
  have hbase : K ^ (2 * n) ≤ T := pow_le_pow_right₀ hK (by omega)
  have hjabs : |d j| = 1 := by rcases hd j with h | h | h <;> simp_all
  have hsmall (i : Fin n) (hi : i ∈ Finset.univ.erase j) :
      |d i * K ^ (2 * n + 2 * i.val + 2)| ≤ T := by
    by_cases hz : d i = 0
    · simp [hz, hT.le]
    have hij : i.val < j.val := by
      have hle := hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
      have hne := (Finset.mem_erase.mp hi).1
      have : i.val ≠ j.val := fun hv => hne (Fin.ext hv)
      omega
    have habs : |d i| = 1 := by rcases hd i with h | h | h <;> simp_all
    rw [abs_mul, habs, one_mul, abs_of_nonneg (by positivity)]
    exact pow_le_pow_right₀ hK (by omega)
  have hsum : |∑ i ∈ Finset.univ.erase j, d i * K ^ (2 * n + 2 * i.val + 2)| ≤ (n : ℝ) * T := by
    calc
      _ ≤ ∑ i ∈ Finset.univ.erase j, |d i * K ^ (2 * n + 2 * i.val + 2)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.univ.erase j, T := Finset.sum_le_sum hsmall
      _ ≤ (n : ℝ) * T := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (show (Finset.univ.erase j).card ≤ n from
          (Finset.card_le_card (Finset.erase_subset j Finset.univ)).trans_eq (Finset.card_fin n))
  have hexpand : K ^ (2 * n + 2 * j.val + 2) = K ^ 2 * T := by
    dsimp [T]
    rw [pow_add, mul_comm]
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun i : Fin n => d i * K ^ (2 * n + 2 * i.val + 2)) (Finset.mem_univ j)
  have hlead : |d j * K ^ (2 * n + 2 * j.val + 2)| ≤ (n : ℝ) * T + C * T := by
    calc
      _ = |(∑ i ∈ Finset.univ.erase j, d i * K ^ (2 * n + 2 * i.val + 2)) + e| := by
        have : d j * K ^ (2 * n + 2 * j.val + 2) =
            -((∑ i ∈ Finset.univ.erase j, d i * K ^ (2 * n + 2 * i.val + 2)) + e) := by linarith
        rw [this, abs_neg]
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hsum (he.trans (mul_le_mul_of_nonneg_left hbase hC)))
  rw [abs_mul, hjabs, one_mul, abs_of_nonneg (by positivity), hexpand] at hlead
  nlinarith
end CSeparatedNPComplete.SquareReduction
