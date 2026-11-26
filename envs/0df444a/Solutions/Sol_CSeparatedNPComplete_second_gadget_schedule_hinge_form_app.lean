-- Prove2me | solution 1 for CSeparatedNPComplete.second_gadget_schedule_hinge_form_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:34.006114+00:00
-- url     : https://prove2.me/submissions/b71c3c2c-ab96-46b4-8b95-5fe6b0314ba9

module
public import Definitions.Def_CSeparatedNPComplete_Schedule
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_CrossGadget
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_diagonal_mono
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_ge_1
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_nonneg
public import Theorems.Thm_CSeparatedNPComplete_hinge_against_eq_zero
public import Theorems.Thm_CSeparatedNPComplete_hinge_form_app_no_cross

section
@[expose] public section
namespace CSeparatedNPComplete
private theorem cross_dot_const {n : ℕ} (a : Vec n) (r : ℝ) :
    dot a (fun _ => r) = r * dot a 1 := by
  simp only [dot, Pi.one_apply, mul_one, ← Finset.sum_mul]
  ring
private theorem cross_dot_mono {n : ℕ} {a u v : Vec n}
    (ha : ∀ i, 0 ≤ a i) (huv : ∀ i, u i ≤ v i) : dot a u ≤ dot a v := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (huv i) (ha i)
private theorem cross_gamma_ge_one {n : ℕ} {m : ℝ} (hm : 2 ≤ m) :
    1 ≤ second_gadget_gamma n m := by
  have hs := gaussian_schedule_separation_sum_nonneg m n n
  unfold second_gadget_gamma
  linarith
private theorem cross_schedule_covariance_bounds {n : ℕ} {m : ℝ} {a : Vec n}
    (hm : 2 ≤ m) (ha : box_constraints a) (hsum : dot a 1 = m)
    {j : ℕ} (hjn : j ≤ n) :
    0 < dot a (gaussian_schedule_sigma m j) ∧
      dot a (gaussian_schedule_sigma m j) ≤ (second_gadget_gamma n m) ^ 2 * m := by
  have hm0 : 0 ≤ m := by linarith
  have hg := cross_gamma_ge_one (n := n) hm
  have hsn := gaussian_schedule_separation_sum_nonneg m n n
  have hupper : gaussian_schedule_separation_sum m n n * (m + 1) ≤
      (second_gadget_gamma n m) ^ 2 := by
    unfold second_gadget_gamma
    nlinarith [sq_nonneg m, sq_nonneg (gaussian_schedule_separation_sum m n n),
      mul_nonneg (show 0 ≤ m - 1 by linarith) hsn]
  have hcoord : ∀ i : Fin n, 1 ≤ gaussian_schedule_sigma m j i ∧
      gaussian_schedule_sigma m j i ≤ (second_gadget_gamma n m) ^ 2 := by
    intro i
    by_cases hj : j = 0
    · simp only [gaussian_schedule_sigma, if_pos hj, Pi.one_apply]
      constructor
      · rfl
      · nlinarith
    · have hs1 := gaussian_schedule_separation_sum_ge_1 hm (Nat.pos_of_ne_zero hj)
      have hs0 := gaussian_schedule_separation_sum_nonneg m j j
      have hsle := gaussian_schedule_separation_sum_diagonal_mono hm hjn
      have he : 0 ≤ canon_e (j - 1) i ∧ canon_e (j - 1) i ≤ 1 := by
        simp only [canon_e]
        split_ifs <;> norm_num
      have haxis : 1 ≤ m * canon_e (j - 1) i + 1 ∧ m * canon_e (j - 1) i + 1 ≤ m + 1 := by
        constructor
        · nlinarith [mul_nonneg hm0 he.1]
        · nlinarith [mul_le_mul_of_nonneg_left he.2 hm0]
      simp only [gaussian_schedule_sigma, if_neg hj]
      constructor
      · nlinarith [mul_le_mul hs1 haxis.1 (by norm_num : (0 : ℝ) ≤ 1) hs0]
      · exact (mul_le_mul hsle haxis.2 (by linarith) hsn).trans hupper
  constructor
  · have hl := cross_dot_mono ha.1 (fun i => (hcoord i).1)
    change dot a 1 ≤ dot a (gaussian_schedule_sigma m j) at hl
    rw [hsum] at hl
    linarith
  · have hu := cross_dot_mono ha.1 (fun i => (hcoord i).2)
    rw [cross_dot_const, hsum] at hu
    exact hu
private theorem cross_mean_gap {n j : ℕ} {m : ℝ} (hm : 2 ≤ m) (hn : 0 < n) (hj : j ≤ n) :
    second_gadget_gamma n m * (m - 1) ≤
      second_gadget_gamma n m * m ^ n - m ^ j := by
  have hm1 : 1 ≤ m := by linarith
  have hg : m ≤ second_gadget_gamma n m := by
    unfold second_gadget_gamma
    exact le_add_of_nonneg_right (gaussian_schedule_separation_sum_nonneg m n n)
  have hpn : m ≤ m ^ n := le_self_pow₀ hm1 (by omega)
  have hpj : m ^ j ≤ m ^ n := pow_le_pow_right₀ hm1 hj
  nlinarith [mul_le_mul_of_nonneg_left hpn
    (show 0 ≤ second_gadget_gamma n m - 1 by linarith)]
private theorem cross_pair_zero {n : ℕ} {m c gap : ℝ} {a : Vec n}
    {g : Gaussian n} {j : ℕ} (ha : box_constraints a) (hsum : dot a 1 = m)
    (hc : 0 ≤ c) (hgap0 : 0 ≤ gap)
    (hgap : ∀ i, gap ≤ g.1 i - m ^ j)
    (hpositive : 0 < dot a (gaussian_schedule_sigma m j))
    (hleft : c * dot a g.2 ≤ gap ^ 2 * m)
    (hright : c * dot a (gaussian_schedule_sigma m j) ≤ gap ^ 2 * m) :
    gaussian_pair_hinge c a g (gaussian_schedule_class m j) = 0 := by
  have hdistance : gap ^ 2 * m ≤ dot a (sqVec (g.1 - gaussian_schedule_mu m j)) := by
    have h := cross_dot_mono ha.1 (fun i =>
      show gap ^ 2 ≤ sqVec (g.1 - gaussian_schedule_mu m j) i from by
        change gap ^ 2 ≤ (g.1 i - m ^ j) * (g.1 i - m ^ j)
        nlinarith [hgap i])
    rw [cross_dot_const, hsum] at h
    exact h
  have hdenom : 0 < max (dot a g.2) (dot a (gaussian_schedule_sigma m j)) :=
    hpositive.trans_le (le_max_right _ _)
  have hbound : c * max (dot a g.2) (dot a (gaussian_schedule_sigma m j)) ≤
      dot a (sqVec (g.1 - gaussian_schedule_mu m j)) := by
    rw [mul_max_of_nonneg _ _ hc]
    exact max_le (hleft.trans hdistance) (hright.trans hdistance)
  unfold gaussian_pair_hinge gaussian_pair_stats gaussian_schedule_class
  dsimp
  unfold hinge
  exact max_eq_left (sub_nonpos.mpr ((le_div_iff₀ hdenom).mpr hbound))
private theorem cross_scale_bound {m x t : ℝ} (hm : 0 ≤ m) (h : x ≤ t ^ 2)
    (gamma : ℝ) : x * (gamma ^ 2 * m) ≤ (gamma * t) ^ 2 * m := by
  calc
    x * (gamma ^ 2 * m) ≤ t ^ 2 * (gamma ^ 2 * m) :=
      mul_le_mul_of_nonneg_right h (mul_nonneg (sq_nonneg _) hm)
    _ = (gamma * t) ^ 2 * m := by ring
private theorem cross_pair_one {n : ℕ} {m c : ℝ} {a : Vec n}
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : box_constraints a) (hsum : dot a 1 = m)
    {j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    gaussian_pair_hinge c a (second_gadget_g1 m c) (gaussian_schedule_class m j) = 0 := by
  let gamma := second_gadget_gamma n m
  have hg : 1 ≤ gamma := cross_gamma_ge_one hm
  have hm0 : 0 ≤ m := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hbase := cross_mean_gap hm hn hj
  change gamma * (m - 1) ≤ gamma * m ^ n - m ^ j at hbase
  have hcov := cross_schedule_covariance_bounds hm ha hsum hj
  have hsmall : c ≤ (c + m) ^ 2 := by nlinarith [sq_nonneg c, sq_nonneg m]
  have hscale := cross_scale_bound hm0 hsmall gamma
  apply cross_pair_zero ha hsum hc0 (mul_nonneg (by linarith) (by linarith))
    (gap := gamma * (c + m))
  · intro i
    change gamma * (c + m) ≤ gamma * (3 * c + m ^ n) - m ^ j
    nlinarith
  · exact hcov.1
  · change c * dot a (fun _ => gamma * gamma) ≤ (gamma * (c + m)) ^ 2 * m
    rw [cross_dot_const, hsum]
    nlinarith only [hscale]
  · exact (mul_le_mul_of_nonneg_left hcov.2 hc0).trans hscale
private theorem cross_pair_two {n : ℕ} {m c : ℝ} {a s : Vec n}
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : box_constraints a) (hsum : dot a 1 = m)
    {j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    gaussian_pair_hinge c a (second_gadget_g2 m c s) (gaussian_schedule_class m j) = 0 := by
  let gamma := second_gadget_gamma n m
  have hg : 1 ≤ gamma := cross_gamma_ge_one hm
  have hm0 : 0 ≤ m := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hbase := cross_mean_gap hm hn hj
  change gamma * (m - 1) ≤ gamma * m ^ n - m ^ j at hbase
  have hcov := cross_schedule_covariance_bounds hm ha hsum hj
  have hsmall : c ≤ (c + m) ^ 2 := by nlinarith [sq_nonneg c, sq_nonneg m]
  have hlarge : c * m ≤ (c + m) ^ 2 := by
    nlinarith [sq_nonneg c, sq_nonneg m, mul_nonneg hc0 hm0]
  apply cross_pair_zero ha hsum hc0 (mul_nonneg (by linarith) (by linarith))
    (gap := gamma * (c + m))
  · intro i
    change gamma * (c + m) ≤ gamma * (3 * c + m ^ n + m * Real.sqrt (s i)) - m ^ j
    have hroot : 0 ≤ gamma * (m * Real.sqrt (s i)) :=
      mul_nonneg (by linarith) (mul_nonneg hm0 (Real.sqrt_nonneg _))
    nlinarith
  · exact hcov.1
  · change c * dot a (fun _ => gamma * gamma * m) ≤ (gamma * (c + m)) ^ 2 * m
    rw [cross_dot_const, hsum]
    have hscale := cross_scale_bound hm0 hlarge gamma
    nlinarith only [hscale]
  · exact (mul_le_mul_of_nonneg_left hcov.2 hc0).trans (cross_scale_bound hm0 hsmall gamma)
private theorem cross_pair_three {n : ℕ} {m c : ℝ} {a s : Vec n}
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : box_constraints a) (hs : is_vec_leq 0 s)
    (hsum : dot a 1 = m) (hstotal : dot s 1 = 2 * c)
    {j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    gaussian_pair_hinge c a (second_gadget_g3 m c s) (gaussian_schedule_class m j) = 0 := by
  let gamma := second_gadget_gamma n m
  have hg : 1 ≤ gamma := cross_gamma_ge_one hm
  have hm0 : 0 ≤ m := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hbase := cross_mean_gap hm hn hj
  change gamma * (m - 1) ≤ gamma * m ^ n - m ^ j at hbase
  have hcov := cross_schedule_covariance_bounds hm ha hsum hj
  have hsmall : c ≤ (2 * c) ^ 2 := by nlinarith
  have has : dot a s ≤ 2 * c := by
    calc
      dot a s ≤ dot s 1 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Pi.one_apply, mul_one, one_mul] using
          mul_le_mul_of_nonneg_right (ha.2 i) (hs i)
      _ = 2 * c := hstotal
  have hlarge : c * dot a s ≤ (2 * c) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left has hc0, sq_nonneg c]
  apply cross_pair_zero ha hsum hc0 (mul_nonneg (by linarith) (by linarith))
    (gap := gamma * (2 * c))
  · intro i
    change gamma * (2 * c) ≤ gamma * (2 * c + m ^ n) - m ^ j
    nlinarith
  · exact hcov.1
  · change c * dot a (fun i => gamma * gamma * m * s i) ≤ (gamma * (2 * c)) ^ 2 * m
    have hdot : dot a (fun i => gamma * gamma * m * s i) = gamma ^ 2 * m * dot a s := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hdot]
    have hscale := cross_scale_bound hm0 hlarge gamma
    nlinarith only [hscale]
  · exact (mul_le_mul_of_nonneg_left hcov.2 hc0).trans (cross_scale_bound hm0 hsmall gamma)
end CSeparatedNPComplete
end
end

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : ℕ} (m c : ℝ) (a s : Vec n)
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : box_constraints a) (hs : is_vec_leq 0 s)
    (hsum : dot a 1 = m) (hstotal : dot s 1 = 2 * c) (hn : 0 < n) :
    hinge_form c a (second_gadget_instance m c s ++ gaussian_schedule m (n + 1)) =
      hinge_form c a (second_gadget_instance m c s) +
        hinge_form c a (gaussian_schedule m (n + 1)) := by
  apply hinge_form_app_no_cross
  intro g hg
  apply hinge_against_eq_zero
  intro h hh
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hh
  have hjn : j ≤ n := by have := List.mem_range.mp hj; omega
  simp only [second_gadget_instance, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact cross_pair_one hm hc ha hsum hn hjn
  · exact cross_pair_two hm hc ha hsum hn hjn
  · exact cross_pair_three hm hc ha hs hsum hstotal hn hjn
end CSeparatedNPComplete
