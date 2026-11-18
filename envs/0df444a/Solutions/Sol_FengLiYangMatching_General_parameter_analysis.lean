-- Prove2me | solution 1 for FengLiYangMatching.General.parameter_analysis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:53:39.600307+00:00
-- url     : https://prove2.me/submissions/5c184f32-1b30-4e16-bc2b-c4e07e2d14a2

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset
open scoped BigOperators
namespace FengLiYangMatching.General
noncomputable section

def F (a : ℝ) : ℝ := L 1 a (3/8) - L 12 a (3/8)

lemma F_formula (a : ℝ) : F a = 5/8 - 5/11*a - 6/11 + (1-a)^12/264 + (17/120 : ℝ)*(5/8)^12 := by
  norm_num [F,L]
  ring

lemma F_anti : StrictAntiOn F (Set.Icc (0 : ℝ) (3/8)) := by
  intro a ha b hb hab
  have hp : (1-b)^12 ≤ (1-a)^12 := pow_le_pow_left₀ (by linarith [hb.2]) (by linarith) 12
  rw [F_formula, F_formula]
  nlinarith

lemma exists_root : ∃ a : ℝ, Root a := by
  let lo : ℝ := 1769129/10000000
  let hi : ℝ := 176913/1000000
  have hc : Continuous F := by unfold F L; fun_prop
  have hlo : 0 ≤ F lo := by norm_num [lo, F_formula]
  have hhi : F hi ≤ 0 := by norm_num [hi, F_formula]
  have hex := intermediate_value_Icc' (show lo ≤ hi by norm_num [lo,hi]) hc.continuousOn
  obtain ⟨a, ha, he⟩ := hex ⟨hhi, hlo⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · dsimp [lo] at ha; linarith [ha.1]
  · dsimp [hi] at ha; linarith [ha.2]
  · exact sub_eq_zero.mp he

lemma root_unique : ∃! a : ℝ, Root a := by
  obtain ⟨a, ha⟩ := exists_root
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply F_anti.injOn ⟨le_of_lt hb.1, le_of_lt hb.2.1⟩ ⟨le_of_lt ha.1, le_of_lt ha.2.1⟩
  simp [F, hb.2.2, ha.2.2]

lemma aStar_root : Root aStar := by
  unfold aStar
  rw [dif_pos exists_root]
  exact Classical.choose_spec exists_root

lemma root_bracket {a : ℝ} (ha : Root a) :
    1769129/10000000 ≤ a ∧ a ≤ 176913/1000000 := by
  have hz : F a = 0 := sub_eq_zero.mpr ha.2.2
  constructor
  · by_contra h
    have := F_anti ⟨le_of_lt ha.1, le_of_lt ha.2.1⟩
      (show (1769129/10000000 : ℝ) ∈ Set.Icc 0 (3/8) by norm_num) (lt_of_not_ge h)
    have : 0 < F (1769129/10000000) := by norm_num [F_formula]
    linarith
  · by_contra h
    have := F_anti (show (176913/1000000 : ℝ) ∈ Set.Icc 0 (3/8) by norm_num)
      ⟨le_of_lt ha.1, le_of_lt ha.2.1⟩ (lt_of_not_ge h)
    have : F (176913/1000000) < 0 := by norm_num [F_formula]
    linarith

lemma root_value_bounds {a : ℝ} (ha : Root a) :
    (1/6 : ℝ) < a ∧ (1089/2000 : ℝ) < L 1 a (3/8) ∧ L 1 a (3/8) < (544586/1000000 : ℝ) := by
  obtain ⟨hlo,hhi⟩ := root_bracket ha
  norm_num [L]
  constructor
  · linarith
  · constructor <;> linarith

lemma L_split (k : ℕ) (a : ℝ) :
    L k a (3/8) = 6/11 + (1/(2*(k:ℝ)) - 1/22)*(1-a)^k -
      (1/(2*(k:ℝ)) + 1/10)*(5/8)^k := by
  unfold L
  norm_num
  ring

set_option maxHeartbeats 800000 in
lemma L_finite {a : ℝ} (ha : Root a) {k : ℕ} (hk : 2 ≤ k) (hk' : k ≤ 15) (hne : k ≠ 12) :
    (544586/1000000 : ℝ) < L k a (3/8) := by
  obtain ⟨hlo,hhi⟩ := root_bracket ha
  have hp0 : (1 - 176913/1000000 : ℝ)^k ≤ (1-a)^k :=
    pow_le_pow_left₀ (by norm_num) (by linarith) k
  have hp1 : (1-a)^k ≤ (1 - 1769129/10000000 : ℝ)^k :=
    pow_le_pow_left₀ (by linarith [ha.2.1]) (by linarith) k
  rw [L_split]
  interval_cases k <;> norm_num at * <;> nlinarith

end
end FengLiYangMatching.General

namespace FengLiYangMatching.General

lemma A_step {a : ℝ} (ha : (1/6 : ℝ) ≤ a) (ha1 : a ≤ 1) (n : ℕ) (hn : 15 ≤ n) :
    (1/22 - 1/(2*((n:ℝ)+1)))*(1-a) ≤ (1/22 - 1/(2*(n:ℝ))) := by
  have hn' : (15:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n:ℝ) := by linarith
  have hpos1 : 0 < (n:ℝ)+1 := by linarith
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_nonneg (le_of_lt hpos) (show 0 ≤ (n:ℝ)-10 by linarith)),
    mul_nonneg (show 0 ≤ (n:ℝ)-15 by linarith) (show 0 ≤ (n:ℝ)-10 by linarith)]

lemma L_tail_step {a : ℝ} (ha : (1/6 : ℝ) ≤ a) (ha1 : a ≤ 1) (n : ℕ) (hn : 15 ≤ n) :
    L n a (3/8) ≤ L (n+1) a (3/8) := by
  have hn' : (15:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n:ℝ) := by linarith
  have hpos1 : 0 < (n:ℝ)+1 := by linarith
  have hA := mul_le_mul_of_nonneg_right (A_step ha ha1 n hn) (pow_nonneg (sub_nonneg.mpr ha1) n)
  have hBi : (1/(2*((n:ℝ)+1)) + 1/10)*(5/8) ≤ (1/(2*(n:ℝ)) + 1/10) := by
    field_simp
    nlinarith [sq_nonneg (n:ℝ)]
  have hB := mul_le_mul_of_nonneg_right hBi (show 0 ≤ (5/8:ℝ)^n by positivity)
  rw [L_split, L_split, pow_succ, pow_succ]
  push_cast
  nlinarith

lemma L_tail {a : ℝ} (ha : Root a) {n : ℕ} (hn : 15 ≤ n) :
    L 15 a (3/8) ≤ L n a (3/8) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    exact ih.trans (L_tail_step (le_of_lt (root_value_bounds ha).1) (by linarith [ha.2.1]) k hk)

lemma L_all {a : ℝ} (ha : Root a) (k : ℕ) (hk : 1 ≤ k) :
    L 1 a (3/8) ≤ L k a (3/8) := by
  by_cases h1 : k = 1
  · subst k; rfl
  by_cases h12 : k = 12
  · subst k; exact le_of_eq ha.2.2
  by_cases h15 : k ≤ 15
  · exact (le_of_lt (root_value_bounds ha).2.2).trans (le_of_lt (L_finite ha (by omega) h15 h12))
  · exact (le_of_lt (root_value_bounds ha).2.2).trans
      ((le_of_lt (L_finite ha (k:=15) (by omega) (by omega) (by omega))).trans (L_tail ha (by omega)))

end FengLiYangMatching.General

open FengLiYangMatching.General
theorem solution :
    (∃! a : ℝ, Root a) ∧ Root aStar ∧ (1/6 : ℝ) < aStar ∧
    (∀ k : ℕ, 1 ≤ k → L k aStar (3/8) ≥ L 1 aStar (3/8)) ∧
    L 1 aStar (3/8) > (1089/2000 : ℝ) := by
  exact ⟨root_unique, aStar_root, (root_value_bounds aStar_root).1, L_all aStar_root, (root_value_bounds aStar_root).2.1⟩
