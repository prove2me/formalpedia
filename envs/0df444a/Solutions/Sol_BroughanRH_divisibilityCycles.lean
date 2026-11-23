-- Prove2me | solution 1 for BroughanRH.divisibilityCycles
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:45:47.640518+00:00
-- url     : https://prove2.me/submissions/e30805f8-0b55-42a7-93e6-2d264f23b81d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace BRHDiv

/-- nonempty divisibility chains inside `T` -/
def chainsNE (T : Finset ℕ) : Finset (Finset ℕ) :=
  T.powerset.filter fun S => S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, a ≤ b → a ∣ b

/-- all divisibility chains inside `T` (including `∅`) -/
def chainsAll (T : Finset ℕ) : Finset (Finset ℕ) :=
  T.powerset.filter fun S => ∀ a ∈ S, ∀ b ∈ S, a ≤ b → a ∣ b

/-- Decomposition of nonempty chains according to their largest element. -/
lemma sum_chainsNE (T : Finset ℕ) :
    ∑ S ∈ chainsNE T, (-1 : ℝ) ^ S.card
      = ∑ m ∈ T, -(∑ S ∈ chainsAll (T.filter fun d => d ∣ m ∧ d < m), (-1 : ℝ) ^ S.card) := by
  have hmaps : ∀ S ∈ chainsNE T, S.sup id ∈ T := by
    intro S hS
    simp only [chainsNE, mem_filter, mem_powerset] at hS
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup S hS.2.1 id
    rw [hxe]; exact hS.1 hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun m hm => ?_
  rw [← sum_neg_distrib]
  refine Finset.sum_nbij' (fun S => S.erase m) (fun S => insert m S) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [chainsNE, mem_filter, mem_powerset] at hS
    obtain ⟨⟨hST, hne, hch⟩, hsup⟩ := hS
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup S hne id
    have hmS : m ∈ S := by rw [← hsup, hxe]; exact hx
    simp only [chainsAll, mem_filter, mem_powerset]
    refine ⟨fun d hd => ?_, fun a ha b hb hab => hch a (mem_of_mem_erase ha) b (mem_of_mem_erase hb) hab⟩
    have hdS := mem_of_mem_erase hd
    have hdm : d ≠ m := ne_of_mem_erase hd
    have hle : d ≤ m := by rw [← hsup]; exact Finset.le_sup (f := id) hdS
    refine mem_filter.2 ⟨hST hdS, hch d hdS m hmS hle, lt_of_le_of_ne hle hdm⟩
  · intro S hS
    simp only [chainsAll, mem_filter, mem_powerset] at hS
    obtain ⟨hST, hch⟩ := hS
    have hlt : ∀ d ∈ S, d ∣ m ∧ d < m := fun d hd => (mem_filter.1 (hST hd)).2
    simp only [chainsNE, mem_filter, mem_powerset]
    refine ⟨⟨?_, insert_nonempty _ _, ?_⟩, ?_⟩
    · intro d hd
      rcases mem_insert.1 hd with rfl | hd
      · exact hm
      · exact (mem_filter.1 (hST hd)).1
    · intro a ha b hb hab
      rcases mem_insert.1 ha with ha | ha <;> rcases mem_insert.1 hb with hb | hb
      · rw [ha, hb]
      · rw [ha] at hab; exact absurd hab (not_le.2 (hlt b hb).2)
      · rw [hb]; exact (hlt a ha).1
      · exact hch a ha b hb hab
    · rw [sup_insert]
      apply le_antisymm
      · exact sup_le (le_refl _) (Finset.sup_le fun d hd => (hlt d hd).2.le)
      · exact le_sup_left
  · intro S hS
    simp only [chainsNE, mem_filter, mem_powerset] at hS
    obtain ⟨⟨_, hne, _⟩, hsup⟩ := hS
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup S hne id
    have hmS : m ∈ S := by rw [← hsup, hxe]; exact hx
    exact insert_erase hmS
  · intro S hS
    simp only [chainsAll, mem_filter, mem_powerset] at hS
    have : m ∉ S := fun h => lt_irrefl m (mem_filter.1 (hS.1 h)).2.2
    exact erase_insert this
  · intro S hS
    simp only [chainsNE, mem_filter, mem_powerset] at hS
    obtain ⟨⟨_, hne, _⟩, hsup⟩ := hS
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup S hne id
    have hmS : m ∈ S := by rw [← hsup, hxe]; exact hx
    rw [← card_erase_add_one hmS, pow_succ]
    ring

lemma sum_chainsAll (T : Finset ℕ) :
    ∑ S ∈ chainsAll T, (-1 : ℝ) ^ S.card = 1 + ∑ S ∈ chainsNE T, (-1 : ℝ) ^ S.card := by
  have h : chainsAll T = insert ∅ (chainsNE T) := by
    ext S
    simp only [chainsAll, chainsNE, mem_filter, mem_powerset, mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases S.eq_empty_or_nonempty with rfl | hne
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, hne, h2⟩
    · rintro (rfl | ⟨h1, _, h2⟩)
      · simp
      · exact ⟨h1, h2⟩
  have hn : (∅ : Finset ℕ) ∉ chainsNE T := by simp [chainsNE]
  rw [h, sum_insert hn]; simp

/-- proper divisors of `m` that are at least `2` -/
def D (m : ℕ) : Finset ℕ := (Icc 2 m).filter fun d => d ∣ m ∧ d < m

lemma filter_D {m0 m : ℕ} (hm : m ∈ D m0) : ((D m0).filter fun d => d ∣ m ∧ d < m) = D m := by
  simp only [D, mem_filter, mem_Icc] at hm
  ext d
  simp only [D, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h2, _⟩, _, _⟩, hdm, hlt⟩
    exact ⟨⟨h2, hlt.le⟩, hdm, hlt⟩
  · rintro ⟨⟨h2, _⟩, hdm, hlt⟩
    exact ⟨⟨⟨h2, by omega⟩, dvd_trans hdm hm.2.1, by omega⟩, hdm, hlt⟩

lemma filter_Icc {N m : ℕ} (hm : m ∈ Icc 2 N) : ((Icc 2 N).filter fun d => d ∣ m ∧ d < m) = D m := by
  rw [mem_Icc] at hm
  ext d
  simp only [D, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨h2, _⟩, hdm, hlt⟩; exact ⟨⟨h2, hlt.le⟩, hdm, hlt⟩
  · rintro ⟨⟨h2, _⟩, hdm, hlt⟩; exact ⟨⟨h2, by omega⟩, hdm, hlt⟩

lemma divisors_eq (m : ℕ) (hm : 2 ≤ m) : m.divisors = insert 1 (insert m (D m)) := by
  ext d
  simp only [Nat.mem_divisors, mem_insert, D, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hd, _⟩
    have := Nat.le_of_dvd (by omega) hd
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d ≠ 0 := by rintro rfl; simp at hd; omega
      left; omega
    · rcases eq_or_lt_of_le this with h' | h'
      · right; left; exact h'
      · right; right; exact ⟨⟨h, this⟩, hd, h'⟩
  · rintro (rfl | rfl | ⟨_, hd, _⟩)
    · exact ⟨one_dvd _, by omega⟩
    · exact ⟨dvd_refl _, by omega⟩
    · exact ⟨hd, by omega⟩

lemma sum_mu_D (m : ℕ) (hm : 2 ≤ m) : ((μ m : ℤ) : ℝ) = -1 - ∑ d ∈ D m, ((μ d : ℤ) : ℝ) := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, ArithmeticFunction.one_apply, if_neg (show m ≠ 1 by omega)] at h
  rw [divisors_eq m hm] at h
  have h1 : (1 : ℕ) ∉ insert m (D m) := by simp [D]; omega
  have h2 : m ∉ D m := by simp [D]
  rw [sum_insert h1, sum_insert h2] at h
  have h' : ((μ 1 + (μ m + ∑ x ∈ D m, μ x) : ℤ) : ℝ) = 0 := by exact_mod_cast h
  push_cast at h'
  simp at h'
  linarith

/-- the signed chain count below `m` equals `-μ(m)` -/
lemma key (m : ℕ) (hm : 2 ≤ m) : -(∑ S ∈ chainsAll (D m), (-1 : ℝ) ^ S.card) = ((μ m : ℤ) : ℝ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [sum_chainsAll, sum_chainsNE, sum_mu_D m hm]
    have : ∑ x ∈ D m, -(∑ S ∈ chainsAll ((D m).filter fun d => d ∣ x ∧ d < x), (-1 : ℝ) ^ S.card)
        = ∑ d ∈ D m, ((μ d : ℤ) : ℝ) := by
      refine sum_congr rfl fun d hd => ?_
      rw [filter_D hd]
      have hd' := hd
      simp only [D, mem_filter, mem_Icc] at hd'
      exact ih d hd'.2.2 hd'.1.1
    rw [this]; ring

lemma chains_sum (N : ℕ) :
    ∑ S ∈ chainsNE (Icc 2 N), (-1 : ℝ) ^ S.card = ∑ m ∈ Icc 2 N, ((μ m : ℤ) : ℝ) := by
  rw [sum_chainsNE]
  refine sum_congr rfl fun m hm => ?_
  rw [filter_Icc hm]
  exact key m (mem_Icc.1 hm).1

lemma Icc_one (N : ℕ) (hN : 1 ≤ N) : ∑ m ∈ Icc 1 N, ((μ m : ℤ) : ℝ) = 1 + ∑ m ∈ Icc 2 N, ((μ m : ℤ) : ℝ) := by
  have : Icc 1 N = insert 1 (Icc 2 N) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  rw [this, sum_insert (by simp)]
  simp

end BRHDiv

open BRHDiv in
theorem solution :
    let chains (N : ℕ) := (Finset.Icc 2 N).powerset.filter fun S =>
      S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, a ≤ b → a ∣ b
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ S ∈ chains N, (-1 : ℝ)^S.card)
      (fun N : ℕ => (N : ℝ)^(1/2 + ε)) := by
  intro chains ε hε
  have hM := moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis ε hε
  have hM' : Asymptotics.IsBigO Filter.atTop (fun N : ℕ => ∑ m ∈ Icc 1 N, ((μ m : ℤ) : ℝ))
      (fun N : ℕ => (N : ℝ)^(1/2 + ε)) := by
    refine Asymptotics.IsBigO.trans ?_ hM
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun N => ?_)
    have hc : (((∑ m ∈ Icc 1 N, ((μ m : ℤ) : ℝ)) : ℝ) : ℂ) = ∑ m ∈ Icc 1 N, ((μ m : ℤ) : ℂ) := by
      push_cast; rfl
    rw [one_mul, ← hc, Complex.norm_real]
  have h1 : Asymptotics.IsBigO Filter.atTop (fun _ : ℕ => (1 : ℝ)) (fun N : ℕ => (N : ℝ)^(1/2 + ε)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rw [norm_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  refine (hM'.sub h1).congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  show _ = ∑ S ∈ chainsNE (Icc 2 N), (-1 : ℝ) ^ S.card
  rw [chains_sum, Icc_one N hN]; ring
