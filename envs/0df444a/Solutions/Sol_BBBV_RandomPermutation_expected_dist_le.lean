-- Prove2me | solution 1 for BBBV.RandomPermutation.expected_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T06:36:08.839626+00:00
-- url     : https://prove2.me/submissions/79ac275b-8851-4d05-b4fa-f1d94cd9ba24

import Definitions.Def_BBBV_RandomPermutation_Chain
import Theorems.Thm_BBBV_RandomPermutation_theorem_3_3
import Theorems.Thm_BBBV_RandomPermutation_expected_queryMag_le

noncomputable section
open Classical Finset BBBV.RandomPermutation
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace WentaoBBBVExpected

private lemma query_nonneg {n : ℕ} {W : Type} [Fintype W]
    (y : BBBV.RandomOracle.Str n)
    (φ : State (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W) :
    0 ≤ queryMag y φ := by
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

private lemma avg_mono {n T : ℕ} (f g : Ω n T → ℝ) (h : ∀ ω, f ω ≤ g ω) :
    avg f ≤ avg g := by
  unfold avg
  exact div_le_div_of_nonneg_right (sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

private lemma avg_const {n T : ℕ} (c : ℝ) : avg (fun _ : Ω n T => c) = c := by
  have hc : (Fintype.card (Ω n T) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [avg, hc]

private lemma avg_mul {n T : ℕ} (c : ℝ) (f : Ω n T → ℝ) :
    avg (fun ω => c * f ω) = c * avg f := by
  unfold avg
  rw [← mul_sum]
  ring

private lemma avg_add {n T : ℕ} (f g : Ω n T → ℝ) :
    avg (fun ω => f ω + g ω) = avg f + avg g := by
  simp only [avg, sum_add_distrib, add_div]

private lemma avg_sum {n T : ℕ} {ι : Type} (s : Finset ι) (f : ι → Ω n T → ℝ) :
    avg (fun ω => ∑ j ∈ s, f j ω) = ∑ j ∈ s, avg (f j) := by
  unfold avg
  rw [sum_comm, sum_div]

private lemma avg_sqrt_le {n T : ℕ} (z : Ω n T → ℝ) (hz : ∀ ω, 0 ≤ z ω)
    (c : ℝ) (hc : 0 ≤ c) (hmean : avg z ≤ c ^ 2) :
    avg (fun ω => Real.sqrt (z ω)) ≤ c := by
  have hΩ : (0 : ℝ) < Fintype.card (Ω n T) := by exact_mod_cast Fintype.card_pos
  unfold avg at hmean ⊢
  rw [div_le_iff₀ hΩ] at hmean ⊢
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset (Ω n T))
    (fun ω => Real.sqrt (z ω)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at hcs
  simp_rw [Real.sq_sqrt (hz _)] at hcs
  have hmul := mul_le_mul_of_nonneg_right hmean hΩ.le
  have hsq : (∑ ω : Ω n T, Real.sqrt (z ω)) ^ 2 ≤
      (c * (Fintype.card (Ω n T) : ℝ)) ^ 2 := by nlinarith
  exact (sq_le_sq₀ (sum_nonneg fun _ _ => Real.sqrt_nonneg _) (mul_nonneg hc hΩ.le)).mp hsq

private lemma chain_unchanged {n T : ℕ} (ω : Ω n T) (i k : ℕ)
    (hik : i ≤ k) (hkT : k ≤ T) (y : BBBV.RandomOracle.Str n)
    (hy : y ∉ (Icc i T).image (x ω)) : piChain ω k y = piChain ω i y := by
  have hne (j : ℕ) (hj : j ∈ Icc i T) : y ≠ x ω j := by
    intro h
    exact hy (mem_image.mpr ⟨j, hj, h.symm⟩)
  have hall : ∀ k, i ≤ k → k ≤ T → piChain ω k y = piChain ω i y := by
    intro k hik
    induction k, hik using Nat.le_induction with
    | base => intro _; rfl
    | succ k hik ih =>
      intro hkt
      change piChain ω k (Equiv.swap (x ω k) (x ω (k + 1)) y) = _
      rw [Equiv.swap_apply_of_ne_of_ne (hne k (by simp; omega))
        (hne (k + 1) (by simp; omega))]
      exact ih (by omega)
  exact hall k hik hkT

end WentaoBBBVExpected

open WentaoBBBVExpected

theorem solution {n T : ℕ} {W : Type} [Fintype W]
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T) (hT1 : 1 ≤ T)
    (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 3) / 100) :
    avg (fun ω : Ω n T =>
      ‖final M (fun _ => ⇑(piChain ω T)) -
        final M (fun _ => ⇑(piChain ω (T - 1)))‖) ≤ 1 / 50 := by
  classical
  let S (ω : Ω n T) (i : Fin T) := (Icc i.val T).image (x ω)
  let F (ω : Ω n T) : Finset (Fin T × BBBV.RandomOracle.Str n) :=
    univ.filter fun p => p.2 ∈ S ω p.1
  let a (ω : Ω n T) : ℝ := ∑ i : Fin T, ∑ j ∈ Icc i.val T,
    queryMag (x ω j) (state M (hybrid ω) i)
  have ha : ∀ ω, 0 ≤ a ω := by
    intro ω
    exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => query_nonneg _ _
  have hmass (ω : Ω n T) :
      (∑ p ∈ F ω, queryMag p.2 (state M (hybrid ω) p.1)) ≤ a ω := by
    have heq : (∑ p ∈ F ω, queryMag p.2 (state M (hybrid ω) p.1)) =
        ∑ i : Fin T, ∑ y ∈ S ω i, queryMag y (state M (hybrid ω) i) := by
      simp only [F, sum_filter, Fintype.sum_prod_type]
      simp
    rw [heq]
    apply sum_le_sum
    intro i _
    exact sum_image_le_of_nonneg (fun y _ => query_nonneg y _)
  have hmean : avg a ≤ (T : ℝ) * (T + 1) / (2 : ℝ) ^ n := by
    calc
      _ = ∑ i : Fin T, ∑ j ∈ Icc i.val T,
          avg (fun ω : Ω n T => queryMag (x ω j) (state M (hybrid ω) i)) := by
        rw [show avg a = avg (fun ω => ∑ i : Fin T, ∑ j ∈ Icc i.val T,
          queryMag (x ω j) (state M (hybrid ω) i)) from rfl, avg_sum]
        apply sum_congr rfl
        intro i _
        exact avg_sum _ _
      _ ≤ ∑ i : Fin T, ∑ _j ∈ Icc i.val T, 1 / (2 : ℝ) ^ n := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j hj
        exact expected_queryMag_le M i j (mem_Icc.mp hj).1
          (by have := (mem_Icc.mp hj).2; omega)
      _ ≤ ∑ _i : Fin T, ∑ _j ∈ range (T + 1), 1 / (2 : ℝ) ^ n := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          have := (mem_Icc.mp hj).2
          exact mem_range.mpr (by omega)
        · intro j _ _; positivity
      _ = _ := by simp; ring
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hD : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcube : ((2 : ℝ) ^ ((n : ℝ) / 3)) ^ 3 = (2 : ℝ) ^ n := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    rw [show (n : ℝ) / 3 * (3 : ℕ) = (n : ℝ) by norm_num, Real.rpow_natCast]
  have hTc : (T : ℝ) ^ 3 ≤ (2 : ℝ) ^ n / 1000000 := by
    have hh : (T : ℝ) ^ 3 ≤ ((2 : ℝ) ^ ((n : ℝ) / 3) / 100) ^ 3 := by gcongr
    rw [div_pow, hcube] at hh
    norm_num at hh ⊢
    exact hh
  have hzmean : avg (fun ω : Ω n T => (T : ℝ) * a ω) ≤ (1 / 500 : ℝ) ^ 2 := by
    rw [avg_mul]
    calc
      _ ≤ (T : ℝ) * ((T : ℝ) * (T + 1) / (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hmean hTr.le
      _ = ((T : ℝ) * ((T : ℝ) * (T + 1))) / (2 : ℝ) ^ n := by ring
      _ ≤ (2 * (T : ℝ) ^ 3) / (2 : ℝ) ^ n := by
        apply div_le_div_of_nonneg_right _ hD.le
        have htone : (1 : ℝ) ≤ T := by exact_mod_cast hT1
        nlinarith [mul_nonneg (sq_nonneg (T : ℝ)) (sub_nonneg.mpr htone)]
      _ ≤ (2 / 1000000 : ℝ) := by
        apply (div_le_iff₀ hD).mpr
        nlinarith
      _ ≤ _ := by norm_num
  have hsqrt : avg (fun ω : Ω n T => Real.sqrt ((T : ℝ) * a ω)) ≤ 1 / 500 :=
    avg_sqrt_le _ (fun ω => mul_nonneg hTr.le (ha ω)) _ (by norm_num) hzmean
  have hpoint (ω : Ω n T) :
      ‖final M (fun _ => ⇑(piChain ω T)) -
        final M (fun _ => ⇑(piChain ω (T - 1)))‖ ≤
          4 * (Real.sqrt ((T : ℝ) * a ω) + 1 / 1000) := by
    let eps := Real.sqrt ((T : ℝ) * a ω) + 1 / 1000
    have heps : 0 < eps := by dsimp [eps]; positivity
    have hbudget : (∑ p ∈ F ω, queryMag p.2 (state M (hybrid ω) p.1)) ≤ eps ^ 2 / T := by
      apply (hmass ω).trans
      apply (le_div_iff₀ hTr).mpr
      have hs := Real.sq_sqrt (mul_nonneg hTr.le (ha ω))
      dsimp [eps]
      nlinarith [Real.sqrt_nonneg ((T : ℝ) * a ω)]
    have hagree (k : ℕ) (hk : ∀ i : Fin T, i.val ≤ k) (hkT : k ≤ T) :
        ∀ i y, (i, y) ∉ F ω → (piChain ω k) y = hybrid ω i y := by
      intro i y hy
      exact chain_unchanged ω i.val k (hk i) hkT y (by simpa [F, S] using hy)
    have hA := theorem_3_3 M (hybrid ω) (fun _ => ⇑(piChain ω T)) (F ω)
      (hagree T (fun i => Nat.le_of_lt i.isLt) le_rfl) eps heps hbudget
    have hB := theorem_3_3 M (hybrid ω) (fun _ => ⇑(piChain ω (T - 1))) (F ω)
      (hagree (T - 1) (fun i => by omega) (by omega)) eps heps hbudget
    have hA' : ‖final M (fun _ => ⇑(piChain ω T)) - final M (hybrid ω)‖ ≤ 2 * eps := by
      rw [norm_sub_rev]
      exact hA
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (final M (fun _ => ⇑(piChain ω T))) (final M (hybrid ω))
      (final M (fun _ => ⇑(piChain ω (T - 1))))
    dsimp [eps] at hA' hB
    linarith
  calc
    _ ≤ avg (fun ω : Ω n T => 4 * (Real.sqrt ((T : ℝ) * a ω) + 1 / 1000)) :=
      avg_mono _ _ hpoint
    _ = 4 * (avg (fun ω : Ω n T => Real.sqrt ((T : ℝ) * a ω)) + 1 / 1000) := by
      rw [avg_mul, avg_add, avg_const]
    _ ≤ 4 * ((1 / 500 : ℝ) + 1 / 1000) := by linarith
    _ ≤ _ := by norm_num
