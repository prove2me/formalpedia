-- Prove2me | solution 1 for EmpiricalBernstein.SVP.svp_excess_risk
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T06:29:33.665727+00:00
-- url     : https://prove2.me/submissions/fb5e00b5-0ac2-4e33-9976-70c5c02ab28a

-- SPDX-License-Identifier: Apache-2.0

import Definitions.Def_EmpiricalBernstein_SVP_PhiPsi
import Definitions.Def_EmpiricalBernstein_SVP_growthFunction
import Definitions.Def_EmpiricalBernstein_SVP_swap
import Mathlib


section

open scoped BigOperators
namespace EmpiricalBernstein.SVP.EBFresh
open VarianceRegularization.Expansion

lemma variance_pair_sum {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, ∑ j, (x i - x j)^2 / 2) =
      (n : ℝ) * ∑ i, (x i)^2 - (∑ i, x i)^2 := by
  simp_rw [show ∀ i j : Fin n, (x i - x j)^2 / 2 =
    (x i)^2 / 2 + (x j)^2 / 2 - x i * x j by intros; ring]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.sum_mul, ← Finset.sum_div]
  ring

lemma mean_sum {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (n : ℝ) * empMean x = ∑ i, x i := by
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [empMean, h]

lemma centered_sum_sq {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (∑ i, (x i - empMean x)^2) =
      (∑ i, (x i)^2) - (n : ℝ) * (empMean x)^2 := by
  simp_rw [show ∀ i : Fin n, (x i - empMean x)^2 =
    (x i)^2 - 2 * empMean x * x i + (empMean x)^2 by intro i; ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mean_sum hn x]
  ring

lemma sampleVar_centered {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    sampleVar x = (∑ i, (x i - empMean x)^2) / ((n : ℝ) - 1) := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [sampleVar, variance_pair_sum, centered_sum_sq (by omega), ← mean_sum (by omega) x]
  field_simp

lemma sampleVar_nonneg {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    0 ≤ sampleVar x := by
  rw [sampleVar_centered hn]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)

lemma sampleVar_le_sum_sq {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    sampleVar x ≤ (∑ i, (x i)^2) / ((n : ℝ) - 1) := by
  rw [sampleVar_centered hn, centered_sum_sq (by omega)]
  apply div_le_div_of_nonneg_right _ (by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

lemma sampleVar_add_const {n : ℕ} (x : Fin n → ℝ) (c : ℝ) :
    sampleVar (fun i => x i + c) = sampleVar x := by
  unfold sampleVar
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  ring

lemma sampleVar_scale {n : ℕ} (x : Fin n → ℝ) (c : ℝ) :
    sampleVar (fun i => c * x i) = c^2 * sampleVar x := by
  unfold sampleVar
  simp_rw [show ∀ i j : Fin n, (c * x i - c * x j)^2 / 2 =
    c^2 * ((x i - x j)^2 / 2) by intros; ring]
  simp only [← Finset.mul_sum]
  ring

lemma continuous_sampleVar {n : ℕ} : Continuous (sampleVar : (Fin n → ℝ) → ℝ) := by
  unfold sampleVar
  fun_prop

lemma measurable_sampleVar {n : ℕ} : Measurable (sampleVar : (Fin n → ℝ) → ℝ) :=
  continuous_sampleVar.measurable

end EmpiricalBernstein.SVP.EBFresh
end


section

open scoped BigOperators
namespace EmpiricalBernstein.SVP.EBFresh
open VarianceRegularization.Expansion

lemma sqrt_sum_sq_add_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Real.sqrt (∑ i, (x i + y i)^2) ≤
      Real.sqrt (∑ i, (x i)^2) + Real.sqrt (∑ i, (y i)^2) := by
  have hx : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy : 0 ≤ ∑ i, (y i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hcross : ∑ i, x i * y i ≤
      Real.sqrt (∑ i, (x i)^2) * Real.sqrt (∑ i, (y i)^2) := by
    have hp := mul_nonneg (Real.sqrt_nonneg (∑ i, (x i)^2))
      (Real.sqrt_nonneg (∑ i, (y i)^2))
    have hs : (Real.sqrt (∑ i, (x i)^2) * Real.sqrt (∑ i, (y i)^2))^2 =
        (∑ i, (x i)^2) * (∑ i, (y i)^2) := by
      rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
    nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have he : (∑ i, (x i + y i)^2) =
      (∑ i, (x i)^2) + (∑ i, (y i)^2) + 2 * ∑ i, x i * y i := by
    simp_rw [show ∀ i, (x i + y i)^2 = (x i)^2 + (y i)^2 + 2 * (x i * y i) by intro i; ring]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [he]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

lemma mean_add {n : ℕ} (x y : Fin n → ℝ) :
    empMean (fun i => x i + y i) = empMean x + empMean y := by
  simp only [empMean, Finset.sum_add_distrib, mul_add]

lemma sqrt_sampleVar_eq {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    Real.sqrt (sampleVar x) =
      Real.sqrt (∑ i, (x i - empMean x)^2) / Real.sqrt ((n : ℝ) - 1) := by
  rw [sampleVar_centered hn, Real.sqrt_div (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

lemma sqrt_sampleVar_add_le {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ) :
    Real.sqrt (sampleVar (fun i => x i + y i)) ≤
      Real.sqrt (sampleVar x) + Real.sqrt (sampleVar y) := by
  rw [sqrt_sampleVar_eq hn, sqrt_sampleVar_eq hn, sqrt_sampleVar_eq hn, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [mean_add]
  have he : ∀ i, x i + y i - (empMean x + empMean y) =
      (x i - empMean x) + (y i - empMean y) := by intro i; ring
  simp_rw [he]
  exact sqrt_sum_sq_add_le _ _

lemma sqrt_sampleVar_le_sup {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hx : ∀ i, |x i| ≤ ε) :
    Real.sqrt (sampleVar x) ≤ Real.sqrt 2 * ε := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (∑ i, (x i)^2) ≤ (n : ℝ) * ε^2 := by
    calc
      _ ≤ ∑ _ : Fin n, ε^2 := Finset.sum_le_sum fun i _ => by
        nlinarith [abs_le.mp (hx i)]
      _ = _ := by simp
  have hv : sampleVar x ≤ 2 * ε^2 := by
    apply (sampleVar_le_sum_sq hn x).trans
    apply (div_le_iff₀ (by linarith : 0 < (n : ℝ) - 1)).mpr
    nlinarith [sq_nonneg ε]
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hε, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hv

lemma sqrt_sampleVar_lipschitz {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hxy : ∀ i, |x i - y i| ≤ ε) :
    |Real.sqrt (sampleVar x) - Real.sqrt (sampleVar y)| ≤ Real.sqrt 2 * ε := by
  have h1 := sqrt_sampleVar_add_le hn y (fun i => x i - y i)
  have he1 : (fun i => y i + (x i - y i)) = x := by funext i; ring
  rw [he1] at h1
  have h2 := sqrt_sampleVar_add_le hn x (fun i => y i - x i)
  have he2 : (fun i => x i + (y i - x i)) = y := by funext i; ring
  rw [he2] at h2
  have hb1 := sqrt_sampleVar_le_sup hn (fun i => x i - y i) hε hxy
  have hb2 := sqrt_sampleVar_le_sup hn (fun i => y i - x i) hε
    (fun i => by simpa only [abs_sub_comm] using hxy i)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end EmpiricalBernstein.SVP.EBFresh
end


section

open scoped BigOperators
namespace EmpiricalBernstein.SVP.EBFresh
open VarianceRegularization.Expansion

lemma mean_lipschitz {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ)
    {ε : ℝ} (hxy : ∀ i, |x i - y i| ≤ ε) :
    |empMean x - empMean y| ≤ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : |∑ i, (x i - y i)| ≤ (n : ℝ) * ε := by
    calc
      _ ≤ ∑ i, |x i - y i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin n, ε := Finset.sum_le_sum fun i _ => hxy i
      _ = _ := by simp
  have he : empMean x - empMean y = (∑ i, (x i - y i)) / n := by
    simp only [empMean, Finset.sum_sub_distrib, div_eq_mul_inv]
    ring
  rw [he, abs_div, abs_of_pos hnR]
  exact (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hs)

lemma variance_score_lipschitz {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    {ε c b : ℝ} (hε : 0 ≤ ε) (hc : 0 ≤ c) (hxy : ∀ i, |x i - y i| ≤ ε) :
    |(empMean x + c * Real.sqrt (sampleVar x) + b) -
      (empMean y + c * Real.sqrt (sampleVar y) + b)| ≤ (1 + c * Real.sqrt 2) * ε := by
  have hm := mean_lipschitz (by omega : 0 < n) x y hxy
  have hv := sqrt_sampleVar_lipschitz hn x y hε hxy
  calc
    _ = |(empMean x - empMean y) + c *
        (Real.sqrt (sampleVar x) - Real.sqrt (sampleVar y))| := by congr 1; ring
    _ ≤ |empMean x - empMean y| + |c *
        (Real.sqrt (sampleVar x) - Real.sqrt (sampleVar y))| := abs_add_le _ _
    _ = |empMean x - empMean y| + c *
        |Real.sqrt (sampleVar x) - Real.sqrt (sampleVar y)| := by rw [abs_mul, abs_of_nonneg hc]
    _ ≤ ε + c * (Real.sqrt 2 * ε) := add_le_add hm (mul_le_mul_of_nonneg_left hv hc)
    _ = _ := by ring

lemma sqrt_variance_factor {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    Real.sqrt (c * sampleVar x * t / n) =
      Real.sqrt (c * t / n) * Real.sqrt (sampleVar x) := by
  have he : c * sampleVar x * t / n = (c * t / n) * sampleVar x := by ring
  rw [he, Real.sqrt_mul (by positivity : 0 ≤ c * t / n)]

lemma sqrt_two_factor {s : ℝ} (_hs : 0 ≤ s) :
    Real.sqrt (2 * s) * Real.sqrt 2 = 2 * Real.sqrt s := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg s]

lemma sqrt_eighteen_factor {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (18 * s) * Real.sqrt 2 = 6 * Real.sqrt s := by
  have he : 18 * s = 9 * (2 * s) := by ring
  rw [he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
  have h9 : Real.sqrt 9 = 3 := by norm_num
  rw [h9]
  calc
    3 * Real.sqrt (2 * s) * Real.sqrt 2 = 3 * (Real.sqrt (2 * s) * Real.sqrt 2) := by ring
    _ = _ := by rw [sqrt_two_factor hs]; ring

lemma Phi_lipschitz {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (hxy : ∀ i, |x i - y i| ≤ ε) :
    |Phi x t - Phi y t| ≤ (1 + 2 * Real.sqrt (t / n)) * ε := by
  unfold Phi
  rw [sqrt_variance_factor hn x (by norm_num) ht,
    sqrt_variance_factor hn y (by norm_num) ht]
  have h := variance_score_lipschitz hn x y hε
    (Real.sqrt_nonneg (2 * t / n)) hxy (b := 7 * t / (3 * ((n : ℝ) - 1)))
  have he : Real.sqrt (2 * t / n) * Real.sqrt 2 = 2 * Real.sqrt (t / n) := by
    rw [mul_div_assoc]
    exact sqrt_two_factor (by positivity)
  simpa only [he] using h

lemma Psi_lipschitz {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (hxy : ∀ i, |x i - y i| ≤ ε) :
    |Psi x t - Psi y t| ≤ (1 + 6 * Real.sqrt (t / n)) * ε := by
  unfold Psi
  rw [sqrt_variance_factor hn x (by norm_num) ht,
    sqrt_variance_factor hn y (by norm_num) ht]
  have h := variance_score_lipschitz hn x y hε
    (Real.sqrt_nonneg (18 * t / n)) hxy (b := 11 * t / ((n : ℝ) - 1))
  have he : Real.sqrt (18 * t / n) * Real.sqrt 2 = 6 * Real.sqrt (t / n) := by
    rw [mul_div_assoc]
    exact sqrt_eighteen_factor (by positivity)
  simpa only [he] using h

end EmpiricalBernstein.SVP.EBFresh
end


section

open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma evaluation_cover {X : Type*} {m : ℕ} (F : Set (X → ℝ)) (x : Fin m → X)
    {ε : ℝ} (hε : 0 ≤ ε) (hfin : growthFunction ε F m < ⊤) :
    ∃ s : Finset (X → ℝ), (∀ g ∈ s, g ∈ F) ∧
      s.card ≤ (growthFunction ε F m).toNat ∧
      ∀ f ∈ F, ∃ g ∈ s, ∀ i, |f (x i) - g (x i)| ≤ ε := by
  classical
  have hle : Metric.coveringNumber (Real.toNNReal ε) (evalSet F x) ≤
      growthFunction ε F m := le_iSup (fun z : Fin m → X =>
        Metric.coveringNumber (Real.toNNReal ε) (evalSet F z)) x
  have hne : Metric.coveringNumber (Real.toNNReal ε) (evalSet F x) ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_of_lt hfin) hle
  obtain ⟨C, hCF, hCfinite, hcover, hcard⟩ :=
    Metric.exists_set_encard_eq_coveringNumber hne
  have hrep : ∀ c : C, ∃ f ∈ F, (fun i => f (x i)) = c.val := by
    intro c
    exact hCF c.property
  choose rep hrepF hrepeq using hrep
  let cs := hCfinite.toFinset
  let s : Finset (X → ℝ) := cs.attach.image (fun c => rep ⟨c.val, hCfinite.mem_toFinset.mp c.property⟩)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hg
    exact hrepF _
  · have hsmall : s.card ≤ cs.card := (Finset.card_image_le).trans_eq Finset.card_attach
    have hcardnat : cs.card ≤ (growthFunction ε F m).toNat := by
      have hc : (cs.card : ℕ∞) ≤ growthFunction ε F m := by
        rw [← hCfinite.encard_eq_coe_toFinset_card, hcard]
        exact hle
      exact_mod_cast ENat.toNat_le_toNat hc (ne_of_lt hfin)
    exact hsmall.trans hcardnat
  · intro f hf
    have hc := hcover.subset_iUnion_closedBall (Set.mem_image_of_mem _ hf)
    simp only [Set.mem_iUnion, Metric.mem_closedBall] at hc
    obtain ⟨c, hc, hdist⟩ := hc
    let c' : C := ⟨c, hc⟩
    refine ⟨rep c', ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨⟨c, hCfinite.mem_toFinset.mpr hc⟩, Finset.mem_attach _ _, rfl⟩
    · intro i
      have hd : dist (fun j => f (x j)) c ≤ ε := by
        simpa only [Real.coe_toNNReal _ hε] using hdist
      have hi := (dist_pi_le_iff hε).mp hd i
      have hei : rep c' (x i) = c i := congrFun (hrepeq c') i
      rw [← hei] at hi
      simpa only [Real.dist_eq] using hi

lemma growth_pos {X : Type*} [Nonempty X] {m : ℕ} {ε : ℝ}
    {F : Set (X → ℝ)} (hF : F.Nonempty) : 0 < growthFunction ε F m := by
  classical
  let x : Fin m → X := fun _ => Classical.choice inferInstance
  have he : (evalSet F x).Nonempty := hF.image _
  exact (Metric.coveringNumber_pos_iff.mpr he).trans_le
    (le_iSup (fun z : Fin m → X => Metric.coveringNumber (Real.toNNReal ε) (evalSet F z)) x)

lemma calM_ge_ten {X : Type*} [Nonempty X] {F : Set (X → ℝ)} {n : ℕ}
    (hF : F.Nonempty) (hfin : growthFunction (1 / (n : ℝ)) F (2 * n) < ⊤) :
    10 ≤ calM F n := by
  have hp := growth_pos (m := 2 * n) (ε := 1 / (n : ℝ)) hF
  have hn : 1 ≤ (growthFunction (1 / (n : ℝ)) F (2 * n)).toNat := by
    have hle : (1 : ℕ∞) ≤ growthFunction (1 / (n : ℝ)) F (2 * n) := Order.one_le_iff_ne_zero.mpr (ne_of_gt hp)
    simpa using ENat.toNat_le_toNat hle (ne_of_lt hfin)
  have hnR : (1 : ℝ) ≤ ((growthFunction (1 / (n : ℝ)) F (2 * n)).toNat : ℝ) := by exact_mod_cast hn
  unfold calM
  linarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
open scoped ENNReal BigOperators
namespace EmpiricalBernstein.SVP.EBFresh

lemma strict_net_gap {n : ℕ} (hn : 2 ≤ n)
    (x y x' y' : Fin n → ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hx : ∀ i, |x i - x' i| ≤ ε) (hy : ∀ i, |y i - y' i| ≤ ε)
    (hgap : Psi y t + (2 + 8 * Real.sqrt (t / n)) * ε < Phi x t) :
    Psi y' t < Phi x' t := by
  have hp := (abs_le.mp (Phi_lipschitz hn x x' hε ht hx)).2
  have hq := (abs_le.mp (Psi_lipschitz hn y y' hε ht hy)).1
  nlinarith

lemma evaluation_cover_gap {X : Type*} {m n : ℕ} (hn : 2 ≤ n)
    (F : Set (X → ℝ)) (z : Fin m → X) (s : Finset (X → ℝ))
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hcover : ∀ f ∈ F, ∃ g ∈ s, ∀ i, |f (z i) - g (z i)| ≤ ε)
    (l r : Fin n → Fin m)
    (hgap : ∃ f ∈ F, Psi (fun i => f (z (r i))) t +
      (2 + 8 * Real.sqrt (t / n)) * ε < Phi (fun i => f (z (l i))) t) :
    ∃ g ∈ s, Psi (fun i => g (z (r i))) t < Phi (fun i => g (z (l i))) t := by
  obtain ⟨f, hf, hgap⟩ := hgap
  obtain ⟨g, hg, hdist⟩ := hcover f hf
  exact ⟨g, hg, strict_net_gap hn _ _ _ _ hε ht (fun i => hdist (l i))
    (fun i => hdist (r i)) hgap⟩

lemma finite_union_bound {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset I) (E : I → Set Ω) {B : Set Ω} {c : ℝ≥0∞}
    (hsub : B ⊆ ⋃ i ∈ s, E i) (hbound : ∀ i ∈ s, μ (E i) ≤ c) :
    μ B ≤ (s.card : ℝ≥0∞) * c := by
  calc
    μ B ≤ μ (⋃ i ∈ s, E i) := measure_mono hsub
    _ ≤ ∑ i ∈ s, μ (E i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ s, c := Finset.sum_le_sum fun i hi => hbound i hi
    _ = _ := by simp

lemma finite_net_probability {X Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (hn : 2 ≤ n) (μ : Measure Ω) (F : Set (X → ℝ)) (z : Fin m → X)
    (s : Finset (X → ℝ)) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hcover : ∀ f ∈ F, ∃ g ∈ s, ∀ i, |f (z i) - g (z i)| ≤ ε)
    (l r : Ω → Fin n → Fin m) {c : ℝ≥0∞}
    (hbound : ∀ g ∈ s, μ {ω | Psi (fun i => g (z (r ω i))) t <
      Phi (fun i => g (z (l ω i))) t} ≤ c) :
    μ {ω | ∃ f ∈ F, Psi (fun i => f (z (r ω i))) t +
      (2 + 8 * Real.sqrt (t / n)) * ε < Phi (fun i => f (z (l ω i))) t} ≤
      (s.card : ℝ≥0∞) * c := by
  apply finite_union_bound μ s
    (fun g => {ω | Psi (fun i => g (z (r ω i))) t < Phi (fun i => g (z (l ω i))) t})
    _ hbound
  intro ω hω
  obtain ⟨g, hg, hgap⟩ := evaluation_cover_gap hn F z s hε ht hcover (l ω) (r ω) hω
  exact Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, hgap⟩⟩

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

noncomputable def fairBool : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
noncomputable def signLaw (n : ℕ) : Measure (Fin n → Bool) := Measure.pi (fun _ => fairBool)

instance fairBool_probability : IsProbabilityMeasure fairBool := by
  unfold fairBool
  infer_instance

instance signLaw_probability (n : ℕ) : IsProbabilityMeasure (signLaw n) := by
  unfold signLaw
  infer_instance

lemma fairBool_not : fairBool.map Bool.not = fairBool := by
  have h : (PMF.uniformOfFintype Bool).map Bool.not = PMF.uniformOfFintype Bool := by
    ext b
    cases b <;> simp [PMF.map_apply, tsum_fintype]
  rw [fairBool, PMF.toMeasure_map Bool.not _ (measurable_of_countable Bool.not), h]

noncomputable def twoPointLaw (x y : ℝ) : Measure ℝ :=
  fairBool.map (fun b : Bool => if b then x else y)

instance twoPointLaw_probability (x y : ℝ) : IsProbabilityMeasure (twoPointLaw x y) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma sign_selected_law {n : ℕ} (x y : Fin n → ℝ) :
    (signLaw n).map (fun σ => swap σ x y) = Measure.pi (fun i => twoPointLaw (x i) (y i)) := by
  exact Measure.pi_map_pi (fun i => (measurable_of_countable
    (fun b : Bool => if b then x i else y i)).aemeasurable)

lemma sign_complement_law {n : ℕ} :
    (signLaw n).map (fun σ i => !σ i) = signLaw n := by
  have hp : IsProbabilityMeasure (fairBool.map Bool.not) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable Bool.not).aemeasurable
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => fairBool)
    (f := fun _ => Bool.not) (fun _ => (measurable_of_countable Bool.not).aemeasurable)
  simpa only [fairBool_not, signLaw] using h

lemma sign_antithetic_law {n : ℕ} (x y : Fin n → ℝ) :
    (signLaw n).map (fun σ => swap (fun i => !σ i) x y) =
      Measure.pi (fun i => twoPointLaw (x i) (y i)) := by
  have hm : Measurable (fun σ : Fin n → Bool => swap σ x y) := measurable_of_countable _
  have hn : Measurable (fun σ : Fin n → Bool => fun i => !σ i) := measurable_of_countable _
  have h := Measure.map_map hm hn (μ := signLaw n)
  rw [sign_complement_law] at h
  simp only [Function.comp_def] at h
  rw [← h]
  exact sign_selected_law x y

lemma twoPointLaw_support {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂twoPointLaw x y, z ∈ Set.Icc (0 : ℝ) 1 := by
  apply (ae_map_iff (measurable_of_countable _).aemeasurable measurableSet_Icc).mpr
  exact Filter.Eventually.of_forall fun b => by
    cases b
    · exact hy
    · exact hx

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

private def leftIndex {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨i.val, by omega⟩
private def rightIndex {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨n + i.val, by omega⟩

def doubledSample {X : Type*} {n : ℕ} (x y : Fin n → X) : Fin (2 * n) → X :=
  fun j => if h : j.val < n then x ⟨j.val, h⟩ else y ⟨j.val - n, by omega⟩

private lemma doubled_left {X : Type*} {n : ℕ} (x y : Fin n → X) (i : Fin n) :
    doubledSample x y (leftIndex i) = x i := by
  simp [doubledSample, leftIndex, i.isLt]

private lemma doubled_right {X : Type*} {n : ℕ} (x y : Fin n → X) (i : Fin n) :
    doubledSample x y (rightIndex i) = y i := by
  simp [doubledSample, rightIndex, show ¬n + i.val < n by omega]

private def signIndex {n : ℕ} (σ : Fin n → Bool) (i : Fin n) : Fin (2 * n) :=
  if σ i then leftIndex i else rightIndex i

private lemma doubled_sign {X : Type*} {n : ℕ} (x y : Fin n → X) (σ : Fin n → Bool) (i : Fin n) :
    doubledSample x y (signIndex σ i) = swap σ x y i := by
  cases h : σ i <;> simp [signIndex, swap, h, doubled_left, doubled_right]

lemma native_sign_net_bound {X : Type*} {n : ℕ} (hn : 2 ≤ n)
    (F : Set (X → ℝ)) (x y : Fin n → X) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hfin : growthFunction ε F (2 * n) < ⊤) {c : ℝ≥0∞}
    (hcomparison : ∀ f ∈ F, signLaw n {σ |
      Psi (fun i => f (swap σ x y i)) t <
        Phi (fun i => f (swap (fun i => !σ i) x y i)) t} ≤ c) :
    signLaw n {σ | ∃ f ∈ F, Psi (fun i => f (swap σ x y i)) t +
      (2 + 8 * Real.sqrt (t / n)) * ε <
        Phi (fun i => f (swap (fun i => !σ i) x y i)) t} ≤
      ((growthFunction ε F (2 * n)).toNat : ℝ≥0∞) * c := by
  obtain ⟨s, hsF, hcard, hcover⟩ := evaluation_cover F (doubledSample x y) hε hfin
  have hc : ∀ g ∈ s, signLaw n {σ |
      Psi (fun i => g (doubledSample x y (signIndex σ i))) t <
        Phi (fun i => g (doubledSample x y (signIndex (fun j => !σ j) i))) t} ≤ c := by
    intro g hg
    simpa only [doubled_sign] using hcomparison g (hsF g hg)
  have h := finite_net_probability hn (signLaw n) F (doubledSample x y) s hε ht hcover
    (fun σ i => signIndex (fun j => !σ j) i) (fun σ i => signIndex σ i) hc
  simp only [doubled_sign] at h
  apply h.trans
  exact mul_le_mul (by exact_mod_cast hcard) le_rfl zero_le zero_le

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
namespace EmpiricalBernstein.SVP.EBFresh

lemma measurable_swap {X : Type*} [MeasurableSpace X] {n : ℕ} (σ : Fin n → Bool) :
    Measurable (fun p : (Fin n → X) × (Fin n → X) => swap σ p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  cases h : σ i <;> simp only [swap, h, Bool.false_eq_true, ↓reduceIte] <;> fun_prop

lemma swap_pair_measurePreserving {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] {n : ℕ} (σ : Fin n → Bool) :
    MeasurePreserving
      (fun p : (Fin n → X) × (Fin n → X) => (swap σ p.1 p.2, swap (fun i => !σ i) p.1 p.2))
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow X X (Fin n) (fun _ => μ) (fun _ => μ)
  let flip : (i : Fin n) → X × X → X × X := fun i p => if σ i then p else p.swap
  have hf : ∀ i, MeasurePreserving (flip i) (μ.prod μ) (μ.prod μ) := by
    intro i
    cases h : σ i
    · simpa only [flip, h, Bool.false_eq_true, ↓reduceIte] using
        (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    · change MeasurePreserving (fun p => if σ i then p else p.swap) (μ.prod μ) (μ.prod μ)
      rw [h]
      exact MeasurePreserving.id (μ.prod μ)
  have hp := measurePreserving_pi (fun _ : Fin n => μ.prod μ) (fun _ : Fin n => μ.prod μ) hf
  have h := he.comp (hp.comp he.symm)
  have heq : (e ∘ (fun a i => flip i (a i)) ∘ e.symm) =
      (fun p : (Fin n → X) × (Fin n → X) =>
        (swap σ p.1 p.2, swap (fun i => !σ i) p.1 p.2)) := by
    funext p
    apply Prod.ext <;> funext i <;> cases hs : σ i <;>
      simp [e, flip, swap, hs, MeasurableEquiv.arrowProdEquivProdArrow]
  rw [← heq]
  exact h

lemma swap_pair_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] {n : ℕ} (σ : Fin n → Bool)
    {E : Set ((Fin n → X) × (Fin n → X))} (hE : MeasurableSet E) :
    ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
      {p | (swap σ p.1 p.2, swap (fun i => !σ i) p.1 p.2) ∈ E} =
    ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) E := by
  exact (swap_pair_measurePreserving μ σ).measure_preimage hE.nullMeasurableSet

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma randomized_probability_bound {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) (ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : S × Ω → Ω) (hT : Measurable T)
    (hpres : ∀ σ, MeasurePreserving (fun x => T (σ, x)) μ μ)
    {E : Set Ω} (hE : MeasurableSet E) {c : ℝ≥0∞}
    (hbound : ∀ x, ν {σ | T (σ, x) ∈ E} ≤ c) : μ E ≤ c := by
  have he : MeasurableSet (T ⁻¹' E) := hE.preimage hT
  have hprod : ν.prod μ (T ⁻¹' E) = μ E := by
    rw [Measure.prod_apply he]
    have hh : (fun σ => μ (Prod.mk σ ⁻¹' (T ⁻¹' E))) = (fun _ : S => μ E) := by
      funext σ
      exact (hpres σ).measure_preimage hE.nullMeasurableSet
    rw [hh]
    simp
  rw [← hprod, Measure.prod_apply_symm he]
  calc
    _ ≤ ∫⁻ _x, c ∂μ := lintegral_mono fun x => hbound x
    _ = c * μ Set.univ := by simp
    _ = c := by simp

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma measurable_joint_swap {X : Type*} [MeasurableSpace X] {n : ℕ} :
    Measurable (fun p : (Fin n → Bool) × ((Fin n → X) × (Fin n → X)) =>
      swap p.1 p.2.1 p.2.2) := by
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun p : (Fin n → Bool) × ((Fin n → X) × (Fin n → X)) =>
    if p.1 i then p.2.1 i else p.2.2 i)
  apply Measurable.ite
  · change MeasurableSet {p : (Fin n → Bool) × ((Fin n → X) × (Fin n → X)) | p.1 i = true}
    exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst) measurable_const
  · fun_prop
  · fun_prop

lemma measurable_joint_antithetic {X : Type*} [MeasurableSpace X] {n : ℕ} :
    Measurable (fun p : (Fin n → Bool) × ((Fin n → X) × (Fin n → X)) =>
      swap (fun i => !p.1 i) p.2.1 p.2.2) := by
  have he : (fun p : (Fin n → Bool) × ((Fin n → X) × (Fin n → X)) =>
      swap (fun i => !p.1 i) p.2.1 p.2.2) = (fun p => swap p.1 p.2.2 p.2.1) := by
    funext p i
    cases h : p.1 i <;> simp [swap, h]
  rw [he]
  exact measurable_joint_swap.comp (measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst))

lemma native_swap_average_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ}
    {E : Set ((Fin n → X) × (Fin n → X))} (hE : MeasurableSet E)
    {c : ℝ≥0∞}
    (hbound : ∀ x y : Fin n → X, signLaw n {σ |
      (swap σ x y, swap (fun i => !σ i) x y) ∈ E} ≤ c) :
    ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) E ≤ c := by
  apply randomized_probability_bound
    ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) (signLaw n)
    (fun p => (swap p.1 p.2.1 p.2.2, swap (fun i => !p.1 i) p.2.1 p.2.2))
    (measurable_joint_swap.prodMk measurable_joint_antithetic)
    (fun σ => swap_pair_measurePreserving μ σ) hE
  intro p
  exact hbound p.1 p.2

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma measurableSet_countable_exists {X I : Type*} [MeasurableSpace X]
    {F : Set I} (hF : F.Countable) {B : I → Set X}
    (hB : ∀ f ∈ F, MeasurableSet (B f)) :
    MeasurableSet {x | ∃ f ∈ F, x ∈ B f} := by
  have he : {x | ∃ f ∈ F, x ∈ B f} = ⋃ f ∈ F, B f := by ext x; simp
  rw [he]
  exact MeasurableSet.biUnion hF hB

lemma ghost_section_lower {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {B : Set X} {E : Set (X × Y)} {p : ℝ≥0∞}
    (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hlower : ∀ x ∈ B, p ≤ ν (Prod.mk x ⁻¹' E)) :
    p * μ B ≤ μ.prod ν E := by
  rw [Measure.prod_apply hE]
  calc
    p * μ B = ∫⁻ x, B.indicator (fun _ => p) x ∂μ := by
      rw [lintegral_indicator hB]
      simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ _ := lintegral_mono fun x => by
      by_cases hx : x ∈ B
      · simpa only [Set.indicator_of_mem hx] using hlower x hx
      · simp only [Set.indicator_of_notMem hx, zero_le]

lemma countable_ghost_bound {X Y I : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {F : Set I} (hF : F.Countable) {B : I → Set X} {G : I → Set Y}
    {E : Set (X × Y)} {p : ℝ≥0∞}
    (hB : ∀ f ∈ F, MeasurableSet (B f)) (hE : MeasurableSet E)
    (hG : ∀ f ∈ F, p ≤ ν (G f))
    (himp : ∀ f ∈ F, ∀ x ∈ B f, ∀ y ∈ G f, (x, y) ∈ E) :
    p * μ {x | ∃ f ∈ F, x ∈ B f} ≤ μ.prod ν E := by
  apply ghost_section_lower μ ν (measurableSet_countable_exists hF hB) hE
  rintro x ⟨f, hf, hxf⟩
  exact (hG f hf).trans (measure_mono fun y hy => himp f hf x hxf y hy)

lemma half_ghost_bound {X Y I : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {F : Set I} (hF : F.Countable) {B : I → Set X} {G : I → Set Y}
    {E : Set (X × Y)}
    (hB : ∀ f ∈ F, MeasurableSet (B f)) (hE : MeasurableSet E)
    (hG : ∀ f ∈ F, (2 : ℝ≥0∞)⁻¹ ≤ ν (G f))
    (himp : ∀ f ∈ F, ∀ x ∈ B f, ∀ y ∈ G f, (x, y) ∈ E) :
    μ {x | ∃ f ∈ F, x ∈ B f} ≤ 2 * μ.prod ν E := by
  have h := countable_ghost_bound μ ν hF hB hE hG himp
  have hh := mul_le_mul (le_refl (2 : ℝ≥0∞)) h zero_le zero_le
  simpa only [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul] using hh

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace EmpiricalBernstein.SVP.EBFresh
open VarianceRegularization.Expansion

lemma unit_interval_integrable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
    exact (hb x).2

lemma unit_interval_risk {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, f x ∂μ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun x => (hb x).1), ?_⟩
  have h := integral_mono (unit_interval_integrable hf hb)
    (integrable_const (1 : ℝ) : Integrable (fun _ : X => (1 : ℝ)) μ) (fun x => (hb x).2)
  simpa using h

lemma continuous_empMean {n : ℕ} : Continuous (empMean : (Fin n → ℝ) → ℝ) := by
  unfold empMean
  fun_prop

lemma continuous_Phi {n : ℕ} (t : ℝ) : Continuous (fun x : Fin n → ℝ => Phi x t) := by
  unfold Phi
  exact (continuous_empMean.add ((continuous_const.mul continuous_sampleVar).mul continuous_const
    |>.div_const (n : ℝ) |>.sqrt)).add continuous_const

lemma continuous_Psi {n : ℕ} (t : ℝ) : Continuous (fun x : Fin n → ℝ => Psi x t) := by
  unfold Psi
  exact (continuous_empMean.add ((continuous_const.mul continuous_sampleVar).mul continuous_const
    |>.div_const (n : ℝ) |>.sqrt)).add continuous_const

lemma measurable_evaluation {X : Type*} [MeasurableSpace X] {n : ℕ}
    {f : X → ℝ} (hf : Measurable f) :
    Measurable (fun x : Fin n → X => fun i => f (x i)) :=
  measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)

lemma measurable_sample_Phi {X : Type*} [MeasurableSpace X] {n : ℕ}
    {f : X → ℝ} (hf : Measurable f) (t : ℝ) :
    Measurable (fun x : Fin n → X => Phi (fun i => f (x i)) t) :=
  (continuous_Phi t).measurable.comp (measurable_evaluation hf)

lemma measurable_sample_Psi {X : Type*} [MeasurableSpace X] {n : ℕ}
    {f : X → ℝ} (hf : Measurable f) (t : ℝ) :
    Measurable (fun x : Fin n → X => Psi (fun i => f (x i)) t) :=
  (continuous_Psi t).measurable.comp (measurable_evaluation hf)

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma uniform_from_comparison {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    (F : Set (X → ℝ)) (hF : F.Countable) (hFm : ∀ f ∈ F, Measurable f)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hfin : growthFunction ε F (2 * n) < ⊤) {c : ℝ≥0∞}
    (hghost : ∀ f ∈ F, (2 : ℝ≥0∞)⁻¹ ≤
      Measure.pi (fun _ : Fin n => μ) {y | (∫ z, f z ∂μ) ≤ Phi (fun i => f (y i)) t})
    (hcomparison : ∀ f ∈ F, ∀ x y : Fin n → X,
      signLaw n {σ | Psi (fun i => f (swap σ x y i)) t <
        Phi (fun i => f (swap (fun i => !σ i) x y i)) t} ≤ c) :
    Measure.pi (fun _ : Fin n => μ) {x | ∃ f ∈ F,
      Psi (fun i => f (x i)) t + (2 + 8 * Real.sqrt (t / n)) * ε < ∫ z, f z ∂μ} ≤
      2 * (((growthFunction ε F (2 * n)).toNat : ℝ≥0∞) * c) := by
  let slack := (2 + 8 * Real.sqrt (t / n)) * ε
  let E : Set ((Fin n → X) × (Fin n → X)) := {p | ∃ f ∈ F,
    Psi (fun i => f (p.1 i)) t + slack < Phi (fun i => f (p.2 i)) t}
  have hEm : MeasurableSet E := by
    apply measurableSet_countable_exists hF
    intro f hf
    exact measurableSet_lt (((measurable_sample_Psi (hFm f hf) t).comp measurable_fst).add_const slack)
      ((measurable_sample_Phi (hFm f hf) t).comp measurable_snd)
  have hpair : ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) E ≤
      ((growthFunction ε F (2 * n)).toNat : ℝ≥0∞) * c := by
    apply native_swap_average_bound μ hEm
    intro x y
    exact native_sign_net_bound hn F x y hε ht hfin (fun f hf => hcomparison f hf x y)
  have hbad (f : X → ℝ) (hf : f ∈ F) : MeasurableSet
      {x : Fin n → X | Psi (fun i => f (x i)) t + slack < ∫ z, f z ∂μ} :=
    measurableSet_lt ((measurable_sample_Psi (hFm f hf) t).add_const slack) measurable_const
  have h := half_ghost_bound (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => μ)
    hF hbad hEm hghost (fun f hf x hx y hy => ?_)
  · exact h.trans (mul_le_mul le_rfl hpair zero_le zero_le)
  · exact ⟨f, hf, lt_of_lt_of_le hx hy⟩

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma unit_interval_memLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (p : ℝ≥0∞) :
    MemLp f p μ := memLp_of_bounded (Filter.Eventually.of_forall hb) hf.aestronglyMeasurable p

lemma mapped_unit_support {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : Measurable f)
    (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂μ.map f, z ∈ Set.Icc (0 : ℝ) 1 := by
  exact (ae_map_iff hf.aemeasurable measurableSet_Icc).mpr (Filter.Eventually.of_forall hb)

lemma sample_pushforward {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ).map (fun x => fun i => f (x i)) =
      Measure.pi (fun _ : Fin n => μ.map f) := by
  have : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  exact Measure.pi_map_pi (fun _ => hf.aemeasurable)

lemma sample_event_transfer {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f) (n : ℕ)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) :
    (Measure.pi fun _ : Fin n => μ) {x | (fun i => f (x i)) ∈ E} =
      (Measure.pi fun _ : Fin n => μ.map f) E := by
  rw [← sample_pushforward μ hf n, Measure.map_apply (measurable_evaluation hf) hE]
  rfl

lemma mapped_risk {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Measurable f) :
    (∫ z : ℝ, z ∂μ.map f) = ∫ x, f x ∂μ := by
  exact integral_map hf.aemeasurable (show AEStronglyMeasurable (fun z : ℝ => z) (μ.map f) from aestronglyMeasurable_id)

lemma mapped_variance {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Measurable f) :
    variance (fun z : ℝ => z) (μ.map f) = variance f μ := by
  simpa only [Function.comp_def] using
    (variance_map (X := fun z : ℝ => z) (Y := f) aemeasurable_id hf.aemeasurable)

end EmpiricalBernstein.SVP.EBFresh
end


section

open VarianceRegularization.Expansion
namespace EmpiricalBernstein.SVP.EBFresh

lemma sqrt_eighteen_three {n : ℕ} {t : ℝ} (_ht : 0 ≤ t) :
    Real.sqrt (18*t/n) = 3*Real.sqrt (2*t/n) := by
  have he : 18*t/n = 9*(2*t/n) := by ring
  rw [he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
  norm_num

lemma score_radius_product {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (2*t/n)*Real.sqrt (2*t/((n : ℝ)-1)) ≤ 2*t/((n : ℝ)-1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  have hle : 2*t/n ≤ 2*t/((n : ℝ)-1) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have h := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hle)
    (Real.sqrt_nonneg (2*t/((n : ℝ)-1)))
  rw [← sq, Real.sq_sqrt (by positivity : 0 ≤ 2*t/((n : ℝ)-1))] at h
  exact h

lemma mean_remainder_le {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    t/(3*n) ≤ t/(3*((n : ℝ)-1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ)-1 := by linarith
  exact div_le_div_of_nonneg_left ht (by positivity) (by linarith)

noncomputable def comparisonLevel {n : ℕ} (M V t : ℝ) : ℝ :=
  M+2*Real.sqrt (2*t/n)*Real.sqrt V+14*t/(3*((n : ℝ)-1))

lemma phi_upper_level {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) {M V t : ℝ}
    (ht : 0 ≤ t)
    (hm : empMean x ≤ M+Real.sqrt (2*t/n)*Real.sqrt V+t/(3*n))
    (hv : Real.sqrt (sampleVar x) ≤ Real.sqrt V+Real.sqrt (2*t/((n : ℝ)-1))) :
    Phi x t ≤ comparisonLevel (n := n) M V t := by
  unfold Phi comparisonLevel
  rw [sqrt_variance_factor hn x (by norm_num) ht]
  have h := mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg (2*t/n))
  have hr := score_radius_product hn ht
  have he := mean_remainder_le hn ht
  simp only [div_mul_eq_div_div] at hm hr he ⊢
  ring_nf at hm hr he h ⊢
  nlinarith

lemma psi_lower_level {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) {M V t : ℝ}
    (ht : 0 ≤ t)
    (hm : M-Real.sqrt (2*t/n)*Real.sqrt V-t/(3*n) ≤ empMean x)
    (hv : Real.sqrt V ≤ Real.sqrt (sampleVar x)+Real.sqrt (2*t/((n : ℝ)-1))) :
    comparisonLevel (n := n) M V t ≤ Psi x t := by
  unfold Psi comparisonLevel
  rw [sqrt_variance_factor hn x (by norm_num) ht, sqrt_eighteen_three ht]
  have h := mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg (2*t/n))
  have hr := score_radius_product hn ht
  have he := mean_remainder_le hn ht
  simp only [div_mul_eq_div_div] at hm hr he ⊢
  ring_nf at hm hr he h ⊢
  nlinarith

lemma mean_le_phi {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) {M V t : ℝ}
    (ht : 0 ≤ t)
    (hm : M-Real.sqrt (2*t/n)*Real.sqrt V-t/(3*n) ≤ empMean x)
    (hv : Real.sqrt V ≤ Real.sqrt (sampleVar x)+Real.sqrt (2*t/((n : ℝ)-1))) :
    M ≤ Phi x t := by
  unfold Phi
  rw [sqrt_variance_factor hn x (by norm_num) ht]
  have h := mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg (2*t/n))
  have hr := score_radius_product hn ht
  have he := mean_remainder_le hn ht
  simp only [div_mul_eq_div_div] at hm hr he ⊢
  ring_nf at hm hr he h ⊢
  nlinarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory VarianceRegularization.Expansion
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

theorem score_probability_bounds {n : ℕ} (hn : 2 ≤ n) (P : Measure (Fin n → ℝ))
    {M V t : ℝ} {ε : ℝ≥0∞} (ht : 0 ≤ t)
    (hmu : P {x : Fin n → ℝ | M+Real.sqrt (2*t/n)*Real.sqrt V+t/(3*n) < empMean x} ≤ ε)
    (hml : P {x : Fin n → ℝ | empMean x < M-Real.sqrt (2*t/n)*Real.sqrt V-t/(3*n)} ≤ ε)
    (hvu : P {x : Fin n → ℝ | Real.sqrt V+Real.sqrt (2*t/((n : ℝ)-1)) < Real.sqrt (sampleVar x)} ≤ ε)
    (hvl : P {x : Fin n → ℝ | Real.sqrt (sampleVar x)+Real.sqrt (2*t/((n : ℝ)-1)) < Real.sqrt V} ≤ ε) :
    P {x : Fin n → ℝ | comparisonLevel (n := n) M V t < Phi x t} ≤ 2*ε ∧
    P {x : Fin n → ℝ | Psi x t < comparisonLevel (n := n) M V t} ≤ 2*ε ∧
    P {x : Fin n → ℝ | Phi x t < M} ≤ 2*ε := by
  have huSub : {x : Fin n → ℝ | comparisonLevel (n := n) M V t < Phi x t} ⊆
      {x : Fin n → ℝ | M+Real.sqrt (2*t/n)*Real.sqrt V+t/(3*n) < empMean x} ∪
      {x : Fin n → ℝ | Real.sqrt V+Real.sqrt (2*t/((n : ℝ)-1)) < Real.sqrt (sampleVar x)} := by
    intro x hx
    by_cases hm : empMean x ≤ M+Real.sqrt (2*t/n)*Real.sqrt V+t/(3*n)
    · by_cases hv : Real.sqrt (sampleVar x) ≤ Real.sqrt V+Real.sqrt (2*t/((n : ℝ)-1))
      · exact False.elim ((not_lt.mpr (phi_upper_level hn x ht hm hv)) hx)
      · exact Or.inr (lt_of_not_ge hv)
    · exact Or.inl (lt_of_not_ge hm)
  have hlSub : {x : Fin n → ℝ | Psi x t < comparisonLevel (n := n) M V t} ⊆
      {x : Fin n → ℝ | empMean x < M-Real.sqrt (2*t/n)*Real.sqrt V-t/(3*n)} ∪
      {x : Fin n → ℝ | Real.sqrt (sampleVar x)+Real.sqrt (2*t/((n : ℝ)-1)) < Real.sqrt V} := by
    intro x hx
    by_cases hm : M-Real.sqrt (2*t/n)*Real.sqrt V-t/(3*n) ≤ empMean x
    · by_cases hv : Real.sqrt V ≤ Real.sqrt (sampleVar x)+Real.sqrt (2*t/((n : ℝ)-1))
      · exact False.elim ((not_lt.mpr (psi_lower_level hn x ht hm hv)) hx)
      · exact Or.inr (lt_of_not_ge hv)
    · exact Or.inl (lt_of_not_ge hm)
  have hgSub : {x : Fin n → ℝ | Phi x t < M} ⊆
      {x : Fin n → ℝ | empMean x < M-Real.sqrt (2*t/n)*Real.sqrt V-t/(3*n)} ∪
      {x : Fin n → ℝ | Real.sqrt (sampleVar x)+Real.sqrt (2*t/((n : ℝ)-1)) < Real.sqrt V} := by
    intro x hx
    by_cases hm : M-Real.sqrt (2*t/n)*Real.sqrt V-t/(3*n) ≤ empMean x
    · by_cases hv : Real.sqrt V ≤ Real.sqrt (sampleVar x)+Real.sqrt (2*t/((n : ℝ)-1))
      · exact False.elim ((not_lt.mpr (mean_le_phi hn x ht hm hv)) hx)
      · exact Or.inr (lt_of_not_ge hv)
    · exact Or.inl (lt_of_not_ge hm)
  have h1 := (measure_mono huSub).trans ((measure_union_le _ _).trans (add_le_add hmu hvu))
  have h2 := (measure_mono hlSub).trans ((measure_union_le _ _).trans (add_le_add hml hvl))
  have h3 := (measure_mono hgSub).trans ((measure_union_le _ _).trans (add_le_add hml hvl))
  simpa only [two_mul] using And.intro h1 (And.intro h2 h3)

end EmpiricalBernstein.SVP.EBFresh
end


section

open scoped BigOperators
namespace EmpiricalBernstein.SVP.EBFresh
open VarianceRegularization.Expansion

noncomputable def otherMean {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ((∑ j, x j) - x i) / ((n : ℝ) - 1)

lemma finite_sum_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (i : ι) (b : ℝ) :
    (∑ j, Function.update x i b j) = (∑ j, x j) - x i + b := by
  have he : ∀ j, Function.update x i b j = x j + if j = i then b - x i else 0 := by
    intro j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

lemma finite_sq_sum_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (i : ι) (b : ℝ) :
    (∑ j, (Function.update x i b j)^2) = (∑ j, (x j)^2) - (x i)^2 + b^2 := by
  have he : (fun j => (Function.update x i b j)^2) = Function.update (fun j => (x j)^2) i (b^2) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  rw [he, finite_sum_update]

lemma otherMean_update {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    otherMean (Function.update x i b) i = otherMean x i := by
  unfold otherMean
  rw [finite_sum_update]
  simp

lemma otherMean_bounds {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    otherMean x i ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (∑ j, x j) - x i = ∑ j ∈ Finset.univ.erase i, x j := by
    have h := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
    linarith
  have hlo : 0 ≤ ∑ j ∈ Finset.univ.erase i, x j :=
    Finset.sum_nonneg fun j _ => (hx j).1
  have hhi : (∑ j ∈ Finset.univ.erase i, x j) ≤ (n : ℝ) - 1 := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) := Finset.sum_le_sum fun j _ => (hx j).2
      _ = _ := by simp [Nat.cast_sub (show 1 ≤ n by omega)]
  unfold otherMean
  rw [he]
  refine ⟨div_nonneg hlo (by linarith), ?_⟩
  exact (div_le_one (by linarith : 0 < (n : ℝ) - 1)).mpr hhi

lemma variance_coordinate_minimum {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (i : Fin n) :
    (n : ℝ) * sampleVar x - (n : ℝ) * sampleVar (Function.update x i (otherMean x i)) =
      (x i - otherMean x i)^2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp only [sampleVar, variance_pair_sum, finite_sum_update, finite_sq_sum_update, otherMean]
  field_simp
  ring

lemma otherMean_centered {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (i : Fin n) :
    x i - otherMean x i = ((n : ℝ) / ((n : ℝ) - 1)) * (x i - empMean x) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold otherMean empMean
  field_simp
  ring

lemma variance_deficits_sum {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    (∑ i, (x i - otherMean x i)^2) =
      ((n : ℝ) / ((n : ℝ) - 1)) * ((n : ℝ) * sampleVar x) := by
  simp_rw [otherMean_centered hn, mul_pow, ← Finset.mul_sum]
  rw [sampleVar_centered hn]
  ring

lemma variance_deficit_bounds {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    (x i - otherMean x i)^2 ∈ Set.Icc (0 : ℝ) 1 := by
  have hm := otherMean_bounds hn x hx i
  have hi := hx i
  refine ⟨sq_nonneg _, (sq_le_one_iff_abs_le_one _).mpr ?_⟩
  exact abs_le.mpr ⟨by linarith [hi.1, hm.2], by linarith [hm.1, hi.2]⟩

lemma variance_squared_deficits {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, ((x i - otherMean x i)^2)^2) ≤
      ((n : ℝ) / ((n : ℝ) - 1)) * ((n : ℝ) * sampleVar x) := by
  rw [← variance_deficits_sum hn]
  apply Finset.sum_le_sum
  intro i _
  have h := variance_deficit_bounds hn x hx i
  nlinarith [h.1, h.2]

lemma continuous_otherMean {n : ℕ} (i : Fin n) :
    Continuous (fun x : Fin n → ℝ => otherMean x i) := by
  unfold otherMean
  fun_prop

end EmpiricalBernstein.SVP.EBFresh
end


section

open scoped BigOperators
namespace EmpiricalBernstein.SVP.EBFresh

noncomputable def clipUnit (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clipUnit_mem (x : ℝ) : clipUnit x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold clipUnit
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clipUnit_eq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : clipUnit x = x := by
  simp [clipUnit, min_eq_right hx.2, max_eq_right hx.1]

lemma continuous_clipUnit : Continuous clipUnit := by
  unfold clipUnit
  fun_prop

noncomputable def varianceZ {n : ℕ} (x : Fin n → ℝ) : ℝ := (n : ℝ) * sampleVar x
noncomputable def varianceBaseline {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  varianceZ (Function.update x i (otherMean x i))
noncomputable def clippedVarianceZ {n : ℕ} (x : Fin n → ℝ) : ℝ := varianceZ (fun i => clipUnit (x i))
noncomputable def clippedVarianceBaseline {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  varianceBaseline (fun j => clipUnit (x j)) i

lemma varianceBaseline_update {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    varianceBaseline (Function.update x i b) i = varianceBaseline x i := by
  unfold varianceBaseline
  rw [otherMean_update, Function.update_idem]

lemma clipUnit_update {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    (fun j => clipUnit (Function.update x i b j)) =
      Function.update (fun j => clipUnit (x j)) i (clipUnit b) := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

lemma clippedVarianceBaseline_update {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    clippedVarianceBaseline (Function.update x i b) i = clippedVarianceBaseline x i := by
  unfold clippedVarianceBaseline
  rw [clipUnit_update, varianceBaseline_update]

lemma continuous_clippedVarianceZ {n : ℕ} : Continuous (clippedVarianceZ : (Fin n → ℝ) → ℝ) := by
  unfold clippedVarianceZ varianceZ
  exact continuous_const.mul (continuous_sampleVar.comp
    (continuous_pi fun i => continuous_clipUnit.comp (continuous_apply i)))

lemma continuous_clippedVarianceBaseline {n : ℕ} (i : Fin n) :
    Continuous (fun x : Fin n → ℝ => clippedVarianceBaseline x i) := by
  have hu : Continuous (fun x : Fin n → ℝ => Function.update x i (otherMean x i)) := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self] using continuous_otherMean i
    · simpa only [Function.update_of_ne h] using (continuous_apply j : Continuous (fun x : Fin n → ℝ => x j))
  unfold clippedVarianceBaseline varianceBaseline varianceZ
  exact (continuous_const.mul (continuous_sampleVar.comp hu)).comp
    (continuous_pi fun j => continuous_clipUnit.comp (continuous_apply j))

lemma clippedVarianceZ_eq {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    clippedVarianceZ x = (n : ℝ) * sampleVar x := by
  unfold clippedVarianceZ varianceZ
  congr 2
  funext i
  exact clipUnit_eq (hx i)

lemma varianceZ_bounds {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    varianceZ x ∈ Set.Icc (0 : ℝ) (2 * n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (∑ i, (x i)^2) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        have hi := hx i
        nlinarith [hi.1, hi.2]
      _ = _ := by simp
  have hv : sampleVar x ≤ 2 := by
    apply (sampleVar_le_sum_sq hn x).trans
    apply (div_le_iff₀ (by linarith : 0 < (n : ℝ) - 1)).mpr
    linarith
  unfold varianceZ
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (sampleVar_nonneg hn x), by nlinarith⟩

lemma clippedVarianceZ_bounds {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    clippedVarianceZ x ∈ Set.Icc (0 : ℝ) (2 * n) :=
  varianceZ_bounds hn _ (fun i => clipUnit_mem (x i))

lemma clippedVariance_deficit_bounds {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (i : Fin n) :
    clippedVarianceZ x - clippedVarianceBaseline x i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold clippedVarianceZ clippedVarianceBaseline varianceBaseline varianceZ
  rw [variance_coordinate_minimum hn]
  exact variance_deficit_bounds hn _ (fun j => clipUnit_mem (x j)) i

lemma clippedVariance_squared_deficits {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    (∑ i, (clippedVarianceZ x - clippedVarianceBaseline x i)^2) ≤
      ((n : ℝ) / ((n : ℝ) - 1)) * clippedVarianceZ x := by
  unfold clippedVarianceZ clippedVarianceBaseline varianceBaseline varianceZ
  simp_rw [variance_coordinate_minimum hn]
  exact variance_squared_deficits hn _ (fun j => clipUnit_mem (x j))

lemma clippedVarianceBaseline_bounds {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (i : Fin n) :
    clippedVarianceBaseline x i ∈ Set.Icc (0 : ℝ) (clippedVarianceZ x) := by
  refine ⟨?_, ?_⟩
  · unfold clippedVarianceBaseline varianceBaseline varianceZ
    exact mul_nonneg (Nat.cast_nonneg _) (sampleVar_nonneg hn _)
  · have h := (clippedVariance_deficit_bounds hn x i).1
    linarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace EmpiricalBernstein.SVP.EBFresh

lemma expectation_sampleVar_independent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 2 ≤ n)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P) (hI : iIndepFun X P) :
    (∫ ω, sampleVar (fun i => X i ω) ∂P) =
      (∑ i, variance (X i) P) / n + sampleVar (fun i => ∫ ω, X i ω ∂P) := by
  have hXi (i : Fin n) : Integrable (X i) P := (hX i).integrable (by norm_num)
  have hsum : MemLp (fun ω => ∑ i, X i ω) 2 P := memLp_finsetSum _ (fun i _ => hX i)
  have hsqsum : Integrable (fun ω => ∑ i, (X i ω)^2) P :=
    integrable_finsetSum Finset.univ (fun i _ => (hX i).integrable_sq)
  have hm : (∫ ω, ∑ i, X i ω ∂P) = ∑ i, ∫ ω, X i ω ∂P :=
    integral_finsetSum Finset.univ (fun i _ => hXi i)
  have hvs := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hX i)
    (fun i _ j _ hij => hI.indepFun hij)
  have hvsi : variance (fun ω => ∑ i, X i ω) P = ∑ i, variance (X i) P := by
    have he : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by funext ω; simp
    rw [he] at hvs
    exact hvs
  have hsecond (i : Fin n) : (∫ ω, (X i ω)^2 ∂P) =
      variance (X i) P + (∫ ω, X i ω ∂P)^2 := by
    have h := variance_eq_sub (hX i)
    simp only [Pi.pow_apply] at h
    linarith
  have hQ : (∫ ω, ∑ i, (X i ω)^2 ∂P) =
      (∑ i, variance (X i) P) + ∑ i, (∫ ω, X i ω ∂P)^2 := by
    rw [integral_finsetSum _ (fun i _ => (hX i).integrable_sq)]
    simp only [hsecond, Finset.sum_add_distrib]
  have hS : (∫ ω, (∑ i, X i ω)^2 ∂P) =
      (∑ i, variance (X i) P) + (∑ i, ∫ ω, X i ω ∂P)^2 := by
    have h := variance_eq_sub hsum
    simp only [Pi.pow_apply] at h
    rw [hvsi, hm] at h
    linarith
  simp only [sampleVar, variance_pair_sum]
  rw [integral_const_mul, integral_sub (hsqsum.const_mul _) hsum.integrable_sq,
    integral_const_mul, hQ, hS]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp
  ring

lemma expectation_sampleVar_ge_average_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 2 ≤ n)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P) (hI : iIndepFun X P) :
    (∑ i, variance (X i) P) / n ≤ ∫ ω, sampleVar (fun i => X i ω) ∂P := by
  rw [expectation_sampleVar_independent hn X hX hI]
  exact le_add_of_nonneg_right (sampleVar_nonneg hn _)

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace EmpiricalBernstein.SVP.EBFresh

lemma variance_comp_eval {n : ℕ} {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X : (i : Fin n) → Ω i → ℝ) (hX : ∀ i, MemLp (X i) 2 (μ i)) (i : Fin n) :
    variance (fun ω => X i (ω i)) (Measure.pi μ) = variance (X i) (μ i) := by
  have hi := (hX i).comp_measurePreserving (measurePreserving_eval μ i)
  change MemLp (fun ω : (j : Fin n) → Ω j => X i (ω i)) 2 (Measure.pi μ) at hi
  rw [variance_eq_sub hi, variance_eq_sub (hX i)]
  simp only [Pi.pow_apply]
  have hsq := integral_comp_eval (μ := μ) ((hX i).aestronglyMeasurable.pow 2)
  simp only [Pi.pow_apply] at hsq
  rw [hsq, integral_comp_eval (hX i).aestronglyMeasurable]

lemma expectation_sampleVar_product {n : ℕ} (hn : 2 ≤ n)
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X : (i : Fin n) → Ω i → ℝ) (hX : ∀ i, MemLp (X i) 2 (μ i)) :
    (∫ ω, sampleVar (fun i => X i (ω i)) ∂Measure.pi μ) =
      (∑ i, variance (X i) (μ i)) / n + sampleVar (fun i => ∫ z, X i z ∂μ i) := by
  have h := expectation_sampleVar_independent hn (fun i (ω : (j : Fin n) → Ω j) => X i (ω i))
    (fun i => (hX i).comp_measurePreserving (measurePreserving_eval μ i))
    (iIndepFun_pi (fun i => (hX i).aemeasurable))
  simpa only [variance_comp_eval μ X hX, integral_comp_eval (hX _).aestronglyMeasurable] using h

lemma expectation_sampleVar_product_ge {n : ℕ} (hn : 2 ≤ n)
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X : (i : Fin n) → Ω i → ℝ) (hX : ∀ i, MemLp (X i) 2 (μ i)) :
    (∑ i, variance (X i) (μ i)) / n ≤
      ∫ ω, sampleVar (fun i => X i (ω i)) ∂Measure.pi μ := by
  rw [expectation_sampleVar_product hn μ X hX]
  exact le_add_of_nonneg_right (sampleVar_nonneg hn _)

lemma expectation_sampleVar_iid {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    (∫ ω, sampleVar (fun i : Fin n => X (ω i)) ∂Measure.pi (fun _ : Fin n => μ)) = variance X μ := by
  rw [expectation_sampleVar_product hn (fun _ : Fin n => μ) (fun _ => X) (fun _ => hX)]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp [sampleVar, hn0]

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace EmpiricalBernstein.SVP.EBFresh

noncomputable def clippedMean (μ : Measure ℝ) : ℝ := ∫ x, clipUnit x ∂μ
noncomputable def centeredClip (μ : Measure ℝ) (x : ℝ) : ℝ := clipUnit x - clippedMean μ

lemma clippedMean_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clippedMean μ ∈ Set.Icc (0 : ℝ) 1 :=
  unit_interval_risk continuous_clipUnit.measurable clipUnit_mem

lemma centeredClip_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    |centeredClip μ x| ≤ 1 := by
  have hx := clipUnit_mem x
  have hm := clippedMean_mem μ
  unfold centeredClip
  exact abs_le.mpr ⟨by linarith [hx.1, hm.2], by linarith [hx.2, hm.1]⟩

lemma measurable_centeredClip (μ : Measure ℝ) : Measurable (centeredClip μ) :=
  continuous_clipUnit.measurable.sub_const _

lemma integral_centeredClip (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ x, centeredClip μ x ∂μ) = 0 := by
  unfold centeredClip clippedMean
  rw [integral_sub (unit_interval_integrable continuous_clipUnit.measurable clipUnit_mem) (integrable_const _)]
  simp

lemma clippedMean_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) : clippedMean μ = ∫ x, x ∂μ := by
  exact integral_congr_ae (hμ.mono fun x hx => clipUnit_eq hx)

lemma centeredClip_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, (centeredClip μ x)^2 ∂μ) = variance (fun x : ℝ => x) μ := by
  have he : clipUnit =ᵐ[μ] fun x : ℝ => x := hμ.mono fun x hx => clipUnit_eq hx
  rw [← variance_congr he, variance_eq_integral continuous_clipUnit.measurable.aemeasurable]
  rfl

lemma native_empMean_expectation {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, VarianceRegularization.Expansion.empMean x ∂Measure.pi μ) =
      VarianceRegularization.Expansion.empMean (fun i => ∫ z, z ∂μ i) := by
  have hm (i : Fin n) : MemLp (fun z : ℝ => z) 2 (μ i) :=
    memLp_of_bounded (hμ i) aestronglyMeasurable_id 2
  have hi (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i) (Measure.pi μ) := by
    exact ((hm i).comp_measurePreserving (measurePreserving_eval μ i)).integrable (by norm_num)
  unfold VarianceRegularization.Expansion.empMean
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
  simp only [integral_eval]

lemma centeredClip_sum {n : ℕ} (hn : 2 ≤ n) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, ∀ᵐ z ∂μ i, z ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, centeredClip (μ i) (x i)) = (n : ℝ) *
      (VarianceRegularization.Expansion.empMean x -
        ∫ y, VarianceRegularization.Expansion.empMean y ∂Measure.pi μ) := by
  simp only [centeredClip, Finset.sum_sub_distrib, clippedMean_eq _ (hμ _), clipUnit_eq (hx _)]
  rw [native_empMean_expectation μ hμ, mul_sub, mean_sum (by omega), mean_sum (by omega)]

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def PositiveBounded (f : Ω → ℝ) (lo hi : ℝ) : Prop :=
  0 < lo ∧ ∀ x, lo ≤ f x ∧ f x ≤ hi

omit [MeasurableSpace Ω] in
theorem PositiveBounded.pos {f : Ω → ℝ} {lo hi : ℝ}
    (hb : PositiveBounded f lo hi) (x : Ω) : 0 < f x := hb.1.trans_le (hb.2 x).1

theorem PositiveBounded.integrable {f : Ω → ℝ} {lo hi : ℝ}
    (hb : PositiveBounded f lo hi) (hf : Measurable f) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable |hi|
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (hb.pos x)]
    exact (hb.2 x).2.trans (le_abs_self hi)

theorem PositiveBounded.mean_bounds {f : Ω → ℝ} {lo hi : ℝ}
    (hb : PositiveBounded f lo hi) (hf : Measurable f) :
    lo ≤ ∫ x, f x ∂μ ∧ (∫ x, f x ∂μ) ≤ hi := by
  constructor
  · simpa using integral_mono (integrable_const (μ := μ) lo) (hb.integrable (μ := μ) hf) (fun x => (hb.2 x).1)
  · simpa using integral_mono (hb.integrable (μ := μ) hf) (integrable_const (μ := μ) hi) (fun x => (hb.2 x).2)

theorem PositiveBounded.mean_pos {f : Ω → ℝ} {lo hi : ℝ}
    (hb : PositiveBounded f lo hi) (hf : Measurable f) : 0 < ∫ x, f x ∂μ :=
  hb.1.trans_le (hb.mean_bounds hf).1

omit [MeasurableSpace Ω] in
theorem PositiveBounded.log_abs_bound {f : Ω → ℝ} {lo hi : ℝ}
    (hb : PositiveBounded f lo hi) (x : Ω) :
    |Real.log (f x)| ≤ |Real.log lo| + |Real.log hi| := by
  have hlow := Real.log_le_log hb.1 (hb.2 x).1
  have hupp := Real.log_le_log (hb.pos x) (hb.2 x).2
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (Real.log lo), le_abs_self (Real.log hi),
    abs_nonneg (Real.log lo), abs_nonneg (Real.log hi)]

theorem PositiveBounded.log_integrable {f : Ω → ℝ} {lo hi : ℝ}
    (hb : PositiveBounded f lo hi) (hf : Measurable f) : Integrable (fun x => Real.log (f x)) μ := by
  apply Integrable.of_bound hf.log.aestronglyMeasurable (|Real.log lo|+|Real.log hi|)
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb.log_abs_bound x

theorem positive_mul_log_integrable {f g : Ω → ℝ} {lo hi lo' hi' : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hbf : PositiveBounded f lo hi) (hbg : PositiveBounded g lo' hi') :
    Integrable (fun x => f x * Real.log (g x)) μ := by
  apply Integrable.of_bound (hf.mul hg.log).aestronglyMeasurable
    (|hi| *(|Real.log lo'|+|Real.log hi'|))
  exact Eventually.of_forall fun x => by
    change |f x * Real.log (g x)| ≤ _
    rw [abs_mul, abs_of_pos (hbf.pos x)]
    exact mul_le_mul ((hbf.2 x).2.trans (le_abs_self hi)) (hbg.log_abs_bound x)
      (abs_nonneg _) (abs_nonneg _)

noncomputable def entropy (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂μ) - (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh

theorem log_ratio_support (u v A B : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hA : 0 < A) (hB : 0 < B) :
    u*(1+Real.log A-Real.log B)-v*(A/B) ≤ u*(Real.log u-Real.log v) := by
  have hz : 0 < v*A/(u*B) := by positivity
  have hl := Real.log_le_sub_one_of_pos hz
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (ne_of_gt hv) (ne_of_gt hA),
    Real.log_mul (ne_of_gt hu) (ne_of_gt hB)] at hl
  have hm := mul_le_mul_of_nonneg_left hl hu.le
  have he : u*(v*A/(u*B)) = v*(A/B) := by field_simp
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem log_sum_integral {f g : Ω → ℝ} {lo hi lo' hi' : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hbf : PositiveBounded f lo hi) (hbg : PositiveBounded g lo' hi') :
    (∫ x, f x ∂μ)*(Real.log (∫ x, f x ∂μ)-Real.log (∫ x, g x ∂μ)) ≤
      ∫ x, f x*(Real.log (f x)-Real.log (g x)) ∂μ := by
  let A := ∫ x, f x ∂μ
  let B := ∫ x, g x ∂μ
  have hA : 0 < A := hbf.mean_pos hf
  have hB : 0 < B := hbg.mean_pos hg
  have hff := positive_mul_log_integrable (μ := μ) hf hf hbf hbf
  have hfg := positive_mul_log_integrable (μ := μ) hf hg hbf hbg
  have hr : Integrable (fun x => f x*(Real.log (f x)-Real.log (g x))) μ := by
    exact (hff.sub hfg).congr (Filter.Eventually.of_forall (fun x => by dsimp; ring))
  have hl : Integrable (fun x => f x*(1+Real.log A-Real.log B)-g x*(A/B)) μ :=
    ((hbf.integrable (μ := μ) hf).mul_const _).sub ((hbg.integrable (μ := μ) hg).mul_const _)
  have h := integral_mono hl hr (fun x => log_ratio_support (f x) (g x) A B
    (hbf.pos x) (hbg.pos x) hA hB)
  have he := integral_sub ((hbf.integrable (μ := μ) hf).mul_const (1+Real.log A-Real.log B))
    ((hbg.integrable (μ := μ) hg).mul_const (A/B))
  rw [he, integral_mul_const, integral_mul_const] at h
  change A*(Real.log A-Real.log B) ≤ _
  change A*(1+Real.log A-Real.log B)-B*(A/B) ≤ _ at h
  have heq : B*(A/B)=A := by field_simp
  rw [heq] at h
  linarith

theorem entropy_variational {f : Ω → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) (c : ℝ) (hc : 0 < c) :
    entropy μ f ≤ ∫ x, f x*(Real.log (f x)-Real.log c)-f x+c ∂μ := by
  have hfint := hb.integrable (μ := μ) hf
  have hff := positive_mul_log_integrable (μ := μ) hf hf hb hb
  have h1 : Integrable (fun x => f x*(Real.log (f x)-Real.log c)) μ := by
    exact (hff.sub (hfint.mul_const (Real.log c))).congr
      (Filter.Eventually.of_forall (fun x => by dsimp; ring))
  have hs := log_ratio_support (∫ x, f x ∂μ) c 1 1 (hb.mean_pos hf) hc zero_lt_one zero_lt_one
  simp only [Real.log_one, add_zero, sub_zero, one_div, inv_one, mul_one] at hs
  have hadd := integral_add (h1.sub hfint) (integrable_const c : Integrable (fun _ : Ω => c) μ)
  have hsub := integral_sub h1 hfint
  have hlog := integral_sub hff (hfint.mul_const (Real.log c))
  simp only [Pi.sub_apply] at hadd hsub hlog
  rw [hadd, hsub]
  simp_rw [mul_sub]
  rw [hlog, integral_mul_const]
  simp only [integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  unfold entropy
  nlinarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
  {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

noncomputable def avgRight (ν : Measure Λ) (f : Ω × Λ → ℝ) (x : Ω) : ℝ := ∫ y, f (x,y) ∂ν
noncomputable def avgLeft (μ : Measure Ω) (f : Ω × Λ → ℝ) (y : Λ) : ℝ := ∫ x, f (x,y) ∂μ

theorem avgRight_measurable {f : Ω × Λ → ℝ} (hf : Measurable f) : Measurable (avgRight ν f) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

theorem avgLeft_measurable {f : Ω × Λ → ℝ} (hf : Measurable f) : Measurable (avgLeft μ f) :=
  hf.stronglyMeasurable.integral_prod_left'.measurable

theorem positiveBounded_avgRight {f : Ω × Λ → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) : PositiveBounded (avgRight ν f) lo hi := by
  refine ⟨hb.1,fun x => ?_⟩
  exact (PositiveBounded.mean_bounds (μ := ν) ⟨hb.1,fun y => hb.2 (x,y)⟩
    (hf.comp measurable_prodMk_left))

theorem positiveBounded_avgLeft {f : Ω × Λ → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) : PositiveBounded (avgLeft μ f) lo hi := by
  refine ⟨hb.1,fun y => ?_⟩
  exact (PositiveBounded.mean_bounds (μ := μ) ⟨hb.1,fun x => hb.2 (x,y)⟩
    (hf.comp measurable_prodMk_right))

theorem avgRight_integral {f : Ω × Λ → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) :
    (∫ x, avgRight ν f x ∂μ) = ∫ p, f p ∂μ.prod ν :=
  (integral_prod f (hb.integrable hf)).symm

theorem avgLeft_integral {f : Ω × Λ → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) :
    (∫ y, avgLeft μ f y ∂ν) = ∫ p, f p ∂μ.prod ν :=
  (integral_prod_symm f (hb.integrable hf)).symm

theorem entropy_sections_integrable {f : Ω × Λ → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) :
    Integrable (fun x => entropy ν (fun y => f (x,y))) μ := by
  have hff := positive_mul_log_integrable (μ := μ.prod ν) hf hf hb hb
  have hg := avgRight_measurable (ν := ν) hf
  have hbg := positiveBounded_avgRight (ν := ν) hf hb
  exact hff.integral_prod_left.sub (positive_mul_log_integrable hg hg hbg hbg)

theorem entropy_chain {f : Ω × Λ → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) :
    entropy (μ.prod ν) f = (∫ x, entropy ν (fun y => f (x,y)) ∂μ) + entropy μ (avgRight ν f) := by
  have hff := positive_mul_log_integrable (μ := μ.prod ν) hf hf hb hb
  have hg := avgRight_measurable (ν := ν) hf
  have hbg := positiveBounded_avgRight (ν := ν) hf hb
  have hgg := positive_mul_log_integrable (μ := μ) hg hg hbg hbg
  have hs := integral_sub hff.integral_prod_left hgg
  have hp := integral_prod (fun p => f p * Real.log (f p)) hff
  have hm := avgRight_integral (μ := μ) (ν := ν) hf hb
  change (∫ p, f p*Real.log (f p) ∂μ.prod ν) -
    (∫ p, f p ∂μ.prod ν)*Real.log (∫ p, f p ∂μ.prod ν) = _
  change _ = (∫ x, (∫ y, f (x,y)*Real.log (f (x,y)) ∂ν) -
      avgRight ν f x*Real.log (avgRight ν f x) ∂μ) +
    ((∫ x, avgRight ν f x*Real.log (avgRight ν f x) ∂μ)-
      (∫ x, avgRight ν f x ∂μ)*Real.log (∫ x, avgRight ν f x ∂μ))
  rw [hs, ← hp, hm]
  ring

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]

theorem entropy_preserving {μ : Measure Ω} {ν : Measure Λ}
    (e : Ω ≃ᵐ Λ) (he : MeasurePreserving e μ ν) (f : Λ → ℝ) :
    entropy μ (fun x => f (e x)) = entropy ν f := by
  unfold entropy
  rw [he.integral_comp' (fun y => f y*Real.log (f y)), he.integral_comp' f]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def coordinateEntropy (μ : ι → Measure Ω) (f : (ι → Ω) → ℝ)
    (i : ι) (x : ι → Ω) : ℝ := entropy (μ i) (fun y => f (Function.update x i y))

omit [Fintype ι] in
theorem measurable_update_pair (i : ι) :
    Measurable (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2) := by
  classical
  refine measurable_pi_lambda _ (fun j => ?_)
  by_cases h : j=i
  · subst j
    simpa only [Function.update_self] using measurable_snd
  · simpa only [Function.update_of_ne h, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst

theorem coordinateEntropy_integrable {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → Ω) → ℝ} {lo hi : ℝ} (hf : Measurable f)
    (hb : PositiveBounded f lo hi) (i : ι) :
    Integrable (coordinateEntropy μ f i) (Measure.pi μ) := by
  exact entropy_sections_integrable (hf.comp (measurable_update_pair i))
    ⟨hb.1,fun p => hb.2 (Function.update p.1 i p.2)⟩

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

noncomputable def finConsEquiv : (Ω × (Fin n → Ω)) ≃ᵐ (Fin (n+1) → Ω) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) 0).symm

@[simp] theorem finConsEquiv_apply (p : Ω × (Fin n → Ω)) :
    finConsEquiv p = Fin.cons p.1 p.2 := by
  simp [finConsEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem finCons_preserving (μ : Fin (n+1) → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (finConsEquiv (n := n))
      ((μ 0).prod (Measure.pi (fun i => μ i.succ))) (Measure.pi μ) := by
  simpa only [Fin.zero_succAbove, finConsEquiv] using (measurePreserving_piFinSuccAbove μ 0).symm

theorem integral_finCons (μ : Fin (n+1) → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin (n+1) → Ω) → ℝ) :
    (∫ p, f (Fin.cons p.1 p.2) ∂(μ 0).prod (Measure.pi (fun i => μ i.succ))) =
      ∫ x, f x ∂Measure.pi μ := by
  simpa only [finConsEquiv_apply] using (finCons_preserving μ).integral_comp' f

omit [MeasurableSpace Ω] in
theorem update_cons_zero (a b : Ω) (x : Fin n → Ω) :
    Function.update (Fin.cons a x : Fin (n+1) → Ω) 0 b = (Fin.cons b x : Fin (n+1) → Ω) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [MeasurableSpace Ω] in
theorem update_cons_succ (a b : Ω) (x : Fin n → Ω) (j : Fin n) :
    Function.update (Fin.cons a x : Fin (n+1) → Ω) j.succ b =
      (Fin.cons a (Function.update x j b) : Fin (n+1) → Ω) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
    simp
  · by_cases h : k=j
    · subst k; simp
    · simp [h, Fin.succ_inj]

@[simp] theorem coordinateEntropy_cons_zero (μ : Fin (n+1) → Measure Ω)
    (f : (Fin (n+1) → Ω) → ℝ) (a : Ω) (x : Fin n → Ω) :
    coordinateEntropy μ f 0 (Fin.cons a x) = entropy (μ 0) (fun b => f (Fin.cons b x)) := by
  simp only [coordinateEntropy, update_cons_zero]

@[simp] theorem coordinateEntropy_cons_succ (μ : Fin (n+1) → Measure Ω)
    (f : (Fin (n+1) → Ω) → ℝ) (a : Ω) (x : Fin n → Ω) (j : Fin n) :
    coordinateEntropy μ f j.succ (Fin.cons a x) =
      coordinateEntropy (fun i => μ i.succ) (fun y => f (Fin.cons a y)) j x := by
  simp only [coordinateEntropy, update_cons_succ]

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
  {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem entropy_average_le {f : Ω × Λ → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) :
    entropy μ (avgRight ν f) ≤ ∫ y, entropy μ (fun x => f (x,y)) ∂ν := by
  let G := avgRight ν f
  let H := avgLeft μ f
  let M := ∫ p, f p ∂μ.prod ν
  have hG := avgRight_measurable (ν := ν) hf
  have hH := avgLeft_measurable (μ := μ) hf
  have hbG := positiveBounded_avgRight (ν := ν) hf hb
  have hbH := positiveBounded_avgLeft (μ := μ) hf hb
  have hgm : (∫ x, G x ∂μ) = M := avgRight_integral hf hb
  have hhm : (∫ y, H y ∂ν) = M := avgLeft_integral hf hb
  have hff := positive_mul_log_integrable (μ := μ.prod ν) hf hf hb hb
  have hfH := positive_mul_log_integrable (μ := μ.prod ν) hf
    (hH.comp measurable_snd) hb ⟨hbH.1,fun p => hbH.2 p.2⟩
  have hdiff : Integrable (fun p => f p*(Real.log (f p)-Real.log (H p.2))) (μ.prod ν) :=
    (hff.sub hfH).congr (Filter.Eventually.of_forall (fun p => by dsimp [H]; ring))
  have hgg := positive_mul_log_integrable (μ := μ) hG hG hbG hbG
  have hleft : Integrable (fun x => G x*(Real.log (G x)-Real.log M)) μ :=
    (hgg.sub ((hbG.integrable (μ := μ) hG).mul_const (Real.log M))).congr
      (Filter.Eventually.of_forall (fun x => by dsimp [G]; ring))
  have hpoint (x : Ω) : G x*(Real.log (G x)-Real.log M) ≤
      ∫ y, f (x,y)*(Real.log (f (x,y))-Real.log (H y)) ∂ν := by
    have h := log_sum_integral (μ := ν) (hf.comp measurable_prodMk_left) hH
      (show PositiveBounded (fun y => f (x,y)) lo hi from ⟨hb.1,fun y => hb.2 (x,y)⟩) hbH
    rw [hhm] at h
    exact h
  have hineq := integral_mono hleft hdiff.integral_prod_left hpoint
  have hl : (∫ x, G x*(Real.log (G x)-Real.log M) ∂μ) = entropy μ G := by
    simp_rw [mul_sub]
    rw [integral_sub hgg ((hbG.integrable (μ := μ) hG).mul_const (Real.log M)), integral_mul_const]
    unfold entropy
    rw [hgm]
  have hr (y : Λ) : (∫ x, f (x,y)*(Real.log (f (x,y))-Real.log (H y)) ∂μ) =
      entropy μ (fun x => f (x,y)) := by
    have hfy : Measurable (fun x => f (x,y)) := hf.comp measurable_prodMk_right
    have hby : PositiveBounded (fun x => f (x,y)) lo hi := ⟨hb.1,fun x => hb.2 (x,y)⟩
    simp_rw [mul_sub]
    rw [integral_sub (positive_mul_log_integrable hfy hfy hby hby)
      ((hby.integrable hfy).mul_const (Real.log (H y))), integral_mul_const]
    rfl
  rw [hl, integral_integral_swap hdiff] at hineq
  simpa only [hr] using hineq

theorem entropy_product_le {f : Ω × Λ → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) :
    entropy (μ.prod ν) f ≤ (∫ x, entropy ν (fun y => f (x,y)) ∂μ) +
      ∫ y, entropy μ (fun x => f (x,y)) ∂ν := by
  rw [entropy_chain (μ := μ) (ν := ν) hf hb]
  exact add_le_add le_rfl (entropy_average_le (μ := μ) (ν := ν) hf hb)

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω]

theorem entropy_fin_tensorization (n : ℕ) (μ : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] {f : (Fin n → Ω) → ℝ} {lo hi : ℝ}
    (hf : Measurable f) (hb : PositiveBounded f lo hi) :
    entropy (Measure.pi μ) f ≤ ∑ i, ∫ x, coordinateEntropy μ f i x ∂Measure.pi μ := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext x
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he]
    simp [entropy]
  | succ n ih =>
    let ν := Measure.pi (fun i : Fin n => μ i.succ)
    let F : Ω × (Fin n → Ω) → ℝ := fun p => f (Fin.cons p.1 p.2)
    have hF : Measurable F := by
      simpa only [Function.comp_def, finConsEquiv_apply] using hf.comp (finConsEquiv (n := n)).measurable
    have hbF : PositiveBounded F lo hi := ⟨hb.1,fun p => hb.2 _⟩
    have hprod := entropy_product_le (μ := μ 0) (ν := ν) hF hbF
    have he : entropy ((μ 0).prod ν) F = entropy (Measure.pi μ) f := by
      simpa only [finConsEquiv_apply] using entropy_preserving finConsEquiv (finCons_preserving μ) f
    rw [he] at hprod
    have hcoord (i : Fin (n+1)) : Integrable (fun p : Ω × (Fin n → Ω) =>
        coordinateEntropy μ f i (Fin.cons p.1 p.2)) ((μ 0).prod ν) := by
      have h := (finCons_preserving μ).integrable_comp_emb
        (finConsEquiv (n := n)).measurableEmbedding (g := coordinateEntropy μ f i)
      have hi := coordinateEntropy_integrable (μ := μ) hf hb i
      simpa only [Function.comp_def, finConsEquiv_apply] using (h.mpr hi)
    have hhead : (∫ x, coordinateEntropy μ f 0 x ∂Measure.pi μ) =
        ∫ y, entropy (μ 0) (fun a => F (a,y)) ∂ν := by
      rw [← integral_finCons μ]
      rw [integral_prod_symm _ (hcoord 0)]
      simp only [coordinateEntropy_cons_zero, integral_const, probReal_univ, one_smul]
      rfl
    have htail (j : Fin n) : (∫ x, coordinateEntropy μ f j.succ x ∂Measure.pi μ) =
        ∫ a, ∫ y, coordinateEntropy (fun i => μ i.succ) (fun z => F (a,z)) j y ∂ν ∂μ 0 := by
      rw [← integral_finCons μ, integral_prod _ (hcoord j.succ)]
      simp only [coordinateEntropy_cons_succ]
      rfl
    have htailint (j : Fin n) : Integrable (fun a =>
        ∫ y, coordinateEntropy (fun i => μ i.succ) (fun z => F (a,z)) j y ∂ν) (μ 0) := by
      simpa only [coordinateEntropy_cons_succ] using (hcoord j.succ).integral_prod_left
    have hineq := integral_mono (entropy_sections_integrable (μ := μ 0) (ν := ν) hF hbF)
      (integrable_finsetSum Finset.univ (fun j _ => htailint j))
      (fun a => ih (fun i => μ i.succ) (hF.comp measurable_prodMk_left)
        (show PositiveBounded (fun y => F (a,y)) lo hi from ⟨hb.1,fun y => hb.2 _⟩))
    rw [integral_finsetSum _ (fun j _ => htailint j)] at hineq
    rw [Fin.sum_univ_succ, hhead]
    simp_rw [htail]
    linarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω]

theorem bounded_measurable_integrable {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → ℝ} {C : ℝ} (hm : Measurable h) (hb : ∀ x, |h x| ≤ C) : Integrable h μ := by
  apply Integrable.of_bound hm.aestronglyMeasurable C
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem bounded_integral_abs {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → ℝ} {C : ℝ} (hm : Measurable h) (hb : ∀ x, |h x| ≤ C) :
    |∫ x, h x ∂μ| ≤ C := by
  have hi := bounded_measurable_integrable (μ := μ) hm hb
  apply abs_le.mpr
  constructor
  · have he := integral_mono (integrable_const (μ := μ) (-C)) hi (fun x => (abs_le.mp (hb x)).1)
    simpa using he
  · have he := integral_mono hi (integrable_const (μ := μ) C) (fun x => (abs_le.mp (hb x)).2)
    simpa using he

theorem integral_coordinate_resampling {n : ℕ} (μ : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] {h : (Fin n → Ω) → ℝ} {C : ℝ}
    (hm : Measurable h) (hb : ∀ x, |h x| ≤ C) (i : Fin n) :
    (∫ x, ∫ y, h (Function.update x i y) ∂μ i ∂Measure.pi μ) = ∫ x, h x ∂Measure.pi μ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) i).symm
    let ν := Measure.pi (fun j => μ (i.succAbove j))
    have he : MeasurePreserving e ((μ i).prod ν) (Measure.pi μ) :=
      (measurePreserving_piFinSuccAbove μ i).symm
    let H : (Fin (n+1) → Ω) → ℝ := fun x => ∫ y, h (Function.update x i y) ∂μ i
    have hH : Measurable H :=
      (hm.comp (measurable_update_pair i)).stronglyMeasurable.integral_prod_right'.measurable
    have hHB (x : Fin (n+1) → Ω) : |H x| ≤ C :=
      bounded_integral_abs ((hm.comp (measurable_update_pair i)).comp measurable_prodMk_left)
        (fun y => hb _)
    have hHI : Integrable (fun p => H (e p)) ((μ i).prod ν) :=
      bounded_measurable_integrable (hH.comp e.measurable) (fun p => hHB _)
    have hhI : Integrable (fun p => h (e p)) ((μ i).prod ν) :=
      bounded_measurable_integrable (hm.comp e.measurable) (fun p => hb _)
    change (∫ x, H x ∂Measure.pi μ) = _
    rw [← he.integral_comp' H, ← he.integral_comp' h]
    rw [integral_prod_symm _ hHI, integral_prod_symm _ hhI]
    apply integral_congr_ae
    filter_upwards [] with z
    change (∫ a, ∫ b, h (Function.update (i.insertNth a z) i b) ∂μ i ∂μ i) =
      ∫ a, h (i.insertNth a z) ∂μ i
    simp only [Fin.update_insertNth, integral_const, probReal_univ, one_smul]

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology ProbabilityTheory
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
theorem positiveBounded_exp {Z : Ω → ℝ} {B : ℝ} (hZ : ∀ x, |Z x| ≤ B) (s : ℝ) :
    PositiveBounded (fun x => Real.exp (s*Z x)) (Real.exp (- (|s| * B))) (Real.exp (|s| * B)) := by
  refine ⟨Real.exp_pos _,fun x => ?_⟩
  have h := mul_le_mul_of_nonneg_left (hZ x) (abs_nonneg s)
  rw [← abs_mul] at h
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp h).1, Real.exp_le_exp.mpr (abs_le.mp h).2⟩

theorem bounded_exp_integrable {Z : Ω → ℝ} {B : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B) (s : ℝ) :
    Integrable (fun x => Real.exp (s*Z x)) μ :=
  (positiveBounded_exp hZ s).integrable ((measurable_const.mul hZm).exp)

theorem bounded_integrableExpSet {Z : Ω → ℝ} {B : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B) : integrableExpSet Z μ = Set.univ := by
  ext s
  simp only [Set.mem_univ, iff_true]
  exact bounded_exp_integrable hZm hZ s

theorem bounded_mgf_hasDerivAt {Z : Ω → ℝ} {B : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B) (s : ℝ) :
    HasDerivAt (mgf Z μ) (∫ x, Z x*Real.exp (s*Z x) ∂μ) s := by
  apply hasDerivAt_mgf
  rw [bounded_integrableExpSet hZm hZ, interior_univ]
  trivial

theorem bounded_cgf_hasDerivAt {Z : Ω → ℝ} {B : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B) (s : ℝ) :
    HasDerivAt (cgf Z μ) ((∫ x, Z x*Real.exp (s*Z x) ∂μ)/mgf Z μ s) s :=
  (bounded_mgf_hasDerivAt hZm hZ s).log (ne_of_gt (mgf_pos (bounded_exp_integrable hZm hZ s)))

omit [IsProbabilityMeasure μ] in
theorem entropy_exp_identity {Z : Ω → ℝ} (s : ℝ) :
    entropy μ (fun x => Real.exp (s*Z x)) =
      s*(∫ x, Z x*Real.exp (s*Z x) ∂μ) - mgf Z μ s*cgf Z μ s := by
  unfold entropy cgf mgf
  simp only [Real.log_exp]
  have he : (fun x => Real.exp (s*Z x)*(s*Z x)) =
      (fun x => s*(Z x*Real.exp (s*Z x))) := by funext x; ring
  rw [he, integral_const_mul]

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh

noncomputable def entropyKernel (s z b : ℝ) : ℝ := Real.exp (s*z)*(Real.exp (-s*(z-b))+s*(z-b)-1)

theorem entropyKernel_bound {s z b B : ℝ} (hz : 0 ≤ z) (hzB : z ≤ B)
    (hb : 0 ≤ b) (hbz : b ≤ z) :
    |entropyKernel s z b| ≤ Real.exp (|s| * B)*(Real.exp (|s| * B)+|s| * B+1) := by
  have hB : 0 ≤ B := hz.trans hzB
  have hd : |z-b| ≤ B := by rw [abs_of_nonneg (sub_nonneg.mpr hbz)]; linarith
  have hsz : |s*z| ≤ |s| * B := by rw [abs_mul, abs_of_nonneg hz]; exact mul_le_mul_of_nonneg_left hzB (abs_nonneg _)
  have hsd : |s*(z-b)| ≤ |s| * B := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hd (abs_nonneg _)
  have hez : Real.exp (s*z) ≤ Real.exp (|s| * B) := Real.exp_le_exp.mpr ((le_abs_self _).trans hsz)
  have hed : Real.exp (-s*(z-b)) ≤ Real.exp (|s| * B) := by
    apply Real.exp_le_exp.mpr
    nlinarith [(abs_le.mp hsd).1]
  have hphi : |Real.exp (-s*(z-b))+s*(z-b)-1| ≤ Real.exp (|s| * B)+|s| * B+1 := by
    calc
      _ ≤ |Real.exp (-s*(z-b))+s*(z-b)|+|1| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (Real.exp (-s*(z-b))+s*(z-b)) (-1)
      _ ≤ |Real.exp (-s*(z-b))|+|s*(z-b)|+|1| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by rw [abs_of_pos (Real.exp_pos _), abs_one]; linarith
  unfold entropyKernel
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hez hphi (abs_nonneg _) (Real.exp_pos _).le

theorem entropyKernel_variational (s z b : ℝ) :
    Real.exp (s*z)*(Real.log (Real.exp (s*z))-Real.log (Real.exp (s*b)))-Real.exp (s*z)+Real.exp (s*b)
      = entropyKernel s z b := by
  simp only [Real.log_exp]
  have he : Real.exp (s*z)*Real.exp (-s*(z-b)) = Real.exp (s*b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold entropyKernel
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Fin n → Measure Ω)
  [∀ i, IsProbabilityMeasure (μ i)]

theorem exponential_entropy_coordinate_sum {Z : (Fin n → Ω) → ℝ}
    {Zi : Fin n → (Fin n → Ω) → ℝ} {B : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, 0 ≤ Z x ∧ Z x ≤ B)
    (hZim : ∀ i, Measurable (Zi i)) (hZi : ∀ i x, 0 ≤ Zi i x ∧ Zi i x ≤ Z x)
    (hinv : ∀ i x y, Zi i (Function.update x i y) = Zi i x) (s : ℝ) :
    entropy (Measure.pi μ) (fun x => Real.exp (s*Z x)) ≤
      ∑ i, ∫ x, entropyKernel s (Z x) (Zi i x) ∂Measure.pi μ := by
  let E := fun x => Real.exp (s*Z x)
  have hEm : Measurable E := (measurable_const.mul hZm).exp
  have hZabs (x) : |Z x| ≤ B := by rw [abs_of_nonneg (hZ x).1]; exact (hZ x).2
  have hEb := positiveBounded_exp hZabs s
  have hK (i : Fin n) : Measurable (fun x => entropyKernel s (Z x) (Zi i x)) := by
    unfold entropyKernel
    fun_prop
  have hKb (i : Fin n) (x) : |entropyKernel s (Z x) (Zi i x)| ≤
      Real.exp (|s| * B)*(Real.exp (|s| * B)+|s| * B+1) :=
    entropyKernel_bound (hZ x).1 (hZ x).2 (hZi i x).1 (hZi i x).2
  apply (entropy_fin_tensorization n μ hEm hEb).trans
  apply Finset.sum_le_sum
  intro i _
  have hrightm : Measurable (fun x => ∫ y, entropyKernel s (Z (Function.update x i y))
      (Zi i (Function.update x i y)) ∂μ i) :=
    ((hK i).comp (measurable_update_pair i)).stronglyMeasurable.integral_prod_right'.measurable
  have hrightb (x) : |∫ y, entropyKernel s (Z (Function.update x i y))
      (Zi i (Function.update x i y)) ∂μ i| ≤
      Real.exp (|s| * B)*(Real.exp (|s| * B)+|s| * B+1) := by
    apply bounded_integral_abs
    · exact ((hK i).comp (measurable_update_pair i)).comp measurable_prodMk_left
    · exact fun y => hKb i _
  have hp (x) : coordinateEntropy μ E i x ≤
      ∫ y, entropyKernel s (Z (Function.update x i y)) (Zi i (Function.update x i y)) ∂μ i := by
    have hm : Measurable (fun y => E (Function.update x i y)) :=
      (hEm.comp (measurable_update_pair i)).comp measurable_prodMk_left
    have hb : PositiveBounded (fun y => E (Function.update x i y))
        (Real.exp (-(|s| * B))) (Real.exp (|s| * B)) := ⟨hEb.1,fun y => hEb.2 _⟩
    have hv := entropy_variational (μ := μ i) hm hb (Real.exp (s*Zi i x)) (Real.exp_pos _)
    apply hv.trans_eq
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hinv]
    exact entropyKernel_variational s _ _
  have h := integral_mono (coordinateEntropy_integrable hEm hEb i)
    (bounded_measurable_integrable hrightm hrightb) hp
  rw [integral_coordinate_resampling μ (hK i) (hKb i) i] at h
  exact h

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh

theorem nonneg_on_nonneg_of_derivative {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (h0 : 0 ≤ f 0)
    (hp : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun y _ => (hd y).continuousAt.continuousWithinAt)
    (fun y _ => (hd y).hasDerivWithinAt)
    (fun y hy => hp y (interior_subset hy))
  exact h0.trans (hm (by simp) hx hx)

theorem exp_negative_remainder_le {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x)-1+x ≤ x^2/2 := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => 1-z+z^2/2-Real.exp (-z))
      (-1+y+Real.exp (-y)) y := by
    exact ((((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub ((hasDerivAt_id y).neg.exp)).congr_deriv (by dsimp; ring)
  have h := nonneg_on_nonneg_of_derivative hd (by norm_num) (fun y _ => by
    have h := Real.add_one_le_exp (-y)
    linarith) hx
  linarith

theorem exp_remainder_derivative_aux {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x-1)*Real.exp x+1 := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => (z-1)*Real.exp z+1)
      (y*Real.exp y) y := by
    exact ((((hasDerivAt_id y).sub_const 1).mul (Real.hasDerivAt_exp y)).add_const 1).congr_deriv (by dsimp; ring)
  exact nonneg_on_nonneg_of_derivative hd (by norm_num) (fun y hy => mul_nonneg hy (Real.exp_pos y).le) hx

theorem exp_remainder_ratio_numerator {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x-2)*Real.exp x+x+2 := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => (z-2)*Real.exp z+z+2)
      ((y-1)*Real.exp y+1) y := by
    exact (((((hasDerivAt_id y).sub_const 2).mul (Real.hasDerivAt_exp y)).add
      (hasDerivAt_id y)).add_const 2).congr_deriv (by dsimp; ring)
  exact nonneg_on_nonneg_of_derivative hd (by norm_num) (fun _ hy => exp_remainder_derivative_aux hy) hx

theorem exp_remainder_ratio_monotone :
    MonotoneOn (fun x : ℝ => (Real.exp x-x-1)/x^2) (Set.Ioi 0) := by
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt (fun y : ℝ => (Real.exp y-y-1)/y^2)
      (((Real.exp x-1)*x^2-(Real.exp x-x-1)*(2*x))/(x^2)^2) x := by
    exact ((((Real.hasDerivAt_exp x).sub (hasDerivAt_id x)).sub_const 1).div
      ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 (ne_of_gt hx))).congr_deriv (by dsimp; ring)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    apply div_nonneg _ (sq_nonneg _)
    have h := mul_nonneg hx'.le (exp_remainder_ratio_numerator hx'.le)
    nlinarith

theorem exp_scaled_remainder_le {t D : ℝ} (ht : 0 ≤ t) (hD : 0 ≤ D) (hD1 : D ≤ 1) :
    Real.exp (t*D)-t*D-1 ≤ D^2*(Real.exp t-t-1) := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num
  rcases hD.eq_or_lt with rfl | hD
  · norm_num
  have hm := exp_remainder_ratio_monotone (mul_pos ht hD) ht
    (mul_le_of_le_one_right ht.le hD1)
  have hpos : 0 < (t*D)^2 := sq_pos_of_pos (mul_pos ht hD)
  have htpos : 0 < t^2 := sq_pos_of_pos ht
  have h := (div_le_div_iff₀ hpos htpos).mp hm
  have he : (t*D)^2 = t^2*D^2 := mul_pow t D 2
  rw [he] at h
  nlinarith

theorem lower_mgf_scalar_comparison {t a : ℝ} (ht : 0 ≤ t) (ha : 1 ≤ a) :
    (1-a*t)*(Real.exp t-t-1) ≤ t^2/2 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y^2/2-(1-y)*(Real.exp y-y-1))
      (x*(Real.exp x-1)) x := by
    exact ((((hasDerivAt_id x).pow 2).div_const 2).sub
      (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul
        (((Real.hasDerivAt_exp x).sub (hasDerivAt_id x)).sub_const 1))).congr_deriv (by dsimp; ring)
  have h := nonneg_on_nonneg_of_derivative hd (by norm_num) (fun x hx =>
    mul_nonneg hx (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx))) ht
  have hp : 0 ≤ Real.exp t-t-1 := by have := Real.add_one_le_exp t; linarith
  have hmul := mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) ht) hp
  nlinarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Fin n → Measure Ω)
  [∀ i, IsProbabilityMeasure (μ i)]

theorem self_bounding_entropy_bound {Z : (Fin n → Ω) → ℝ}
    {Zi : Fin n → (Fin n → Ω) → ℝ} {B a s c : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, 0 ≤ Z x ∧ Z x ≤ B)
    (hZim : ∀ i, Measurable (Zi i)) (hZi : ∀ i x, 0 ≤ Zi i x ∧ Zi i x ≤ Z x)
    (hinv : ∀ i x y, Zi i (Function.update x i y) = Zi i x)
    (hc : 0 ≤ c) (hsq : ∀ x, (∑ i, (Z x-Zi i x)^2) ≤ a*Z x)
    (hrem : ∀ i x, Real.exp (-s*(Z x-Zi i x))+s*(Z x-Zi i x)-1 ≤ c*(Z x-Zi i x)^2) :
    entropy (Measure.pi μ) (fun x => Real.exp (s*Z x)) ≤
      c*a*(∫ x, Z x*Real.exp (s*Z x) ∂Measure.pi μ) := by
  have hK (i : Fin n) : Integrable (fun x => entropyKernel s (Z x) (Zi i x)) (Measure.pi μ) := by
    apply bounded_measurable_integrable (C := Real.exp (|s| * B)*(Real.exp (|s| * B)+|s| * B+1))
    · unfold entropyKernel
      fun_prop
    · exact fun x => entropyKernel_bound (hZ x).1 (hZ x).2 (hZi i x).1 (hZi i x).2
  have hZE : Integrable (fun x => Z x*Real.exp (s*Z x)) (Measure.pi μ) := by
    apply bounded_measurable_integrable (hZm.mul (measurable_const.mul hZm).exp) (C := B*Real.exp (|s| * B))
    intro x
    change |Z x*Real.exp (s*Z x)| ≤ _
    rw [abs_mul, abs_of_nonneg (hZ x).1, abs_of_pos (Real.exp_pos _)]
    have hsZ : s*Z x ≤ |s| * B := by
      calc
        s*Z x ≤ |s| * Z x := mul_le_mul_of_nonneg_right (le_abs_self s) (hZ x).1
        _ ≤ _ := mul_le_mul_of_nonneg_left (hZ x).2 (abs_nonneg s)
    exact mul_le_mul (hZ x).2 (Real.exp_le_exp.mpr hsZ) (Real.exp_pos _).le ((hZ x).1.trans (hZ x).2)
  have hp (x) : (∑ i, entropyKernel s (Z x) (Zi i x)) ≤ c*a*(Z x*Real.exp (s*Z x)) := by
    calc
      _ ≤ ∑ i, Real.exp (s*Z x)*(c*(Z x-Zi i x)^2) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrem i x) (Real.exp_pos _).le)
      _ = (Real.exp (s*Z x)*c)*(∑ i, (Z x-Zi i x)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ (Real.exp (s*Z x)*c)*(a*Z x) :=
        mul_le_mul_of_nonneg_left (hsq x) (mul_nonneg (Real.exp_pos _).le hc)
      _ = _ := by ring
  calc
    _ ≤ ∑ i, ∫ x, entropyKernel s (Z x) (Zi i x) ∂Measure.pi μ :=
      exponential_entropy_coordinate_sum μ hZm hZ hZim hZi hinv s
    _ = ∫ x, ∑ i, entropyKernel s (Z x) (Zi i x) ∂Measure.pi μ :=
      (integral_finsetSum _ (fun i _ => hK i)).symm
    _ ≤ ∫ x, c*a*(Z x*Real.exp (s*Z x)) ∂Measure.pi μ :=
      integral_mono (integrable_finsetSum _ (fun i _ => hK i)) (hZE.const_mul _) hp
    _ = _ := integral_const_mul _ _

theorem self_bounding_entropy_upper {Z : (Fin n → Ω) → ℝ}
    {Zi : Fin n → (Fin n → Ω) → ℝ} {B a t : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, 0 ≤ Z x ∧ Z x ≤ B)
    (hZim : ∀ i, Measurable (Zi i)) (hZi : ∀ i x, 0 ≤ Zi i x ∧ Zi i x ≤ Z x)
    (hinv : ∀ i x y, Zi i (Function.update x i y) = Zi i x)
    (hsq : ∀ x, (∑ i, (Z x-Zi i x)^2) ≤ a*Z x) (ht : 0 ≤ t) :
    entropy (Measure.pi μ) (fun x => Real.exp (t*Z x)) ≤
      (t^2/2)*a*(∫ x, Z x*Real.exp (t*Z x) ∂Measure.pi μ) := by
  apply self_bounding_entropy_bound μ hZm hZ hZim hZi hinv (by positivity) hsq
  intro i x
  have h := exp_negative_remainder_le (mul_nonneg ht (sub_nonneg.mpr (hZi i x).2))
  simp only [neg_mul] at h ⊢
  nlinarith

theorem self_bounding_entropy_lower {Z : (Fin n → Ω) → ℝ}
    {Zi : Fin n → (Fin n → Ω) → ℝ} {B a t : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, 0 ≤ Z x ∧ Z x ≤ B)
    (hZim : ∀ i, Measurable (Zi i)) (hZi : ∀ i x, 0 ≤ Zi i x ∧ Zi i x ≤ Z x)
    (hinv : ∀ i x y, Zi i (Function.update x i y) = Zi i x)
    (hsq : ∀ x, (∑ i, (Z x-Zi i x)^2) ≤ a*Z x)
    (hD : ∀ i x, Z x-Zi i x ≤ 1) (ht : 0 ≤ t) :
    entropy (Measure.pi μ) (fun x => Real.exp (-t*Z x)) ≤
      (Real.exp t-t-1)*a*(∫ x, Z x*Real.exp (-t*Z x) ∂Measure.pi μ) := by
  apply self_bounding_entropy_bound μ hZm hZ hZim hZi hinv
    (by have := Real.add_one_le_exp t; linarith) hsq
  intro i x
  have h := exp_scaled_remainder_le ht (sub_nonneg.mpr (hZi i x).2) (hD i x)
  simpa only [neg_neg, neg_mul, sub_eq_add_neg, mul_comm] using h

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology ProbabilityTheory
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem entropy_upper_cgf_inequality {Z : Ω → ℝ} {B a t : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B)
    (he : entropy μ (fun x => Real.exp (t*Z x)) ≤
      (t^2/2)*a*(∫ x, Z x*Real.exp (t*Z x) ∂μ)) :
    t*(1-a*t/2)*deriv (cgf Z μ) t ≤ cgf Z μ t := by
  have hd := bounded_cgf_hasDerivAt (μ := μ) hZm hZ t
  rw [hd.deriv]
  rw [entropy_exp_identity] at he
  have hp := mgf_pos (bounded_exp_integrable (μ := μ) hZm hZ t)
  apply (mul_le_mul_iff_of_pos_right hp).mp
  have hcancel : ((∫ x, Z x*Real.exp (t*Z x) ∂μ)/mgf Z μ t)*mgf Z μ t =
      ∫ x, Z x*Real.exp (t*Z x) ∂μ := div_mul_cancel₀ _ (ne_of_gt hp)
  rw [mul_assoc, hcancel]
  nlinarith

theorem bounded_negative_cgf_hasDerivAt {Z : Ω → ℝ} {B : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B) (t : ℝ) :
    HasDerivAt (fun s => cgf Z μ (-s))
      (-(∫ x, Z x*Real.exp (-t*Z x) ∂μ)/mgf Z μ (-t)) t := by
  have h := (bounded_cgf_hasDerivAt (μ := μ) hZm hZ (-t)).comp t (hasDerivAt_id t).neg
  exact h.congr_deriv (by ring)

theorem entropy_lower_cgf_inequality {Z : Ω → ℝ} {B a t : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B)
    (he : entropy μ (fun x => Real.exp (-t*Z x)) ≤
      (Real.exp t-t-1)*a*(∫ x, Z x*Real.exp (-t*Z x) ∂μ)) :
    (t+a*(Real.exp t-t-1))*deriv (fun s => cgf Z μ (-s)) t ≤ cgf Z μ (-t) := by
  have hd := bounded_negative_cgf_hasDerivAt (μ := μ) hZm hZ t
  rw [hd.deriv]
  rw [entropy_exp_identity] at he
  have hp := mgf_pos (bounded_exp_integrable (μ := μ) hZm hZ (-t))
  apply (mul_le_mul_iff_of_pos_right hp).mp
  have hcancel : (-(∫ x, Z x*Real.exp (-t*Z x) ∂μ)/mgf Z μ (-t))*mgf Z μ (-t) =
      -(∫ x, Z x*Real.exp (-t*Z x) ∂μ) := div_mul_cancel₀ _ (ne_of_gt hp)
  rw [mul_assoc, hcancel]
  nlinarith

theorem negative_cgf_nonpositive {Z : Ω → ℝ} {B t : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, 0 ≤ Z x ∧ Z x ≤ B) (ht : 0 ≤ t) : cgf Z μ (-t) ≤ 0 := by
  have hab (x) : |Z x| ≤ B := by rw [abs_of_nonneg (hZ x).1]; exact (hZ x).2
  have hp := mgf_pos (bounded_exp_integrable (μ := μ) hZm hab (-t))
  have hle : mgf Z μ (-t) ≤ 1 := by
    have hi := integral_mono (bounded_exp_integrable (μ := μ) hZm hab (-t))
      (integrable_const (μ := μ) 1) (fun x => Real.exp_le_one_iff.mpr (by nlinarith [(hZ x).1]))
    change (∫ x, Real.exp (-t*Z x) ∂μ) ≤ 1
    simpa only [integral_const, probReal_univ, one_smul] using hi
  exact Real.log_nonpos hp.le hle

theorem bounded_cgf_deriv_zero {Z : Ω → ℝ} {B : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B) :
    HasDerivAt (cgf Z μ) (∫ x, Z x ∂μ) 0 := by
  simpa only [zero_mul, Real.exp_zero, mul_one, mgf_zero, div_one] using
    bounded_cgf_hasDerivAt (μ := μ) hZm hZ 0

theorem bounded_negative_cgf_deriv_zero {Z : Ω → ℝ} {B : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B) :
    HasDerivAt (fun s => cgf Z μ (-s)) (-(∫ x, Z x ∂μ)) 0 := by
  simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one, mgf_zero, div_one] using
    bounded_negative_cgf_hasDerivAt (μ := μ) hZm hZ 0

end EmpiricalBernstein.SVP.EBFresh
end


section

open Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh

lemma differential_ratio_bound {ψ r ψ' r' : ℝ → ℝ} {m s : ℝ} (hs : 0 < s)
    (hψzero : ψ 0 = 0) (hrzero : r 0 = 0)
    (hψ0 : HasDerivAt ψ m 0) (hr0 : HasDerivAt r 1 0)
    (hψ : ∀ t ∈ Set.Ioc 0 s, HasDerivAt ψ (ψ' t) t)
    (hr : ∀ t ∈ Set.Ioc 0 s, HasDerivAt r (r' t) t)
    (hrpos : ∀ t ∈ Set.Ioc 0 s, 0 < r t)
    (hcross : ∀ t ∈ Set.Ioc 0 s, ψ' t * r t - ψ t * r' t ≤ 0) :
    ψ s ≤ m * r s := by
  let f : ℝ → ℝ := fun t => ψ t / r t
  have hd (t : ℝ) (ht : t ∈ Set.Ioc 0 s) :
      HasDerivAt f ((ψ' t * r t - ψ t * r' t) / (r t)^2) t :=
    (hψ t ht).div (hr t ht) (ne_of_gt (hrpos t ht))
  have ha : AntitoneOn f (Set.Ioc 0 s) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 s)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact div_nonpos_of_nonpos_of_nonneg (hcross t (interior_subset ht)) (sq_nonneg _)
  have hp := (hasDerivAt_iff_tendsto_slope_left_right.mp hψ0).2
  have hq := (hasDerivAt_iff_tendsto_slope_left_right.mp hr0).2
  have hlim0 := hp.div hq (by norm_num : (1 : ℝ) ≠ 0)
  have he : ∀ t, slope ψ 0 t / slope r 0 t = f t := by
    intro t
    by_cases ht : t = 0
    · subst t; simp [slope, f, hψzero, hrzero]
    · simp only [slope, hψzero, hrzero, vsub_eq_sub, sub_zero, smul_eq_mul, f]
      field_simp
  have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 m) := by
    simpa only [div_one] using hlim0.congr he
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < s :=
    (gt_mem_nhds hs).filter_mono nhdsWithin_le_nhds
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), f s ≤ f t := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hts
    exact ha ⟨ht, hts.le⟩ ⟨hs, le_rfl⟩ hts.le
  have hbound : f s ≤ m := ge_of_tendsto hlim hb
  exact (div_le_iff₀ (hrpos s ⟨hs, le_rfl⟩)).mp hbound

end EmpiricalBernstein.SVP.EBFresh
end


section

open Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh

lemma upper_comparison_deriv (a t : ℝ) (ht : 1 - a * t / 2 ≠ 0) :
    HasDerivAt (fun u : ℝ => u / (1 - a * u / 2))
      (1 / (1 - a * t / 2)^2) t := by
  have h := (hasDerivAt_id t).div
    ((hasDerivAt_const t 1).sub (((hasDerivAt_id t).const_mul a).div_const 2)) ht
  exact h.congr_deriv (by dsimp; ring)

lemma upper_cgf_comparison {ψ ψ' : ℝ → ℝ} {m a s : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hsa : s < 2 / a)
    (hzero : ψ 0 = 0) (h0 : HasDerivAt ψ m 0)
    (hψ : ∀ t ∈ Set.Ioc 0 s, HasDerivAt ψ (ψ' t) t)
    (hdiff : ∀ t ∈ Set.Ioc 0 s, t * (1 - a * t / 2) * ψ' t ≤ ψ t) :
    ψ s ≤ m * s / (1 - a * s / 2) := by
  have hden (t : ℝ) (ht : t ∈ Set.Ioc 0 s) : 0 < 1 - a * t / 2 := by
    have hmul := (lt_div_iff₀ ha).mp hsa
    nlinarith [mul_le_mul_of_nonneg_left ht.2 ha.le]
  have h := differential_ratio_bound (r := fun t => t / (1 - a * t / 2))
    (r' := fun t => 1 / (1 - a * t / 2)^2) hs hzero (by simp) h0
    (by simpa using upper_comparison_deriv a 0 (by norm_num)) hψ
    (fun t ht => upper_comparison_deriv a t (ne_of_gt (hden t ht)))
    (fun t ht => div_pos ht.1 (hden t ht)) (fun t ht => ?_)
  · simpa only [mul_div_assoc] using h
  · have he : ψ' t * (t / (1 - a * t / 2)) - ψ t * (1 / (1 - a * t / 2)^2) =
        (t * (1 - a * t / 2) * ψ' t - ψ t) / (1 - a * t / 2)^2 := by
      field_simp [ne_of_gt (hden t ht)]
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hdiff t ht)) (sq_nonneg _)

lemma lower_comparison_deriv (a t : ℝ) :
    HasDerivAt (fun u : ℝ => u - a * u^2 / 2) (1 - a * t) t := by
  have h := (hasDerivAt_id t).sub ((((hasDerivAt_id t).pow 2).const_mul a).div_const 2)
  exact h.congr_deriv (by dsimp; ring)

lemma lower_cgf_comparison {ψ ψ' : ℝ → ℝ} {m a s : ℝ}
    (ha : 1 ≤ a) (hs : 0 < s) (hsa : s ≤ 1 / a)
    (hzero : ψ 0 = 0) (h0 : HasDerivAt ψ (-m) 0)
    (hψ : ∀ t ∈ Set.Ioc 0 s, HasDerivAt ψ (ψ' t) t)
    (hnonpos : ∀ t ∈ Set.Ioc 0 s, ψ t ≤ 0)
    (hdiff : ∀ t ∈ Set.Ioc 0 s,
      (t + a * (Real.exp t - t - 1)) * ψ' t ≤ ψ t) :
    ψ s ≤ -m * s + a * m * s^2 / 2 := by
  have ha0 : 0 < a := by linarith
  have hts (t : ℝ) (ht : t ∈ Set.Ioc 0 s) : a * t ≤ 1 := by
    have h := (le_div_iff₀ ha0).mp hsa
    nlinarith [mul_le_mul_of_nonneg_left ht.2 ha0.le]
  have hrpos (t : ℝ) (ht : t ∈ Set.Ioc 0 s) : 0 < t - a * t^2 / 2 := by
    have h := mul_le_mul_of_nonneg_right (hts t ht) ht.1.le
    nlinarith [ht.1]
  have h := differential_ratio_bound (r := fun t => t - a * t^2 / 2)
    (r' := fun t => 1 - a * t) hs hzero (by simp) h0
    (by simpa using lower_comparison_deriv a 0) hψ
    (fun t _ => lower_comparison_deriv a t) hrpos (fun t ht => ?_)
  · nlinarith
  · let q := t + a * (Real.exp t - t - 1)
    have hexp : 0 ≤ Real.exp t - t - 1 := by linarith [Real.add_one_le_exp t]
    have hq : 0 < q := by
      dsimp [q]
      linarith [mul_nonneg ha0.le hexp, ht.1]
    have hscalar := lower_mgf_scalar_comparison ht.1.le ha
    have hcomp : q * (1 - a * t) ≤ t - a * t^2 / 2 := by
      dsimp [q]
      nlinarith [mul_le_mul_of_nonneg_left hscalar ha0.le]
    have h1 := mul_le_mul_of_nonneg_left (hdiff t ht) (hrpos t ht).le
    have h2 := mul_le_mul_of_nonpos_left hcomp (hnonpos t ht)
    have htotal : q * (ψ' t * (t - a * t^2 / 2) - ψ t * (1 - a * t)) ≤ 0 := by
      dsimp [q] at *
      nlinarith
    exact nonpos_of_mul_nonpos_right htotal hq

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology ProbabilityTheory
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Fin n → Measure Ω)
  [∀ i, IsProbabilityMeasure (μ i)]

theorem self_bounding_upper_cgf {Z : (Fin n → Ω) → ℝ}
    {Zi : Fin n → (Fin n → Ω) → ℝ} {B a s : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, 0 ≤ Z x ∧ Z x ≤ B)
    (hZim : ∀ i, Measurable (Zi i)) (hZi : ∀ i x, 0 ≤ Zi i x ∧ Zi i x ≤ Z x)
    (hinv : ∀ i x y, Zi i (Function.update x i y) = Zi i x)
    (hsq : ∀ x, (∑ i, (Z x-Zi i x)^2) ≤ a*Z x)
    (ha : 0 < a) (hs : 0 < s) (hsa : s < 2/a) :
    cgf Z (Measure.pi μ) s ≤ (∫ x, Z x ∂Measure.pi μ)*s/(1-a*s/2) := by
  have hab (x) : |Z x| ≤ B := by rw [abs_of_nonneg (hZ x).1]; exact (hZ x).2
  apply upper_cgf_comparison ha hs hsa (cgf_zero) (bounded_cgf_deriv_zero hZm hab)
    (ψ' := deriv (cgf Z (Measure.pi μ)))
  · intro t _
    exact (bounded_cgf_hasDerivAt hZm hab t).differentiableAt.hasDerivAt
  · intro t ht
    exact entropy_upper_cgf_inequality hZm hab
      (self_bounding_entropy_upper μ hZm hZ hZim hZi hinv hsq ht.1.le)

theorem self_bounding_lower_cgf {Z : (Fin n → Ω) → ℝ}
    {Zi : Fin n → (Fin n → Ω) → ℝ} {B a s : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, 0 ≤ Z x ∧ Z x ≤ B)
    (hZim : ∀ i, Measurable (Zi i)) (hZi : ∀ i x, 0 ≤ Zi i x ∧ Zi i x ≤ Z x)
    (hinv : ∀ i x y, Zi i (Function.update x i y) = Zi i x)
    (hsq : ∀ x, (∑ i, (Z x-Zi i x)^2) ≤ a*Z x)
    (hD : ∀ i x, Z x-Zi i x ≤ 1)
    (ha : 1 ≤ a) (hs : 0 < s) (hsa : s ≤ 1/a) :
    cgf Z (Measure.pi μ) (-s) ≤ -(∫ x, Z x ∂Measure.pi μ)*s+
      a*(∫ x, Z x ∂Measure.pi μ)*s^2/2 := by
  have hab (x) : |Z x| ≤ B := by rw [abs_of_nonneg (hZ x).1]; exact (hZ x).2
  apply lower_cgf_comparison ha hs hsa (by simp)
    (bounded_negative_cgf_deriv_zero hZm hab)
    (ψ' := deriv (fun s => cgf Z (Measure.pi μ) (-s)))
  · intro t _
    exact (bounded_negative_cgf_hasDerivAt hZm hab t).differentiableAt.hasDerivAt
  · intro t ht
    exact negative_cgf_nonpositive hZm hZ ht.1.le
  · intro t ht
    exact entropy_lower_cgf_inequality hZm hab
      (self_bounding_entropy_lower μ hZm hZ hZim hZi hinv hsq hD ht.1.le)

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology ProbabilityTheory
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upper_chernoff_optimized {Z : Ω → ℝ} {B a m d : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B)
    (ha : 0 < a) (hm : 0 < m) (hd : 0 < d)
    (hcgf : ∀ s, 0 < s → s < 2/a → cgf Z μ s ≤ m*s/(1-a*s/2)) :
    μ.real {x | m+d ≤ Z x} ≤ Real.exp (-(d^2/(2*a*m+a*d))) := by
  let s := 2*d/(a*(2*m+d))
  have hden : 0 < a*(2*m+d) := by positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hslt : s < 2/a := by
    dsimp [s]
    apply (div_lt_div_iff₀ hden ha).mpr
    nlinarith
  have h := measure_ge_le_exp_cgf (μ := μ) (X := Z) (m+d) hs.le
    (bounded_exp_integrable hZm hZ s)
  apply h.trans
  apply Real.exp_le_exp.mpr
  apply (add_le_add le_rfl (hcgf s hs hslt)).trans
  have htwo : 2*m+d ≠ 0 := ne_of_gt (by positivity : 0 < 2*m+d)
  have ha0 := ne_of_gt ha
  have hm0 := ne_of_gt hm
  have he : -s*(m+d)+m*s/(1-a*s/2) = -(d^2/(2*a*m+a*d)) := by
    dsimp [s]
    field_simp
    ring
  exact he.le

theorem lower_chernoff_optimized {Z : Ω → ℝ} {B a m d : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, |Z x| ≤ B)
    (ha : 0 < a) (hm : 0 < m) (hd : 0 < d) (hdm : d ≤ m)
    (hcgf : ∀ s, 0 < s → s ≤ 1/a → cgf Z μ (-s) ≤ -m*s+a*m*s^2/2) :
    μ.real {x | Z x ≤ m-d} ≤ Real.exp (-(d^2/(2*a*m))) := by
  let s := d/(a*m)
  have hs : 0 < s := by dsimp [s]; positivity
  have hsle : s ≤ 1/a := by
    dsimp [s]
    apply (div_le_div_iff₀ (mul_pos ha hm) ha).mpr
    nlinarith
  have h := measure_le_le_exp_mul_mgf (μ := μ) (X := Z) (m-d) (neg_nonpos.mpr hs.le)
    (bounded_exp_integrable hZm hZ (-s))
  have hmgf : mgf Z μ (-s) = Real.exp (cgf Z μ (-s)) :=
    (Real.exp_log (mgf_pos (bounded_exp_integrable hZm hZ (-s)))).symm
  rw [hmgf, ← Real.exp_add] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hbound := hcgf s hs hsle
  have he : -(-s)*(m-d)+(-m*s+a*m*s^2/2) = -(d^2/(2*a*m)) := by
    dsimp [s]
    field_simp
    ring
  linarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upper_sqrt_tail_of_deviation {Z : Ω → ℝ} {m a t : ℝ}
    (hZ : ∀ x, 0 ≤ Z x) (hm : 0 < m) (ha : 0 < a) (ht : 0 < t)
    (hdev : ∀ d, 0 < d → μ.real {x | m+d ≤ Z x} ≤ Real.exp (-(d^2/(2*a*m+a*d)))) :
    μ.real {x | Real.sqrt m+Real.sqrt (2*a*t) < Real.sqrt (Z x)} ≤ Real.exp (-t) := by
  let u := Real.sqrt m
  let v := Real.sqrt (2*a*t)
  let d := 2*u*v+v^2
  have hu : 0 < u := Real.sqrt_pos.mpr hm
  have hv : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hu2 : u^2 = m := Real.sq_sqrt hm.le
  have hv2 : v^2 = 2*a*t := Real.sq_sqrt (by positivity)
  have hd : 0 < d := by dsimp [d]; positivity
  have hsub : {x | u+v < Real.sqrt (Z x)} ⊆ {x | m+d ≤ Z x} := by
    intro x hx
    have hs := Real.sq_sqrt (hZ x)
    have hnn := Real.sqrt_nonneg (Z x)
    change u+v < Real.sqrt (Z x) at hx
    change m+d ≤ Z x
    dsimp [d]
    nlinarith
  apply (measureReal_mono hsub).trans ((hdev d hd).trans ?_)
  apply Real.exp_le_exp.mpr
  have hden : 0 < 2*a*m+a*d := by positivity
  have hcross : t*(2*a*m+a*d) ≤ d^2 := by
    dsimp [d]
    nlinarith [sq_nonneg (u*v), mul_nonneg hu.le (pow_nonneg hv.le 3), sq_nonneg (v^2)]
  have hrat := (le_div_iff₀ hden).mpr hcross
  linarith

theorem lower_sqrt_tail_of_deviation {Z : Ω → ℝ} {m a t : ℝ}
    (hZ : ∀ x, 0 ≤ Z x) (hm : 0 ≤ m) (ha : 0 < a) (ht : 0 < t)
    (hdev : ∀ d, 0 < d → d ≤ m → μ.real {x | Z x ≤ m-d} ≤ Real.exp (-(d^2/(2*a*m)))) :
    μ.real {x | Real.sqrt (Z x)+Real.sqrt (2*a*t) < Real.sqrt m} ≤ Real.exp (-t) := by
  let u := Real.sqrt m
  let v := Real.sqrt (2*a*t)
  have hu : 0 ≤ u := Real.sqrt_nonneg m
  have hv : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hu2 : u^2 = m := Real.sq_sqrt hm
  have hv2 : v^2 = 2*a*t := Real.sq_sqrt (by positivity)
  by_cases huv : u ≤ v
  · have he : {x | Real.sqrt (Z x)+v < u} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hnn := Real.sqrt_nonneg (Z x)
      change Real.sqrt (Z x)+v < u at hx
      linarith
    rw [he]
    simp [Real.exp_nonneg]
  · have hvu : v < u := lt_of_not_ge huv
    let d := 2*u*v-v^2
    have hd : 0 < d := by dsimp [d]; nlinarith [mul_pos hv (sub_pos.mpr hvu)]
    have hdm : d ≤ m := by dsimp [d]; nlinarith [sq_nonneg (u-v)]
    have hmpos : 0 < m := by nlinarith
    have hsub : {x | Real.sqrt (Z x)+v < u} ⊆ {x | Z x ≤ m-d} := by
      intro x hx
      have hs := Real.sq_sqrt (hZ x)
      have hnn := Real.sqrt_nonneg (Z x)
      change Real.sqrt (Z x)+v < u at hx
      change Z x ≤ m-d
      dsimp [d]
      nlinarith
    apply (measureReal_mono hsub).trans ((hdev d hd hdm).trans ?_)
    apply Real.exp_le_exp.mpr
    have hden : 0 < 2*a*m := by positivity
    have hcross : t*(2*a*m) ≤ d^2 := by
      dsimp [d]
      have h := mul_nonneg (sq_nonneg v) (mul_nonneg (sub_nonneg.mpr hvu.le) (by linarith : 0 ≤ 3*u-v))
      nlinarith
    have hrat := (le_div_iff₀ hden).mpr hcross
    linarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology ProbabilityTheory
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Fin n → Measure Ω)
  [∀ i, IsProbabilityMeasure (μ i)]

theorem self_bounding_sqrt_tails {Z : (Fin n → Ω) → ℝ}
    {Zi : Fin n → (Fin n → Ω) → ℝ} {B a t : ℝ}
    (hZm : Measurable Z) (hZ : ∀ x, 0 ≤ Z x ∧ Z x ≤ B)
    (hZim : ∀ i, Measurable (Zi i)) (hZi : ∀ i x, 0 ≤ Zi i x ∧ Zi i x ≤ Z x)
    (hinv : ∀ i x y, Zi i (Function.update x i y) = Zi i x)
    (hsq : ∀ x, (∑ i, (Z x-Zi i x)^2) ≤ a*Z x)
    (hD : ∀ i x, Z x-Zi i x ≤ 1) (ha : 1 ≤ a) (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | Real.sqrt (∫ y, Z y ∂Measure.pi μ)+Real.sqrt (2*a*t) < Real.sqrt (Z x)} ≤ Real.exp (-t) ∧
    (Measure.pi μ).real {x | Real.sqrt (Z x)+Real.sqrt (2*a*t) < Real.sqrt (∫ y, Z y ∂Measure.pi μ)} ≤ Real.exp (-t) := by
  let P := Measure.pi μ
  let m := ∫ x, Z x ∂P
  have hab (x) : |Z x| ≤ B := by rw [abs_of_nonneg (hZ x).1]; exact (hZ x).2
  have hZi0 := bounded_measurable_integrable (μ := P) hZm hab
  have hm : 0 ≤ m := integral_nonneg (fun x => (hZ x).1)
  have ha0 : 0 < a := by linarith
  rcases ht.eq_or_lt with ht | ht
  · subst t
    constructor <;> simp only [neg_zero, Real.exp_zero] <;>
      exact (measureReal_mono (μ := P) (Set.subset_univ _)).trans (by simp)
  rcases hm.eq_or_lt with hm | hm
  · have hma : (∫ x, Z x ∂P) = 0 := hm.symm
    have hzero : Z =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg (fun x => (hZ x).1) hZi0).mp hma
    have hu : P {x | Real.sqrt m+Real.sqrt (2*a*t) < Real.sqrt (Z x)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hzero] with x hx
      simp only [Pi.zero_apply] at hx
      simp only [hm.symm, Real.sqrt_zero, zero_add, hx]
      exact not_lt.mpr (Real.sqrt_nonneg _)
    have hl : P {x | Real.sqrt (Z x)+Real.sqrt (2*a*t) < Real.sqrt m} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [] with x
      simp only [hm.symm, Real.sqrt_zero]
      exact not_lt.mpr (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    constructor
    · change P.real _ ≤ _
      rw [Measure.real, hu, ENNReal.toReal_zero]
      exact (Real.exp_pos _).le
    · change P.real _ ≤ _
      rw [Measure.real, hl, ENNReal.toReal_zero]
      exact (Real.exp_pos _).le
  · constructor
    · apply upper_sqrt_tail_of_deviation (fun x => (hZ x).1) hm ha0 ht
      intro d hd
      exact upper_chernoff_optimized hZm hab ha0 hm hd (fun s hs hsa =>
        self_bounding_upper_cgf μ hZm hZ hZim hZi hinv hsq ha0 hs hsa)
    · apply lower_sqrt_tail_of_deviation (fun x => (hZ x).1) hm.le ha0 ht
      intro d hd hdm
      exact lower_chernoff_optimized hZm hab ha0 hm hd hdm (fun s hs hsa =>
        self_bounding_lower_cgf μ hZm hZ hZim hZi hinv hsq hD ha hs hsa)

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology
namespace EmpiricalBernstein.SVP.EBFresh

theorem product_cube_ae {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂Measure.pi μ, ∀ i, x i ∈ Set.Icc (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := μ) (i := i)).eventually (hμ i)

theorem clipped_variance_sqrt_tails {n : ℕ} (hn : 2 ≤ n) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | Real.sqrt (∫ y, clippedVarianceZ y ∂Measure.pi μ)+
      Real.sqrt (2*((n : ℝ)/(n-1))*t) < Real.sqrt (clippedVarianceZ x)} ≤ Real.exp (-t) ∧
    (Measure.pi μ).real {x | Real.sqrt (clippedVarianceZ x)+Real.sqrt (2*((n : ℝ)/(n-1))*t) <
      Real.sqrt (∫ y, clippedVarianceZ y ∂Measure.pi μ)} ≤ Real.exp (-t) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply self_bounding_sqrt_tails μ continuous_clippedVarianceZ.measurable
    (fun x => clippedVarianceZ_bounds hn x)
    (fun i => (continuous_clippedVarianceBaseline i).measurable)
    (fun i x => clippedVarianceBaseline_bounds hn x i)
    (fun i x y => clippedVarianceBaseline_update x i y)
    (fun x => clippedVariance_squared_deficits hn x)
    (fun i x => (clippedVariance_deficit_bounds hn x i).2) _ ht
  exact (le_div_iff₀ (by linarith : 0 < (n : ℝ)-1)).mpr (by linarith)

theorem native_variance_sqrt_tails {n : ℕ} (hn : 2 ≤ n) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ) {x | Real.sqrt (∫ y, sampleVar y ∂Measure.pi μ)+Real.sqrt (2*t/(n-1)) < Real.sqrt (sampleVar x)} ≤ ENNReal.ofReal (Real.exp (-t)) ∧
    (Measure.pi μ) {x | Real.sqrt (sampleVar x)+Real.sqrt (2*t/(n-1)) < Real.sqrt (∫ y, sampleVar y ∂Measure.pi μ)} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  let P := Measure.pi μ
  let V := ∫ y, sampleVar y ∂P
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hsN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hV : 0 ≤ V := integral_nonneg (fun x => sampleVar_nonneg hn x)
  have hae := product_cube_ae μ hμ
  have hZeq : clippedVarianceZ =ᵐ[P] fun x => (n : ℝ)*sampleVar x := by
    filter_upwards [hae] with x hx
    exact clippedVarianceZ_eq x hx
  have hmean : (∫ y, clippedVarianceZ y ∂P) = (n : ℝ)*V := by
    rw [integral_congr_ae hZeq, integral_const_mul]
  have hrad : Real.sqrt (2*((n : ℝ)/(n-1))*t) = Real.sqrt (n : ℝ)*Real.sqrt (2*t/(n-1)) := by
    rw [← Real.sqrt_mul hn0.le]
    congr 1
    ring
  have hu := (clipped_variance_sqrt_tails hn μ ht).1
  have hl := (clipped_variance_sqrt_tails hn μ ht).2
  have heU : P {x | Real.sqrt (∫ y, clippedVarianceZ y ∂P)+Real.sqrt (2*((n : ℝ)/(n-1))*t) < Real.sqrt (clippedVarianceZ x)} =
      P {x | Real.sqrt V+Real.sqrt (2*t/(n-1)) < Real.sqrt (sampleVar x)} := by
    apply measure_congr
    filter_upwards [hZeq] with x hx
    change (Real.sqrt (∫ y, clippedVarianceZ y ∂P)+Real.sqrt (2*((n : ℝ)/(n-1))*t) < Real.sqrt (clippedVarianceZ x)) = _
    apply propext
    rw [hmean, hx, hrad, Real.sqrt_mul hn0.le, Real.sqrt_mul hn0.le, ← mul_add]
    exact mul_lt_mul_iff_of_pos_left hsN
  have heL : P {x | Real.sqrt (clippedVarianceZ x)+Real.sqrt (2*((n : ℝ)/(n-1))*t) < Real.sqrt (∫ y, clippedVarianceZ y ∂P)} =
      P {x | Real.sqrt (sampleVar x)+Real.sqrt (2*t/(n-1)) < Real.sqrt V} := by
    apply measure_congr
    filter_upwards [hZeq] with x hx
    change (Real.sqrt (clippedVarianceZ x)+Real.sqrt (2*((n : ℝ)/(n-1))*t) < Real.sqrt (∫ y, clippedVarianceZ y ∂P)) = _
    apply propext
    rw [hmean, hx, hrad, Real.sqrt_mul hn0.le, Real.sqrt_mul hn0.le, ← mul_add]
    exact mul_lt_mul_iff_of_pos_left hsN
  change P.real _ ≤ _ at hu hl
  rw [Measure.real, heU] at hu
  rw [Measure.real, heL] at hl
  constructor
  · rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal hu
  · rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal hl

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology ProbabilityTheory
namespace EmpiricalBernstein.SVP.EBFresh

theorem positive_exp_remainder_ge {s : ℝ} (hs : 0 ≤ s) :
    s^2/2 ≤ Real.exp s-s-1 := by
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => Real.exp u-u-1-u^2/2)
      (Real.exp t-1-t) t := by
    exact ((((Real.hasDerivAt_exp t).sub (hasDerivAt_id t)).sub_const 1).sub
      (((hasDerivAt_id t).pow 2).div_const 2)).congr_deriv (by dsimp; ring)
  have h := nonneg_on_nonneg_of_derivative hd (by norm_num) (fun t _ => by
    have := Real.add_one_le_exp t
    linarith) hs
  linarith

theorem bounded_exp_quadratic {s x : ℝ} (hs : 0 ≤ s) (hx : |x| ≤ 1) :
    Real.exp (s*x) ≤ 1+s*x+x^2*(Real.exp s-s-1) := by
  by_cases hxp : 0 ≤ x
  · have h := exp_scaled_remainder_le hs hxp (abs_le.mp hx).2
    linarith
  · have hx0 : x ≤ 0 := le_of_not_ge hxp
    have h := exp_negative_remainder_le (mul_nonneg hs (neg_nonneg.mpr hx0))
    have h2 := mul_le_mul_of_nonneg_left (positive_exp_remainder_ge hs) (sq_nonneg x)
    simp only [mul_neg, neg_neg] at h
    nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem centered_bounded_mgf {X : Ω → ℝ} {s : ℝ}
    (hXm : Measurable X) (hX : ∀ x, |X x| ≤ 1) (hmean : (∫ x, X x ∂μ) = 0)
    (hs : 0 ≤ s) :
    mgf X μ s ≤ Real.exp ((∫ x, (X x)^2 ∂μ)*(Real.exp s-s-1)) := by
  have hXi := bounded_measurable_integrable (μ := μ) hXm hX
  have hX2 : Integrable (fun x => (X x)^2) μ := by
    apply bounded_measurable_integrable (hXm.pow_const 2) (C := 1)
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr (hX x)
  have hR := ((integrable_const (μ := μ) 1).add (hXi.const_mul s)).add
    (hX2.mul_const (Real.exp s-s-1))
  have h := integral_mono (bounded_exp_integrable hXm hX s) hR
    (fun x => bounded_exp_quadratic hs (hX x))
  have he : (∫ x, 1+s*X x+(X x)^2*(Real.exp s-s-1) ∂μ) =
      1+(∫ x, (X x)^2 ∂μ)*(Real.exp s-s-1) := by
    have hA := integral_add ((integrable_const (μ := μ) 1).add (hXi.const_mul s))
      (hX2.mul_const (Real.exp s-s-1))
    have hB := integral_add (integrable_const (μ := μ) 1) (hXi.const_mul s)
    simp only [Pi.add_apply] at hA hB
    rw [hA, hB, integral_const_mul, integral_mul_const, hmean]
    simp
  simp only [Pi.add_apply] at h
  rw [he] at h
  exact h.trans (by have := Real.add_one_le_exp ((∫ x, (X x)^2 ∂μ)*(Real.exp s-s-1)); linarith)

theorem independent_centered_mgf {n : ℕ} (μ : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] {X : Fin n → Ω → ℝ} {s : ℝ}
    (hXm : ∀ i, Measurable (X i)) (hX : ∀ i x, |X i x| ≤ 1)
    (hmean : ∀ i, (∫ x, X i x ∂μ i) = 0) (hs : 0 ≤ s) :
    mgf (fun x => ∑ i, X i (x i)) (Measure.pi μ) s ≤
      Real.exp ((∑ i, ∫ x, (X i x)^2 ∂μ i)*(Real.exp s-s-1)) := by
  have he : mgf (fun x => ∑ i, X i (x i)) (Measure.pi μ) s = ∏ i, mgf (X i) (μ i) s := by
    unfold mgf
    simp_rw [Finset.mul_sum, Real.exp_sum]
    exact integral_fintype_prod_eq_prod (μ := μ) (fun i x => Real.exp (s*X i x))
  rw [he]
  calc
    _ ≤ ∏ i, Real.exp ((∫ x, (X i x)^2 ∂μ i)*(Real.exp s-s-1)) :=
      Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => centered_bounded_mgf (hXm i) (hX i) (hmean i) hs)
    _ = _ := by rw [← Real.exp_sum, Finset.sum_mul]

end EmpiricalBernstein.SVP.EBFresh
end


section

namespace EmpiricalBernstein.SVP.EBFresh

lemma bennett_log_lower {r : ℝ} (hr : 0 ≤ r) :
    3 * r / (r + 3) ≤ Real.log (1 + r + r^2 / 6) := by
  let A : ℝ → ℝ := fun x => 1 + x + x^2 / 6
  let f : ℝ → ℝ := fun x => Real.log (A x) - 3 * x / (x + 3)
  let d : ℝ → ℝ := fun x => (1 + x / 3) / A x - 9 / (x + 3)^2
  have hA (x : ℝ) (hx : 0 ≤ x) : 0 < A x := by dsimp [A]; positivity
  have hd (x : ℝ) (hx : 0 ≤ x) : HasDerivAt f (d x) x := by
    have hpoly := ((hasDerivAt_const x 1).add (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 6)
    have hlog := hpoly.log (ne_of_gt (hA x hx))
    have hquot := ((hasDerivAt_id x).const_mul 3).div
      ((hasDerivAt_id x).add_const 3) (by linarith : x + 3 ≠ 0)
    exact (hlog.sub hquot).congr_deriv (by dsimp [d]; ring)
  have hnonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ d x := by
    have hp : 0 < x + 3 := by linarith
    have he : d x = x^2 * (2*x + 9) / (6 * A x * (x + 3)^2) := by
      dsimp [d]
      field_simp [ne_of_gt (hA x hx), ne_of_gt hp]
      dsimp [A]
      ring
    rw [he]
    positivity
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    exact fun x hx => hnonneg x (interior_subset hx)
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hr hr
  have hz : f 0 = 0 := by simp [f, A]
  rw [hz] at h
  exact sub_nonneg.mp h

lemma bennett_parametric {r : ℝ} (hr : 0 ≤ r) :
    r^2 / 2 ≤ (1 + (r + r^2 / 6)) * Real.log (1 + (r + r^2 / 6)) - (r + r^2 / 6) := by
  let A : ℝ → ℝ := fun x => 1 + x + x^2 / 6
  let f : ℝ → ℝ := fun x => A x * Real.log (A x) - (x + x^2 / 6) - x^2 / 2
  let d : ℝ → ℝ := fun x => (1 + x / 3) * Real.log (A x) - x
  have hA (x : ℝ) (hx : 0 ≤ x) : 0 < A x := by dsimp [A]; positivity
  have hd (x : ℝ) (hx : 0 ≤ x) : HasDerivAt f (d x) x := by
    have hpoly := ((hasDerivAt_const x 1).add (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 6)
    have hlog := hpoly.log (ne_of_gt (hA x hx))
    have hu := (hasDerivAt_id x).add (((hasDerivAt_id x).pow 2).div_const 6)
    have h := ((hpoly.mul hlog).sub hu).sub (((hasDerivAt_id x).pow 2).div_const 2)
    exact h.congr_deriv (by
      dsimp [d]
      field_simp [ne_of_gt (hA x hx)]
      dsimp [A]
      ring)
  have hnonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ d x := by
    have hb := mul_le_mul_of_nonneg_left (bennett_log_lower hx)
      (show 0 ≤ 1 + x / 3 by positivity)
    have he : (1 + x / 3) * (3 * x / (x + 3)) = x := by
      field_simp
      ring
    rw [he] at hb
    exact sub_nonneg.mpr hb
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    exact fun x hx => hnonneg x (interior_subset hx)
  have h := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hr hr
  have hz : f 0 = 0 := by simp [f, A]
  rw [hz] at h
  dsimp [f, A] at h
  simpa only [add_assoc] using (sub_nonneg.mp h)

lemma bennett_sharp_inversion {t : ℝ} (ht : 0 ≤ t) :
    t ≤ (1 + (Real.sqrt (2*t) + t/3)) * Real.log (1 + (Real.sqrt (2*t) + t/3)) -
      (Real.sqrt (2*t) + t/3) := by
  have h := bennett_parametric (Real.sqrt_nonneg (2*t))
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2*t)] at h
  have he : 2 * t / 6 = t / 3 := by ring
  rw [he] at h
  convert h using 1
  ring

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory Filter Topology ProbabilityTheory
namespace EmpiricalBernstein.SVP.EBFresh
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem bennett_chernoff_parameter {X : Ω → ℝ} {B v u : ℝ}
    (hXm : Measurable X) (hX : ∀ x, |X x| ≤ B) (hu : 0 < u)
    (hmgf : ∀ s, 0 ≤ s → mgf X μ s ≤ Real.exp (v*(Real.exp s-s-1))) :
    μ.real {x | v*u ≤ X x} ≤ Real.exp (-v*((1+u)*Real.log (1+u)-u)) := by
  let s := Real.log (1+u)
  have hsu : 0 < 1+u := by linarith
  have hs : 0 < s := Real.log_pos (by linarith)
  have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) (v*u) hs.le
    (bounded_exp_integrable hXm hX s)
  apply h.trans
  calc
    _ ≤ Real.exp (-s*(v*u))*Real.exp (v*(Real.exp s-s-1)) :=
      mul_le_mul_of_nonneg_left (hmgf s hs.le) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [s]
      rw [Real.exp_log hsu]
      ring

theorem bennett_sharp_tail {X : Ω → ℝ} {B v t : ℝ}
    (hXm : Measurable X) (hX : ∀ x, |X x| ≤ B) (hv : 0 ≤ v) (ht : 0 ≤ t)
    (hmgf : ∀ s, 0 ≤ s → mgf X μ s ≤ Real.exp (v*(Real.exp s-s-1))) :
    μ.real {x | Real.sqrt (2*v*t)+t/3 ≤ X x} ≤ Real.exp (-t) := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simp only [neg_zero, Real.exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans (by simp)
  rcases hv.eq_or_lt with hv | hv
  · subst v
    have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) (t/3) (by norm_num : (0 : ℝ) ≤ 3)
      (bounded_exp_integrable hXm hX 3)
    have hb := hmgf 3 (by norm_num)
    simp only [zero_mul, Real.exp_zero] at hb
    simp only [mul_zero, zero_mul, Real.sqrt_zero, zero_add]
    apply h.trans
    have he : -(3 : ℝ)*(t/3) = -t := by ring
    rw [he]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (Real.exp_pos (-t)).le
  let w := t/v
  let u := Real.sqrt (2*w)+w/3
  have hw : 0 < w := div_pos ht hv
  have hu : 0 < u := by dsimp [u]; positivity
  have h := bennett_chernoff_parameter hXm hX hu hmgf
  have hnorm : v*u = Real.sqrt (2*v*t)+t/3 := by
    have hroot : v*Real.sqrt (2*w) = Real.sqrt (2*v*t) := by
      calc
        v*Real.sqrt (2*w) = Real.sqrt (v^2)*Real.sqrt (2*w) := by rw [Real.sqrt_sq hv.le]
        _ = Real.sqrt (v^2*(2*w)) := (Real.sqrt_mul (sq_nonneg v) _).symm
        _ = Real.sqrt (2*v*t) := by
          congr 1
          dsimp [w]
          field_simp
    dsimp [u]
    rw [mul_add, hroot]
    congr 1
    dsimp [w]
    field_simp
  rw [hnorm] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hb := mul_le_mul_of_nonneg_left (bennett_sharp_inversion hw.le) hv.le
  have he : v*w = t := by dsimp [w]; field_simp
  rw [he] at hb
  dsimp [u] at *
  linarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace EmpiricalBernstein.SVP.EBFresh
open VarianceRegularization.Expansion

lemma native_mean_signed_tail {n : ℕ} (hn : 2 ≤ n) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, ∀ᵐ z ∂μ i, z ∈ Set.Icc (0 : ℝ) 1)
    {t σ : ℝ} (ht : 0 ≤ t) (hσ : |σ| = 1) :
    (Measure.pi μ) {x | Real.sqrt (2 * (∫ y, sampleVar y ∂Measure.pi μ) * t / n) +
      t / (3 * n) < σ * (empMean x - ∫ y, empMean y ∂Measure.pi μ)} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  let P := Measure.pi μ
  let V := ∫ y, sampleVar y ∂P
  let W := ∑ i, variance (fun z : ℝ => z) (μ i)
  let X : Fin n → ℝ → ℝ := fun i z => σ * centeredClip (μ i) z
  let Z : (Fin n → ℝ) → ℝ := fun x => ∑ i, X i (x i)
  have hσ2 : σ^2 = 1 := by rw [← sq_abs σ, hσ]; norm_num
  have hXm (i : Fin n) : Measurable (X i) := measurable_const.mul (measurable_centeredClip (μ i))
  have hXb (i : Fin n) (z : ℝ) : |X i z| ≤ 1 := by
    dsimp [X]
    simpa only [abs_mul, hσ, one_mul] using centeredClip_bound (μ i) z
  have hXzero (i : Fin n) : (∫ z, X i z ∂μ i) = 0 := by
    dsimp [X]
    rw [integral_const_mul, integral_centeredClip, mul_zero]
  have hXsecond (i : Fin n) : (∫ z, (X i z)^2 ∂μ i) = variance (fun z : ℝ => z) (μ i) := by
    simp only [X, mul_pow, hσ2, one_mul]
    exact centeredClip_second_moment (μ i) (hμ i)
  have hZm : Measurable Z := by dsimp [Z]; fun_prop
  have hZb (x : Fin n → ℝ) : |Z x| ≤ n := by
    calc
      _ ≤ ∑ i, |X i (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hXb i (x i)
      _ = _ := by simp
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => variance_nonneg _ _
  have hmgf (s : ℝ) (hs : 0 ≤ s) : mgf Z P s ≤ Real.exp (W * (Real.exp s - s - 1)) := by
    have h := independent_centered_mgf μ hXm hXb hXzero hs
    simpa only [hXsecond] using h
  have htail := bennett_sharp_tail (μ := P) hZm hZb hW ht hmgf
  have htail' : P {x | Real.sqrt (2 * W * t) + t / 3 ≤ Z x} ≤ ENNReal.ofReal (Real.exp (-t)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal htail
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hV : 0 ≤ V := integral_nonneg (fun y => sampleVar_nonneg hn y)
  have hLp (i : Fin n) : MemLp (fun z : ℝ => z) 2 (μ i) :=
    memLp_of_bounded (hμ i) aestronglyMeasurable_id 2
  have hWV : W ≤ (n : ℝ) * V := by
    have h := expectation_sampleVar_product_ge hn μ (fun _ z => z) hLp
    change W / n ≤ V at h
    exact (div_le_iff₀ hn0).mp h |>.trans_eq (mul_comm V n)
  have hscale : (n : ℝ) * Real.sqrt (2 * V * t / n) = Real.sqrt (2 * (n : ℝ) * V * t) := by
    calc
      _ = Real.sqrt ((n : ℝ)^2) * Real.sqrt (2 * V * t / n) := by rw [Real.sqrt_sq hn0.le]
      _ = Real.sqrt ((n : ℝ)^2 * (2 * V * t / n)) := (Real.sqrt_mul (sq_nonneg (n : ℝ)) _).symm
      _ = _ := by
        congr 1
        field_simp
  have hrad : Real.sqrt (2 * W * t) ≤ (n : ℝ) * Real.sqrt (2 * V * t / n) := by
    rw [hscale]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_right hWV ht]
  have hthreshold : Real.sqrt (2 * W * t) + t / 3 ≤
      (n : ℝ) * (Real.sqrt (2 * V * t / n) + t / (3 * n)) := by
    have he : (n : ℝ) * (t / (3 * n)) = t / 3 := by field_simp
    rw [mul_add, he]
    exact add_le_add hrad le_rfl
  apply (measure_mono_ae ?_).trans htail'
  filter_upwards [product_cube_ae μ hμ] with x hx
  intro hbad
  change Real.sqrt (2 * W * t) + t / 3 ≤ Z x
  change Real.sqrt (2 * V * t / n) + t / (3 * n) < σ * (empMean x - ∫ y, empMean y ∂P) at hbad
  have hsum : Z x = (n : ℝ) * (σ * (empMean x - ∫ y, empMean y ∂P)) := by
    dsimp [Z, X]
    rw [← Finset.mul_sum, centeredClip_sum hn μ hμ x hx]
    ring
  rw [hsum]
  have hmul := mul_lt_mul_of_pos_left hbad hn0
  exact hthreshold.trans hmul.le

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory VarianceRegularization.Expansion
namespace EmpiricalBernstein.SVP.EBFresh

theorem native_score_probability {n : ℕ} (hn : 2 ≤ n) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, ∀ᵐ x ∂μ i, x ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    let M := ∫ y, empMean y ∂Measure.pi μ
    let V := ∫ y, sampleVar y ∂Measure.pi μ
    let ε := ENNReal.ofReal (Real.exp (-t))
    (Measure.pi μ) {x | comparisonLevel (n := n) M V t < Phi x t} ≤ 2*ε ∧
    (Measure.pi μ) {x | Psi x t < comparisonLevel (n := n) M V t} ≤ 2*ε ∧
    (Measure.pi μ) {x | Phi x t < M} ≤ 2*ε := by
  dsimp only
  let M := ∫ y, empMean y ∂Measure.pi μ
  let V := ∫ y, sampleVar y ∂Measure.pi μ
  have he : Real.sqrt (2*V*t/n) = Real.sqrt (2*t/n)*Real.sqrt V := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*t/n)]
    congr 1
    ring
  apply score_probability_bounds hn (Measure.pi μ) ht
  · have h := native_mean_signed_tail hn μ hμ ht (σ := 1) (by norm_num)
    change (Measure.pi μ) {x | Real.sqrt (2*V*t/n)+t/(3*n) < 1*(empMean x-M)} ≤ _ at h
    rw [he] at h
    apply (measure_mono ?_).trans h
    intro x hx
    change M+Real.sqrt (2*t/n)*Real.sqrt V+t/(3*n) < empMean x at hx
    change Real.sqrt (2*t/n)*Real.sqrt V+t/(3*n) < 1*(empMean x-M)
    linarith
  · have h := native_mean_signed_tail hn μ hμ ht (σ := -1) (by norm_num)
    change (Measure.pi μ) {x | Real.sqrt (2*V*t/n)+t/(3*n) < -1*(empMean x-M)} ≤ _ at h
    rw [he] at h
    apply (measure_mono ?_).trans h
    intro x hx
    change empMean x < M-Real.sqrt (2*t/n)*Real.sqrt V-t/(3*n) at hx
    change Real.sqrt (2*t/n)*Real.sqrt V+t/(3*n) < -1*(empMean x-M)
    linarith
  · exact (native_variance_sqrt_tails hn μ hμ ht).1
  · exact (native_variance_sqrt_tails hn μ hμ ht).2

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory VarianceRegularization.Expansion
open scoped ENNReal BigOperators
namespace EmpiricalBernstein.SVP.EBFresh

lemma native_iid_moments {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {f : X → ℝ} (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y, empMean y ∂Measure.pi (fun _ : Fin n => μ.map f)) = (∫ z, f z ∂μ) ∧
    (∫ y, sampleVar y ∂Measure.pi (fun _ : Fin n => μ.map f)) = variance f μ := by
  have : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hν := mapped_unit_support (μ := μ) hf hb
  have hLp : MemLp (fun z : ℝ => z) 2 (μ.map f) := memLp_of_bounded hν aestronglyMeasurable_id 2
  constructor
  · rw [native_empMean_expectation (fun _ : Fin n => μ.map f) (fun _ => hν)]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp [empMean, hn0, mapped_risk hf]
  · rw [expectation_sampleVar_iid (μ.map f) hn (fun z : ℝ => z) hLp, mapped_variance hf]

lemma native_iid_confidence {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {f : X → ℝ} (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => μ) {x | Phi (fun i => f (x i)) t < ∫ z, f z ∂μ} ≤
      2 * ENNReal.ofReal (Real.exp (-t)) ∧
    (Measure.pi fun _ : Fin n => μ) {x | (∫ z, f z ∂μ) +
      Real.sqrt (2 * variance f μ * t / n) + t / (3*n) < empMean (fun i => f (x i))} ≤
      ENNReal.ofReal (Real.exp (-t)) ∧
    (Measure.pi fun _ : Fin n => μ) {x | Real.sqrt (variance f μ) +
      Real.sqrt (2*t/((n : ℝ)-1)) < Real.sqrt (sampleVar (fun i => f (x i)))} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  have : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  let ν := fun _ : Fin n => μ.map f
  have hν : ∀ i, ∀ᵐ z ∂ν i, z ∈ Set.Icc (0 : ℝ) 1 := fun _ => mapped_unit_support (μ := μ) hf hb
  obtain ⟨hM, hV⟩ := native_iid_moments μ hn hf hb
  have hghost := (native_score_probability hn ν hν ht).2.2
  change (Measure.pi ν) {x | Phi x t < ∫ y, empMean y ∂Measure.pi ν} ≤ _ at hghost
  rw [hM] at hghost
  have hmean := native_mean_signed_tail hn ν hν ht (σ := 1) (by norm_num)
  rw [hM, hV] at hmean
  have hvar := (native_variance_sqrt_tails hn ν hν ht).1
  rw [hV] at hvar
  constructor
  · calc
      _ = (Measure.pi ν) {x | Phi x t < ∫ z, f z ∂μ} :=
        sample_event_transfer μ hf n (measurableSet_lt (continuous_Phi t).measurable measurable_const)
      _ ≤ _ := hghost
  constructor
  · calc
      _ = (Measure.pi ν) {x | (∫ z, f z ∂μ) + Real.sqrt (2 * variance f μ * t / n) +
          t / (3*n) < empMean x} :=
        sample_event_transfer μ hf n (measurableSet_lt measurable_const continuous_empMean.measurable)
      _ ≤ _ := (measure_mono (fun x hx => by
        change (∫ z, f z ∂μ) + Real.sqrt (2 * variance f μ * t / n) + t/(3*n) < empMean x at hx
        change Real.sqrt (2 * variance f μ * t / n) + t/(3*n) < 1*(empMean x - ∫ z, f z ∂μ)
        linarith)).trans hmean
  · calc
      _ = (Measure.pi ν) {x | Real.sqrt (variance f μ) + Real.sqrt (2*t/((n : ℝ)-1)) < Real.sqrt (sampleVar x)} :=
        sample_event_transfer μ hf n (measurableSet_lt measurable_const continuous_sampleVar.sqrt.measurable)
      _ ≤ _ := hvar

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory VarianceRegularization.Expansion
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

theorem fixed_sign_comparison {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    signLaw n {σ : Fin n → Bool | Psi (swap (fun i => !σ i) x y) t < Phi (swap σ x y) t} ≤
      5*ENNReal.ofReal (Real.exp (-t)) := by
  let μ := fun i => twoPointLaw (x i) (y i)
  let P := Measure.pi μ
  let M := ∫ z, empMean z ∂P
  let V := ∫ z, sampleVar z ∂P
  let A := comparisonLevel (n := n) M V t
  let ε := ENNReal.ofReal (Real.exp (-t))
  have hs := native_score_probability hn μ (fun i => twoPointLaw_support (hx i) (hy i)) ht
  change P {z | A < Phi z t} ≤ 2*ε ∧ P {z | Psi z t < A} ≤ 2*ε ∧ _ at hs
  have heL : signLaw n {σ : Fin n → Bool | A < Phi (swap σ x y) t} = P {z | A < Phi z t} := by
    rw [show P = (signLaw n).map (fun σ => swap σ x y) from (sign_selected_law x y).symm]
    exact (Measure.map_apply (measurable_of_countable _)
      (measurableSet_lt measurable_const (continuous_Phi t).measurable)).symm
  have heR : signLaw n {σ : Fin n → Bool | Psi (swap (fun i => !σ i) x y) t < A} = P {z | Psi z t < A} := by
    rw [show P = (signLaw n).map (fun σ => swap (fun i => !σ i) x y) from (sign_antithetic_law x y).symm]
    exact (Measure.map_apply (measurable_of_countable _)
      (measurableSet_lt (continuous_Psi t).measurable measurable_const)).symm
  have hsub : {σ : Fin n → Bool | Psi (swap (fun i => !σ i) x y) t < Phi (swap σ x y) t} ⊆
      {σ : Fin n → Bool | A < Phi (swap σ x y) t} ∪ {σ : Fin n → Bool | Psi (swap (fun i => !σ i) x y) t < A} := by
    intro σ hσ
    by_cases h : A < Phi (swap σ x y) t
    · exact Or.inl h
    · exact Or.inr (lt_of_lt_of_le hσ (le_of_not_gt h))
  calc
    _ ≤ signLaw n {σ : Fin n → Bool | A < Phi (swap σ x y) t} + signLaw n {σ : Fin n → Bool | Psi (swap (fun i => !σ i) x y) t < A} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 2*ε+2*ε := by rw [heL, heR]; exact add_le_add hs.1 hs.2.1
    _ = 4*ε := by rw [← add_mul]; norm_num
    _ ≤ 5*ε := mul_le_mul (by norm_num : (4 : ℝ≥0∞) ≤ 5) le_rfl zero_le zero_le

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
namespace EmpiricalBernstein.SVP.EBFresh

theorem fixed_sign_comparison_mirrored {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    signLaw n {σ | Psi (swap σ x y) t < Phi (swap (fun i => !σ i) x y) t} ≤
      5*ENNReal.ofReal (Real.exp (-t)) := by
  have h1 (σ : Fin n → Bool) : swap σ x y = swap (fun i => !σ i) y x := by
    funext i
    cases h : σ i <;> simp [swap, h]
  have h2 (σ : Fin n → Bool) : swap (fun i => !σ i) x y = swap σ y x := by
    funext i
    cases h : σ i <;> simp [swap, h]
  have he : {σ : Fin n → Bool | Psi (swap σ x y) t < Phi (swap (fun i => !σ i) x y) t} =
      {σ | Psi (swap (fun i => !σ i) y x) t < Phi (swap σ y x) t} := by
    ext σ
    change (Psi (swap σ x y) t < Phi (swap (fun i => !σ i) x y) t) ↔
      (Psi (swap (fun i => !σ i) y x) t < Phi (swap σ y x) t)
    rw [h1, h2]
  rw [he]
  exact fixed_sign_comparison hn y x hy hx ht

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma confidence_exp_identity {M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ) :
    Real.exp (-Real.log (3*M/δ)) = δ/(3*M) := by
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 3*M/δ)]
  field_simp

lemma confidence_uniform_budget {M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ) :
    M * Real.exp (-Real.log (3*M/δ)) = δ/3 := by
  rw [confidence_exp_identity hM hδ]
  field_simp

lemma confidence_point_budget {M δ : ℝ} (hM : 10 ≤ M) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    Real.exp (-Real.log (3*M/δ)) ≤ δ/3 ∧
      Real.exp (-Real.log (3*M/δ)) ≤ 1/4 := by
  rw [confidence_exp_identity (by linarith) hδ.1]
  constructor
  · apply div_le_div_of_nonneg_left hδ.1.le (by norm_num)
    linarith
  · apply (div_le_iff₀ (by linarith : 0 < 3*M)).mpr
    nlinarith [hδ.2]

lemma ennreal_net_factor (N : ℕ) {e : ℝ} (_he : 0 ≤ e) :
    (2 : ℝ≥0∞) * ((N : ℝ≥0∞) * ENNReal.ofReal (5*e)) =
      ENNReal.ofReal ((10*(N : ℝ))*e) := by
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 10*(N : ℝ)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num
  ring

lemma good_complement_half {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {B : Set Ω} (hB : MeasurableSet B)
    (hbad : P B ≤ (2 : ℝ≥0∞)⁻¹) : (2 : ℝ≥0∞)⁻¹ ≤ P Bᶜ := by
  rw [measure_compl hB (measure_ne_top P B), measure_univ]
  have h := tsub_le_tsub_left hbad (1 : ℝ≥0∞)
  norm_num at h ⊢
  exact h

lemma confidence_three_budgets {δ : ℝ} (hδ : 0 ≤ δ) :
    ENNReal.ofReal (δ/3) + ENNReal.ofReal (δ/3) + ENNReal.ofReal (δ/3) = ENNReal.ofReal δ := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end EmpiricalBernstein.SVP.EBFresh
end


section

namespace EmpiricalBernstein.SVP.EBFresh

lemma uniform_cover_slack {n : ℕ} (hn : 16 ≤ n) {t : ℝ} (ht : 1 ≤ t) :
    (2 + 8 * Real.sqrt (t / n)) / n ≤ 4 * t / ((n : ℝ) - 1) := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have ht0 : 0 ≤ t := by linarith
  have hs : Real.sqrt (t / n) ≤ t / 4 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hdiv : t / n ≤ t / 16 := div_le_div_of_nonneg_left ht0 (by norm_num) hnR
    have htt : t ≤ t^2 := by nlinarith
    nlinarith
  have hnum : 2 + 8 * Real.sqrt (t / n) ≤ 4 * t := by linarith
  calc
    _ ≤ (4 * t) / n := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

lemma root_sqrt_constants : Real.sqrt 18 + Real.sqrt 2 = Real.sqrt 32 := by
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h18 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 18)
  have h32 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32)
  have h : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 18, Real.sqrt_nonneg 2]
  rw [h]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 32]

lemma root_additive_constants {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    15 * t / ((n : ℝ) - 1) + 6 * t / Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) +
      t / (3 * n) ≤ 22 * t / ((n : ℝ) - 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) - 1 := by linarith
  have hs : (n : ℝ) - 1 ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hmid : 6 * t / Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) ≤ 6 * t / ((n : ℝ) - 1) :=
    div_le_div_of_nonneg_left (by positivity) hp hs
  have hend : t / (3 * n) ≤ t / ((n : ℝ) - 1) :=
    div_le_div_of_nonneg_left ht hp (by linarith)
  have he : 15 * t / ((n : ℝ) - 1) + 6 * t / ((n : ℝ) - 1) +
      t / ((n : ℝ) - 1) = 22 * t / ((n : ℝ) - 1) := by ring
  linarith

lemma small_sample_threshold {n : ℕ} (hn : 2 ≤ n) (hnsmall : n < 16)
    {t : ℝ} (ht : 1 < t) : 1 < 22 * t / ((n : ℝ) - 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR' : (n : ℝ) < 16 := by exact_mod_cast hnsmall
  apply (lt_div_iff₀ (by linarith : 0 < (n : ℝ) - 1)).mpr
  nlinarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory VarianceRegularization.Expansion
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma uniform_native_confidence {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ} (hn : 16 ≤ n)
    (F : Set (X → ℝ)) (hF : F.Countable) (hFm : ∀ f ∈ F, Measurable f)
    (hF01 : ∀ f ∈ F, ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hfin : growthFunction (1 / (n : ℝ)) F (2*n) < ⊤)
    {t : ℝ} (ht : 1 ≤ t) (he : Real.exp (-t) ≤ 1/4) :
    (Measure.pi fun _ : Fin n => μ) {x | ∃ f ∈ F,
      empMean (fun i => f (x i)) + Real.sqrt (18 * sampleVar (fun i => f (x i)) * t / n) +
        15*t/((n : ℝ)-1) < ∫ z, f z ∂μ} ≤ ENNReal.ofReal (calM F n * Real.exp (-t)) := by
  have hn2 : 2 ≤ n := by omega
  have ht0 : 0 ≤ t := by linarith
  let P := Measure.pi (fun _ : Fin n => μ)
  have hghost (f : X → ℝ) (hf : f ∈ F) : (2 : ℝ≥0∞)⁻¹ ≤
      P {y | (∫ z, f z ∂μ) ≤ Phi (fun i => f (y i)) t} := by
    have hb := (native_iid_confidence μ hn2 (hFm f hf) (hF01 f hf) ht0).1
    have hhalf : P {y | Phi (fun i => f (y i)) t < ∫ z, f z ∂μ} ≤ (2 : ℝ≥0∞)⁻¹ := by
      apply hb.trans
      calc
        2 * ENNReal.ofReal (Real.exp (-t)) ≤ 2 * ENNReal.ofReal (1/4 : ℝ) :=
          mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal he) zero_le zero_le
        _ = ENNReal.ofReal ((2 : ℝ) * (1/4)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        _ = ENNReal.ofReal (1/2 : ℝ) := by congr 1; norm_num
        _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]; norm_num
    have hm : MeasurableSet {y : Fin n → X | Phi (fun i => f (y i)) t < ∫ z, f z ∂μ} :=
      measurableSet_lt (measurable_sample_Phi (hFm f hf) t) measurable_const
    have hh := good_complement_half P hm hhalf
    have heq : {y : Fin n → X | (∫ z, f z ∂μ) ≤ Phi (fun i => f (y i)) t} =
        {y : Fin n → X | Phi (fun i => f (y i)) t < ∫ z, f z ∂μ}ᶜ := by ext y; simp
    rw [heq]
    exact hh
  have hcomp (f : X → ℝ) (hf : f ∈ F) (x y : Fin n → X) :
      signLaw n {σ | Psi (fun i => f (swap σ x y i)) t <
        Phi (fun i => f (swap (fun i => !σ i) x y i)) t} ≤ 5 * ENNReal.ofReal (Real.exp (-t)) := by
    have hmap (σ : Fin n → Bool) : (fun i => f (swap σ x y i)) =
        swap σ (fun i => f (x i)) (fun i => f (y i)) := by
      funext i
      cases h : σ i <;> simp [swap, h]
    simpa only [hmap] using fixed_sign_comparison_mirrored hn2 (fun i => f (x i))
      (fun i => f (y i)) (fun i => hF01 f hf (x i)) (fun i => hF01 f hf (y i)) ht0
  have h := uniform_from_comparison μ hn2 F hF hFm (by positivity : 0 ≤ 1 / (n : ℝ))
    ht0 hfin hghost hcomp
  have hf : (5 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-t)) = ENNReal.ofReal (5 * Real.exp (-t)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  rw [hf, ennreal_net_factor _ (Real.exp_pos _).le] at h
  change P _ ≤ ENNReal.ofReal (calM F n * Real.exp (-t)) at h
  apply (measure_mono ?_).trans h
  rintro x ⟨f, hfF, hbad⟩
  refine ⟨f, hfF, ?_⟩
  have hslack := uniform_cover_slack hn ht
  have heq : (2 + 8 * Real.sqrt (t / n)) * (1 / (n : ℝ)) =
      (2 + 8 * Real.sqrt (t / n)) / n := by ring
  rw [heq]
  unfold Psi
  have hadd : 11*t/((n : ℝ)-1) + 4*t/((n : ℝ)-1) = 15*t/((n : ℝ)-1) := by ring
  linarith

end EmpiricalBernstein.SVP.EBFresh
end


section

namespace EmpiricalBernstein.SVP.EBFresh

lemma sqrt_penalty_product {n : ℕ} {t V : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (18 * t) * Real.sqrt (V / n) = Real.sqrt (18 * V * t / n) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 18 * t)]
  congr 1
  ring

lemma sqrt_variance_coefficient {n : ℕ} {t V c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    Real.sqrt (c * V * t / n) = Real.sqrt (c * t / n) * Real.sqrt V := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ c * t / n)]
  congr 1
  ring

lemma root_variance_constants {n : ℕ} {t v : ℝ} (_hv : 0 ≤ v) (_ht : 0 ≤ t) :
    Real.sqrt (18 * v * t / n) + Real.sqrt (2 * v * t / n) =
      Real.sqrt (32 * v * t / n) := by
  have he (c : ℝ) : c * v * t / n = c * (v * t / n) := by ring
  simp_rw [he]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 18),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32), ← add_mul, root_sqrt_constants]

lemma root_cross_penalty {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (18 * t / n) * Real.sqrt (2 * t / ((n : ℝ) - 1)) =
      6 * t / Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 18 * t / n)]
  have he : (18 * t / n) * (2 * t / ((n : ℝ) - 1)) =
      (36 * t^2) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [he, Real.sqrt_div (by positivity : 0 ≤ 36 * t^2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 36), Real.sqrt_sq_eq_abs, abs_of_nonneg ht]
  norm_num

lemma svp_deterministic_bound {n : ℕ} (hn : 2 ≤ n) {t v V : ℝ}
    (ht : 0 ≤ t) (hv : 0 ≤ v) {r rstar estar : ℝ}
    (huniform_min : r ≤ estar + Real.sqrt (18 * V * t / n) + 15 * t / ((n : ℝ) - 1))
    (hmean : estar ≤ rstar + Real.sqrt (2 * v * t / n) + t / (3 * n))
    (hvariance : Real.sqrt V ≤ Real.sqrt v + Real.sqrt (2 * t / ((n : ℝ) - 1))) :
    r - rstar ≤ Real.sqrt (32 * v * t / n) + 22 * t / ((n : ℝ) - 1) := by
  have hpen := mul_le_mul_of_nonneg_left hvariance (Real.sqrt_nonneg (18 * t / n))
  rw [mul_add, ← sqrt_variance_coefficient ht (by norm_num : (0 : ℝ) ≤ 18),
    ← sqrt_variance_coefficient ht (by norm_num : (0 : ℝ) ≤ 18), root_cross_penalty hn ht] at hpen
  have hmain := root_variance_constants (n := n) hv ht
  have hadd := root_additive_constants hn ht
  linarith

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory VarianceRegularization.Expansion
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma svp_outer_closure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    (F : Set (X → ℝ)) (fstar : X → ℝ) (hfstar : fstar ∈ F)
    (svp : (Fin n → X) → (X → ℝ)) (hsvpF : ∀ x, svp x ∈ F)
    {t : ℝ} (ht : 0 ≤ t)
    (hsvp : ∀ x, ∀ f ∈ F,
      empMean (fun i => svp x (x i)) + Real.sqrt (18*t) * Real.sqrt (sampleVar (fun i => svp x (x i)) / n) ≤
      empMean (fun i => f (x i)) + Real.sqrt (18*t) * Real.sqrt (sampleVar (fun i => f (x i)) / n))
    {cU cM cV : ℝ≥0∞}
    (hU : Measure.pi (fun _ : Fin n => μ) {x | ∃ f ∈ F,
      empMean (fun i => f (x i)) + Real.sqrt (18*sampleVar (fun i => f (x i))*t/n) +
        15*t/((n : ℝ)-1) < ∫ y, f y ∂μ} ≤ cU)
    (hM : Measure.pi (fun _ : Fin n => μ) {x |
      (∫ y, fstar y ∂μ) + Real.sqrt (2*variance fstar μ*t/n) + t/(3*n) <
        empMean (fun i => fstar (x i))} ≤ cM)
    (hV : Measure.pi (fun _ : Fin n => μ) {x |
      Real.sqrt (variance fstar μ) + Real.sqrt (2*t/((n : ℝ)-1)) <
        Real.sqrt (sampleVar (fun i => fstar (x i)))} ≤ cV) :
    Measure.pi (fun _ : Fin n => μ) {x |
      (∫ y, svp x y ∂μ) - (∫ y, fstar y ∂μ) >
        Real.sqrt (32*variance fstar μ*t/n) + 22*t/((n : ℝ)-1)} ≤ cU+cM+cV := by
  let U : Set (Fin n → X) := {x | ∃ f ∈ F,
    empMean (fun i => f (x i)) + Real.sqrt (18*sampleVar (fun i => f (x i))*t/n) +
      15*t/((n : ℝ)-1) < ∫ y, f y ∂μ}
  let M : Set (Fin n → X) := {x |
    (∫ y, fstar y ∂μ) + Real.sqrt (2*variance fstar μ*t/n) + t/(3*n) <
      empMean (fun i => fstar (x i))}
  let V : Set (Fin n → X) := {x |
    Real.sqrt (variance fstar μ) + Real.sqrt (2*t/((n : ℝ)-1)) <
      Real.sqrt (sampleVar (fun i => fstar (x i)))}
  have hsub : {x : Fin n → X |
      (∫ y, svp x y ∂μ) - (∫ y, fstar y ∂μ) >
        Real.sqrt (32*variance fstar μ*t/n) + 22*t/((n : ℝ)-1)} ⊆ (U ∪ M) ∪ V := by
    intro x hx
    by_contra hnot
    have hnotU : x ∉ U := fun h => hnot (Or.inl (Or.inl h))
    have hnotM : x ∉ M := fun h => hnot (Or.inl (Or.inr h))
    have hnotV : x ∉ V := fun h => hnot (Or.inr h)
    have hu : (∫ y, svp x y ∂μ) ≤ empMean (fun i => svp x (x i)) +
        Real.sqrt (18*sampleVar (fun i => svp x (x i))*t/n) + 15*t/((n : ℝ)-1) := by
      apply le_of_not_gt
      exact fun h => hnotU ⟨svp x, hsvpF x, h⟩
    have hm := hsvp x fstar hfstar
    rw [sqrt_penalty_product ht, sqrt_penalty_product ht] at hm
    have hu' : (∫ y, svp x y ∂μ) ≤ empMean (fun i => fstar (x i)) +
        Real.sqrt (18*sampleVar (fun i => fstar (x i))*t/n) + 15*t/((n : ℝ)-1) := by linarith
    have hbound := svp_deterministic_bound hn ht (variance_nonneg fstar μ) hu'
      (le_of_not_gt hnotM) (le_of_not_gt hnotV)
    exact (not_lt_of_ge hbound) hx
  calc
    _ ≤ Measure.pi (fun _ : Fin n => μ) ((U ∪ M) ∪ V) := measure_mono hsub
    _ ≤ (Measure.pi (fun _ : Fin n => μ) (U ∪ M)) + Measure.pi (fun _ : Fin n => μ) V := measure_union_le _ _
    _ ≤ (Measure.pi (fun _ : Fin n => μ) U + Measure.pi (fun _ : Fin n => μ) M) +
        Measure.pi (fun _ : Fin n => μ) V := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hU hM) hV

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

lemma confidence_log_gt_one {M δ : ℝ} (hM : 10 ≤ M) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    1 < Real.log (3 * M / δ) := by
  have hpos : 0 < 3 * M / δ := div_pos (by linarith) hδ.1
  apply (Real.lt_log_iff_exp_lt hpos).mpr
  have h3 : 3 < 3 * M / δ := by
    apply (lt_div_iff₀ hδ.1).mpr
    nlinarith [hδ.2]
  exact Real.exp_one_lt_three.trans h3

lemma native_small_sample_svp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : Set (X → ℝ)) (hFm : ∀ f ∈ F, Measurable f)
    (hF01 : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) (hn : 2 ≤ n) (hnsmall : n < 16)
    (hfin : growthFunction (1 / (n : ℝ)) F (2 * n) < ⊤)
    (fstar : X → ℝ) (hfstar : fstar ∈ F)
    (svp : (Fin n → X) → (X → ℝ)) (hsvpF : ∀ x, svp x ∈ F) :
    Measure.pi (fun _ : Fin n => μ) {x |
        (∫ y, svp x y ∂μ) - (∫ y, fstar y ∂μ) >
          Real.sqrt (32 * variance fstar μ * Real.log (3 * calM F n / δ) / n) +
            22 * Real.log (3 * calM F n / δ) / ((n : ℝ) - 1)} ≤ ENNReal.ofReal δ := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure μ
  have ht := confidence_log_gt_one (calM_ge_ten ⟨fstar, hfstar⟩ hfin) hδ
  have hthreshold := small_sample_threshold hn hnsmall ht
  have hf := unit_interval_risk (μ := μ) (hFm fstar hfstar) (hF01 fstar hfstar)
  have hempty : {x : Fin n → X |
        (∫ y, svp x y ∂μ) - (∫ y, fstar y ∂μ) >
          Real.sqrt (32 * variance fstar μ * Real.log (3 * calM F n / δ) / n) +
            22 * Real.log (3 * calM F n / δ) / ((n : ℝ) - 1)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hs := unit_interval_risk (μ := μ) (hFm (svp x) (hsvpF x)) (hF01 (svp x) (hsvpF x))
    have hroot := Real.sqrt_nonneg (32 * variance fstar μ * Real.log (3 * calM F n / δ) / n)
    simp only [Set.mem_ofPred_eq] at hx
    linarith [hf.1, hs.2]
  rw [hempty, measure_empty]
  exact zero_le

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory VarianceRegularization.Expansion
open scoped ENNReal
namespace EmpiricalBernstein.SVP.EBFresh

theorem native_svp_excess_risk {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (F : Set (𝒳 → ℝ)) (hFc : F.Countable) (hFm : ∀ f ∈ F, Measurable f)
    (hF01 : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) (hn : 2 ≤ n)
    (hfin : growthFunction (1 / (n : ℝ)) F (2 * n) < ⊤)
    (lam : ℝ) (hlam : lam = Real.sqrt (18 * Real.log (3 * calM F n / δ)))
    (fstar : 𝒳 → ℝ) (hfstar : fstar ∈ F)
    (svp : (Fin n → 𝒳) → (𝒳 → ℝ)) (hsvpF : ∀ x, svp x ∈ F)
    (hsvp : ∀ x, ∀ f ∈ F,
      empMean (fun i => svp x (x i)) + lam * Real.sqrt (sampleVar (fun i => svp x (x i)) / n)
        ≤ empMean (fun i => f (x i)) + lam * Real.sqrt (sampleVar (fun i => f (x i)) / n)) :
    Measure.pi (fun _ : Fin n => μ) {x |
        (∫ y, svp x y ∂μ) - (∫ y, fstar y ∂μ)
          > Real.sqrt (32 * variance fstar μ * Real.log (3 * calM F n / δ) / n)
            + 22 * Real.log (3 * calM F n / δ) / ((n : ℝ) - 1)}
      ≤ ENNReal.ofReal δ := by
  by_cases hnsmall : n < 16
  · exact native_small_sample_svp μ F hFm hF01 δ hδ n hn hnsmall hfin fstar hfstar svp hsvpF
  have hn16 : 16 ≤ n := by omega
  have : Nonempty 𝒳 := nonempty_of_isProbabilityMeasure μ
  let t := Real.log (3 * calM F n / δ)
  have hMge : 10 ≤ calM F n := calM_ge_ten ⟨fstar, hfstar⟩ hfin
  have hMpos : 0 < calM F n := by linarith
  have ht1 : 1 < t := confidence_log_gt_one hMge hδ
  have ht0 : 0 ≤ t := by linarith
  have hbud : Real.exp (-t) ≤ δ/3 ∧ Real.exp (-t) ≤ 1/4 := confidence_point_budget hMge hδ
  have hu := uniform_native_confidence μ hn16 F hFc hFm hF01 hfin ht1.le hbud.2
  have heq : calM F n * Real.exp (-t) = δ/3 := confidence_uniform_budget hMpos hδ.1
  rw [heq] at hu
  have hfixed := native_iid_confidence μ hn (hFm fstar hfstar) (hF01 fstar hfstar) ht0
  have hm := hfixed.2.1.trans (ENNReal.ofReal_le_ofReal hbud.1)
  have hv := hfixed.2.2.trans (ENNReal.ofReal_le_ofReal hbud.1)
  have hmin : ∀ x, ∀ f ∈ F,
      empMean (fun i => svp x (x i)) + Real.sqrt (18*t) * Real.sqrt (sampleVar (fun i => svp x (x i)) / n) ≤
      empMean (fun i => f (x i)) + Real.sqrt (18*t) * Real.sqrt (sampleVar (fun i => f (x i)) / n) := by
    intro x f hf
    have h := hsvp x f hf
    rw [hlam] at h
    exact h
  have h := svp_outer_closure μ hn F fstar hfstar svp hsvpF ht0 hmin hu hm hv
  rw [confidence_three_budgets hδ.1.le] at h
  exact h

end EmpiricalBernstein.SVP.EBFresh
end


section

open MeasureTheory ProbabilityTheory VarianceRegularization.Expansion

namespace EmpiricalBernstein.SVP

/-- Theorem 15 (arXiv:0907.3740v1, p. 6): excess risk of sample variance penalization (10) with
`λ = √(18 ln(3ℳ(n)/δ))`. `svp` is any selector returning, for every sample `x`, a minimizer over
`F` of `P_n(f, x) + λ √(V_n(f, x)/n)` (the paper's `arg min`). `F` is a countable class of
measurable `[0,1]`-valued functions with finite growth function `N∞(1/n, F, 2n)`. The probability
of the (possibly non-measurable) bad event is its outer measure under `μ^n`. -/
theorem svp_excess_risk {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (F : Set (𝒳 → ℝ)) (hFc : F.Countable) (hFm : ∀ f ∈ F, Measurable f)
    (hF01 : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) (hn : 2 ≤ n)
    (hfin : growthFunction (1 / (n : ℝ)) F (2 * n) < ⊤)
    (lam : ℝ) (hlam : lam = Real.sqrt (18 * Real.log (3 * calM F n / δ)))
    (fstar : 𝒳 → ℝ) (hfstar : fstar ∈ F)
    (svp : (Fin n → 𝒳) → (𝒳 → ℝ)) (hsvpF : ∀ x, svp x ∈ F)
    (hsvp : ∀ x, ∀ f ∈ F,
      empMean (fun i => svp x (x i)) + lam * Real.sqrt (sampleVar (fun i => svp x (x i)) / n)
        ≤ empMean (fun i => f (x i)) + lam * Real.sqrt (sampleVar (fun i => f (x i)) / n)) :
    Measure.pi (fun _ : Fin n => μ) {x |
        (∫ y, svp x y ∂μ) - (∫ y, fstar y ∂μ)
          > Real.sqrt (32 * variance fstar μ * Real.log (3 * calM F n / δ) / n)
            + 22 * Real.log (3 * calM F n / δ) / ((n : ℝ) - 1)}
      ≤ ENNReal.ofReal δ := by
  exact EBFresh.native_svp_excess_risk μ F hFc hFm hF01 δ hδ n hn hfin lam hlam fstar hfstar svp hsvpF hsvp

end EmpiricalBernstein.SVP
end


open MeasureTheory ProbabilityTheory VarianceRegularization.Expansion

theorem solution {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (F : Set (𝒳 → ℝ)) (hFc : F.Countable) (hFm : ∀ f ∈ F, Measurable f)
    (hF01 : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) (hn : 2 ≤ n)
    (hfin : EmpiricalBernstein.SVP.growthFunction (1 / (n : ℝ)) F (2 * n) < ⊤)
    (lam : ℝ) (hlam : lam = Real.sqrt (18 * Real.log (3 * EmpiricalBernstein.SVP.calM F n / δ)))
    (fstar : 𝒳 → ℝ) (hfstar : fstar ∈ F)
    (svp : (Fin n → 𝒳) → (𝒳 → ℝ)) (hsvpF : ∀ x, svp x ∈ F)
    (hsvp : ∀ x, ∀ f ∈ F,
      VarianceRegularization.Expansion.empMean (fun i => svp x (x i)) + lam * Real.sqrt (EmpiricalBernstein.SVP.sampleVar (fun i => svp x (x i)) / n)
        ≤ VarianceRegularization.Expansion.empMean (fun i => f (x i)) + lam * Real.sqrt (EmpiricalBernstein.SVP.sampleVar (fun i => f (x i)) / n)) :
    Measure.pi (fun _ : Fin n => μ) {x |
        (∫ y, svp x y ∂μ) - (∫ y, fstar y ∂μ)
          > Real.sqrt (32 * variance fstar μ * Real.log (3 * EmpiricalBernstein.SVP.calM F n / δ) / n)
            + 22 * Real.log (3 * EmpiricalBernstein.SVP.calM F n / δ) / ((n : ℝ) - 1)}
      ≤ ENNReal.ofReal δ := by
  exact EmpiricalBernstein.SVP.svp_excess_risk μ F hFc hFm hF01 δ hδ n hn hfin lam hlam fstar hfstar svp hsvpF hsvp
