-- Prove2me | solution 1 for CompOT.Sinkhorn.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T06:52:12.396672+00:00
-- url     : https://prove2.me/submissions/0e9aebae-8c4c-4afa-a366-5fc589ed7f8a

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

section

open Filter Topology
open scoped BigOperators

namespace CompOT.Sinkhorn.Fresh

end CompOT.Sinkhorn.Fresh
end

section
open scoped BigOperators
namespace CompOT.Sinkhorn.Fresh

noncomputable def logPath {m : ℕ} (v w : Fin m → ℝ) (t : ℝ) (j : Fin m) : ℝ :=
  w j * Real.exp (t * Real.log (v j / w j))

theorem logPath_pos {m : ℕ} (v w : Fin m → ℝ) (hw : ∀ j, 0 < w j)
    (t : ℝ) (j : Fin m) : 0 < logPath v w t j :=
  mul_pos (hw j) (Real.exp_pos _)

theorem logPath_zero {m : ℕ} (v w : Fin m → ℝ) : logPath v w 0 = w := by
  funext j
  simp [logPath]

theorem logPath_one {m : ℕ} (v w : Fin m → ℝ)
    (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j) : logPath v w 1 = v := by
  funext j
  simp only [logPath, one_mul, Real.exp_log (div_pos (hv j) (hw j))]
  field_simp [ne_of_gt (hw j)]

theorem logPath_hasDerivAt {m : ℕ} (v w : Fin m → ℝ) (t : ℝ) (j : Fin m) :
    HasDerivAt (fun s => logPath v w s j)
      (logPath v w t j * Real.log (v j/w j)) t := by
  have hh := (((hasDerivAt_id t).mul_const (Real.log (v j/w j))).exp).const_mul (w j)
  simpa only [logPath, id_eq, one_mul, mul_assoc] using hh
end CompOT.Sinkhorn.Fresh
end

section
open scoped BigOperators
open Matrix
namespace CompOT.Sinkhorn.Fresh

theorem cross_ratio_le_eta {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ)
    (i j : Fin n) (k l : Fin m) : K i k*K j l/(K j k*K i l) ≤ eta K := by
  calc
    _ ≤ ⨆ l, K i k*K j l/(K j k*K i l) := le_ciSup (f := fun l => K i k*K j l/(K j k*K i l)) (Set.finite_range _).bddAbove l
    _ ≤ ⨆ k, ⨆ l, K i k*K j l/(K j k*K i l) := le_ciSup (f := fun k => ⨆ l, K i k*K j l/(K j k*K i l)) (Set.finite_range _).bddAbove k
    _ ≤ ⨆ j, ⨆ k, ⨆ l, K i k*K j l/(K j k*K i l) := le_ciSup (f := fun j => ⨆ k, ⨆ l, K i k*K j l/(K j k*K i l)) (Set.finite_range _).bddAbove j
    _ ≤ eta K := le_ciSup (f := fun i => ⨆ j, ⨆ k, ⨆ l, K i k*K j l/(K j k*K i l)) (Set.finite_range _).bddAbove i

theorem eta_ge_one {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j) : 1 ≤ eta K := by
  let i : Fin n := ⟨0,hn⟩
  let j : Fin m := ⟨0,hm⟩
  have hh := cross_ratio_le_eta K i i j j
  simpa only [div_self (ne_of_gt (mul_pos (hK i j) (hK i j)))] using hh

theorem lam_bounds {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j) :
    0 ≤ lam K ∧ lam K < 1 := by
  have he := eta_ge_one hn hm K hK
  have hs : 1 ≤ Real.sqrt (eta K) := Real.one_le_sqrt.mpr he
  have hp : 0 < Real.sqrt (eta K)+1 := by positivity
  exact ⟨div_nonneg (by linarith) hp.le, (div_lt_one hp).2 (by linarith)⟩

theorem mulVec_pos {n m : ℕ} (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (v : Fin m → ℝ) (hv : ∀ j, 0 < v j) (i : Fin n) : 0 < (K *ᵥ v) i := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (hK i j) (hv j)) Finset.univ_nonempty
end CompOT.Sinkhorn.Fresh
end

section
open scoped BigOperators
open Matrix
namespace CompOT.Sinkhorn.Fresh

noncomputable def rowProb {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ)
    (w : Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ := K i j * w j / (K *ᵥ w) i

theorem rowProb_pos {n m : ℕ} (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (w : Fin m → ℝ) (hw : ∀ j, 0 < w j) (i : Fin n) (j : Fin m) :
    0 < rowProb K w i j :=
  div_pos (mul_pos (hK i j) (hw j)) (mulVec_pos hm K hK w hw i)

theorem rowProb_sum {n m : ℕ} (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (w : Fin m → ℝ) (hw : ∀ j, 0 < w j) (i : Fin n) :
    ∑ j, rowProb K w i j = 1 := by
  simp only [rowProb, ← Finset.sum_div]
  exact div_self (ne_of_gt (mulVec_pos hm K hK w hw i))

theorem rowProb_cross {n m : ℕ} (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (w : Fin m → ℝ) (hw : ∀ j, 0 < w j) (i j : Fin n) (k l : Fin m) :
    rowProb K w i k * rowProb K w j l ≤
      eta K * rowProb K w j k * rowProb K w i l := by
  have h := (div_le_iff₀ (mul_pos (hK j k) (hK i l))).mp (cross_ratio_le_eta K i j k l)
  have hmul := mul_le_mul_of_nonneg_right h (mul_pos (hw k) (hw l)).le
  have hi := mulVec_pos hm K hK w hw i
  have hj := mulVec_pos hm K hK w hw j
  dsimp only [rowProb]
  apply (le_of_mul_le_mul_right _ (mul_pos hi hj))
  convert hmul using 1 <;> field_simp

end CompOT.Sinkhorn.Fresh
end

section
open scoped BigOperators
open Matrix
namespace CompOT.Sinkhorn.Fresh

theorem mulVec_path_hasDerivAt {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ)
    (v w : Fin m → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s => (K *ᵥ logPath v w s) i)
      (∑ j, K i j * (logPath v w t j * Real.log (v j/w j))) t := by
  have hh : HasDerivAt (∑ j : Fin m, fun s : ℝ => K i j * logPath v w s j)
      (∑ j, K i j * (logPath v w t j * Real.log (v j/w j))) t :=
    HasDerivAt.sum (fun j _ => (logPath_hasDerivAt v w t j).const_mul (K i j))
  have he : (∑ j : Fin m, fun s : ℝ => K i j * logPath v w s j) =
      (fun s => (K *ᵥ logPath v w s) i) := by
    funext s
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  rw [he] at hh
  exact hh

theorem log_mulVec_path_hasDerivAt {n m : ℕ} (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (v w : Fin m → ℝ) (hw : ∀ j, 0 < w j) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s => Real.log ((K *ᵥ logPath v w s) i))
      (∑ j, rowProb K (logPath v w t) i j * Real.log (v j/w j)) t := by
  have hh := (mulVec_path_hasDerivAt K v w i t).log
    (ne_of_gt (mulVec_pos hm K hK _ (logPath_pos v w hw t) i))
  convert hh using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [rowProb]
  ring

end CompOT.Sinkhorn.Fresh
end

section
open scoped BigOperators
namespace CompOT.Sinkhorn.Fresh

theorem ratio_le_metric_sup {n : ℕ} (u v : Fin n → ℝ) (i j : Fin n) :
    u i*v j/(u j*v i) ≤ ⨆ a, ⨆ b, u a*v b/(u b*v a) := by
  calc
    u i*v j/(u j*v i) ≤ ⨆ b, u i*v b/(u b*v i) :=
      le_ciSup (f := fun b => u i*v b/(u b*v i)) (Set.finite_range _).bddAbove j
    _ ≤ ⨆ a, ⨆ b, u a*v b/(u b*v a) :=
      le_ciSup (f := fun a => ⨆ b, u a*v b/(u b*v a)) (Set.finite_range _).bddAbove i

theorem metric_sup_pos {n : ℕ} (hn : 0 < n) {u v : Fin n → ℝ}
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) :
    0 < ⨆ i, ⨆ j, u i*v j/(u j*v i) := by
  let i : Fin n := ⟨0,hn⟩
  exact (div_pos (mul_pos (hu i) (hv i)) (mul_pos (hu i) (hv i))).trans_le
    (ratio_le_metric_sup u v i i)

theorem metric_nonneg {n : ℕ} (hn : 0 < n) {u v : Fin n → ℝ}
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) : 0 ≤ hilbertMetric u v := by
  apply Real.log_nonneg
  let i : Fin n := ⟨0,hn⟩
  have hh := ratio_le_metric_sup u v i i
  simpa only [div_self (ne_of_gt (mul_pos (hu i) (hv i)))] using hh

theorem log_difference_le_metric {n : ℕ} (_hn : 0 < n) {u v : Fin n → ℝ}
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) (i j : Fin n) :
    Real.log (u i/v i)-Real.log (u j/v j) ≤ hilbertMetric u v := by
  have hh := Real.log_le_log (div_pos (mul_pos (hu i) (hv j)) (mul_pos (hu j) (hv i)))
    (ratio_le_metric_sup u v i j)
  rw [Real.log_div (ne_of_gt (mul_pos (hu i) (hv j))) (ne_of_gt (mul_pos (hu j) (hv i))),
    Real.log_mul (ne_of_gt (hu i)) (ne_of_gt (hv j)),
    Real.log_mul (ne_of_gt (hu j)) (ne_of_gt (hv i))] at hh
  rw [Real.log_div (ne_of_gt (hu i)) (ne_of_gt (hv i)),
    Real.log_div (ne_of_gt (hu j)) (ne_of_gt (hv j))]
  unfold hilbertMetric
  linarith

theorem metric_le_of_log_ratios {n : ℕ} (hn : 0 < n) {u v : Fin n → ℝ}
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) {C : ℝ}
    (h : ∀ i j, Real.log (u i*v j/(u j*v i)) ≤ C) : hilbertMetric u v ≤ C := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  apply (Real.log_le_iff_le_exp (metric_sup_pos hn hu hv)).2
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  exact (Real.log_le_iff_le_exp (div_pos (mul_pos (hu i) (hv j)) (mul_pos (hu j) (hv i)))).mp (h i j)
end CompOT.Sinkhorn.Fresh
end

section

open scoped BigOperators
namespace CompOT.Sinkhorn.Fresh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mass_compl (p : ι → ℝ) (hp : ∑ i, p i = 1) (S : Finset ι) :
    ∑ i ∈ Sᶜ, p i = 1 - ∑ i ∈ S, p i := by
  classical
  have h := Finset.sum_add_sum_compl S p
  rw [hp] at h
  linarith

theorem cross_mass_bound (p q : ι → ℝ) (E : ℝ) (S : Finset ι)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (hcross : ∀ i j, p i * q j ≤ E * q i * p j) :
    (∑ i ∈ S, p i) * (1 - ∑ i ∈ S, q i) ≤
      E * (∑ i ∈ S, q i) * (1 - ∑ i ∈ S, p i) := by
  classical
  rw [← mass_compl q hq S, ← mass_compl p hp S]
  calc
    _ = ∑ i ∈ S, ∑ j ∈ Sᶜ, p i * q j := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, E * q i * p j :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcross i j
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

theorem split_quadratic_bound (p q : ι → ℝ) (E : ℝ) (S : Finset ι)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (hE : 1 ≤ E) (hS : ∑ i ∈ S, q i ≤ ∑ i ∈ S, p i)
    (hcross : ∀ i j, p i * q j ≤ E * q i * p j) :
    0 ≤ (∑ i ∈ S, p i) - ∑ i ∈ S, q i ∧
    (∑ i ∈ S, p i) - ∑ i ∈ S, q i ≤ 1 ∧
    4 * ((∑ i ∈ S, p i) - ∑ i ∈ S, q i) ≤
      (E - 1) * (1 - ((∑ i ∈ S, p i) - ∑ i ∈ S, q i)) ^ 2 := by
  classical
  let u := ∑ i ∈ S, p i
  let v := ∑ i ∈ S, q i
  have hu0 : 0 ≤ u := Finset.sum_nonneg fun i _ => hp0 i
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun i _ => hq0 i
  have hu1 : u ≤ 1 := by
    have hc : 0 ≤ ∑ i ∈ Sᶜ, p i := Finset.sum_nonneg fun i _ => hp0 i
    rw [mass_compl p hp S] at hc
    dsimp [u]
    linarith
  have huv : v ≤ u := hS
  have hc := cross_mass_bound p q E S hp hq hcross
  change u * (1 - v) ≤ E * v * (1 - u) at hc
  have hprod : 4 * (v * (1 - u)) ≤ (1 - (u - v)) ^ 2 := by
    nlinarith [sq_nonneg (v - (1 - u))]
  have hm := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hE)
  change 0 ≤ u - v ∧ u - v ≤ 1 ∧ _
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

end CompOT.Sinkhorn.Fresh
end

section

open scoped BigOperators
namespace CompOT.Sinkhorn.Fresh

variable {ι : Type*} [Fintype ι]

theorem mean_difference_le_positive_mass (p q f : ι → ℝ) (L D : ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (hf : ∀ i, L ≤ f i ∧ f i ≤ L + D) :
    (∑ i, p i * f i) - ∑ i, q i * f i ≤
      D * (∑ i ∈ Finset.univ.filter (fun i => q i ≤ p i), (p i - q i)) := by
  classical
  have hid : (∑ i, p i * f i) - ∑ i, q i * f i =
      ∑ i, (p i - q i) * (f i - L) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, hq]
    ring
  rw [hid]
  calc
    _ ≤ ∑ i, if q i ≤ p i then D * (p i - q i) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · have hh := mul_le_mul_of_nonneg_left (hf i).2 (sub_nonneg.mpr hi)
        nlinarith
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hi))
          (sub_nonneg.mpr (hf i).1)
    _ = _ := by simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]

end CompOT.Sinkhorn.Fresh
end

section

noncomputable section
namespace CompOT.Sinkhorn.Fresh

lemma sharp_tv_quadratic (E d : ℝ) (hE : 1 ≤ E) (_hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hquad : 4 * d ≤ (E - 1) * (1 - d) ^ 2) :
    d ≤ (Real.sqrt E - 1) / (Real.sqrt E + 1) := by
  have hE0 : 0 ≤ E := by linarith
  have hs := Real.sq_sqrt hE0
  have hs0 := Real.sqrt_nonneg E
  have hs1 : 1 ≤ Real.sqrt E := by nlinarith
  have hb : 2 ≤ (Real.sqrt E + 1) - (Real.sqrt E - 1) * d := by
    have hh := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hd1)
    nlinarith
  have hid : ((Real.sqrt E - 1) - (Real.sqrt E + 1) * d) *
      ((Real.sqrt E + 1) - (Real.sqrt E - 1) * d) =
      (E - 1) * (1 - d) ^ 2 - 4 * d := by
    calc
      _ = ((Real.sqrt E) ^ 2 - 1) * (1 - d) ^ 2 - 4 * d := by ring
      _ = _ := by rw [hs]
  have hp : 0 ≤ ((Real.sqrt E - 1) - (Real.sqrt E + 1) * d) *
      ((Real.sqrt E + 1) - (Real.sqrt E - 1) * d) := by
    rw [hid]
    linarith
  have hfirst : 0 ≤ (Real.sqrt E - 1) - (Real.sqrt E + 1) * d :=
    nonneg_of_mul_nonneg_left hp (by linarith)
  apply (le_div_iff₀ (by linarith : 0 < Real.sqrt E + 1)).mpr
  nlinarith

lemma sharp_tv_two_masses (E u v : ℝ) (hE : 1 ≤ E)
    (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (_hv1 : v ≤ 1)
    (hvu : v ≤ u) (hcross : u * (1 - v) ≤ E * v * (1 - u)) :
    u - v ≤ (Real.sqrt E - 1) / (Real.sqrt E + 1) := by
  apply sharp_tv_quadratic E (u - v) hE (sub_nonneg.mpr hvu) (by linarith)
  have hh := mul_nonneg (sub_nonneg.mpr hE) (sq_nonneg (v - (1 - u)))
  nlinarith

end CompOT.Sinkhorn.Fresh
end

section

open scoped BigOperators
namespace CompOT.Sinkhorn.Fresh

variable {ι : Type*} [Fintype ι]

theorem sharp_mean_difference (p q f : ι → ℝ) (E L D : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (hE : 1 ≤ E) (hD : 0 ≤ D)
    (hcross : ∀ i j, p i * q j ≤ E * q i * p j)
    (hf : ∀ i, L ≤ f i ∧ f i ≤ L + D) :
    (∑ i, p i * f i) - ∑ i, q i * f i ≤
      ((Real.sqrt E - 1) / (Real.sqrt E + 1)) * D := by
  classical
  let S := Finset.univ.filter (fun i => q i ≤ p i)
  have hS : ∑ i ∈ S, q i ≤ ∑ i ∈ S, p i := by
    apply Finset.sum_le_sum
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨hd0, hd1, hdquad⟩ := split_quadratic_bound p q E S hp0 hq0 hp hq hE hS hcross
  have htv := sharp_tv_quadratic E _ hE hd0 hd1 hdquad
  have hm := mean_difference_le_positive_mass p q f L D hp hq hf
  have hmass : (∑ i ∈ S, (p i - q i)) = (∑ i ∈ S, p i) - ∑ i ∈ S, q i :=
    Finset.sum_sub_distrib p q
  change _ ≤ D * (∑ i ∈ S, (p i - q i)) at hm
  rw [hmass] at hm
  calc
    _ ≤ D * ((∑ i ∈ S, p i) - ∑ i ∈ S, q i) := hm
    _ ≤ D * ((Real.sqrt E - 1) / (Real.sqrt E + 1)) :=
      mul_le_mul_of_nonneg_left htv hD
    _ = _ := mul_comm _ _

end CompOT.Sinkhorn.Fresh
end

section
open scoped BigOperators
open Matrix
namespace CompOT.Sinkhorn.Fresh

theorem path_mean_difference_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (v w : Fin m → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (i j : Fin n) (t : ℝ) :
    (∑ k, rowProb K (logPath v w t) i k * Real.log (v k/w k)) -
      (∑ k, rowProb K (logPath v w t) j k * Real.log (v k/w k)) ≤
      lam K * hilbertMetric v w := by
  classical
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun k => Real.log (v k/w k)) Finset.univ_nonempty
  apply sharp_mean_difference _ _ _ (eta K) (Real.log (v a/w a)) (hilbertMetric v w)
  · intro k
    exact (rowProb_pos hm K hK _ (logPath_pos v w hw t) i k).le
  · intro k
    exact (rowProb_pos hm K hK _ (logPath_pos v w hw t) j k).le
  · exact rowProb_sum hm K hK _ (logPath_pos v w hw t) i
  · exact rowProb_sum hm K hK _ (logPath_pos v w hw t) j
  · exact eta_ge_one hn hm K hK
  · exact metric_nonneg hm hv hw
  · exact rowProb_cross hm K hK _ (logPath_pos v w hw t) i j
  · intro k
    constructor
    · exact ha k (Finset.mem_univ k)
    · have h := log_difference_le_metric hm hv hw k a
      linarith

theorem log_output_difference_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (v w : Fin m → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (i j : Fin n) :
    (Real.log ((K *ᵥ v) i) - Real.log ((K *ᵥ v) j)) -
      (Real.log ((K *ᵥ w) i) - Real.log ((K *ᵥ w) j)) ≤
      lam K * hilbertMetric v w := by
  let F := fun t => Real.log ((K *ᵥ logPath v w t) i) -
    Real.log ((K *ᵥ logPath v w t) j)
  have hder (t : ℝ) := (log_mulVec_path_hasDerivAt hm K hK v w hw i t).sub
    (log_mulVec_path_hasDerivAt hm K hK v w hw j t)
  have hF : Differentiable ℝ F := fun t => (hder t).differentiableAt
  have hbound : ∀ t, deriv F t ≤ lam K * hilbertMetric v w := by
    intro t
    have he : deriv F t =
        (∑ k, rowProb K (logPath v w t) i k * Real.log (v k/w k)) -
        (∑ k, rowProb K (logPath v w t) j k * Real.log (v k/w k)) := (hder t).deriv
    rw [he]
    exact path_mean_difference_bound hn hm K hK v w hv hw i j t
  have hh := image_sub_le_mul_sub_of_deriv_le hF hbound (show (0:ℝ) ≤ 1 by norm_num)
  simpa only [F, logPath_zero, logPath_one v w hv hw, sub_zero, mul_one] using hh

end CompOT.Sinkhorn.Fresh
end

section
open Matrix
namespace CompOT.Sinkhorn.Fresh

theorem native_theorem_4_1 {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (v v' : Fin m → ℝ) (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j) :
    hilbertMetric (K *ᵥ v) (K *ᵥ v') ≤ lam K * hilbertMetric v v' ∧ lam K < 1 := by
  refine ⟨?_, (lam_bounds hn hm K hK).2⟩
  apply metric_le_of_log_ratios hn (mulVec_pos hm K hK v hv) (mulVec_pos hm K hK v' hv')
  intro i j
  have hh := log_output_difference_bound hn hm K hK v v' hv hv' i j
  rw [Real.log_div
    (ne_of_gt (mul_pos (mulVec_pos hm K hK v hv i) (mulVec_pos hm K hK v' hv' j)))
    (ne_of_gt (mul_pos (mulVec_pos hm K hK v hv j) (mulVec_pos hm K hK v' hv' i))),
    Real.log_mul (ne_of_gt (mulVec_pos hm K hK v hv i)) (ne_of_gt (mulVec_pos hm K hK v' hv' j)),
    Real.log_mul (ne_of_gt (mulVec_pos hm K hK v hv j)) (ne_of_gt (mulVec_pos hm K hK v' hv' i))]
  linarith

end CompOT.Sinkhorn.Fresh
end

open CompOT.Sinkhorn Matrix

theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (v v' : Fin m → ℝ) (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j) :
    hilbertMetric (K *ᵥ v) (K *ᵥ v') ≤ lam K * hilbertMetric v v' ∧ lam K < 1 := by
  exact Fresh.native_theorem_4_1 hn hm K hK v v' hv hv'
