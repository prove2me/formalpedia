-- Prove2me | solution 1 for CompOT.Sinkhorn.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T07:23:51.104989+00:00
-- url     : https://prove2.me/submissions/db5a314e-5fd8-41d9-b05f-7deb40056cc5

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs


section
namespace SinkhornProof
lemma scalar_variation (a b r : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1)
    (hr : 1 ≤ r) (hodds : a*(1-b) ≤ r*b*(1-a)) :
    a-b ≤ (Real.sqrt r-1)/(Real.sqrt r+1) := by
  have hs : 1 ≤ Real.sqrt r := by
    simpa using Real.sqrt_le_sqrt hr
  have hs2 := Real.sq_sqrt (show 0 ≤ r by linarith)
  have hd0 : 0 ≤ a-b := sub_nonneg.mpr hba
  have hd1 : a-b ≤ 1 := by linarith
  have hsq := sq_nonneg (2*b-(1-(a-b)))
  have hmax : 4*b*(1-a) ≤ (1-(a-b))^2 := by nlinarith
  have hp : 4*(a-b) ≤ (r-1)*(1-(a-b))^2 := by
    have hm := mul_le_mul_of_nonneg_left hmax (show 0 ≤ r-1 by linarith)
    nlinarith
  apply (le_div_iff₀ (show 0 < Real.sqrt r+1 by linarith)).2
  by_contra h
  have hv : 0 < (Real.sqrt r+1)*(a-b)-(Real.sqrt r-1) := by
    have hh := lt_of_not_ge h
    nlinarith
  have hw : 0 < (Real.sqrt r+1)-(Real.sqrt r-1)*(a-b) := by
    have hm := mul_le_mul_of_nonneg_left hd1 (show 0 ≤ Real.sqrt r-1 by linarith)
    linarith
  have hprod := mul_pos hv hw
  have he : ((Real.sqrt r+1)*(a-b)-(Real.sqrt r-1))*
      ((Real.sqrt r+1)-(Real.sqrt r-1)*(a-b)) =
      4*(a-b)-(r-1)*(1-(a-b))^2 := by
    nlinarith [hs2]
  rw [he] at hprod
  linarith
end SinkhornProof
end

section
open Finset
namespace SinkhornProof
lemma probability_variation {m : ℕ} (p q : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j)
    (hp1 : ∑ j, p j = 1) (hq1 : ∑ j, q j = 1)
    (r : ℝ) (hr : 1 ≤ r) (hodds : ∀ j l, p j*q l ≤ r*q j*p l) :
    (∑ j, |p j-q j|)/2 ≤ (Real.sqrt r-1)/(Real.sqrt r+1) := by
  classical
  let S : Finset (Fin m) := univ.filter (fun j => q j ≤ p j)
  let a := ∑ j ∈ S, p j
  let b := ∑ j ∈ S, q j
  have hpa : a+(∑ j ∈ Sᶜ,p j)=1 := by simpa [a] using (S.sum_add_sum_compl p).trans hp1
  have hqb : b+(∑ j ∈ Sᶜ,q j)=1 := by simpa [b] using (S.sum_add_sum_compl q).trans hq1
  have hb : 0 ≤ b := sum_nonneg fun j _ => hq j
  have ha : a ≤ 1 := by have := sum_nonneg (fun j (_ : j ∈ Sᶜ) => hp j); linarith
  have hba : b ≤ a := sum_le_sum fun j hj => (mem_filter.mp hj).2
  have ho : a*(1-b) ≤ r*b*(1-a) := by
    have h := sum_le_sum (s := S) fun i _ => sum_le_sum (s := Sᶜ) fun j _ => hodds i j
    simp only [← mul_sum, ← sum_mul] at h
    dsimp [a,b] at hpa hqb ⊢
    rw [show 1-(∑ j ∈ S,q j)=(∑ j ∈ Sᶜ,q j) by linarith,
      show 1-(∑ j ∈ S,p j)=(∑ j ∈ Sᶜ,p j) by linarith]
    simpa only [← mul_sum] using h
  have he : (∑ j, |p j-q j|)=2*(a-b) := by
    rw [← S.sum_add_sum_compl (fun j => |p j-q j|)]
    have h1 : (∑ j ∈ S, |p j-q j|)=a-b := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro j hj
      exact abs_of_nonneg (sub_nonneg.mpr (mem_filter.mp hj).2)
    have h2 : (∑ j ∈ Sᶜ, |p j-q j|)=(∑ j ∈ Sᶜ,q j)-(∑ j ∈ Sᶜ,p j) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro j hj
      have hj' : p j < q j := by
        have hn := mem_compl.mp hj
        simp only [S,mem_filter,mem_univ,true_and,not_le] at hn
        exact hn
      rw [abs_of_nonpos (sub_nonpos.mpr hj'.le)]
      ring
    rw [h1,h2]
    linarith
  rw [he]
  convert scalar_variation a b r hb hba ha hr ho using 1
  ring

lemma expectation_difference_range {m : ℕ} (p q h : Fin m → ℝ)
    (hp1 : ∑ j,p j=1) (hq1 : ∑ j,q j=1) (lo hi : ℝ)
    (hh : ∀ j, lo ≤ h j ∧ h j ≤ hi) :
    |∑ j,(p j-q j)*h j| ≤ ((∑ j,|p j-q j|)/2)*(hi-lo) := by
  have he : (∑ j,(p j-q j)*h j)=(∑ j,(p j-q j)*(h j-(hi+lo)/2)) := by
    simp only [mul_sub,sum_sub_distrib,← sum_mul]
    rw [hp1,hq1]
    simp
  rw [he]
  calc |∑ j,(p j-q j)*(h j-(hi+lo)/2)| ≤ ∑ j,|(p j-q j)*(h j-(hi+lo)/2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j,|p j-q j| *((hi-lo)/2) := by
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_le]
      constructor <;> linarith [(hh j).1,(hh j).2]
    _ = _ := by rw [← sum_mul];ring
end SinkhornProof
end

section
open CompOT.Sinkhorn Matrix
namespace SinkhornProof
lemma eta_cross {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) (k l : Fin m) :
    K i k*K j l/(K j k*K i l) ≤ eta K := by
  unfold eta
  exact (le_ciSup (Set.finite_range (fun l => K i k*K j l/(K j k*K i l))).bddAbove l).trans
    ((le_ciSup (Set.finite_range (fun k => ⨆ l,K i k*K j l/(K j k*K i l))).bddAbove k).trans
    ((le_ciSup (Set.finite_range (fun j => ⨆ k,⨆ l,K i k*K j l/(K j k*K i l))).bddAbove j).trans
    (le_ciSup (Set.finite_range (fun i => ⨆ j,⨆ k,⨆ l,K i k*K j l/(K j k*K i l))).bddAbove i)))
lemma eta_ge_one {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j) : 1 ≤ eta K := by
  let i : Fin n := ⟨0,hn⟩
  let j : Fin m := ⟨0,hm⟩
  simpa only [div_self (mul_pos (hK i j) (hK i j)).ne'] using eta_cross K i i j j
lemma eta_transpose {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (K : Matrix (Fin n) (Fin m) ℝ) :
    eta Kᵀ = eta K := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  apply le_antisymm
  · apply ciSup_le; intro k; apply ciSup_le; intro l; apply ciSup_le; intro i; apply ciSup_le; intro j
    simpa only [transpose_apply,mul_comm] using eta_cross K i j k l
  · apply ciSup_le; intro i; apply ciSup_le; intro j; apply ciSup_le; intro k; apply ciSup_le; intro l
    simpa only [transpose_apply,mul_comm] using eta_cross Kᵀ k l i j
lemma lam_transpose {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (K : Matrix (Fin n) (Fin m) ℝ) :
    lam Kᵀ = lam K := by simp only [lam,eta_transpose hn hm]
lemma lam_nonneg {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j) : 0 ≤ lam K := by
  have he := eta_ge_one hn hm hK
  have hs : 1 ≤ Real.sqrt (eta K) := by exact Real.le_sqrt_of_sq_le (by nlinarith)
  unfold lam
  positivity
lemma lam_lt_one {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) : lam K < 1 := by
  unfold lam
  have hs := Real.sqrt_nonneg (eta K)
  apply (div_lt_one (by positivity)).mpr
  linarith
lemma mulVec_pos {n m : ℕ} (hm : 0 < m) {K : Matrix (Fin n) (Fin m) ℝ}
    (hK : ∀ i j,0 < K i j) {v : Fin m → ℝ} (hv : ∀ j,0 < v j) : ∀ i,0 < (K *ᵥ v) i := by
  intro i
  exact Finset.sum_pos (fun j _ => mul_pos (hK i j) (hv j)) ⟨⟨0,hm⟩,Finset.mem_univ _⟩
end SinkhornProof
end

section
open Finset Matrix CompOT.Sinkhorn
namespace SinkhornProof
noncomputable def rowWeight {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) (z : Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ := K i j*z j/(K *ᵥ z) i
lemma rowWeight_pos {n m : ℕ} (hm : 0 < m) {K : Matrix (Fin n) (Fin m) ℝ}
    (hK : ∀ i j,0 < K i j) {z : Fin m → ℝ} (hz : ∀ j,0 < z j) (i j) :
    0 < rowWeight K z i j := div_pos (mul_pos (hK i j) (hz j)) (mulVec_pos hm hK hz i)
lemma rowWeight_sum {n m : ℕ} (hm : 0 < m) {K : Matrix (Fin n) (Fin m) ℝ}
    (hK : ∀ i j,0 < K i j) {z : Fin m → ℝ} (hz : ∀ j,0 < z j) (i) :
    ∑ j,rowWeight K z i j=1 := by
  simp only [rowWeight,← sum_div]
  exact div_self (ne_of_gt (mulVec_pos hm hK hz i))
lemma rowWeight_odds {n m : ℕ} (hm : 0 < m) {K : Matrix (Fin n) (Fin m) ℝ}
    (hK : ∀ i j,0 < K i j) {z : Fin m → ℝ} (hz : ∀ j,0 < z j) (i l : Fin n) (j k : Fin m) :
    rowWeight K z i j*rowWeight K z l k ≤ eta K*rowWeight K z l j*rowWeight K z i k := by
  have hc := (div_le_iff₀ (mul_pos (hK l j) (hK i k))).mp (eta_cross K i l j k)
  have hv := mul_le_mul_of_nonneg_right hc (mul_pos (hz j) (hz k)).le
  have hdi := mulVec_pos hm hK hz i
  have hdl := mulVec_pos hm hK hz l
  calc rowWeight K z i j*rowWeight K z l k
      = (K i j*K l k*(z j*z k))/((K *ᵥ z) i*(K *ᵥ z) l) := by
          simp only [rowWeight,div_eq_mul_inv,_root_.mul_inv_rev]
          ring
    _ ≤ (eta K*(K l j*K i k)*(z j*z k))/((K *ᵥ z) i*(K *ᵥ z) l) := div_le_div_of_nonneg_right hv (mul_pos hdi hdl).le
    _ = eta K*rowWeight K z l j*rowWeight K z i k := by
          simp only [rowWeight,div_eq_mul_inv,_root_.mul_inv_rev]
          ring
end SinkhornProof
end

section
open Finset Matrix CompOT.Sinkhorn
namespace SinkhornProof
noncomputable def logPath {m : ℕ} (y h : Fin m → ℝ) (t : ℝ) (j : Fin m) : ℝ := y j * Real.exp (t*h j)
lemma logPath_pos {m : ℕ} {y : Fin m → ℝ} (hy : ∀ j, 0 < y j) (h) (t j) : 0 < logPath y h t j := mul_pos (hy j) (Real.exp_pos _)
lemma logPath_deriv {m : ℕ} (y h : Fin m → ℝ) (t j) : HasDerivAt (fun t => logPath y h t j) (logPath y h t j*h j) t := by
  simpa only [logPath,one_mul,mul_assoc,id_eq] using (((hasDerivAt_id t).mul_const (h j)).exp.const_mul (y j))
lemma logRow_deriv {n m : ℕ} (hm : 0 < m) {K : Matrix (Fin n) (Fin m) ℝ}
    (hK : ∀ i j, 0 < K i j) {y : Fin m → ℝ} (hy : ∀ j, 0 < y j) (h : Fin m → ℝ) (t : ℝ) (i : Fin n) :
    HasDerivAt (fun t => Real.log ((K *ᵥ logPath y h t) i)) (∑ j,rowWeight K (logPath y h t) i j*h j) t := by
  have hd : HasDerivAt (fun t => (K *ᵥ logPath y h t) i) (∑ j,K i j*(logPath y h t j*h j)) t := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (logPath_deriv y h t j).const_mul (K i j))
  convert hd.log (ne_of_gt (mulVec_pos hm hK (logPath_pos hy h t) i)) using 1
  rw [sum_div]
  apply sum_congr rfl
  intro j _
  unfold rowWeight
  ring
end SinkhornProof
end

section
open CompOT.Sinkhorn
namespace SinkhornProof
lemma var_pair_le {n : ℕ} (f : Fin n → ℝ) (i j : Fin n) : f i-f j ≤ varNorm f := by
  have hi := le_ciSup (Set.finite_range f).bddAbove i
  have hj := ciInf_le (Set.finite_range f).bddBelow j
  unfold varNorm
  linarith
lemma var_le_iff {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (C : ℝ) :
    varNorm f ≤ C ↔ ∀ i j, f i-f j ≤ C := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  constructor
  · intro h i j; exact (var_pair_le f i j).trans h
  · intro h
    obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite (f := f)
    obtain ⟨j,hj⟩ := exists_eq_ciInf_of_finite (f := f)
    simpa only [varNorm,← hi,← hj] using h i j
lemma var_nonneg {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : 0 ≤ varNorm f := by
  simpa only [sub_self] using var_pair_le f ⟨0,hn⟩ ⟨0,hn⟩
lemma log_cross {n : ℕ} {x y : Fin n → ℝ} (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) (i j : Fin n) :
    Real.log (x i*y j/(x j*y i)) = (Real.log (x i)-Real.log (y i))-(Real.log (x j)-Real.log (y j)) := by
  rw [Real.log_div (mul_pos (hx i) (hy j)).ne' (mul_pos (hx j) (hy i)).ne',
    Real.log_mul (hx i).ne' (hy j).ne',Real.log_mul (hx j).ne' (hy i).ne']
  ring
lemma hilbert_eq_var {n : ℕ} (hn : 0 < n) {x y : Fin n → ℝ}
    (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) :
    hilbertMetric x y = varNorm (fun i => Real.log (x i)-Real.log (y i)) := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let f := fun i => Real.log (x i)-Real.log (y i)
  obtain ⟨a,ha⟩ := exists_eq_ciSup_of_finite (f := f)
  obtain ⟨b,hb⟩ := exists_eq_ciInf_of_finite (f := f)
  have hbound (i j : Fin n) : x i*y j/(x j*y i) ≤ x a*y b/(x b*y a) := by
    apply (Real.log_le_log_iff (div_pos (mul_pos (hx i) (hy j)) (mul_pos (hx j) (hy i))) (div_pos (mul_pos (hx a) (hy b)) (mul_pos (hx b) (hy a)))).mp
    rw [log_cross hx hy,log_cross hx hy]
    have hi := le_ciSup (Set.finite_range f).bddAbove i
    have hj := ciInf_le (Set.finite_range f).bddBelow j
    change f i-f j ≤ f a-f b
    rw [← ha] at hi
    rw [← hb] at hj
    linarith
  have he : (⨆ i,⨆ j,x i*y j/(x j*y i))=x a*y b/(x b*y a) := by
    apply le_antisymm
    · exact ciSup_le fun i => ciSup_le fun j => hbound i j
    · exact (le_ciSup (Set.finite_range (fun j => x a*y j/(x j*y a))).bddAbove b).trans
        (le_ciSup (Set.finite_range (fun i => ⨆ j,x i*y j/(x j*y i))).bddAbove a)
  unfold hilbertMetric
  rw [he,log_cross hx hy]
  change f a-f b = varNorm f
  simp only [varNorm,ha,hb]
lemma hilbert_le_iff {n : ℕ} (hn : 0 < n) {x y : Fin n → ℝ}
    (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) (C : ℝ) :
    hilbertMetric x y ≤ C ↔ ∀ i j,(Real.log (x i)-Real.log (y i))-(Real.log (x j)-Real.log (y j))≤C := by
  rw [hilbert_eq_var hn hx hy,var_le_iff hn]
lemma logratio_pair_le {n : ℕ} (hn : 0 < n) {x y : Fin n → ℝ}
    (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) (i j : Fin n) :
    (Real.log (x i)-Real.log (y i))-(Real.log (x j)-Real.log (y j)) ≤ hilbertMetric x y :=
  (hilbert_le_iff hn hx hy _).mp le_rfl i j
lemma metric_nonneg {n : ℕ} (hn : 0 < n) {x y : Fin n → ℝ}
    (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) : 0≤hilbertMetric x y := by
  rw [hilbert_eq_var hn hx hy]
  exact var_nonneg hn _
end SinkhornProof
end

section
open Finset Matrix CompOT.Sinkhorn
namespace SinkhornProof
lemma row_expectation_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (K : Matrix (Fin n) (Fin m) ℝ)
    (hK : ∀ i j, 0 < K i j) (z h : Fin m → ℝ) (hz : ∀ j, 0 < z j) (i l : Fin n) :
    |(∑ j,rowWeight K z i j*h j)-(∑ j,rowWeight K z l j*h j)| ≤ lam K*varNorm h := by
  have : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have he := expectation_difference_range (rowWeight K z i) (rowWeight K z l) h
    (rowWeight_sum hm hK hz i) (rowWeight_sum hm hK hz l) (⨅ j,h j) (⨆ j,h j)
    (fun j => ⟨ciInf_le (Set.finite_range h).bddBelow j,le_ciSup (Set.finite_range h).bddAbove j⟩)
  have hv := probability_variation (rowWeight K z i) (rowWeight K z l)
    (fun j => (rowWeight_pos hm hK hz i j).le) (fun j => (rowWeight_pos hm hK hz l j).le)
    (rowWeight_sum hm hK hz i) (rowWeight_sum hm hK hz l) (eta K) (eta_ge_one hn hm hK)
    (rowWeight_odds hm hK hz i l)
  simp only [sub_mul,sum_sub_distrib] at he
  exact he.trans (mul_le_mul_of_nonneg_right hv (var_nonneg hm h))
lemma birkhoff_contraction {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (K : Matrix (Fin n) (Fin m) ℝ)
    (hK : ∀ i j, 0 < K i j) (x y : Fin m → ℝ) (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j) :
    hilbertMetric (K *ᵥ x) (K *ᵥ y) ≤ lam K*hilbertMetric x y := by
  let h : Fin m → ℝ := fun j => Real.log (x j)-Real.log (y j)
  have h0 : logPath y h 0=y := by ext j;simp [logPath]
  have h1 : logPath y h 1=x := by
    ext j
    simp only [logPath,one_mul,h,Real.exp_sub,Real.exp_log (hx j),Real.exp_log (hy j)]
    field_simp [(hy j).ne']
  apply (hilbert_le_iff hn (mulVec_pos hm hK hx) (mulVec_pos hm hK hy) _).mpr
  intro i l
  have hd (t : ℝ) := (logRow_deriv hm hK hy h t i).sub (logRow_deriv hm hK hy h t l)
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01' (fun t _ => (hd t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using row_expectation_bound hn hm K hK (logPath y h t) h (logPath_pos hy h t) i l)
  simp only [Pi.sub_apply] at hb
  rw [h0,h1] at hb
  change |(Real.log ((K *ᵥ x) i)-Real.log ((K *ᵥ x) l))-(Real.log ((K *ᵥ y) i)-Real.log ((K *ᵥ y) l))| ≤ lam K*varNorm (fun j => Real.log (x j)-Real.log (y j)) at hb
  rw [← hilbert_eq_var hm hx hy] at hb
  have := (le_abs_self _).trans hb
  linarith
end SinkhornProof
end

section
open CompOT.Sinkhorn
namespace SinkhornProof
lemma metric_self {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ} (hx : ∀ i,0 < x i) : hilbertMetric x x=0 := by
  apply le_antisymm
  · apply (hilbert_le_iff hn hx hx _).mpr
    intro i j; simp
  · exact metric_nonneg hn hx hx
lemma metric_symm {n : ℕ} (hn : 0 < n) {x y : Fin n → ℝ}
    (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) : hilbertMetric x y=hilbertMetric y x := by
  apply le_antisymm
  · apply (hilbert_le_iff hn hx hy _).mpr
    intro i j
    have h := logratio_pair_le hn hy hx j i
    linarith
  · apply (hilbert_le_iff hn hy hx _).mpr
    intro i j
    have h := logratio_pair_le hn hx hy j i
    linarith
lemma metric_triangle {n : ℕ} (hn : 0 < n) {x y z : Fin n → ℝ}
    (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) (hz : ∀ i,0 < z i) :
    hilbertMetric x z ≤ hilbertMetric x y+hilbertMetric y z := by
  apply (hilbert_le_iff hn hx hz _).mpr
  intro i j
  have h1 := logratio_pair_le hn hx hy i j
  have h2 := logratio_pair_le hn hy hz i j
  linarith
lemma metric_eq_of_logdiff {n : ℕ} (hn : 0 < n) {x y u v : Fin n → ℝ}
    (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) (hu : ∀ i,0 < u i) (hv : ∀ i,0 < v i)
    (h : ∀ i,Real.log (x i)-Real.log (y i)=Real.log (u i)-Real.log (v i)) :
    hilbertMetric x y=hilbertMetric u v := by
  rw [hilbert_eq_var hn hx hy,hilbert_eq_var hn hu hv]
  congr 1
  funext i
  exact h i
lemma metric_div_left {n : ℕ} (hn : 0 < n) {a x y : Fin n → ℝ}
    (ha : ∀ i,0 < a i) (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) :
    hilbertMetric (a/x) (a/y)=hilbertMetric x y := by
  have hax : ∀ i,0 < (a/x) i := fun i => div_pos (ha i) (hx i)
  have hay : ∀ i,0 < (a/y) i := fun i => div_pos (ha i) (hy i)
  rw [metric_symm hn hx hy]
  apply metric_eq_of_logdiff hn hax hay hy hx
  intro i
  change Real.log (a i / x i)-Real.log (a i / y i)=Real.log (y i)-Real.log (x i)
  rw [Real.log_div (ha i).ne' (hx i).ne',Real.log_div (ha i).ne' (hy i).ne']
  ring
lemma metric_mul_same {n : ℕ} (hn : 0 < n) {a x y : Fin n → ℝ}
    (ha : ∀ i,0 < a i) (hx : ∀ i,0 < x i) (hy : ∀ i,0 < y i) :
    hilbertMetric (x*a) (y*a)=hilbertMetric x y := by
  apply metric_eq_of_logdiff hn (fun i => mul_pos (hx i) (ha i)) (fun i => mul_pos (hy i) (ha i)) hx hy
  intro i
  simp only [Real.log_mul (hx i).ne' (ha i).ne',Real.log_mul (hy i).ne' (ha i).ne']
  ring
end SinkhornProof
end

section
open CompOT.Sinkhorn Matrix
namespace SinkhornProof
lemma run_positive {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j)
    {a : Fin n → ℝ} (ha : ∀ i,0 < a i) {b : Fin m → ℝ} (hb : ∀ j,0 < b j)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hr : IsSinkhornRun K a b u v) :
    (∀ l j,0 < v l j) ∧ (∀ l i,0 < u (l+1) i) := by
  have hv : ∀ l j,0 < v l j := by
    intro l
    induction l with
    | zero => intro j; rw [hr.1]; norm_num
    | succ l ih =>
      have hu : ∀ i,0 < u (l+1) i := by
        intro i
        rw [hr.2.1]
        exact div_pos (ha i) (mulVec_pos hm hK ih i)
      intro j
      rw [hr.2.2]
      exact div_pos (hb j) (mulVec_pos hn (fun j i => hK i j) hu j)
  refine ⟨hv,?_⟩
  intro l i
  rw [hr.2.1]
  exact div_pos (ha i) (mulVec_pos hm hK (hv l) i)
lemma solution_updates {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j)
    {a : Fin n → ℝ} {b : Fin m → ℝ} {us : Fin n → ℝ} {vs : Fin m → ℝ}
    (hu : ∀ i,0 < us i) (hv : ∀ j,0 < vs j) (hs : IsScalingSolution K a b us vs) :
    us=a/(K *ᵥ vs) ∧ vs=b/(Kᵀ *ᵥ us) := by
  constructor
  · funext i
    exact (eq_div_iff (mulVec_pos hm hK hv i).ne').mpr (congrFun hs.1 i)
  · funext j
    exact (eq_div_iff (mulVec_pos hn (fun j i => hK i j) hu j).ne').mpr (congrFun hs.2 j)
lemma coupling_apply {n m : ℕ} (u : Fin n → ℝ) (K : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ)
    (i : Fin n) (j : Fin m) : scaledCoupling u K v i j=u i*K i j*v j := by
  simp only [scaledCoupling,Matrix.mul_diagonal,Matrix.diagonal_mul]
lemma coupling_rows {n m : ℕ} (u : Fin n → ℝ) (K : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ) :
    scaledCoupling u K v *ᵥ 1=u*(K *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec,dotProduct,coupling_apply,Pi.one_apply,mul_one,Pi.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma coupling_cols {n m : ℕ} (u : Fin n → ℝ) (K : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ) :
    (scaledCoupling u K v)ᵀ *ᵥ 1=v*(Kᵀ *ᵥ u) := by
  funext j
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,coupling_apply,Pi.one_apply,mul_one,Pi.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end SinkhornProof
end

section
open Filter Topology
namespace SinkhornProof
lemma halfstep_rates {c : ℝ} (hc : 0 ≤ c) {U V : ℕ → ℝ}
    (hU : ∀ l,U (l+1) ≤ c*V l) (hV : ∀ l,V (l+1) ≤ c*U (l+1)) :
    (∀ l,V l ≤ c^(2*l)*V 0) ∧ (∀ l,U (l+1) ≤ c^(2*l+1)*V 0) := by
  have hv : ∀ l,V l ≤ c^(2*l)*V 0 := by
    intro l
    induction l with
    | zero => simp
    | succ l ih =>
      calc
        V (l+1) ≤ c*(c*V l) := (hV l).trans (mul_le_mul_of_nonneg_left (hU l) hc)
        _ ≤ c*(c*(c^(2*l)*V 0)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ih hc) hc
        _ = c^(2*(l+1))*V 0 := by rw [show 2*(l+1)=2*l+2 by omega,pow_add];ring
  refine ⟨hv,?_⟩
  intro l
  calc
    U (l+1) ≤ c*V l := hU l
    _ ≤ c*(c^(2*l)*V 0) := mul_le_mul_of_nonneg_left (hv l) hc
    _ = c^(2*l+1)*V 0 := by rw [pow_succ];ring
lemma geometric_convergence {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) {U V : ℕ → ℝ}
    (hUn : ∀ l,0 ≤ U (l+1)) (hVn : ∀ l,0 ≤ V l)
    (hU : ∀ l,U (l+1) ≤ c*V l) (hV : ∀ l,V (l+1) ≤ c*U (l+1)) :
    Tendsto U atTop (𝓝 0) ∧ Tendsto V atTop (𝓝 0) := by
  have hr := halfstep_rates hc hU hV
  have hc2 : c^2 < 1 := by nlinarith
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg c) hc2
  have hv : Tendsto (fun l => c^(2*l)*V 0) atTop (𝓝 0) := by
    simpa only [pow_mul,zero_mul] using hp.mul_const (V 0)
  have hu : Tendsto (fun l => c^(2*l+1)*V 0) atTop (𝓝 0) := by
    have ht := hv.mul_const c
    convert ht using 1
    · funext l; rw [pow_succ];ring
    · simp
  exact ⟨(tendsto_add_atTop_iff_nat 1).mp (squeeze_zero hUn hr.2 hu),squeeze_zero hVn hr.1 hv⟩
end SinkhornProof
end

section
open CompOT.Sinkhorn Matrix Filter Topology
namespace SinkhornProof
lemma run_halfsteps {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j)
    {a : Fin n → ℝ} (ha : ∀ i,0 < a i) {b : Fin m → ℝ} (hb : ∀ j,0 < b j)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hr : IsSinkhornRun K a b u v)
    {us : Fin n → ℝ} {vs : Fin m → ℝ} (hus : ∀ i,0 < us i) (hvs : ∀ j,0 < vs j)
    (hs : IsScalingSolution K a b us vs) :
    (∀ l,hilbertMetric (u (l+1)) us ≤ lam K*hilbertMetric (v l) vs) ∧
    (∀ l,hilbertMetric (v (l+1)) vs ≤ lam K*hilbertMetric (u (l+1)) us) := by
  have hp := run_positive hn hm hK ha hb hr
  have hsol := solution_updates hn hm hK hus hvs hs
  constructor
  · intro l
    calc
      hilbertMetric (u (l+1)) us = hilbertMetric (a/(K *ᵥ v l)) (a/(K *ᵥ vs)) := by rw [hr.2.1,hsol.1]
      _ = hilbertMetric (K *ᵥ v l) (K *ᵥ vs) := metric_div_left hn ha (mulVec_pos hm hK (hp.1 l)) (mulVec_pos hm hK hvs)
      _ ≤ lam K*hilbertMetric (v l) vs := birkhoff_contraction hn hm K hK (v l) vs (hp.1 l) hvs
  · intro l
    calc
      hilbertMetric (v (l+1)) vs = hilbertMetric (b/(Kᵀ *ᵥ u (l+1))) (b/(Kᵀ *ᵥ us)) := by rw [hr.2.2,hsol.2]
      _ = hilbertMetric (Kᵀ *ᵥ u (l+1)) (Kᵀ *ᵥ us) := metric_div_left hm hb (mulVec_pos hn (fun j i => hK i j) (hp.2 l)) (mulVec_pos hn (fun j i => hK i j) hus)
      _ ≤ lam Kᵀ*hilbertMetric (u (l+1)) us := birkhoff_contraction hm hn Kᵀ (fun j i => hK i j) (u (l+1)) us (hp.2 l) hus
      _ = lam K*hilbertMetric (u (l+1)) us := by rw [lam_transpose hn hm]
end SinkhornProof
end

section
open CompOT.Sinkhorn Matrix
namespace SinkhornProof
lemma update_marginals {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j)
    {a : Fin n → ℝ} (ha : ∀ i,0 < a i) {b : Fin m → ℝ} (hb : ∀ j,0 < b j)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hr : IsSinkhornRun K a b u v) :
    (∀ l,u (l+1)*(K *ᵥ v l)=a) ∧ (∀ l,v (l+1)*(Kᵀ *ᵥ u (l+1))=b) := by
  have hp := run_positive hn hm hK ha hb hr
  constructor
  · intro l
    rw [hr.2.1]
    funext i
    exact div_mul_cancel₀ (a i) (mulVec_pos hm hK (hp.1 l) i).ne'
  · intro l
    rw [hr.2.2]
    funext j
    exact div_mul_cancel₀ (b j) (mulVec_pos hn (fun j i => hK i j) (hp.2 l) j).ne'
lemma run_column_sums {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j)
    {a : Fin n → ℝ} (ha : ∀ i,0 < a i) {b : Fin m → ℝ} (hb : ∀ j,0 < b j)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hr : IsSinkhornRun K a b u v)
    {l : ℕ} (hl : 1 ≤ l) : (scaledCoupling (u l) K (v l))ᵀ *ᵥ 1=b := by
  rw [coupling_cols]
  have he : l-1+1=l := Nat.sub_add_cancel hl
  simpa only [he] using (update_marginals hn hm hK ha hb hr).2 (l-1)
lemma run_u_positive {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j)
    {a : Fin n → ℝ} (ha : ∀ i,0 < a i) {b : Fin m → ℝ} (hb : ∀ j,0 < b j)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hr : IsSinkhornRun K a b u v)
    {l : ℕ} (hl : 1 ≤ l) : ∀ i,0 < u l i := by
  have he : l-1+1=l := Nat.sub_add_cancel hl
  simpa only [he] using (run_positive hn hm hK ha hb hr).2 (l-1)
end SinkhornProof
end

section
open CompOT.Sinkhorn Matrix
namespace SinkhornProof
lemma run_residual_bounds {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j)
    {a : Fin n → ℝ} (ha : ∀ i,0 < a i) {b : Fin m → ℝ} (hb : ∀ j,0 < b j)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hr : IsSinkhornRun K a b u v)
    {us : Fin n → ℝ} {vs : Fin m → ℝ} (hus : ∀ i,0 < us i) (hvs : ∀ j,0 < vs j)
    (hs : IsScalingSolution K a b us vs) :
    (∀ l,1 ≤ l → hilbertMetric (u l) us ≤ hilbertMetric (scaledCoupling (u l) K (v l) *ᵥ 1) a/(1-lam K^2)) ∧
    (∀ l,hilbertMetric (v l) vs ≤ hilbertMetric ((scaledCoupling (u (l+1)) K (v l))ᵀ *ᵥ 1) b/(1-lam K^2)) := by
  have hp := run_positive hn hm hK ha hb hr
  have hbnd := run_halfsteps hn hm hK ha hb hr hus hvs hs
  have hc := lam_nonneg hn hm hK
  have hc1 := lam_lt_one K
  have hd : 0 < 1-lam K^2 := by nlinarith
  have hmarg := update_marginals hn hm hK ha hb hr
  constructor
  · intro l hl
    have hu := run_u_positive hn hm hK ha hb hr hl
    have he : l-1+1=l := Nat.sub_add_cancel hl
    have hvbound : hilbertMetric (v l) vs ≤ lam K*hilbertMetric (u l) us := by
      simpa only [he] using hbnd.2 (l-1)
    have hcont := (hbnd.1 l).trans (mul_le_mul_of_nonneg_left hvbound hc)
    have ht := metric_triangle hn hu (hp.2 l) hus
    have hstep : hilbertMetric (u l) (u (l+1))=hilbertMetric (scaledCoupling (u l) K (v l) *ᵥ 1) a := by
      calc
        _ = hilbertMetric (u l*(K *ᵥ v l)) (u (l+1)*(K *ᵥ v l)) :=
          (metric_mul_same hn (mulVec_pos hm hK (hp.1 l)) hu (hp.2 l)).symm
        _ = _ := by rw [hmarg.1,coupling_rows]
    rw [hstep] at ht
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · intro l
    have hcont := (hbnd.2 l).trans (mul_le_mul_of_nonneg_left (hbnd.1 l) hc)
    have ht := metric_triangle hm (hp.1 l) (hp.1 (l+1)) hvs
    have hstep : hilbertMetric (v l) (v (l+1))=hilbertMetric ((scaledCoupling (u (l+1)) K (v l))ᵀ *ᵥ 1) b := by
      calc
        _ = hilbertMetric (v l*(Kᵀ *ᵥ u (l+1))) (v (l+1)*(Kᵀ *ᵥ u (l+1))) :=
          (metric_mul_same hm (mulVec_pos hn (fun j i => hK i j) (hp.2 l)) (hp.1 l) (hp.1 (l+1))).symm
        _ = _ := by rw [hmarg.2,coupling_cols]
    rw [hstep] at ht
    apply (le_div_iff₀ hd).mpr
    nlinarith
end SinkhornProof
end

section
open CompOT.Sinkhorn Matrix
namespace SinkhornProof
lemma log_entry_difference {n m : ℕ} {K : Matrix (Fin n) (Fin m) ℝ}
    (hK : ∀ i j,0 < K i j) {u us : Fin n → ℝ} {v vs : Fin m → ℝ}
    (hu : ∀ i,0 < u i) (hus : ∀ i,0 < us i) (hv : ∀ j,0 < v j) (hvs : ∀ j,0 < vs j)
    (i : Fin n) (j : Fin m) :
    Real.log (u i*K i j*v j)-Real.log (us i*K i j*vs j)=
      (Real.log (u i)-Real.log (us i))+(Real.log (v j)-Real.log (vs j)) := by
  rw [Real.log_mul (mul_pos (hu i) (hK i j)).ne' (hv j).ne',
    Real.log_mul (hu i).ne' (hK i j).ne',
    Real.log_mul (mul_pos (hus i) (hK i j)).ne' (hvs j).ne',
    Real.log_mul (hus i).ne' (hK i j).ne']
  ring
lemma coupling_log_bound {n m : ℕ} (hn : 0 < n)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j)
    {u us : Fin n → ℝ} {v vs : Fin m → ℝ}
    (hu : ∀ i,0 < u i) (hus : ∀ i,0 < us i) (hv : ∀ j,0 < v j) (hvs : ∀ j,0 < vs j)
    (hcols : ∀ j,(∑ i,u i*K i j*v j)=∑ i,us i*K i j*vs j) (i : Fin n) (j : Fin m) :
    |Real.log (scaledCoupling u K v i j)-Real.log (scaledCoupling us K vs i j)| ≤ hilbertMetric u us := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  obtain ⟨a,_,ha⟩ := Finset.exists_le_of_sum_le hne (hcols j).le
  obtain ⟨b,_,hb⟩ := Finset.exists_le_of_sum_le hne (hcols j).ge
  have hla : Real.log (u a*K a j*v j)-Real.log (us a*K a j*vs j) ≤ 0 := by
    have h := Real.log_le_log (mul_pos (mul_pos (hu a) (hK a j)) (hv j)) ha
    linarith
  have hlb : 0 ≤ Real.log (u b*K b j*v j)-Real.log (us b*K b j*vs j) := by
    have h := Real.log_le_log (mul_pos (mul_pos (hus b) (hK b j)) (hvs j)) hb
    linarith
  rw [log_entry_difference hK hu hus hv hvs] at hla hlb
  simp only [coupling_apply,log_entry_difference hK hu hus hv hvs]
  have hia := logratio_pair_le hn hu hus i a
  have hbi := logratio_pair_le hn hu hus b i
  exact abs_le.mpr ⟨by linarith,by linarith⟩
end SinkhornProof
end

section
open CompOT.Sinkhorn Matrix
namespace SinkhornProof
lemma run_coupling_log_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {K : Matrix (Fin n) (Fin m) ℝ} (hK : ∀ i j,0 < K i j)
    {a : Fin n → ℝ} (ha : ∀ i,0 < a i) {b : Fin m → ℝ} (hb : ∀ j,0 < b j)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hr : IsSinkhornRun K a b u v)
    {us : Fin n → ℝ} {vs : Fin m → ℝ} (hus : ∀ i,0 < us i) (hvs : ∀ j,0 < vs j)
    (hs : IsScalingSolution K a b us vs) {l : ℕ} (hl : 1 ≤ l) :
    (⨆ i,⨆ j,|Real.log (scaledCoupling (u l) K (v l) i j)-Real.log (scaledCoupling us K vs i j)|) ≤
      hilbertMetric (u l) us+hilbertMetric (v l) vs := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hp := run_positive hn hm hK ha hb hr
  have hu := run_u_positive hn hm hK ha hb hr hl
  have he (j : Fin m) : (∑ i,u l i*K i j*v l j)=∑ i,us i*K i j*vs j := by
    have hcm := run_column_sums hn hm hK ha hb hr hl
    rw [coupling_cols] at hcm
    have hc := congrFun hcm j
    have hsc := congrFun hs.2 j
    simp only [Pi.mul_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply] at hc hsc
    calc
      _ = v l j*(∑ i,K i j*u l i) := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring
      _ = b j := hc
      _ = vs j*(∑ i,K i j*us i) := hsc.symm
      _ = _ := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  exact (coupling_log_bound hn hK hu hus (hp.1 l) hvs he i j).trans
    (le_add_of_nonneg_right (metric_nonneg hm (hp.1 l) hvs))
end SinkhornProof
end

section
namespace CompOT.Sinkhorn

open Matrix Filter Topology

/-- Theorem 4.2 (Franklin–Lorenz), Remark 4.14, p. 441, with the explicit constants of
the book's proof in place of the `O(·)` of (4.22), and the second inequality of (4.23)
stated with the half-step coupling `diag(u^{(ℓ+1)}) K diag(v^{(ℓ)})` (as printed, with
`P^{(ℓ)}`, its right side is `0` for `ℓ ≥ 1`). Here `P⋆ = diag(u⋆) K diag(v⋆)`.
Iterates `u^{(ℓ)}` exist only for `ℓ ≥ 1`. -/
theorem proved_root {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (b : Fin m → ℝ) (hb : ∀ j, 0 < b j)
    (u : ℕ → Fin n → ℝ) (v : ℕ → Fin m → ℝ) (hrun : IsSinkhornRun K a b u v)
    (us : Fin n → ℝ) (vs : Fin m → ℝ) (hus : ∀ i, 0 < us i) (hvs : ∀ j, 0 < vs j)
    (hsol : IsScalingSolution K a b us vs) :
    -- (4.22), explicit: d_H(v^{(ℓ)}, v⋆) ≤ λ^{2ℓ} d_H(v^{(0)}, v⋆)
    (∀ ℓ : ℕ, hilbertMetric (v ℓ) vs ≤ lam K ^ (2 * ℓ) * hilbertMetric (v 0) vs) ∧
    -- (4.22), explicit: d_H(u^{(ℓ+1)}, u⋆) ≤ λ^{2ℓ+1} d_H(v^{(0)}, v⋆)
    (∀ ℓ : ℕ, hilbertMetric (u (ℓ + 1)) us ≤
      lam K ^ (2 * ℓ + 1) * hilbertMetric (v 0) vs) ∧
    -- projective convergence (u^{(ℓ)}, v^{(ℓ)}) → (u⋆, v⋆) in d_H
    Tendsto (fun ℓ => hilbertMetric (u ℓ) us) atTop (𝓝 0) ∧
    Tendsto (fun ℓ => hilbertMetric (v ℓ) vs) atTop (𝓝 0) ∧
    -- (4.23), first part as printed, for ℓ ≥ 1
    (∀ ℓ : ℕ, 1 ≤ ℓ → hilbertMetric (u ℓ) us ≤
      hilbertMetric (scaledCoupling (u ℓ) K (v ℓ) *ᵥ 1) a / (1 - lam K ^ 2)) ∧
    -- (4.23), second part, with the half-step coupling diag(u^{(ℓ+1)}) K diag(v^{(ℓ)})
    (∀ ℓ : ℕ, hilbertMetric (v ℓ) vs ≤
      hilbertMetric ((scaledCoupling (u (ℓ + 1)) K (v ℓ))ᵀ *ᵥ 1) b / (1 - lam K ^ 2)) ∧
    -- (4.24), for ℓ ≥ 1, with P⋆ = diag(u⋆) K diag(v⋆)
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      (⨆ i, ⨆ j, |Real.log (scaledCoupling (u ℓ) K (v ℓ) i j) -
          Real.log (scaledCoupling us K vs i j)|) ≤
        hilbertMetric (u ℓ) us + hilbertMetric (v ℓ) vs) := by
  have hp := SinkhornProof.run_positive hn hm hK ha hb hrun
  have hhalf := SinkhornProof.run_halfsteps hn hm hK ha hb hrun hus hvs hsol
  have hc := SinkhornProof.lam_nonneg hn hm hK
  have hrates := SinkhornProof.halfstep_rates (U := fun l => hilbertMetric (u l) us) (V := fun l => hilbertMetric (v l) vs) hc hhalf.1 hhalf.2
  have hlim := SinkhornProof.geometric_convergence (U := fun l => hilbertMetric (u l) us) (V := fun l => hilbertMetric (v l) vs) hc (SinkhornProof.lam_lt_one K)
    (fun l => SinkhornProof.metric_nonneg hn (hp.2 l) hus)
    (fun l => SinkhornProof.metric_nonneg hm (hp.1 l) hvs) hhalf.1 hhalf.2
  have hres := SinkhornProof.run_residual_bounds hn hm hK ha hb hrun hus hvs hsol
  exact ⟨hrates.1,hrates.2,hlim.1,hlim.2,hres.1,hres.2,
    fun l hl => SinkhornProof.run_coupling_log_bound hn hm hK ha hb hrun hus hvs hsol hl⟩

end CompOT.Sinkhorn
end

open Matrix Filter Topology CompOT.Sinkhorn

theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (b : Fin m → ℝ) (hb : ∀ j, 0 < b j)
    (u : ℕ → Fin n → ℝ) (v : ℕ → Fin m → ℝ) (hrun : IsSinkhornRun K a b u v)
    (us : Fin n → ℝ) (vs : Fin m → ℝ) (hus : ∀ i, 0 < us i) (hvs : ∀ j, 0 < vs j)
    (hsol : IsScalingSolution K a b us vs) :
    -- (4.22), explicit: d_H(v^{(ℓ)}, v⋆) ≤ λ^{2ℓ} d_H(v^{(0)}, v⋆)
    (∀ ℓ : ℕ, hilbertMetric (v ℓ) vs ≤ lam K ^ (2 * ℓ) * hilbertMetric (v 0) vs) ∧
    -- (4.22), explicit: d_H(u^{(ℓ+1)}, u⋆) ≤ λ^{2ℓ+1} d_H(v^{(0)}, v⋆)
    (∀ ℓ : ℕ, hilbertMetric (u (ℓ + 1)) us ≤
      lam K ^ (2 * ℓ + 1) * hilbertMetric (v 0) vs) ∧
    -- projective convergence (u^{(ℓ)}, v^{(ℓ)}) → (u⋆, v⋆) in d_H
    Tendsto (fun ℓ => hilbertMetric (u ℓ) us) atTop (𝓝 0) ∧
    Tendsto (fun ℓ => hilbertMetric (v ℓ) vs) atTop (𝓝 0) ∧
    -- (4.23), first part as printed, for ℓ ≥ 1
    (∀ ℓ : ℕ, 1 ≤ ℓ → hilbertMetric (u ℓ) us ≤
      hilbertMetric (scaledCoupling (u ℓ) K (v ℓ) *ᵥ 1) a / (1 - lam K ^ 2)) ∧
    -- (4.23), second part, with the half-step coupling diag(u^{(ℓ+1)}) K diag(v^{(ℓ)})
    (∀ ℓ : ℕ, hilbertMetric (v ℓ) vs ≤
      hilbertMetric ((scaledCoupling (u (ℓ + 1)) K (v ℓ))ᵀ *ᵥ 1) b / (1 - lam K ^ 2)) ∧
    -- (4.24), for ℓ ≥ 1, with P⋆ = diag(u⋆) K diag(v⋆)
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      (⨆ i, ⨆ j, |Real.log (scaledCoupling (u ℓ) K (v ℓ) i j) -
          Real.log (scaledCoupling us K vs i j)|) ≤
        hilbertMetric (u ℓ) us + hilbertMetric (v ℓ) vs) := by
  exact CompOT.Sinkhorn.proved_root hn hm K hK a ha b hb u v hrun us vs hus hvs hsol

theorem CompOT.Sinkhorn.theorem_4_2 {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (b : Fin m → ℝ) (hb : ∀ j, 0 < b j)
    (u : ℕ → Fin n → ℝ) (v : ℕ → Fin m → ℝ) (hrun : IsSinkhornRun K a b u v)
    (us : Fin n → ℝ) (vs : Fin m → ℝ) (hus : ∀ i, 0 < us i) (hvs : ∀ j, 0 < vs j)
    (hsol : IsScalingSolution K a b us vs) :
    -- (4.22), explicit: d_H(v^{(ℓ)}, v⋆) ≤ λ^{2ℓ} d_H(v^{(0)}, v⋆)
    (∀ ℓ : ℕ, hilbertMetric (v ℓ) vs ≤ lam K ^ (2 * ℓ) * hilbertMetric (v 0) vs) ∧
    -- (4.22), explicit: d_H(u^{(ℓ+1)}, u⋆) ≤ λ^{2ℓ+1} d_H(v^{(0)}, v⋆)
    (∀ ℓ : ℕ, hilbertMetric (u (ℓ + 1)) us ≤
      lam K ^ (2 * ℓ + 1) * hilbertMetric (v 0) vs) ∧
    -- projective convergence (u^{(ℓ)}, v^{(ℓ)}) → (u⋆, v⋆) in d_H
    Tendsto (fun ℓ => hilbertMetric (u ℓ) us) atTop (𝓝 0) ∧
    Tendsto (fun ℓ => hilbertMetric (v ℓ) vs) atTop (𝓝 0) ∧
    -- (4.23), first part as printed, for ℓ ≥ 1
    (∀ ℓ : ℕ, 1 ≤ ℓ → hilbertMetric (u ℓ) us ≤
      hilbertMetric (scaledCoupling (u ℓ) K (v ℓ) *ᵥ 1) a / (1 - lam K ^ 2)) ∧
    -- (4.23), second part, with the half-step coupling diag(u^{(ℓ+1)}) K diag(v^{(ℓ)})
    (∀ ℓ : ℕ, hilbertMetric (v ℓ) vs ≤
      hilbertMetric ((scaledCoupling (u (ℓ + 1)) K (v ℓ))ᵀ *ᵥ 1) b / (1 - lam K ^ 2)) ∧
    -- (4.24), for ℓ ≥ 1, with P⋆ = diag(u⋆) K diag(v⋆)
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      (⨆ i, ⨆ j, |Real.log (scaledCoupling (u ℓ) K (v ℓ) i j) -
          Real.log (scaledCoupling us K vs i j)|) ≤
        hilbertMetric (u ℓ) us + hilbertMetric (v ℓ) vs) := by
  exact _root_.solution hn hm K hK a ha b hb u v hrun us vs hus hvs hsol
