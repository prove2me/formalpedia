-- Prove2me | solution 1 for FiniteFields.Dwork.borelDwork_rationalityCriterion
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:32:24.163911+00:00
-- url     : https://prove2.me/submissions/aaf1540e-74df-430c-8230-fa8860a03156

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Meromorphy
section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
variable {K : Type*} [Field K]
@[simp]
theorem hankelMinor_zero (F : K⟦X⟧) (n : ℕ) : hankelMinor F 0 n = 1 :=
  Matrix.det_isEmpty
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
variable {K : Type*} [Field K]
private theorem coe_trunc_of_tail_zero {G : K⟦X⟧} {M : ℕ} (h : ∀ m, M ≤ m → coeff m G = 0) :
    ((PowerSeries.trunc M G : K[X]) : K⟦X⟧) = G := by
  ext m
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hm : m < M
  · simp [hm]
  · simp only [hm, if_false]
    exact (h m (Nat.le_of_not_lt hm)).symm
private theorem coeff_coe_mul (Q : K[X]) (F : K⟦X⟧) (m : ℕ) :
    coeff m ((Q : K⟦X⟧) * F) =
      ∑ x ∈ antidiagonal m, Q.coeff x.1 * coeff x.2 F := by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_congr rfl fun x _ => by rw [Polynomial.coeff_coe]
private theorem recurrenceDenominator_eval_zero (r : ℕ) (c : ℕ → K) :
    (recurrenceDenominator r c).eval 0 = 1 := by
  simp only [recurrenceDenominator, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  have : ∀ i ∈ range r, c i * (0 : K) ^ (r - i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [zero_pow (by omega : r - i ≠ 0), mul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_const_zero, sub_zero]
private theorem recurrenceDenominator_ne_zero (r : ℕ) (c : ℕ → K) :
    recurrenceDenominator r c ≠ 0 := by
  intro h
  have := recurrenceDenominator_eval_zero r c
  rw [h, Polynomial.eval_zero] at this
  exact zero_ne_one this
private theorem coeff_recurrenceDenominator_mul (r : ℕ) (c : ℕ → K) (F : K⟦X⟧) (n : ℕ) :
    coeff (n + r) ((recurrenceDenominator r c : K⟦X⟧) * F) =
      coeff (n + r) F - ∑ i ∈ range r, c i * coeff (n + i) F := by
  have hcoe : ((recurrenceDenominator r c : K[X]) : K⟦X⟧)
      = 1 - ∑ i ∈ range r, PowerSeries.C (c i) * PowerSeries.X ^ (r - i) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, recurrenceDenominator, map_sub, map_one,
      map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]
  rw [hcoe, sub_mul, one_mul, map_sub, Finset.sum_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [mul_assoc, PowerSeries.coeff_C_mul,
    show n + r = (n + i) + (r - i) from by omega, PowerSeries.coeff_X_pow_mul]
theorem CoefficientRecurrence.isRationalPowerSeries {F : K⟦X⟧}
    (h : CoefficientRecurrence F) : IsRationalPowerSeries F := by
  obtain ⟨r, N, c, hrec⟩ := h
  have htail : ∀ m, N + r ≤ m →
      coeff m ((recurrenceDenominator r c : K⟦X⟧) * F) = 0 := by
    intro m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + r := ⟨m - r, by omega⟩
    rw [coeff_recurrenceDenominator_mul, hrec n (by omega), sub_self]
  refine ⟨PowerSeries.trunc (N + r) ((recurrenceDenominator r c : K⟦X⟧) * F),
    recurrenceDenominator r c, recurrenceDenominator_ne_zero r c, ?_, ?_⟩
  · rw [recurrenceDenominator_eval_zero]
    exact one_ne_zero
  · exact (coe_trunc_of_tail_zero htail).symm
theorem IsRationalPowerSeries.coefficientRecurrence {F : K⟦X⟧}
    (h : IsRationalPowerSeries F) : CoefficientRecurrence F := by
  obtain ⟨P, Q, _, hQ, hPQ⟩ := h
  have hq0 : Q.coeff 0 ≠ 0 := by
    rwa [Polynomial.coeff_zero_eq_eval_zero]
  refine ⟨Q.natDegree, P.natDegree + 1, fun i => -(Q.coeff (Q.natDegree - i)) / Q.coeff 0, ?_⟩
  intro n hn
  have hzero : coeff (n + Q.natDegree) ((Q : K⟦X⟧) * F) = 0 := by
    rw [hPQ, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have htrunc : ∑ k ∈ range (n + Q.natDegree + 1), Q.coeff k * coeff (n + Q.natDegree - k) F
      = ∑ k ∈ range (Q.natDegree + 1), Q.coeff k * coeff (n + Q.natDegree - k) F := by
    refine (Finset.sum_subset (s₁ := range (Q.natDegree + 1))
      (s₂ := range (n + Q.natDegree + 1))
      (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega) ?_).symm
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  have hexp : coeff (n + Q.natDegree) ((Q : K⟦X⟧) * F)
      = ∑ i ∈ range (Q.natDegree + 1),
          Q.coeff (Q.natDegree - i) * coeff (n + i) F := by
    rw [coeff_coe_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => Q.coeff a * coeff b F), Nat.succ_eq_add_one, htrunc,
      ← Finset.sum_range_reflect (fun k => Q.coeff k * coeff (n + Q.natDegree - k) F)
        (Q.natDegree + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    rw [show Q.natDegree + 1 - 1 - i = Q.natDegree - i from by omega,
      show n + Q.natDegree - (Q.natDegree - i) = n + i from by omega]
  rw [hexp, Finset.sum_range_succ, Nat.sub_self] at hzero
  have hsum : ∑ i ∈ range Q.natDegree,
        -(Q.coeff (Q.natDegree - i)) / Q.coeff 0 * coeff (n + i) F
      = -(∑ i ∈ range Q.natDegree, Q.coeff (Q.natDegree - i) * coeff (n + i) F) / Q.coeff 0 := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, eq_div_iff hq0]
  linear_combination hzero
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
variable {K : Type*} [Field K]
private theorem hankelMinor_eq_det (F : K⟦X⟧) (m n : ℕ) :
    hankelMinor F m n = (hankelMatrix F m n).det := rfl
private theorem exists_localCoeffs {F : K⟦X⟧} {r N : ℕ} (h : HankelRank F r N)
    {n : ℕ} (hn : N ≤ n) :
    ∃ c : Fin r → K, ∀ i : Fin (r + 1),
      coeff (n + (i : ℕ) + r) F = ∑ j : Fin r, c j * coeff (n + (i : ℕ) + (j : ℕ)) F := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    ((hankelMinor_eq_det F (r + 1) n) ▸ h.2 n hn)
  have hrow : ∀ i : Fin (r + 1),
      ∑ j : Fin (r + 1), coeff (n + (i : ℕ) + (j : ℕ)) F * v j = 0 := by
    intro i
    have hi := congrFun hv i
    simpa [Matrix.mulVec, dotProduct, hankelMatrix] using hi
  have hlast : v (Fin.last r) ≠ 0 := by
    intro hz
    have hw : Matrix.mulVec (hankelMatrix F r n) (fun j : Fin r => v j.castSucc) = 0 := by
      funext i
      have hi := hrow i.castSucc
      rw [Fin.sum_univ_castSucc, hz, mul_zero, add_zero] at hi
      simpa [Matrix.mulVec, dotProduct, hankelMatrix] using hi
    have hzero := Matrix.eq_zero_of_mulVec_eq_zero
      ((hankelMinor_eq_det F r n) ▸ h.1 n hn) hw
    refine hv0 (funext fun j => Fin.lastCases ?_ ?_ j)
    · exact hz
    · intro i
      exact congrFun hzero i
  refine ⟨fun j => -(v j.castSucc) / v (Fin.last r), fun i => ?_⟩
  have hi := hrow i
  rw [Fin.sum_univ_castSucc, Fin.val_last] at hi
  simp only [Fin.val_castSucc] at hi
  have hsum : ∑ j : Fin r, -(v j.castSucc) / v (Fin.last r) * coeff (n + (i : ℕ) + (j : ℕ)) F
      = -(∑ j : Fin r, coeff (n + (i : ℕ) + (j : ℕ)) F * v j.castSucc) / v (Fin.last r) := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, eq_div_iff hlast]
  linear_combination hi
private theorem localCoeffs_eq {F : K⟦X⟧} {r N : ℕ} (h : HankelRank F r N)
    {n : ℕ} (hn : N ≤ n) {c c' : Fin r → K}
    (hc : ∀ i : Fin (r + 1),
      coeff (n + (i : ℕ) + r) F = ∑ j : Fin r, c j * coeff (n + (i : ℕ) + (j : ℕ)) F)
    (hc' : ∀ i : Fin (r + 1),
      coeff (n + 1 + (i : ℕ) + r) F
        = ∑ j : Fin r, c' j * coeff (n + 1 + (i : ℕ) + (j : ℕ)) F) :
    c = c' := by
  have hker : Matrix.mulVec (hankelMatrix F r (n + 1)) (c - c') = 0 := by
    funext i
    have h1 := hc i.succ
    have h2 := hc' i.castSucc
    rw [Fin.val_succ] at h1
    rw [Fin.val_castSucc] at h2
    have hshift : n + ((i : ℕ) + 1) = n + 1 + (i : ℕ) := by omega
    rw [hshift] at h1
    have hsub : ∑ j : Fin r, (c j - c' j) * coeff (n + 1 + (i : ℕ) + (j : ℕ)) F = 0 := by
      rw [Finset.sum_congr rfl fun j _ => sub_mul (c j) (c' j) _, Finset.sum_sub_distrib,
        ← h1, ← h2, sub_self]
    simpa [Matrix.mulVec, dotProduct, hankelMatrix, Pi.sub_apply, mul_comm] using hsub
  have := Matrix.eq_zero_of_mulVec_eq_zero
    ((hankelMinor_eq_det F r (n + 1)) ▸ h.1 (n + 1) (by omega)) hker
  funext j
  have := congrFun this j
  simpa [sub_eq_zero] using this
theorem HankelEventuallyZero.coefficientRecurrence {F : K⟦X⟧}
    (h : HankelEventuallyZero F) : CoefficientRecurrence F := by
  obtain ⟨r, N, hF⟩ := h
  obtain ⟨c, hc⟩ := exists_localCoeffs hF (le_refl N)
  have key : ∀ n, N ≤ n → ∀ i : Fin (r + 1),
      coeff (n + (i : ℕ) + r) F = ∑ j : Fin r, c j * coeff (n + (i : ℕ) + (j : ℕ)) F := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hc
    | succ m hm ih =>
        obtain ⟨c', hc'⟩ := exists_localCoeffs hF (le_trans hm (Nat.le_succ m))
        have hcc : c = c' := localCoeffs_eq hF hm ih hc'
        rw [hcc]
        exact hc'
  refine ⟨r, N, fun j => if hj : j < r then c ⟨j, hj⟩ else 0, ?_⟩
  intro n hn
  have h0 := key n hn 0
  rw [Fin.val_zero, Nat.add_zero] at h0
  rw [h0, ← Fin.sum_univ_eq_sum_range
    (fun j => (if hj : j < r then c ⟨j, hj⟩ else 0) * coeff (n + j) F) r]
  exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]
private theorem hankelMinor_succ_eq_zero {F : K⟦X⟧} {r N : ℕ} {c : ℕ → K}
    (hrec : ∀ m, N ≤ m → coeff (m + r) F = ∑ i ∈ range r, c i * coeff (m + i) F)
    {n : ℕ} (hn : N ≤ n) : hankelMinor F (r + 1) n = 0 := by
  rw [hankelMinor_eq_det]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun j => Fin.lastCases 1 (fun l => -c l) j, ?_, ?_⟩
  · intro hzero
    have := congrFun hzero (Fin.last r)
    rw [Fin.lastCases_last] at this
    exact one_ne_zero this
  · funext i
    have hi := hrec (n + (i : ℕ)) (by omega)
    have hexpand : ∑ j : Fin (r + 1), coeff (n + (i : ℕ) + (j : ℕ)) F
          * Fin.lastCases (motive := fun _ => K) 1 (fun l => -c l) j
        = coeff (n + (i : ℕ) + r) F
          - ∑ l : Fin r, c l * coeff (n + (i : ℕ) + (l : ℕ)) F := by
      rw [Fin.sum_univ_castSucc, Fin.lastCases_last, Fin.val_last, mul_one]
      simp only [Fin.lastCases_castSucc, Fin.val_castSucc]
      have hneg : ∑ x : Fin r, coeff (n + (i : ℕ) + (x : ℕ)) F * -c (x : ℕ)
          = -∑ l : Fin r, c (l : ℕ) * coeff (n + (i : ℕ) + (l : ℕ)) F := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [hneg]
      ring
    rw [← Fin.sum_univ_eq_sum_range
      (fun l => c l * coeff (n + (i : ℕ) + l) F) r] at hi
    simp only [Matrix.mulVec, dotProduct, hankelMatrix, Matrix.of_apply, Pi.zero_apply]
    rw [hexpand, hi, sub_self]
private theorem combination_vanishes {F : K⟦X⟧} {r N n : ℕ} {c w : ℕ → K}
    (hrec : ∀ m, N ≤ m → coeff (m + r) F = ∑ i ∈ range r, c i * coeff (m + i) F)
    (hn : N ≤ n)
    (hinit : ∀ i < r, ∑ j ∈ range r, w j * coeff (n + i + j) F = 0) :
    ∀ m, n ≤ m → ∑ j ∈ range r, w j * coeff (m + j) F = 0 := by
  have hstep : ∀ m, N ≤ m →
      ∑ j ∈ range r, w j * coeff (m + r + j) F
        = ∑ i ∈ range r, c i * ∑ j ∈ range r, w j * coeff (m + i + j) F := by
    intro m hm
    have hL : ∀ j ∈ range r, w j * coeff (m + r + j) F
        = ∑ i ∈ range r, w j * (c i * coeff (m + i + j) F) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show m + r + j = (m + j) + r from by omega, hrec (m + j) (by omega), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [show m + j + i = m + i + j from by omega]
    rw [Finset.sum_congr rfl hL, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      by_cases hlt : m < n + r
      · have h0 := hinit (m - n) (by omega)
        rwa [show n + (m - n) = m from by omega] at h0
      · have hrw : m = (m - r) + r := by omega
        rw [hrw, hstep (m - r) (by omega)]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [ih (m - r + i) (by omega) (by omega), mul_zero]
private theorem shorter_recurrence {F : K⟦X⟧} {n : ℕ} :
    ∀ (r : ℕ) (w : ℕ → K), (∃ j < r, w j ≠ 0) →
      (∀ m, n ≤ m → ∑ j ∈ range r, w j * coeff (m + j) F = 0) →
      ∃ r' < r, ∃ (N' : ℕ) (c : ℕ → K),
        ∀ m, N' ≤ m → coeff (m + r') F = ∑ i ∈ range r', c i * coeff (m + i) F := by
  intro r
  induction r with
  | zero => intro w hw _; obtain ⟨j, hj, _⟩ := hw; omega
  | succ r ih =>
      intro w hw hvan
      by_cases hlast : w r = 0
      · refine (ih w ?_ ?_).imp fun r' h => ⟨Nat.lt_succ_of_lt h.1, h.2⟩
        · obtain ⟨j, hj, hjne⟩ := hw
          refine ⟨j, ?_, hjne⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt' | heq
          · exact hlt'
          · exact absurd hlast (heq ▸ hjne)
        · intro m hm
          have := hvan m hm
          rwa [Finset.sum_range_succ, hlast, zero_mul, add_zero] at this
      · refine ⟨r, by omega, n, fun i => -(w i) / w r, ?_⟩
        intro m hm
        have hv := hvan m hm
        rw [Finset.sum_range_succ] at hv
        have hsum : ∑ i ∈ range r, -(w i) / w r * coeff (m + i) F
            = -(∑ i ∈ range r, w i * coeff (m + i) F) / w r := by
          rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hsum, eq_div_iff hlast]
        linear_combination hv
theorem CoefficientRecurrence.hankelEventuallyZero {F : K⟦X⟧}
    (h : CoefficientRecurrence F) : HankelEventuallyZero F := by
  classical
  have hex : ∃ r : ℕ, ∃ (N : ℕ) (c : ℕ → K),
      ∀ n, N ≤ n → coeff (n + r) F = ∑ i ∈ range r, c i * coeff (n + i) F := h
  obtain ⟨N, c, hrec⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, N, ?_, fun n hn => hankelMinor_succ_eq_zero hrec hn⟩
  intro n hn hzero
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    ((hankelMinor_eq_det F (Nat.find hex) n) ▸ hzero)
  set w : ℕ → K := fun j => if hj : j < Nat.find hex then v ⟨j, hj⟩ else 0 with hw
  have hwval : ∀ j : Fin (Nat.find hex), w (j : ℕ) = v j := fun j => by
    show (if hj : (j : ℕ) < Nat.find hex then v ⟨(j : ℕ), hj⟩ else 0) = v j
    rw [dif_pos j.isLt, Fin.eta]
  have hwne : ∃ j < Nat.find hex, w j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hv0 (funext fun j => ?_)
    have hj := hcon (j : ℕ) j.isLt
    rwa [hwval j] at hj
  have hinit : ∀ i < Nat.find hex,
      ∑ j ∈ range (Nat.find hex), w j * coeff (n + i + j) F = 0 := by
    intro i hi
    have hrow := congrFun hv ⟨i, hi⟩
    rw [← Fin.sum_univ_eq_sum_range (fun j => w j * coeff (n + i + j) F) (Nat.find hex)]
    have hterm : ∀ j : Fin (Nat.find hex), w (j : ℕ) * coeff (n + i + (j : ℕ)) F
        = coeff (n + i + (j : ℕ)) F * v j := by
      intro j
      rw [hwval j, mul_comm]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    simpa [Matrix.mulVec, dotProduct, hankelMatrix] using hrow
  obtain ⟨r', hr', N', c', hrec'⟩ :=
    shorter_recurrence (Nat.find hex) w hwne (combination_vanishes hrec hn hinit)
  exact absurd ⟨N', c', hrec'⟩ (Nat.find_min hex hr')
theorem isRationalPowerSeries_iff_coefficientRecurrence (F : K⟦X⟧) :
    IsRationalPowerSeries F ↔ CoefficientRecurrence F :=
  ⟨IsRationalPowerSeries.coefficientRecurrence, CoefficientRecurrence.isRationalPowerSeries⟩
private theorem hankelMatrix_mulVec_apply (F : K⟦X⟧) (m n : ℕ) (v : Fin m → K) (i : Fin m) :
    Matrix.mulVec (hankelMatrix F m n) v i
      = ∑ j : Fin m, coeff (n + (i : ℕ) + (j : ℕ)) F * v j := rfl
private theorem hankelMatrix_mulVec_castSucc {F : K⟦X⟧} {s n : ℕ} {z : Fin (s + 1) → K}
    (hzl : z (Fin.last s) = 0) (i : Fin s) :
    Matrix.mulVec (hankelMatrix F (s + 1) n) z i.castSucc
      = Matrix.mulVec (hankelMatrix F s n) (fun j : Fin s => z j.castSucc) i := by
  rw [hankelMatrix_mulVec_apply, hankelMatrix_mulVec_apply, Fin.sum_univ_castSucc, hzl,
    mul_zero, add_zero]
  exact Finset.sum_congr rfl fun _ _ => rfl
private theorem hankelMatrix_mulVec_succ {F : K⟦X⟧} {s n : ℕ} {z : Fin (s + 1) → K}
    (hzl : z (Fin.last s) = 0) (i : Fin s) :
    Matrix.mulVec (hankelMatrix F (s + 1) n) z i.succ
      = Matrix.mulVec (hankelMatrix F s (n + 1)) (fun j : Fin s => z j.castSucc) i := by
  rw [hankelMatrix_mulVec_apply, hankelMatrix_mulVec_apply, Fin.sum_univ_castSucc, hzl,
    mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hshift : n + ((i.succ : Fin (s + 1)) : ℕ) + ((j.castSucc : Fin (s + 1)) : ℕ)
      = n + 1 + (i : ℕ) + (j : ℕ) := by
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  rw [hshift]
private theorem hankelMatrix_pairing (F : K⟦X⟧) (m n : ℕ) (x y : Fin m → K) :
    ∑ i : Fin m, x i * Matrix.mulVec (hankelMatrix F m n) y i
      = ∑ i : Fin m, y i * Matrix.mulVec (hankelMatrix F m n) x i := by
  simp only [hankelMatrix_mulVec_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show n + (j : ℕ) + (i : ℕ) = n + (i : ℕ) + (j : ℕ) from by omega]
  ring
private theorem hankelMinor_eq_zero_of_kernel {F : K⟦X⟧} {s n : ℕ} {z : Fin (s + 1) → K}
    (hz0 : z ≠ 0) (hzl : z (Fin.last s) = 0)
    (hz : Matrix.mulVec (hankelMatrix F (s + 1) n) z = 0) :
    hankelMinor F s (n + 1) = 0 := by
  rw [hankelMinor_eq_det]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun i : Fin s => z i.castSucc, ?_, ?_⟩
  · intro hcon
    refine hz0 (funext fun j => Fin.lastCases ?_ ?_ j)
    · exact hzl
    · intro i
      exact congrFun hcon i
  · funext i
    rw [← hankelMatrix_mulVec_succ hzl i]
    exact congrFun hz i.succ
private theorem hankelMinor_shift_eq_zero {F : K⟦X⟧} {s n : ℕ}
    (hA : hankelMinor F (s + 1) n = 0) (hB : hankelMinor F s n = 0) :
    hankelMinor F s (n + 1) = 0 := by
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    ((hankelMinor_eq_det F (s + 1) n) ▸ hA)
  by_cases hzl : z (Fin.last s) = 0
  · exact hankelMinor_eq_zero_of_kernel hz0 hzl hz
  · obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      ((hankelMinor_eq_det F s n) ▸ hB)
    obtain ⟨U, hUlast, hUcast⟩ : ∃ U : Fin (s + 1) → K,
        U (Fin.last s) = 0 ∧ ∀ i : Fin s, U i.castSucc = u i :=
      ⟨fun j => Fin.lastCases (motive := fun _ => K) (0 : K) u j,
        Fin.lastCases_last, fun i => Fin.lastCases_castSucc i⟩
    have hUfun : (fun j : Fin s => U j.castSucc) = u := funext hUcast
    have hU0 : U ≠ 0 := by
      intro hcon
      refine hu0 ?_
      rw [← hUfun, hcon]
      rfl
    have hUtop : ∀ i : Fin s, Matrix.mulVec (hankelMatrix F (s + 1) n) U i.castSucc = 0 := by
      intro i
      rw [hankelMatrix_mulVec_castSucc hUlast i, hUfun]
      exact congrFun hu i
    have hpair : ∑ i : Fin (s + 1), z i * Matrix.mulVec (hankelMatrix F (s + 1) n) U i = 0 := by
      rw [hankelMatrix_pairing]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hzi : Matrix.mulVec (hankelMatrix F (s + 1) n) z i = 0 := congrFun hz i
      rw [hzi, mul_zero]
    rw [Fin.sum_univ_castSucc] at hpair
    simp only [hUtop, mul_zero, Finset.sum_const_zero, zero_add] at hpair
    have hUall : Matrix.mulVec (hankelMatrix F (s + 1) n) U = 0 := by
      funext j
      refine Fin.lastCases ?_ ?_ j
      · exact (mul_eq_zero.mp hpair).resolve_left hzl
      · exact hUtop
    exact hankelMinor_eq_zero_of_kernel hU0 hUlast hUall
private theorem hankelMinor_eq_zero_of_ge {F : K⟦X⟧} {s N n₀ : ℕ}
    (hbig : ∀ n, N ≤ n → hankelMinor F (s + 1) n = 0)
    (hn₀ : N ≤ n₀) (h₀ : hankelMinor F s n₀ = 0) :
    ∀ n, n₀ ≤ n → hankelMinor F s n = 0 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h₀
  | succ m hm ih => exact hankelMinor_shift_eq_zero (hbig m (le_trans hn₀ hm)) ih
private theorem hankelEventuallyZero_of_eventually_eq_zero {F : K⟦X⟧} :
    ∀ r : ℕ, (∃ N : ℕ, ∀ n, N ≤ n → hankelMinor F r n = 0) → HankelEventuallyZero F := by
  classical
  intro r
  induction r with
  | zero =>
      rintro ⟨N, hN⟩
      have h1 := hN N le_rfl
      rw [hankelMinor_zero] at h1
      exact absurd h1 one_ne_zero
  | succ s ih =>
      rintro ⟨N, hN⟩
      by_cases hcase : ∃ n₀, N ≤ n₀ ∧ hankelMinor F s n₀ = 0
      · obtain ⟨n₀, hn₀, h₀⟩ := hcase
        exact ih ⟨n₀, hankelMinor_eq_zero_of_ge hN hn₀ h₀⟩
      · exact ⟨s, N, fun n hn h0 => hcase ⟨n, hn, h0⟩, hN⟩
theorem FixedSizeHankelEventuallyZero.hankelEventuallyZero {F : K⟦X⟧}
    (h : FixedSizeHankelEventuallyZero F) : HankelEventuallyZero F := by
  obtain ⟨r, N, _, hN⟩ := h
  exact hankelEventuallyZero_of_eventually_eq_zero r ⟨N, hN⟩
theorem FixedSizeHankelEventuallyZero.coefficientRecurrence {F : K⟦X⟧}
    (h : FixedSizeHankelEventuallyZero F) : CoefficientRecurrence F :=
  h.hankelEventuallyZero.coefficientRecurrence
theorem HankelEventuallyZero.fixedSizeHankelEventuallyZero {F : K⟦X⟧}
    (h : HankelEventuallyZero F) : FixedSizeHankelEventuallyZero F := by
  obtain ⟨r, N, hF⟩ := h
  exact ⟨r + 1, N, Nat.succ_pos r, hF.2⟩
theorem coefficientRecurrence_iff_fixedSizeHankelEventuallyZero (F : K⟦X⟧) :
    CoefficientRecurrence F ↔ FixedSizeHankelEventuallyZero F :=
  ⟨fun h => h.hankelEventuallyZero.fixedSizeHankelEventuallyZero,
    FixedSizeHankelEventuallyZero.coefficientRecurrence⟩
theorem isRationalPowerSeries_iff_fixedSizeHankelEventuallyZero (F : K⟦X⟧) :
    IsRationalPowerSeries F ↔ FixedSizeHankelEventuallyZero F :=
  (isRationalPowerSeries_iff_coefficientRecurrence F).trans
    (coefficientRecurrence_iff_fixedSizeHankelEventuallyZero F)
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section PadicGrowth
variable {K : Type*} [NontriviallyNormedField K]
theorem isPadicEntire_iff_exists_bound (F : K⟦X⟧) :
    IsPadicEntire F ↔
      ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ n : ℕ, ‖PowerSeries.coeff n F‖ * R ^ n ≤ C := by
  constructor
  · intro hF R hR
    obtain ⟨C, hC⟩ := (hF R hR).bddAbove_range
    exact ⟨C, fun n ↦ hC (Set.mem_range_self n)⟩
  · intro hF R hR
    obtain ⟨C, hC⟩ := hF (2 * R + 1) (by linarith)
    have hR' : (0 : ℝ) < 2 * R + 1 := by linarith
    set ρ : ℝ := R / (2 * R + 1) with hρdef
    have hρ0 : 0 ≤ ρ := div_nonneg hR hR'.le
    have hρ1 : ρ < 1 := by
      rw [hρdef, div_lt_one hR']
      linarith
    have hfactor : (2 * R + 1) * ρ = R := by
      rw [hρdef]
      field_simp
    refine squeeze_zero (g := fun n ↦ C * ρ ^ n) (fun n ↦ by positivity) (fun n ↦ ?_) ?_
    · have hsplit : R ^ n = (2 * R + 1) ^ n * ρ ^ n := by
        rw [← mul_pow, hfactor]
      calc ‖PowerSeries.coeff n F‖ * R ^ n
          = (‖PowerSeries.coeff n F‖ * (2 * R + 1) ^ n) * ρ ^ n := by
            rw [hsplit]; ring
        _ ≤ C * ρ ^ n := mul_le_mul_of_nonneg_right (hC n) (by positivity)
    · simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
end PadicGrowth
section PadicGrowthUltra
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
end PadicGrowthUltra
section PadicGrowthComplete
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
end PadicGrowthComplete
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
private theorem sum_hankel_indices (r n : ℕ) (σ : Equiv.Perm (Fin r)) :
    ∑ i : Fin r, (n + (σ i : ℕ) + (i : ℕ)) = r * n + r * (r - 1) := by
  have hperm : ∑ i : Fin r, ((σ i : Fin r) : ℕ) = ∑ i : Fin r, (i : ℕ) :=
    Equiv.sum_comp σ (fun i : Fin r ↦ (i : ℕ))
  have hgauss : (∑ i : Fin r, (i : ℕ)) * 2 = r * (r - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ i) r]
    exact Finset.sum_range_id_mul_two r
  have hsplit : ∑ i : Fin r, (n + (σ i : ℕ) + (i : ℕ))
      = (∑ _i : Fin r, n) + (∑ i : Fin r, ((σ i : Fin r) : ℕ)) + ∑ i : Fin r, (i : ℕ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hsplit, hperm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega
theorem hankelMinor_archimedean_bound (F : ℚ⟦X⟧) {C B : ℚ}
    (hgrowth : ∀ m : ℕ, |PowerSeries.coeff m F| ≤ C * B ^ m) (r n : ℕ) :
    |hankelMinor F r n| ≤ (Nat.factorial r : ℚ) * C ^ r * B ^ (r * n + r * (r - 1)) := by
  classical
  rw [hankelMinor, Matrix.det_apply']
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans
    (Finset.sum_le_sum (g := fun _ : Equiv.Perm (Fin r) ↦ C ^ r * B ^ (r * n + r * (r - 1))) ?_) ?_
  · intro σ _
    have hsign : |((Equiv.Perm.sign σ : ℤ) : ℚ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
    rw [abs_mul, hsign, one_mul, Finset.abs_prod]
    simp only [Matrix.of_apply]
    calc ∏ i : Fin r, |PowerSeries.coeff (n + (σ i : ℕ) + (i : ℕ)) F|
        ≤ ∏ i : Fin r, C * B ^ (n + (σ i : ℕ) + (i : ℕ)) :=
          Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) (fun i _ ↦ hgrowth _)
      _ = C ^ r * B ^ (∑ i : Fin r, (n + (σ i : ℕ) + (i : ℕ))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
            Finset.card_univ, Fintype.card_fin]
      _ = C ^ r * B ^ (r * n + r * (r - 1)) := by rw [sum_hankel_indices]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc]
theorem hankelMinor_denominator_bound (F : ℚ⟦X⟧) (D : ℤ) (z : ℕ → ℤ)
    (hz : ∀ m : ℕ, (D : ℚ) ^ (m + 1) * PowerSeries.coeff m F = (z m : ℚ)) (r n : ℕ) :
    (((Matrix.of fun i j : Fin r ↦ z (n + i + j)).det : ℤ) : ℚ)
      = (D : ℚ) ^ (r * (n + 1) + r * (r - 1)) * hankelMinor F r n := by
  classical
  rw [Int.cast_det]
  have hmap : ((Matrix.of fun i j : Fin r ↦ z (n + i + j)).map fun x : ℤ ↦ (x : ℚ))
      = Matrix.of fun i j : Fin r ↦
          (D : ℚ) ^ (n + (i : ℕ) + (j : ℕ) + 1) *
            PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) F := by
    ext i j
    rw [Matrix.map_apply]
    show ((z (n + (i : ℕ) + (j : ℕ)) : ℤ) : ℚ)
      = (D : ℚ) ^ (n + (i : ℕ) + (j : ℕ) + 1) * PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) F
    exact (hz (n + (i : ℕ) + (j : ℕ))).symm
  rw [hmap, Matrix.det_apply', hankelMinor, Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [Matrix.of_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ i : Fin r, (n + (σ i : ℕ) + (i : ℕ) + 1) = r * (n + 1) + r * (r - 1) := by
    rw [Finset.sum_add_distrib, sum_hankel_indices, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    ring
  rw [hsum]
  ring
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
section SupBounded
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
omit [IsUltrametricDist K] in
private theorem SupBounded.nonneg {c : ℝ} {S : K⟦X⟧} (h : SupBounded c S) : 0 ≤ c :=
  le_trans (norm_nonneg _) (h 0)
private theorem SupBounded.mul {c c' : ℝ} {S T : K⟦X⟧} (hS : SupBounded c S)
    (hT : SupBounded c' T) : SupBounded (c * c') (S * T) := by
  intro m
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (M := K)
    (mul_nonneg hS.nonneg hT.nonneg) ?_
  intro ij _
  rw [norm_mul]
  exact mul_le_mul (hS _) (hT _) (norm_nonneg _) hS.nonneg
omit [IsUltrametricDist K] in
@[simp]
private theorem coeff_shiftDown (e : ℕ) (S : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (shiftDown e S) = PowerSeries.coeff (n + e) S := by
  simp [shiftDown]
omit [IsUltrametricDist K] in
private theorem SupBounded.shiftDown {c : ℝ} {S : K⟦X⟧} (h : SupBounded c S) (e : ℕ) :
    SupBounded c (shiftDown e S) := by
  intro m; rw [coeff_shiftDown]; exact h _
omit [IsUltrametricDist K] in
private theorem SupBounded.trunc {c : ℝ} {S : K⟦X⟧} (h : SupBounded c S) (e : ℕ) :
    SupBounded c ((PowerSeries.trunc e S : K[X]) : K⟦X⟧) := by
  intro m
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split
  · exact h m
  · simpa using h.nonneg
omit [IsUltrametricDist K] in
private theorem shiftDown_X_pow (e : ℕ) : shiftDown e ((PowerSeries.X : K⟦X⟧) ^ e) = 1 := by
  ext n
  rw [coeff_shiftDown, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  by_cases hn : n = 0 <;> simp [hn]
omit [IsUltrametricDist K] in
private theorem trunc_add_X_pow_mul_shiftDown (e : ℕ) (S : K⟦X⟧) :
    ((PowerSeries.trunc e S : K[X]) : K⟦X⟧) + PowerSeries.X ^ e * shiftDown e S = S := by
  have hzero : ∀ (m : ℕ) (T : K⟦X⟧), m < e → PowerSeries.coeff m (PowerSeries.X ^ e * T) = 0 := by
    intro m T hm
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ij hij ↦ ?_
    have hij' : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]
  ext n
  rw [map_add, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hn : n < e
  · rw [if_pos hn, hzero n _ hn, add_zero]
  · rw [if_neg hn, zero_add]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + e := ⟨n - e, by omega⟩
    rw [PowerSeries.coeff_X_pow_mul, coeff_shiftDown]
end SupBounded
section Inverse
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
omit [IsUltrametricDist K] in
private theorem coeff_inv_recursion (S : K⟦X⟧) (hS : PowerSeries.constantCoeff S ≠ 0) (n : ℕ) :
    PowerSeries.constantCoeff S * PowerSeries.coeff (n + 1) S⁻¹
      = -∑ i ∈ Finset.range (n + 1),
          PowerSeries.coeff (i + 1) S * PowerSeries.coeff (n - i) S⁻¹ := by
  have h := congrArg (PowerSeries.coeff (n + 1)) (PowerSeries.mul_inv_cancel S hS)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ'] at h
  simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  linear_combination h
private theorem supBounded_inv_of_norm_constantCoeff_eq_one {S : K⟦X⟧}
    (hone : ‖PowerSeries.constantCoeff S‖ = 1) (hS : SupBounded 1 S) :
    SupBounded 1 S⁻¹ := by
  have hne : PowerSeries.constantCoeff S ≠ 0 := by
    intro h; rw [h, norm_zero] at hone; exact zero_ne_one hone
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero =>
          rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
            norm_inv, hone, inv_one]
      | succ m =>
          have hrec := coeff_inv_recursion S hne m
          have hbound : ‖PowerSeries.constantCoeff S * PowerSeries.coeff (m + 1) S⁻¹‖ ≤ 1 := by
            rw [hrec, norm_neg]
            refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (M := K) zero_le_one ?_
            intro i _
            rw [norm_mul]
            exact mul_le_one₀ (hS _) (norm_nonneg _) (ih (m - i) (by omega))
          rwa [norm_mul, hone, one_mul] at hbound
end Inverse
section WeierstrassDivision
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {Hh : K⟦X⟧} {e : ℕ} {θ : ℝ}
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem constantCoeff_wQ : PowerSeries.constantCoeff (wQ Hh e) = PowerSeries.coeff e Hh := by
  rw [wQ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_shiftDown, Nat.zero_add]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem wQ_ne_zero (hu : ‖PowerSeries.coeff e Hh‖ = 1) :
    PowerSeries.constantCoeff (wQ Hh e) ≠ 0 := by
  rw [constantCoeff_wQ]
  intro h
  rw [h, norm_zero] at hu
  exact zero_ne_one hu
omit [CompleteSpace K] in
private theorem supBounded_wQinv (hb : SupBounded 1 Hh) (hu : ‖PowerSeries.coeff e Hh‖ = 1) :
    SupBounded 1 (wQ Hh e)⁻¹ :=
  supBounded_inv_of_norm_constantCoeff_eq_one (by rw [constantCoeff_wQ]; exact hu)
    (hb.shiftDown e)
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem supBounded_wL (hθ : 0 ≤ θ) (hlow : ∀ m, m < e → ‖PowerSeries.coeff m Hh‖ ≤ θ) :
    SupBounded θ (wL Hh e) := by
  intro m
  rw [wL, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split
  · rename_i hm; exact hlow m hm
  · simpa using hθ
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem wIter_eq (hu : ‖PowerSeries.coeff e Hh‖ = 1) (k : ℕ) :
    wIter Hh e k = wQuo Hh e k * Hh + wRem Hh e k + wIter Hh e (k + 1) := by
  have hsplit : wL Hh e + PowerSeries.X ^ e * wQ Hh e = Hh :=
    trunc_add_X_pow_mul_shiftDown e Hh
  have hQinv : (wQ Hh e)⁻¹ * wQ Hh e = 1 := PowerSeries.inv_mul_cancel _ (wQ_ne_zero hu)
  have hlow : wRem Hh e k + PowerSeries.X ^ e * shiftDown e (wIter Hh e k) = wIter Hh e k :=
    trunc_add_X_pow_mul_shiftDown e (wIter Hh e k)
  have hfactor : wQuo Hh e k * Hh
      = wQuo Hh e k * (wL Hh e + PowerSeries.X ^ e * wQ Hh e) := by rw [hsplit]
  have hprod : wQuo Hh e k * Hh
      = wQuo Hh e k * wL Hh e + PowerSeries.X ^ e * shiftDown e (wIter Hh e k) := by
    rw [hfactor, mul_add]
    congr 1
    calc wQuo Hh e k * (PowerSeries.X ^ e * wQ Hh e)
        = ((wQ Hh e)⁻¹ * wQ Hh e) * (PowerSeries.X ^ e * shiftDown e (wIter Hh e k)) := by
          rw [wQuo]; ring
      _ = PowerSeries.X ^ e * shiftDown e (wIter Hh e k) := by rw [hQinv, one_mul]
  have hnext : wIter Hh e (k + 1) = -(wQuo Hh e k) * wL Hh e := by
    rw [wIter, wQuo, neg_mul]
  rw [hprod, hnext]
  linear_combination -hlow
omit [CompleteSpace K] in
private theorem supBounded_wIter (hb : SupBounded 1 Hh) (hu : ‖PowerSeries.coeff e Hh‖ = 1)
    (hθ : 0 ≤ θ) (hlow : ∀ m, m < e → ‖PowerSeries.coeff m Hh‖ ≤ θ) :
    ∀ k, SupBounded (θ ^ k) (wIter Hh e k)
  | 0 => by
      intro m
      rw [pow_zero]
      show ‖PowerSeries.coeff m ((PowerSeries.X : K⟦X⟧) ^ e)‖ ≤ 1
      rw [PowerSeries.coeff_X_pow]
      split <;> simp
  | k + 1 => by
      have h := ((supBounded_wQinv hb hu).mul
        ((supBounded_wIter hb hu hθ hlow k).shiftDown e)).mul (supBounded_wL hθ hlow)
      rw [one_mul, ← pow_succ] at h
      intro m
      show ‖PowerSeries.coeff m
        (-((wQ Hh e)⁻¹ * shiftDown e (wIter Hh e k)) * wL Hh e)‖ ≤ θ ^ (k + 1)
      rw [neg_mul, map_neg, norm_neg]
      exact h m
omit [CompleteSpace K] in
private theorem supBounded_wQuo (hb : SupBounded 1 Hh) (hu : ‖PowerSeries.coeff e Hh‖ = 1)
    (hθ : 0 ≤ θ) (hlow : ∀ m, m < e → ‖PowerSeries.coeff m Hh‖ ≤ θ) (k : ℕ) :
    SupBounded (θ ^ k) (wQuo Hh e k) := by
  have h := (supBounded_wQinv hb hu).mul ((supBounded_wIter hb hu hθ hlow k).shiftDown e)
  rw [one_mul] at h
  exact h
omit [CompleteSpace K] in
private theorem supBounded_wRem (hb : SupBounded 1 Hh) (hu : ‖PowerSeries.coeff e Hh‖ = 1)
    (hθ : 0 ≤ θ) (hlow : ∀ m, m < e → ‖PowerSeries.coeff m Hh‖ ≤ θ) (k : ℕ) :
    SupBounded (θ ^ k) (wRem Hh e k) :=
  (supBounded_wIter hb hu hθ hlow k).trunc e
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem coeff_wRem_of_le (k n : ℕ) (hn : e ≤ n) :
    PowerSeries.coeff n (wRem Hh e k) = 0 := by
  rw [wRem, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_neg (by omega)]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem wIter_partial (hu : ‖PowerSeries.coeff e Hh‖ = 1) :
    ∀ N : ℕ, (PowerSeries.X : K⟦X⟧) ^ e
      = (∑ k ∈ Finset.range N, wQuo Hh e k) * Hh
        + (∑ k ∈ Finset.range N, wRem Hh e k) + wIter Hh e N
  | 0 => by simp [wIter]
  | N + 1 => by
      have hstep := wIter_eq (Hh := Hh) (e := e) hu N
      rw [Finset.sum_range_succ, Finset.sum_range_succ, add_mul]
      linear_combination (wIter_partial hu N) + hstep
end WeierstrassDivision
section WeierstrassLimit
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {Hh : K⟦X⟧} {e : ℕ} {θ : ℝ}
omit [CompleteSpace K] in
private theorem norm_tsum_le_of_forall {f : ℕ → K} {c : ℝ} (hc : 0 ≤ c)
    (hsum : Summable f) (hf : ∀ k, ‖f k‖ ≤ c) : ‖∑' k, f k‖ ≤ c := by
  refine le_of_tendsto (hsum.hasSum.tendsto_sum_nat.norm) (Filter.Eventually.of_forall fun N ↦ ?_)
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (M := K) hc fun k _ ↦ hf k
private theorem summable_coeff_of_geometric {S : ℕ → K⟦X⟧} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ k, SupBounded (θ ^ k) (S k)) (n : ℕ) :
    Summable (fun k ↦ PowerSeries.coeff n (S k)) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun k ↦ norm_nonneg _) (fun k ↦ h k n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1)
variable (hb : SupBounded 1 Hh) (hu : ‖PowerSeries.coeff e Hh‖ = 1)
variable (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hlow : ∀ m, m < e → ‖PowerSeries.coeff m Hh‖ ≤ θ)
include hb hu hθ0 hθ1 hlow
private theorem supBounded_wQuoSum : SupBounded 1 (wQuoSum Hh e) := by
  intro n
  rw [wQuoSum, PowerSeries.coeff_mk]
  refine norm_tsum_le_of_forall zero_le_one
    (summable_coeff_of_geometric hθ0 hθ1 (supBounded_wQuo hb hu hθ0 hlow) n) fun k ↦ ?_
  exact (supBounded_wQuo hb hu hθ0 hlow k n).trans (pow_le_one₀ hθ0 hθ1.le)
omit [IsUltrametricDist K] [CompleteSpace K] hb hu hθ0 hθ1 hlow in
private theorem coeff_wRemSum_of_le (n : ℕ) (hn : e ≤ n) :
    PowerSeries.coeff n (wRemSum Hh e) = 0 := by
  rw [wRemSum, PowerSeries.coeff_mk]
  simp [coeff_wRem_of_le (Hh := Hh) (e := e) _ n hn]
private theorem X_pow_eq_wQuoSum_mul_add :
    (PowerSeries.X : K⟦X⟧) ^ e = wQuoSum Hh e * Hh + wRemSum Hh e := by
  ext n
  have hqsum : ∀ i : ℕ,
      Filter.Tendsto (fun N ↦ ∑ k ∈ Finset.range N, PowerSeries.coeff i (wQuo Hh e k))
        Filter.atTop (nhds (PowerSeries.coeff i (wQuoSum Hh e))) := by
    intro i
    rw [wQuoSum, PowerSeries.coeff_mk]
    exact (summable_coeff_of_geometric hθ0 hθ1
      (supBounded_wQuo hb hu hθ0 hlow) i).hasSum.tendsto_sum_nat
  have hrsum : Filter.Tendsto (fun N ↦ ∑ k ∈ Finset.range N, PowerSeries.coeff n (wRem Hh e k))
      Filter.atTop (nhds (PowerSeries.coeff n (wRemSum Hh e))) := by
    rw [wRemSum, PowerSeries.coeff_mk]
    exact (summable_coeff_of_geometric hθ0 hθ1
      (supBounded_wRem hb hu hθ0 hlow) n).hasSum.tendsto_sum_nat
  have hiter : Filter.Tendsto (fun N ↦ PowerSeries.coeff n (wIter Hh e N)) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun N ↦ norm_nonneg _)
      (fun N ↦ supBounded_wIter hb hu hθ0 hlow N n)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1)
  have hprodtend : Filter.Tendsto
      (fun N ↦ PowerSeries.coeff n ((∑ k ∈ Finset.range N, wQuo Hh e k) * Hh)) Filter.atTop
      (nhds (PowerSeries.coeff n (wQuoSum Hh e * Hh))) := by
    have hrewrite : ∀ N : ℕ, PowerSeries.coeff n ((∑ k ∈ Finset.range N, wQuo Hh e k) * Hh)
        = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            (∑ k ∈ Finset.range N, PowerSeries.coeff ij.1 (wQuo Hh e k)) *
              PowerSeries.coeff ij.2 Hh := by
      intro N
      rw [PowerSeries.coeff_mul]
      exact Finset.sum_congr rfl fun ij _ ↦ by rw [map_sum]
    simp only [hrewrite]
    rw [PowerSeries.coeff_mul]
    exact tendsto_finsetSum _ fun ij _ ↦ (hqsum ij.1).mul_const _
  have heq : ∀ N : ℕ, PowerSeries.coeff n ((PowerSeries.X : K⟦X⟧) ^ e)
      = PowerSeries.coeff n ((∑ k ∈ Finset.range N, wQuo Hh e k) * Hh)
        + (∑ k ∈ Finset.range N, PowerSeries.coeff n (wRem Hh e k))
        + PowerSeries.coeff n (wIter Hh e N) := by
    intro N
    rw [wIter_partial hu N, map_add, map_add, map_sum]
  have hf1 : Filter.Tendsto
      (fun N : ℕ ↦ PowerSeries.coeff n ((∑ k ∈ Finset.range N, wQuo Hh e k) * Hh)
        + (∑ k ∈ Finset.range N, PowerSeries.coeff n (wRem Hh e k))
        + PowerSeries.coeff n (wIter Hh e N)) Filter.atTop
      (nhds (PowerSeries.coeff n ((PowerSeries.X : K⟦X⟧) ^ e))) :=
    Filter.Tendsto.congr heq tendsto_const_nhds
  have hf2 := (hprodtend.add hrsum).add hiter
  rw [map_add, tendsto_nhds_unique hf1 hf2, add_zero]
private theorem norm_coeff_zero_wQuoSum_ge :
    1 - θ ≤ ‖PowerSeries.coeff 0 (wQuoSum Hh e)‖ := by
  have hsum := summable_coeff_of_geometric hθ0 hθ1 (supBounded_wQuo hb hu hθ0 hlow) 0
  have h0 : ‖PowerSeries.coeff 0 (wQuo Hh e 0)‖ = 1 := by
    have hq0 : wQuo Hh e 0 = (wQ Hh e)⁻¹ := by
      show (wQ Hh e)⁻¹ * shiftDown e ((PowerSeries.X : K⟦X⟧) ^ e) = (wQ Hh e)⁻¹
      rw [shiftDown_X_pow, mul_one]
    rw [hq0, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
      norm_inv, constantCoeff_wQ, hu, inv_one]
  have htail : ‖∑' k, PowerSeries.coeff 0 (wQuo Hh e (k + 1))‖ ≤ θ := by
    refine norm_tsum_le_of_forall hθ0 ((summable_nat_add_iff 1).mpr hsum) fun k ↦ ?_
    refine (supBounded_wQuo hb hu hθ0 hlow (k + 1) 0).trans ?_
    calc θ ^ (k + 1) = θ ^ k * θ := pow_succ θ k
      _ ≤ 1 * θ := mul_le_mul_of_nonneg_right (pow_le_one₀ hθ0 hθ1.le) hθ0
      _ = θ := one_mul θ
  rw [wQuoSum, PowerSeries.coeff_mk, hsum.tsum_eq_zero_add]
  have hrev := norm_sub_norm_le (PowerSeries.coeff 0 (wQuo Hh e 0))
    (-(∑' k, PowerSeries.coeff 0 (wQuo Hh e (k + 1))))
  rw [norm_neg, sub_neg_eq_add, h0] at hrev
  linarith
end WeierstrassLimit
section Proposition3
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
private theorem exists_dominant_index {w : ℕ → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hpos : 0 < w 0)
    (htend : Filter.Tendsto w Filter.atTop (nhds 0)) :
    ∃ e, (∀ m, w m ≤ w e) ∧ ∀ m, m < e → w m < w e := by
  classical
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend (w 0) hpos
  have hsub : ∀ m, w 0 ≤ w m → m < N := by
    intro m hm
    by_contra hcon
    have h := hN m (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hw0 m)] at h
    linarith
  set s : Finset ℕ := (Finset.range N).filter (fun m ↦ w 0 ≤ w m) with hs
  have h0s : 0 ∈ s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hsub 0 le_rfl), le_rfl⟩
  obtain ⟨e0, he0s, he0max⟩ := s.exists_max_image w ⟨0, h0s⟩
  set t : Finset ℕ := s.filter (fun m ↦ w m = w e0) with ht
  have he0t : e0 ∈ t := Finset.mem_filter.mpr ⟨he0s, rfl⟩
  have htne : t.Nonempty := ⟨e0, he0t⟩
  refine ⟨t.min' htne, ?_, ?_⟩
  · have hmem := t.min'_mem htne
    have hval : w (t.min' htne) = w e0 := (Finset.mem_filter.mp hmem).2
    intro m
    rw [hval]
    by_cases hm : w 0 ≤ w m
    · exact he0max m (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hsub m hm), hm⟩)
    · exact le_trans (le_of_not_ge hm) (he0max 0 h0s)
  · intro m hm
    have hmem := t.min'_mem htne
    have hval : w (t.min' htne) = w e0 := (Finset.mem_filter.mp hmem).2
    have hle : w m ≤ w (t.min' htne) := by
      rw [hval]
      by_cases hmm : w 0 ≤ w m
      · exact he0max m (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hsub m hmm), hmm⟩)
      · exact le_trans (le_of_not_ge hmm) (he0max 0 h0s)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hm0 : w 0 ≤ w m := by rw [h, hval]; exact he0max 0 h0s
      have hmt : m ∈ t :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hsub m hm0), hm0⟩, by rw [h, hval]⟩
      exact absurd (t.min'_le m hmt) (by omega)
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem coe_trunc_eq_of_tail_zero {S : K⟦X⟧} {N : ℕ}
    (h : ∀ m, N ≤ m → PowerSeries.coeff m S = 0) :
    ((PowerSeries.trunc N S : Polynomial K) : K⟦X⟧) = S := by
  ext m
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hm : m < N
  · rw [if_pos hm]
  · rw [if_neg hm]
    exact (h m (by omega)).symm
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem rescale_rescale_inv {ϖ : K} (hϖ : ϖ ≠ 0) (S : K⟦X⟧) :
    PowerSeries.rescale ϖ⁻¹ (PowerSeries.rescale ϖ S) = S := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hϖ, one_pow, one_mul]
theorem exists_padicPolynomialWitness {Fk G H : K⟦X⟧}
    (hG : IsPadicEntire G) (hH : IsPadicEntire H)
    (hH1 : PowerSeries.constantCoeff H = 1) (hmul : H * Fk = G)
    {ϖ : K} (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    ∃ (P : Polynomial K) (cB : ℝ), P.coeff 0 = 1 ∧ 0 ≤ cB ∧
      ∀ n, ‖PowerSeries.coeff n ((P : K⟦X⟧) * Fk)‖ ≤ cB * ‖ϖ‖ ^ n := by
  classical
  have hρ0 : 0 < ‖ϖ‖ := norm_pos_iff.mpr hϖ0
  have hRnn : (0 : ℝ) ≤ ‖ϖ‖⁻¹ := by positivity
  have hnormcoeff : ∀ (S : K⟦X⟧) (m : ℕ),
      ‖PowerSeries.coeff m (PowerSeries.rescale ϖ⁻¹ S)‖
        = ‖PowerSeries.coeff m S‖ * ‖ϖ‖⁻¹ ^ m := by
    intro S m
    rw [PowerSeries.coeff_rescale, norm_mul, norm_pow, norm_inv]
    ring
  set Ht := PowerSeries.rescale ϖ⁻¹ H with hHt
  set Gt := PowerSeries.rescale ϖ⁻¹ G with hGt
  set Ft := PowerSeries.rescale ϖ⁻¹ Fk with hFt
  have hmult : Ht * Ft = Gt := by rw [hHt, hFt, hGt, ← map_mul, hmul]
  have hHtend : Filter.Tendsto (fun m ↦ ‖PowerSeries.coeff m Ht‖) Filter.atTop (nhds 0) :=
    (hH ‖ϖ‖⁻¹ hRnn).congr fun m ↦ (hnormcoeff H m).symm
  obtain ⟨cG, hcG⟩ := (isPadicEntire_iff_exists_bound G).1 hG ‖ϖ‖⁻¹ hRnn
  have hGbound : SupBounded cG Gt := fun m ↦ by rw [hGt, hnormcoeff G m]; exact hcG m
  have hHt0 : ‖PowerSeries.coeff 0 Ht‖ = 1 := by
    rw [hHt, hnormcoeff H 0, pow_zero, mul_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hH1, norm_one]
  obtain ⟨e, hemax, heleast⟩ := exists_dominant_index (w := fun m ↦ ‖PowerSeries.coeff m Ht‖)
    (fun m ↦ norm_nonneg _) (by rw [hHt0]; exact zero_lt_one) hHtend
  have hMpos : 0 < ‖PowerSeries.coeff e Ht‖ := by
    have := hemax 0
    rw [hHt0] at this
    linarith
  have hcne : PowerSeries.coeff e Ht ≠ 0 := norm_pos_iff.mp hMpos
  set Hh := PowerSeries.C (PowerSeries.coeff e Ht)⁻¹ * Ht with hHh
  have hcoeffHh : ∀ m, PowerSeries.coeff m Hh
      = (PowerSeries.coeff e Ht)⁻¹ * PowerSeries.coeff m Ht := by
    intro m; rw [hHh, PowerSeries.coeff_C_mul]
  have hnormHh : ∀ m, ‖PowerSeries.coeff m Hh‖
      = ‖PowerSeries.coeff m Ht‖ / ‖PowerSeries.coeff e Ht‖ := by
    intro m
    rw [hcoeffHh m, norm_mul, norm_inv, div_eq_inv_mul]
  have hb : SupBounded 1 Hh := by
    intro m
    rw [hnormHh m, div_le_one hMpos]
    exact hemax m
  have hu : ‖PowerSeries.coeff e Hh‖ = 1 := by
    rw [hnormHh e, div_self hMpos.ne']
  obtain ⟨θ, hθ0, hθ1, hlow⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ m, m < e → ‖PowerSeries.coeff m Hh‖ ≤ θ := by
    rcases Nat.eq_zero_or_pos e with rfl | hepos
    · exact ⟨0, le_rfl, zero_lt_one, fun m hm ↦ absurd hm (Nat.not_lt_zero m)⟩
    · obtain ⟨m0, hm0mem, hm0max⟩ := (Finset.range e).exists_max_image
        (fun m ↦ ‖PowerSeries.coeff m Hh‖) ⟨0, Finset.mem_range.mpr hepos⟩
      refine ⟨‖PowerSeries.coeff m0 Hh‖, norm_nonneg _, ?_, fun m hm ↦
        hm0max m (Finset.mem_range.mpr hm)⟩
      have hm0lt : m0 < e := Finset.mem_range.mp hm0mem
      rw [hnormHh m0, div_lt_one hMpos]
      exact heleast m0 hm0lt
  have hdiv := X_pow_eq_wQuoSum_mul_add hb hu hθ0 hθ1 hlow
  set Phat := (PowerSeries.X : K⟦X⟧) ^ e - wRemSum Hh e with hPhat
  have hPhateq : Phat = wQuoSum Hh e * Hh := by
    rw [hPhat, hdiv]; ring
  have hPhattail : ∀ m, e + 1 ≤ m → PowerSeries.coeff m Phat = 0 := by
    intro m hm
    rw [hPhat, map_sub, PowerSeries.coeff_X_pow, if_neg (by omega),
      coeff_wRemSum_of_le (Hh := Hh) (e := e) m (by omega), sub_zero]
  have hPhatbound : SupBounded (‖PowerSeries.coeff e Ht‖⁻¹ * cG) (Phat * Ft) := by
    have hrw : Phat * Ft
        = PowerSeries.C (PowerSeries.coeff e Ht)⁻¹ * (wQuoSum Hh e * Gt) := by
      rw [hPhateq, hHh, ← hmult]
      ring
    rw [hrw]
    have hC : SupBounded (‖PowerSeries.coeff e Ht‖⁻¹)
        (PowerSeries.C ((PowerSeries.coeff e Ht)⁻¹) : K⟦X⟧) := by
      intro m
      rw [PowerSeries.coeff_C]
      split
      · rw [norm_inv]
      · simp
    have := hC.mul ((supBounded_wQuoSum hb hu hθ0 hθ1 hlow).mul hGbound)
    rwa [one_mul] at this
  set P0 := PowerSeries.rescale ϖ Phat with hP0
  have hP0back : PowerSeries.rescale ϖ⁻¹ (P0 * Fk) = Phat * Ft := by
    rw [hP0, hFt, map_mul, rescale_rescale_inv hϖ0]
  have hP0bound : ∀ n, ‖PowerSeries.coeff n (P0 * Fk)‖
      ≤ (‖PowerSeries.coeff e Ht‖⁻¹ * cG) * ‖ϖ‖ ^ n := by
    intro n
    have h1 : ‖PowerSeries.coeff n (P0 * Fk)‖ * ‖ϖ‖⁻¹ ^ n
        = ‖PowerSeries.coeff n (Phat * Ft)‖ := by
      rw [← hP0back, hnormcoeff (P0 * Fk) n]
    have h2 : ‖PowerSeries.coeff n (P0 * Fk)‖
        = ‖PowerSeries.coeff n (Phat * Ft)‖ * ‖ϖ‖ ^ n := by
      rw [← h1, mul_assoc, ← mul_pow, inv_mul_cancel₀ hρ0.ne', one_pow, mul_one]
    rw [h2]
    exact mul_le_mul_of_nonneg_right (hPhatbound n) (by positivity)
  have hP0tail : ∀ m, e + 1 ≤ m → PowerSeries.coeff m P0 = 0 := by
    intro m hm
    rw [hP0, PowerSeries.coeff_rescale, hPhattail m hm, mul_zero]
  have hP00 : PowerSeries.coeff 0 P0 = PowerSeries.coeff 0 Phat := by
    rw [hP0, PowerSeries.coeff_rescale, pow_zero, one_mul]
  have hP0ne : PowerSeries.coeff 0 P0 ≠ 0 := by
    rw [hP00, hPhateq, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
    refine mul_ne_zero ?_ ?_
    · intro hzero
      have hge := norm_coeff_zero_wQuoSum_ge hb hu hθ0 hθ1 hlow
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero, norm_zero] at hge
      linarith
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeffHh 0]
      refine mul_ne_zero (inv_ne_zero hcne) ?_
      intro hzero
      rw [hzero, norm_zero] at hHt0
      exact zero_ne_one hHt0
  have hcG0 : (0 : ℝ) ≤ cG := hGbound.nonneg
  refine ⟨Polynomial.C (PowerSeries.coeff 0 P0)⁻¹ * PowerSeries.trunc (e + 1) P0,
    ‖PowerSeries.coeff 0 P0‖⁻¹ * (‖PowerSeries.coeff e Ht‖⁻¹ * cG), ?_,
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hcG0), ?_⟩
  · rw [Polynomial.coeff_C_mul, PowerSeries.coeff_trunc, if_pos (by omega),
      inv_mul_cancel₀ hP0ne]
  · intro n
    have hcoe : ((Polynomial.C (PowerSeries.coeff 0 P0)⁻¹ * PowerSeries.trunc (e + 1) P0 :
          Polynomial K) : K⟦X⟧)
        = PowerSeries.C (PowerSeries.coeff 0 P0)⁻¹ * P0 := by
      rw [Polynomial.coe_mul, Polynomial.coe_C, coe_trunc_eq_of_tail_zero hP0tail]
    rw [hcoe, mul_assoc, PowerSeries.coeff_C_mul, norm_mul, norm_inv, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hP0bound n) (by positivity)
end Proposition3
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
section ColumnTransform
variable {K : Type*} [Field K]
private theorem det_dworkColumnMatrix (P : Polynomial K) (hP0 : P.coeff 0 = 1) (e r : ℕ) :
    (dworkColumnMatrix P e r).det = 1 := by
  classical
  have htri : (dworkColumnMatrix P e r).BlockTriangular id := by
    intro i j hij
    have hij' : (j : ℕ) < (i : ℕ) := hij
    rw [dworkColumnMatrix]
    show (if (j : ℕ) < e then (if i = j then 1 else 0)
      else if (i : ℕ) ≤ (j : ℕ) then P.coeff ((j : ℕ) - (i : ℕ)) else 0) = 0
    split
    · rw [if_neg (by intro h; rw [h] at hij'; omega)]
    · rw [if_neg (by omega)]
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one fun i _ ↦ ?_
  rw [dworkColumnMatrix]
  show (if (i : ℕ) < e then (if i = i then 1 else 0)
    else if (i : ℕ) ≤ (i : ℕ) then P.coeff ((i : ℕ) - (i : ℕ)) else 0) = 1
  split
  · rw [if_pos rfl]
  · rw [if_pos le_rfl, Nat.sub_self, hP0]
private theorem hankelMinor_eq_det_columnTransform (Fk : K⟦X⟧) (P : Polynomial K)
    (hP0 : P.coeff 0 = 1) {e r : ℕ} (hPe : P.natDegree ≤ e) (n : ℕ) :
    hankelMinor Fk r n
      = (Matrix.of fun i j : Fin r ↦
          if (j : ℕ) < e then PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) Fk
          else PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) ((P : K⟦X⟧) * Fk)).det := by
  classical
  have hmul : (Matrix.of fun i j : Fin r ↦ PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) Fk) *
      dworkColumnMatrix P e r
      = Matrix.of fun i j : Fin r ↦
          if (j : ℕ) < e then PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) Fk
          else PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) ((P : K⟦X⟧) * Fk) := by
    ext i j
    rw [Matrix.mul_apply]
    show (∑ j' : Fin r, PowerSeries.coeff (n + (i : ℕ) + (j' : ℕ)) Fk *
        (if (j : ℕ) < e then (if j' = j then 1 else 0)
          else if (j' : ℕ) ≤ (j : ℕ) then P.coeff ((j : ℕ) - (j' : ℕ)) else 0)) = _
    by_cases hj : (j : ℕ) < e
    · simp only [hj, if_true, Matrix.of_apply]
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl, mul_one]
      · intro b _ hb
        rw [if_neg hb, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    · simp only [hj, if_false, Matrix.of_apply]
      have hje : e ≤ (j : ℕ) := by omega
      have hjr : (j : ℕ) < r := j.isLt
      have hsub1 : Finset.range ((j : ℕ) + 1) ⊆ Finset.range r := by
        intro k hk
        rw [Finset.mem_range] at hk ⊢
        omega
      have hsub2 : Finset.range ((j : ℕ) + 1)
          ⊆ Finset.range (n + (i : ℕ) + (j : ℕ) + 1) := by
        intro k hk
        rw [Finset.mem_range] at hk ⊢
        omega
      have hzero1 : ∀ k ∈ Finset.range r, k ∉ Finset.range ((j : ℕ) + 1) →
          PowerSeries.coeff (n + (i : ℕ) + k) Fk *
            (if k ≤ (j : ℕ) then P.coeff ((j : ℕ) - k) else 0) = 0 := by
        intro k _ hk
        rw [Finset.mem_range, not_lt] at hk
        rw [if_neg (by omega), mul_zero]
      have hzero2 : ∀ u ∈ Finset.range (n + (i : ℕ) + (j : ℕ) + 1),
          u ∉ Finset.range ((j : ℕ) + 1) →
          PowerSeries.coeff u ((P : K⟦X⟧)) *
            PowerSeries.coeff (n + (i : ℕ) + (j : ℕ) - u) Fk = 0 := by
        intro u _ hu
        rw [Finset.mem_range, not_lt] at hu
        rw [Polynomial.coeff_coe, P.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      calc ∑ j' : Fin r, PowerSeries.coeff (n + (i : ℕ) + (j' : ℕ)) Fk *
            (if (j' : ℕ) ≤ (j : ℕ) then P.coeff ((j : ℕ) - (j' : ℕ)) else 0)
          = ∑ k ∈ Finset.range r, PowerSeries.coeff (n + (i : ℕ) + k) Fk *
              (if k ≤ (j : ℕ) then P.coeff ((j : ℕ) - k) else 0) :=
            Fin.sum_univ_eq_sum_range
              (fun k ↦ PowerSeries.coeff (n + (i : ℕ) + k) Fk *
                (if k ≤ (j : ℕ) then P.coeff ((j : ℕ) - k) else 0)) r
        _ = ∑ k ∈ Finset.range ((j : ℕ) + 1), PowerSeries.coeff (n + (i : ℕ) + k) Fk *
              P.coeff ((j : ℕ) - k) := by
            rw [← Finset.sum_subset hsub1 hzero1]
            exact Finset.sum_congr rfl fun k hk ↦ by
              rw [if_pos (by have := Finset.mem_range.mp hk; omega)]
        _ = ∑ u ∈ Finset.range ((j : ℕ) + 1),
              P.coeff u * PowerSeries.coeff (n + (i : ℕ) + ((j : ℕ) - u)) Fk := by
            rw [← Finset.sum_range_reflect
              (fun u ↦ P.coeff u * PowerSeries.coeff (n + (i : ℕ) + ((j : ℕ) - u)) Fk)
              ((j : ℕ) + 1)]
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            have hk' : k ≤ (j : ℕ) := by have := Finset.mem_range.mp hk; omega
            rw [show (j : ℕ) + 1 - 1 - k = (j : ℕ) - k from by omega,
              show n + (i : ℕ) + ((j : ℕ) - ((j : ℕ) - k)) = n + (i : ℕ) + k from by omega]
            ring
        _ = PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) ((P : K⟦X⟧) * Fk) := by
            rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
              ← Finset.sum_subset hsub2 hzero2]
            refine Finset.sum_congr rfl fun u hu ↦ ?_
            have hu' : u ≤ (j : ℕ) := by have := Finset.mem_range.mp hu; omega
            rw [Polynomial.coeff_coe,
              show n + (i : ℕ) + (j : ℕ) - u = n + (i : ℕ) + ((j : ℕ) - u) from by omega]
  rw [hankelMinor, ← hmul, Matrix.det_mul, det_dworkColumnMatrix P hP0, mul_one]
end ColumnTransform
section PadicBound
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
private theorem card_filter_val_lt (e r : ℕ) (her : e ≤ r) :
    (Finset.univ.filter (fun j : Fin r ↦ (j : ℕ) < e)).card = e := by
  classical
  have hbij : (Finset.univ.filter (fun j : Fin r ↦ (j : ℕ) < e)).card
      = (Finset.range e).card := by
    refine Finset.card_bij (fun (j : Fin r) _ ↦ (j : ℕ)) ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro j₁ _ j₂ _ h
      exact Fin.val_injective h
    · intro k hk
      have hkr : k < r := by have := Finset.mem_range.mp hk; omega
      exact ⟨⟨k, hkr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hk⟩, rfl⟩
  rw [hbij, Finset.card_range]
theorem hankelMinor_padic_bound (Fk : K⟦X⟧) (P : Polynomial K) (hP0 : P.coeff 0 = 1)
    {e : ℕ} (hPe : P.natDegree ≤ e) (hFk : ∀ m, ‖PowerSeries.coeff m Fk‖ ≤ 1)
    {cB ρ : ℝ} (hcB : 0 ≤ cB) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hbnd : ∀ m, ‖PowerSeries.coeff m ((P : K⟦X⟧) * Fk)‖ ≤ cB * ρ ^ m)
    {r : ℕ} (her : e ≤ r) (n : ℕ) :
    ‖hankelMinor Fk r n‖ ≤ (cB * ρ ^ n) ^ (r - e) := by
  classical
  have htnn : (0 : ℝ) ≤ cB * ρ ^ n := by positivity
  rw [hankelMinor_eq_det_columnTransform Fk P hP0 hPe n, Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (M := K) (by positivity) ?_
  intro σ _
  have hsign : ‖((Equiv.Perm.sign σ : ℤ) : K)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  rw [norm_mul, hsign, one_mul]
  have hentry : ∀ j : Fin r,
      ‖(Matrix.of fun i j : Fin r ↦
          if (j : ℕ) < e then PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) Fk
          else PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) ((P : K⟦X⟧) * Fk)) (σ j) j‖
        ≤ if (j : ℕ) < e then 1 else cB * ρ ^ n := by
    intro j
    show ‖if (j : ℕ) < e then PowerSeries.coeff (n + ((σ j : Fin r) : ℕ) + (j : ℕ)) Fk
        else PowerSeries.coeff (n + ((σ j : Fin r) : ℕ) + (j : ℕ)) ((P : K⟦X⟧) * Fk)‖
      ≤ if (j : ℕ) < e then 1 else cB * ρ ^ n
    split
    · exact hFk _
    · refine (hbnd _).trans ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hρ0 hρ1 (by omega : n ≤ n + ((σ j : Fin r) : ℕ) + (j : ℕ))) hcB
  calc ‖∏ j : Fin r, (Matrix.of fun i j : Fin r ↦
          if (j : ℕ) < e then PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) Fk
          else PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) ((P : K⟦X⟧) * Fk)) (σ j) j‖
      ≤ ∏ j : Fin r, ‖(Matrix.of fun i j : Fin r ↦
          if (j : ℕ) < e then PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) Fk
          else PowerSeries.coeff (n + (i : ℕ) + (j : ℕ)) ((P : K⟦X⟧) * Fk)) (σ j) j‖ :=
        Finset.norm_prod_le _ _
    _ ≤ ∏ j : Fin r, (if (j : ℕ) < e then 1 else cB * ρ ^ n) :=
        Finset.prod_le_prod (fun j _ ↦ norm_nonneg _) (fun j _ ↦ hentry j)
    _ = (cB * ρ ^ n) ^ (r - e) := by
        rw [Finset.prod_ite (fun _ ↦ (1 : ℝ)) (fun _ ↦ cB * ρ ^ n)]
        simp only [Finset.prod_const, one_pow, one_mul]
        congr 1
        have hsplit := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin r))) (p := fun j : Fin r ↦ (j : ℕ) < e)
        rw [card_filter_val_lt e r her, Finset.card_univ, Fintype.card_fin] at hsplit
        omega
end PadicBound
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
section ProductFormula
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
private theorem norm_intCast_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime)
    (hplt : ‖(p : K)‖ < 1) {N : ℤ} (hdvd : ¬ ((p : ℤ) ∣ N)) : ‖(N : K)‖ = 1 := by
  have hle : ‖(N : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K N
  refine le_antisymm hle ?_
  have hgcd : Int.gcd N (p : ℤ) = 1 := by
    have hdvd' : ¬ (p ∣ N.natAbs) := by
      intro h
      exact hdvd (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
    have hcop := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd'
    simpa [Int.gcd] using hcop.symm
  obtain ⟨a, b, hab⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  by_contra hcon
  rw [not_le] at hcon
  have ha := IsUltrametricDist.norm_intCast_le_one K a
  have hb := IsUltrametricDist.norm_intCast_le_one K b
  have hcast : (1 : K) = (a : K) * (N : K) + (b : K) * (p : K) := by
    have := congrArg (fun x : ℤ ↦ (x : K)) hab
    push_cast at this
    exact this.symm
  have hone : (1 : ℝ) ≤ max (‖(a : K)‖ * ‖(N : K)‖) (‖(b : K)‖ * ‖(p : K)‖) := by
    have hmax := IsUltrametricDist.norm_add_le_max ((a : K) * (N : K)) ((b : K) * (p : K))
    rw [norm_mul, norm_mul] at hmax
    rw [← norm_one (α := K), hcast]
    exact hmax
  rcases max_cases (‖(a : K)‖ * ‖(N : K)‖) (‖(b : K)‖ * ‖(p : K)‖) with ⟨hmax, _⟩ | ⟨hmax, _⟩ <;>
    rw [hmax] at hone
  · nlinarith [norm_nonneg ((a : K)), norm_nonneg ((N : K))]
  · nlinarith [norm_nonneg ((b : K)), norm_nonneg ((p : K))]
theorem one_le_norm_mul_abs_intCast {p : ℕ} (hp : p.Prime)
    (hpnorm : ((p : ℝ))⁻¹ ≤ ‖(p : K)‖) (hplt : ‖(p : K)‖ < 1) :
    ∀ N : ℤ, N ≠ 0 → 1 ≤ ‖(N : K)‖ * |(N : ℝ)| := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpmul : (1 : ℝ) ≤ (p : ℝ) * ‖(p : K)‖ := by
    have h := mul_le_mul_of_nonneg_left hpnorm hppos.le
    rwa [mul_inv_cancel₀ hppos.ne'] at h
  have key : ∀ k : ℕ, ∀ N : ℤ, N.natAbs = k → N ≠ 0 → 1 ≤ ‖(N : K)‖ * |(N : ℝ)| := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
        intro N hk hN
        by_cases hdvd : (p : ℤ) ∣ N
        · obtain ⟨M, rfl⟩ := hdvd
          have hM : M ≠ 0 := by
            rintro rfl
            exact hN (by ring)
          have hpabs : ((p : ℤ)).natAbs = p := Int.natAbs_natCast p
          have hMlt : M.natAbs < k := by
            rw [← hk, Int.natAbs_mul, hpabs]
            have hMpos : 0 < M.natAbs := Int.natAbs_pos.mpr hM
            calc M.natAbs = 1 * M.natAbs := (one_mul _).symm
              _ < p * M.natAbs := (Nat.mul_lt_mul_right hMpos).mpr hp.one_lt
          have hIH := ih M.natAbs hMlt M rfl hM
          have hcast1 : (((p : ℤ) * M : ℤ) : K) = (p : K) * (M : K) := by push_cast; ring
          have hcast2 : (((p : ℤ) * M : ℤ) : ℝ) = (p : ℝ) * (M : ℝ) := by push_cast; ring
          rw [hcast1, hcast2, norm_mul, abs_mul, abs_of_pos hppos]
          calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
            _ ≤ ((p : ℝ) * ‖(p : K)‖) * (‖(M : K)‖ * |(M : ℝ)|) :=
                mul_le_mul hpmul hIH zero_le_one (by positivity)
            _ = ‖(p : K)‖ * ‖(M : K)‖ * ((p : ℝ) * |(M : ℝ)|) := by ring
        · rw [norm_intCast_eq_one_of_not_dvd hp hplt hdvd, one_mul]
          have hone : (1 : ℤ) ≤ |N| := Int.one_le_abs hN
          rw [← Int.cast_abs]
          exact_mod_cast hone
  exact fun N hN ↦ key N.natAbs N rfl hN
end ProductFormula
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries Finset
open scoped Polynomial
namespace FiniteFields.Dwork
section Criterion
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [CharZero K]
omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem hankelMinor_map (F : ℚ⟦X⟧) (r n : ℕ) :
    hankelMinor (PowerSeries.map (algebraMap ℚ K) F) r n
      = algebraMap ℚ K (hankelMinor F r n) := by
  rw [hankelMinor, hankelMinor, RingHom.map_det]
  congr 1
omit [CompleteSpace K] in
theorem hankelMinor_eq_zero_of_productFormula {p : ℕ} (hp : p.Prime)
    (hpnorm : ((p : ℝ))⁻¹ ≤ ‖(p : K)‖) (hplt : ‖(p : K)‖ < 1)
    (F : ℚ⟦X⟧) (z : ℕ → ℤ) (hz : ∀ m, PowerSeries.coeff m F = (z m : ℚ)) (r n : ℕ)
    (hsmall : ‖hankelMinor (PowerSeries.map (algebraMap ℚ K) F) r n‖ *
        |((hankelMinor F r n : ℚ) : ℝ)| < 1) :
    hankelMinor F r n = 0 := by
  classical
  have hz1 : ∀ m : ℕ, ((1 : ℤ) : ℚ) ^ (m + 1) * PowerSeries.coeff m F = (z m : ℚ) := by
    intro m; rw [hz m]; norm_num
  have hden := hankelMinor_denominator_bound F 1 z hz1 r n
  simp only [Int.cast_one, one_pow, one_mul] at hden
  set N : ℤ := (Matrix.of fun i j : Fin r ↦ z (n + (i : ℕ) + (j : ℕ))).det with hN
  have hQ : hankelMinor F r n = (N : ℚ) := hden.symm
  have hK : hankelMinor (PowerSeries.map (algebraMap ℚ K) F) r n = (N : K) := by
    rw [hankelMinor_map, hQ, map_intCast]
  have hR : ((hankelMinor F r n : ℚ) : ℝ) = (N : ℝ) := by rw [hQ, Rat.cast_intCast]
  rw [hK, hR] at hsmall
  have hNzero : N = 0 := by
    by_contra hcon
    exact absurd hsmall (not_lt.mpr (one_le_norm_mul_abs_intCast hp hpnorm hplt N hcon))
  rw [hQ, hNzero, Int.cast_zero]
end Criterion
end FiniteFields.Dwork
end
end
open PowerSeries Finset
open scoped Polynomial
open FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [CharZero K]
theorem solution {p : ℕ} (hp : p.Prime)
    (hpnorm : ((p : ℝ))⁻¹ ≤ ‖(p : K)‖) (hplt : ‖(p : K)‖ < 1)
    (F : ℚ⟦X⟧) (z : ℕ → ℤ) (hz : ∀ m, PowerSeries.coeff m F = (z m : ℚ))
    {C B : ℚ} (hB : 1 ≤ B) (hgrowth : ∀ m : ℕ, |PowerSeries.coeff m F| ≤ C * B ^ m)
    (hmero : IsPadicMeromorphic (PowerSeries.map (algebraMap ℚ K) F)) :
    IsRationalPowerSeries F := by
  classical
  rw [isRationalPowerSeries_iff_fixedSizeHankelEventuallyZero]
  obtain ⟨G, H, hG, hH, hH1, hmulGH⟩ := hmero
  have hC0 : (0 : ℚ) ≤ C := by
    have := hgrowth 0
    rw [pow_zero, mul_one] at this
    exact le_trans (abs_nonneg _) this
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le zero_lt_one hBR
  have hFkball : ∀ m, ‖PowerSeries.coeff m (PowerSeries.map (algebraMap ℚ K) F)‖ ≤ 1 := by
    intro m
    rw [PowerSeries.coeff_map, hz m]
    rw [map_intCast]
    exact IsUltrametricDist.norm_intCast_le_one K (z m)
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm K 1
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; linarith
  have hϖ0ne : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hϖ0pos : 0 < ‖x⁻¹‖ := norm_pos_iff.mpr hϖ0ne
  have hϖ0lt : ‖x⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one_iff₀]
    exact Or.inr hx
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ‖x⁻¹‖ ^ j * (B : ℝ) < 1 := by
    have htend := (tendsto_pow_atTop_nhds_zero_of_lt_one hϖ0pos.le hϖ0lt).mul_const (B : ℝ)
    rw [zero_mul] at htend
    obtain ⟨j, hjj⟩ := (Metric.tendsto_atTop.mp htend 1 zero_lt_one)
    refine ⟨j, ?_⟩
    have := hjj j le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  set ϖ : K := x⁻¹ ^ j with hϖdef
  have hϖne : ϖ ≠ 0 := pow_ne_zero _ hϖ0ne
  have hϖnorm : ‖ϖ‖ = ‖x⁻¹‖ ^ j := by rw [hϖdef, norm_pow]
  have hρpos : 0 < ‖ϖ‖ := by rw [hϖnorm]; positivity
  have hρB : ‖ϖ‖ * (B : ℝ) < 1 := by rw [hϖnorm]; exact hj
  have hρ1 : ‖ϖ‖ < 1 := by nlinarith
  obtain ⟨P, cB, hP0, hcB0, hPbnd⟩ :=
    exists_padicPolynomialWitness hG hH hH1 hmulGH hϖne hρ1
  set e := P.natDegree with hedef
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℕ, ∀ r, r0 ≤ r → (‖ϖ‖ * (B : ℝ)) ^ r < ‖ϖ‖ ^ e := by
    have htend := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hρB
    obtain ⟨r0, hr0⟩ := Metric.tendsto_atTop.mp htend (‖ϖ‖ ^ e) (by positivity)
    refine ⟨r0, fun r hr ↦ ?_⟩
    have := hr0 r hr
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  set r := max (e + 1) r0 with hrdef
  have her : e < r := lt_of_lt_of_le (Nat.lt_succ_self e) (le_max_left _ _)
  have hrpos : 0 < r := by omega
  set κ : ℝ := ‖ϖ‖ ^ (r - e) * (B : ℝ) ^ r with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ < 1 := by
    have hsplit : (‖ϖ‖ * (B : ℝ)) ^ r = ‖ϖ‖ ^ e * κ := by
      rw [hκdef, mul_pow,
        show ‖ϖ‖ ^ e * (‖ϖ‖ ^ (r - e) * (B : ℝ) ^ r)
          = (‖ϖ‖ ^ e * ‖ϖ‖ ^ (r - e)) * (B : ℝ) ^ r from by ring,
        ← pow_add, show e + (r - e) = r from by omega]
    have hlt := hr0 r (le_max_right _ _)
    rw [hsplit] at hlt
    have hpe : (0 : ℝ) < ‖ϖ‖ ^ e := by positivity
    nlinarith
  set D : ℝ := cB ^ (r - e) * ((Nat.factorial r : ℝ) * (C : ℝ) ^ r * (B : ℝ) ^ (r * (r - 1)))
    with hDdef
  have hD0 : 0 ≤ D := by
    have hCR : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC0
    rw [hDdef]; positivity
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ n, N0 ≤ n → D * κ ^ n < 1 := by
    have htend := (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul D
    rw [mul_zero] at htend
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp htend 1 zero_lt_one
    refine ⟨N0, fun n hn ↦ ?_⟩
    have := hN0 n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  refine ⟨r, N0, hrpos, fun n hn ↦ ?_⟩
  refine hankelMinor_eq_zero_of_productFormula hp hpnorm hplt F z hz r n ?_
  have hpad : ‖hankelMinor (PowerSeries.map (algebraMap ℚ K) F) r n‖
      ≤ (cB * ‖ϖ‖ ^ n) ^ (r - e) :=
    hankelMinor_padic_bound _ P hP0 le_rfl hFkball hcB0 hρpos.le hρ1.le hPbnd her.le n
  have harch : |((hankelMinor F r n : ℚ) : ℝ)|
      ≤ (Nat.factorial r : ℝ) * (C : ℝ) ^ r * (B : ℝ) ^ (r * n + r * (r - 1)) := by
    have hq := hankelMinor_archimedean_bound F hgrowth r n
    have := (Rat.cast_le (K := ℝ)).mpr hq
    rw [Rat.cast_abs] at this
    push_cast at this
    exact this
  have hprod : ‖hankelMinor (PowerSeries.map (algebraMap ℚ K) F) r n‖ *
      |((hankelMinor F r n : ℚ) : ℝ)| ≤ D * κ ^ n := by
    refine le_trans (mul_le_mul hpad harch (abs_nonneg _) (by positivity)) (le_of_eq ?_)
    have h1 : (cB * ‖ϖ‖ ^ n) ^ (r - e) = cB ^ (r - e) * ‖ϖ‖ ^ ((r - e) * n) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm]
    have h2 : (B : ℝ) ^ (r * n + r * (r - 1))
        = (B : ℝ) ^ (r * n) * (B : ℝ) ^ (r * (r - 1)) := pow_add _ _ _
    have h3 : κ ^ n = ‖ϖ‖ ^ ((r - e) * n) * (B : ℝ) ^ (r * n) := by
      rw [hκdef, mul_pow, ← pow_mul, ← pow_mul]
    rw [h1, h2, h3, hDdef]
    ring
  exact lt_of_le_of_lt hprod (hN0 n hn)
