-- Prove2me | solution 1 for BoydADMM.Consensus.nonneg_prox_positive_part
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:26:51.895407+00:00
-- url     : https://prove2.me/submissions/0284f402-6a23-4d8b-9a7d-445d44b2e676

import Definitions.Def_BoydADMM_Consensus_Model


open scoped BigOperators InnerProductSpace
open BoydADMM.Consensus

namespace NProof

lemma avg_add {n N : ℕ} (a b : Fin N → EuclideanSpace ℝ (Fin n)) :
    avg (fun i => a i + b i) = avg a + avg b := by
  simp [avg, Finset.sum_add_distrib, smul_add]

lemma avg_sub {n N : ℕ} (a b : Fin N → EuclideanSpace ℝ (Fin n)) :
    avg (fun i => a i - b i) = avg a - avg b := by
  simp [avg, Finset.sum_sub_distrib, smul_sub]

lemma avg_smul {n N : ℕ} (r : ℝ) (a : Fin N → EuclideanSpace ℝ (Fin n)) :
    avg (fun i => r • a i) = r • avg a := by
  simp [avg, ← Finset.smul_sum, smul_smul, mul_comm]

lemma avg_const {n N : ℕ} (hN : 0 < N) (w : EuclideanSpace ℝ (Fin n)) :
    avg (fun _ : Fin N => w) = w := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp [avg, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hN0]

lemma sum_eq_smul_avg {n N : ℕ} (hN : 0 < N)
    (a : Fin N → EuclideanSpace ℝ (Fin n)) :
    ∑ i, a i = (N : ℝ) • avg a := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp [avg, smul_smul, hN0]

lemma lift_avg {n N : ℕ} (hN : 0 < N)
    (a : Fin N → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n)) :
    avg (fun i => a i + w - avg a) = w := by
  rw [avg_sub, avg_add, avg_const hN, avg_const hN]
  abel

lemma variance {n N : ℕ} (hN : 0 < N)
    (a z : Fin N → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n))
    (hz : avg z = w) :
    ∑ i, ‖z i - a i‖ ^ 2 =
      (∑ i, ‖z i - (a i + w - avg a)‖ ^ 2) + ∑ _i : Fin N, ‖w - avg a‖ ^ 2 := by
  have hsum : ∑ i, (z i - (a i + w - avg a)) = 0 := by
    rw [sum_eq_smul_avg hN, avg_sub, hz, lift_avg hN, sub_self, smul_zero]
  have hi (i : Fin N) : z i - a i = (z i - (a i + w - avg a)) + (w - avg a) := by abel
  simp_rw [hi, norm_add_sq_real]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_inner, hsum, inner_zero_left,
    mul_zero, add_zero]

lemma fixed_average {n N : ℕ} (hN : 0 < N)
    (a z : Fin N → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n)) :
    (avg z = w ∧ ∀ z' : Fin N → EuclideanSpace ℝ (Fin n), avg z' = w →
        ∑ i, ‖z i - a i‖ ^ 2 ≤ ∑ i, ‖z' i - a i‖ ^ 2) ↔
      ∀ i, z i = a i + w - avg a := by
  constructor
  · rintro ⟨hz, hm⟩
    have h := hm (fun i => a i + w - avg a) (lift_avg hN a w)
    have hc (i : Fin N) : a i + w - avg a - a i = w - avg a := by abel
    simp_rw [hc] at h
    rw [variance hN a z w hz] at h
    have hs : ∑ i, ‖z i - (a i + w - avg a)‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg
      ‖z j - (a j + w - avg a)‖)).mp hs i (Finset.mem_univ i)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hi))
  · intro hz
    have he : z = (fun i => a i + w - avg a) := funext hz
    constructor
    · rw [he]; exact lift_avg hN a w
    · intro z' hz'
      rw [variance hN a z' w hz', he]
      have hc (i : Fin N) : a i + w - avg a - a i = w - avg a := by abel
      simp_rw [hc]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => sq_nonneg _)

end NProof


open scoped BigOperators InnerProductSpace
open BoydADMM.Consensus

namespace NProof

lemma norm_sq_coords {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖^2 = ∑ j, (x j)^2 := by
  simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]

lemma separable_min {n : ℕ} (D : Fin n → Set ℝ) (F : Fin n → ℝ → ℝ)
    (s : Fin n → ℝ) (hs : ∀ j, s j ∈ D j)
    (hm : ∀ j t, t ∈ D j → F j (s j) ≤ F j t ∧ (F j t = F j (s j) → t = s j))
    (z : EuclideanSpace ℝ (Fin n)) :
    ((∀ j, z j ∈ D j) ∧ ∀ z' : EuclideanSpace ℝ (Fin n), (∀ j, z' j ∈ D j) →
      ∑ j, F j (z j) ≤ ∑ j, F j (z' j)) ↔ ∀ j, z j = s j := by
  constructor
  · rintro ⟨hz, hmin⟩
    let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 s
    have hv : ∀ j, v j ∈ D j := hs
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)), F j (s j) ≤ F j (z j) :=
      fun j _ => (hm j (z j) (hz j)).1
    have he : (∑ j, F j (s j)) = ∑ j, F j (z j) :=
      le_antisymm (Finset.sum_le_sum hle) (hmin v hv)
    have hi := (Finset.sum_eq_sum_iff_of_le hle).mp he
    intro j
    exact (hm j (z j) (hz j)).2 (hi j (Finset.mem_univ j)).symm
  · intro hz
    refine ⟨fun j => (hz j).symm ▸ hs j, ?_⟩
    intro z' hz'
    apply Finset.sum_le_sum
    intro j _
    rw [hz j]
    exact (hm j (z' j) (hz' j)).1

lemma l1_subgradient_gap (lam r v s q t : ℝ)
    (hqL : -lam ≤ q) (hqU : q ≤ lam)
    (hqs : q*s = lam*|s|) (hstat : r*(s-v)+q=0) :
    lam*|s| + r/2*(s-v)^2 + r/2*(t-s)^2 ≤ lam*|t| + r/2*(t-v)^2 := by
  have habs : q*t ≤ lam*|t| := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_right hqU ht
    · have ht' : t ≤ 0 := le_of_not_ge ht
      rw [abs_of_nonpos ht']
      nlinarith [mul_le_mul_of_nonpos_right hqL ht']
  have he : (r*(s-v)+q)*(t-s)=0 := by rw [hstat, zero_mul]
  nlinarith

lemma soft_gap (lam r v t : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    let s := BoydADMM.Prox.softThreshold (lam/r) v
    lam*|s| + r/2*(s-v)^2 + r/2*(t-s)^2 ≤ lam*|t| + r/2*(t-v)^2 := by
  have hrk : r*(lam/r)=lam := by field_simp
  have hk : 0 < lam/r := div_pos hlam hr
  unfold BoydADMM.Prox.softThreshold
  split_ifs with hpos hneg
  · apply l1_subgradient_gap lam r v (v-lam/r) lam t
    · linarith
    · rfl
    · rw [abs_of_pos (by linarith)]
    · nlinarith
  · apply l1_subgradient_gap lam r v (v+lam/r) (-lam) t
    · rfl
    · linarith
    · rw [abs_of_neg (by linarith)]; ring
    · nlinarith
  · apply l1_subgradient_gap lam r v 0 (r*v) t
    · have h := (mul_le_mul_of_nonneg_left (le_of_not_gt hneg) hr.le)
      nlinarith
    · have h := (mul_le_mul_of_nonneg_left (le_of_not_gt hpos) hr.le)
      nlinarith
    · simp
    · ring

lemma soft_min (lam r v t : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    let s := BoydADMM.Prox.softThreshold (lam/r) v
    lam*|s| + r/2*(s-v)^2 ≤ lam*|t| + r/2*(t-v)^2 ∧
      (lam*|t| + r/2*(t-v)^2 = lam*|s| + r/2*(s-v)^2 → t=s) := by
  dsimp only
  have h := soft_gap lam r v t hlam hr
  dsimp only at h
  have hn := sq_nonneg (t-BoydADMM.Prox.softThreshold (lam/r) v)
  constructor
  · nlinarith
  · intro he
    have hz : (t-BoydADMM.Prox.softThreshold (lam/r) v)^2 = 0 := by nlinarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

lemma positive_gap (r v t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
    r/2*(max v 0-v)^2 + r/2*(t-max v 0)^2 ≤ r/2*(t-v)^2 := by
  by_cases hv : 0 ≤ v
  · rw [max_eq_left hv]; nlinarith
  · have hv' : v ≤ 0 := le_of_not_ge hv
    rw [max_eq_right hv']
    nlinarith [mul_nonneg hr.le (mul_nonneg ht (neg_nonneg.mpr hv'))]

lemma positive_min (r v t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
    r/2*(max v 0-v)^2 ≤ r/2*(t-v)^2 ∧
      (r/2*(t-v)^2 = r/2*(max v 0-v)^2 → t=max v 0) := by
  have h := positive_gap r v t hr ht
  have hn := sq_nonneg (t-max v 0)
  constructor
  · nlinarith
  · intro he
    have hz : (t-max v 0)^2=0 := by nlinarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

lemma l1_soft {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (lam : ℝ) (hlam : 0 < lam)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    (∀ z' : EuclideanSpace ℝ (Fin n),
        lam * ∑ j, |z j| + ((N : ℝ) * ρ / 2) * ‖z - avg x - (1 / ρ) • avg y‖ ^ 2 ≤
          lam * ∑ j, |z' j| + ((N : ℝ) * ρ / 2) * ‖z' - avg x - (1 / ρ) • avg y‖ ^ 2) ↔
      ∀ j, z j = BoydADMM.Prox.softThreshold (lam / ((N : ℝ) * ρ)) ((avg x + (1 / ρ) • avg y) j) := by
  let v := avg x + (1/ρ) • avg y
  let r := (N : ℝ)*ρ
  have hr : 0 < r := by dsimp [r]; positivity
  have he (w : EuclideanSpace ℝ (Fin n)) :
      lam*∑ j, |w j| + r/2*‖w-avg x-(1/ρ) • avg y‖^2 =
      ∑ j, (lam*|w j| + r/2*(w j-v j)^2) := by
    rw [sub_sub, norm_sq_coords, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    rfl
  dsimp only [r] at he
  simp_rw [he]
  have h := separable_min (fun _ : Fin n => Set.univ)
    (fun j t => lam*|t|+r/2*(t-v j)^2)
    (fun j => BoydADMM.Prox.softThreshold (lam/r) (v j))
    (fun _ => Set.mem_univ _) (fun j t _ => soft_min lam r (v j) t hlam hr) z
  simpa only [Set.mem_univ, implies_true, true_and, forall_const] using h

lemma nonneg_positive {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    ((∀ j, 0 ≤ z j) ∧ ∀ z' : EuclideanSpace ℝ (Fin n), (∀ j, 0 ≤ z' j) →
        ((N : ℝ) * ρ / 2) * ‖z - avg x - (1 / ρ) • avg y‖ ^ 2 ≤
          ((N : ℝ) * ρ / 2) * ‖z' - avg x - (1 / ρ) • avg y‖ ^ 2) ↔
      ∀ j, z j = max ((avg x + (1 / ρ) • avg y) j) 0 := by
  let v := avg x + (1/ρ) • avg y
  let r := (N : ℝ)*ρ
  have hr : 0 < r := by dsimp [r]; positivity
  have he (w : EuclideanSpace ℝ (Fin n)) :
      r/2*‖w-avg x-(1/ρ) • avg y‖^2 = ∑ j, r/2*(w j-v j)^2 := by
    rw [sub_sub, norm_sq_coords, Finset.mul_sum]
    rfl
  dsimp only [r] at he
  simp_rw [he]
  exact separable_min (fun _ : Fin n => Set.Ici 0)
    (fun j t => r/2*(t-v j)^2) (fun j => max (v j) 0)
    (fun j => by change (0 : ℝ) ≤ max (v j) 0; exact le_max_right _ _)
    (fun j t ht => positive_min r (v j) t hr ht) z

end NProof


/-- §7.1.1, p. 52 (sign corrected): for `g` the indicator function of `ℝⁿ₊` (effective domain
`{z | z ≥ 0}`, value `0` there), the proximal step
`argmin_z (g(z) + (Nρ/2)‖z − x̄^{k+1} − (1/ρ)ȳ^k‖²)` has the unique solution
`z = (x̄^{k+1} + (1/ρ)ȳ^k)₊`, componentwise. The book prints `x̄^{k+1} − (1/ρ)ȳ^k`. -/
theorem solution {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    ((∀ j, 0 ≤ z j) ∧ ∀ z' : EuclideanSpace ℝ (Fin n), (∀ j, 0 ≤ z' j) →
        ((N : ℝ) * ρ / 2) * ‖z - avg x - (1 / ρ) • avg y‖ ^ 2 ≤
          ((N : ℝ) * ρ / 2) * ‖z' - avg x - (1 / ρ) • avg y‖ ^ 2) ↔
      ∀ j, z j = max ((avg x + (1 / ρ) • avg y) j) 0 := by
  exact @NProof.nonneg_positive n N hN ρ hρ x y z

