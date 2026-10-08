-- Prove2me | solution 1 for BoydADMM.Consensus.general_dual_sums_zero
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:27:38.00512+00:00
-- url     : https://prove2.me/submissions/ae240c2f-d225-4678-80e0-2451ccdc1cef

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


open scoped BigOperators InnerProductSpace
open BoydADMM.Consensus

namespace NProof

lemma finite_quad_gap {ι : Type*} (s : Finset ι) (hs : 0 < s.card)
    (ρ : ℝ) (hρ : 0 < ρ) (x y : ι → ℝ) (t : ℝ) :
    let c := (∑ p ∈ s, (x p+(1/ρ)*y p)) / (s.card : ℝ)
    (∑ p ∈ s, (-y p*t+ρ/2*(x p-t)^2)) =
      (∑ p ∈ s, (-y p*c+ρ/2*(x p-c)^2)) +
        ((s.card : ℝ)*ρ/2)*(t-c)^2 := by
  classical
  dsimp only
  let c := (∑ p ∈ s, (x p+(1/ρ)*y p)) / (s.card : ℝ)
  have hk : (s.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have hc : (s.card : ℝ)*c = (∑ p ∈ s, x p)+(1/ρ)*(∑ p ∈ s, y p) := by
    dsimp [c]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    field_simp
  have hc' : ρ*((s.card : ℝ)*c) = ρ*(∑ p ∈ s, x p)+(∑ p ∈ s, y p) := by
    rw [hc, mul_add, ← mul_assoc, mul_one_div_cancel (ne_of_gt hρ), one_mul]
  have hsum : ∑ p ∈ s, (ρ*(c-x p)-y p) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    nlinarith [hc']
  have he (p : ι) : -y p*t+ρ/2*(x p-t)^2 =
      (-y p*c+ρ/2*(x p-c)^2)+ρ/2*(t-c)^2+(ρ*(c-x p)-y p)*(t-c) := by ring
  change (∑ p ∈ s, _) = (∑ p ∈ s, (-y p*c+ρ/2*(x p-c)^2))+
    ((s.card : ℝ)*ρ/2)*(t-c)^2
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  ring

lemma finite_quad_min {ι : Type*} (s : Finset ι) (hs : 0 < s.card)
    (ρ : ℝ) (hρ : 0 < ρ) (x y : ι → ℝ) (t : ℝ) :
    let c := (∑ p ∈ s, (x p+(1/ρ)*y p)) / (s.card : ℝ)
    (∑ p ∈ s, (-y p*c+ρ/2*(x p-c)^2)) ≤ (∑ p ∈ s, (-y p*t+ρ/2*(x p-t)^2)) ∧
      ((∑ p ∈ s, (-y p*t+ρ/2*(x p-t)^2)) = (∑ p ∈ s, (-y p*c+ρ/2*(x p-c)^2)) → t=c) := by
  dsimp only
  have h := finite_quad_gap s hs ρ hρ x y t
  dsimp only at h
  have hp : 0 < (s.card : ℝ)*ρ/2 := by positivity
  have hn := sq_nonneg (t-(∑ p ∈ s, (x p+(1/ρ)*y p))/(s.card : ℝ))
  constructor
  · nlinarith
  · intro he
    have hz : (t-(∑ p ∈ s, (x p+(1/ρ)*y p))/(s.card : ℝ))^2=0 := by nlinarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

lemma general_obj_coords {n N : ℕ} {nl : Fin N → ℕ}
    (G : (i : Fin N) → Fin (nl i) → Fin n) (ρ : ℝ)
    (x y : (i : Fin N) → EuclideanSpace ℝ (Fin (nl i))) (z : EuclideanSpace ℝ (Fin n)) :
    (∑ i, (-⟪y i,ztil G z i⟫_ℝ + ρ/2*‖x i-ztil G z i‖^2)) =
      ∑ g, ∑ p ∈ entriesOf G g, (-y p.1 p.2*z g+ρ/2*(x p.1 p.2-z g)^2) := by
  classical
  calc
    _ = ∑ i, ∑ j, (-y i j*z (G i j)+ρ/2*(x i j-z (G i j))^2) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [PiLp.inner_apply, norm_sq_coords, ztil, Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_comm]
    _ = ∑ p : (Σ i : Fin N, Fin (nl i)),
        (-y p.1 p.2*z (G p.1 p.2)+ρ/2*(x p.1 p.2-z (G p.1 p.2))^2) := by
      rw [Finset.sum_sigma']
      rfl
    _ = ∑ g, ∑ p ∈ entriesOf G g,
        (-y p.1 p.2*z (G p.1 p.2)+ρ/2*(x p.1 p.2-z (G p.1 p.2))^2) := by
      exact (Finset.sum_fiberwise Finset.univ
        (fun p : (Σ i : Fin N, Fin (nl i)) => G p.1 p.2) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro p hp
      have hG : G p.1 p.2 = g := (Finset.mem_filter.mp hp).2
      rw [hG]

lemma general_average {n N : ℕ} {nl : Fin N → ℕ}
    (G : (i : Fin N) → Fin (nl i) → Fin n) (hG : ∀ g, 1 ≤ kg G g) (ρ : ℝ) (hρ : 0 < ρ)
    (x y : (i : Fin N) → EuclideanSpace ℝ (Fin (nl i))) (z : EuclideanSpace ℝ (Fin n)) :
    (∀ z' : EuclideanSpace ℝ (Fin n),
        ∑ i, (-⟪y i, ztil G z i⟫_ℝ + (ρ / 2) * ‖x i - ztil G z i‖ ^ 2) ≤
          ∑ i, (-⟪y i, ztil G z' i⟫_ℝ + (ρ / 2) * ‖x i - ztil G z' i‖ ^ 2)) ↔
      ∀ g, z g = (∑ p ∈ entriesOf G g, (x p.1 p.2 + (1 / ρ) * y p.1 p.2)) / (kg G g : ℝ) := by
  simp_rw [general_obj_coords]
  have h := separable_min (fun _ : Fin n => Set.univ)
    (fun g t => ∑ p ∈ entriesOf G g, (-y p.1 p.2*t+ρ/2*(x p.1 p.2-t)^2))
    (fun g => (∑ p ∈ entriesOf G g, (x p.1 p.2+(1/ρ)*y p.1 p.2))/(kg G g : ℝ))
    (fun _ => Set.mem_univ _) (fun g t _ => finite_quad_min (entriesOf G g) (hG g) ρ hρ
      (fun p => x p.1 p.2) (fun p => y p.1 p.2) t) z
  simpa only [Set.mem_univ, implies_true, true_and, forall_const] using h

lemma general_dual {n N : ℕ} {nl : Fin N → ℕ}
    (G : (i : Fin N) → Fin (nl i) → Fin n) (hG : ∀ g, 1 ≤ kg G g) (ρ : ℝ) (hρ : 0 < ρ)
    (Cf : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (nl i))))
    (f : (i : Fin N) → EuclideanSpace ℝ (Fin (nl i)) → ℝ)
    (x : ℕ → (i : Fin N) → EuclideanSpace ℝ (Fin (nl i))) (z : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → (i : Fin N) → EuclideanSpace ℝ (Fin (nl i)))
    (hrun : IsGeneralConsensusADMMRun G Cf f ρ x z y) :
    (∀ k, 1 ≤ k → ∀ g, ∑ p ∈ entriesOf G g, y k p.1 p.2 = 0) ∧
    (∀ k, 1 ≤ k → ∀ g,
      z (k + 1) g = (1 / (kg G g : ℝ)) * ∑ p ∈ entriesOf G g, x (k + 1) p.1 p.2) := by
  have hz (k : ℕ) (g : Fin n) :=
    ((general_average G hG ρ hρ (x (k+1)) (y k) (z (k+1))).mp (hrun.z_min k)) g
  have hy (k : ℕ) (g : Fin n) : ∑ p ∈ entriesOf G g, y (k+1) p.1 p.2 = 0 := by
    have he (p : (Σ i : Fin N, Fin (nl i))) (hp : p ∈ entriesOf G g) :
        y (k+1) p.1 p.2 = y k p.1 p.2 + ρ*(x (k+1) p.1 p.2-z (k+1) g) := by
      have hG' : G p.1 p.2 = g := (Finset.mem_filter.mp hp).2
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (nl p.1)) => v p.2) (hrun.y_succ k p.1)
      simpa [ztil, hG'] using h
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
    have hk : (kg G g : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hG g))
    have heq := (eq_div_iff hk).mp (hz k g)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at heq
    have hh := congrArg (fun v : ℝ => ρ*v) heq
    simp only [mul_add, ← mul_assoc, mul_one_div_cancel (ne_of_gt hρ), one_mul] at hh
    change _ + ρ*(_-(kg G g : ℝ)*_) = 0
    nlinarith [hh]
  have hy' (k : ℕ) (hk : 1 ≤ k) (g : Fin n) : ∑ p ∈ entriesOf G g, y k p.1 p.2=0 := by
    obtain ⟨l,rfl⟩ : ∃ l, k=l+1 := ⟨k-1, by omega⟩
    exact hy l g
  refine ⟨hy', ?_⟩
  intro k hk g
  rw [hz, Finset.sum_add_distrib, ← Finset.mul_sum, hy' k hk g]
  ring

end NProof


/-- §7.2, p. 55: along every run of general form consensus ADMM with `ρ > 0` and every
`k_g ≥ 1`, after the first iteration (`k ≥ 1`) the dual entries attached to each global index
sum to zero, `∑_{G(i,j)=g} (y_i^k)_j = 0`, and the `z`-update is plain local averaging,
`z_g^{k+1} = (1/k_g) ∑_{G(i,j)=g} (x_i^{k+1})_j`. -/
theorem solution {n N : ℕ} {nl : Fin N → ℕ}
    (G : (i : Fin N) → Fin (nl i) → Fin n) (hG : ∀ g, 1 ≤ kg G g) (ρ : ℝ) (hρ : 0 < ρ)
    (Cf : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (nl i))))
    (f : (i : Fin N) → EuclideanSpace ℝ (Fin (nl i)) → ℝ)
    (x : ℕ → (i : Fin N) → EuclideanSpace ℝ (Fin (nl i))) (z : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → (i : Fin N) → EuclideanSpace ℝ (Fin (nl i)))
    (hrun : IsGeneralConsensusADMMRun G Cf f ρ x z y) :
    (∀ k, 1 ≤ k → ∀ g, ∑ p ∈ entriesOf G g, y k p.1 p.2 = 0) ∧
    (∀ k, 1 ≤ k → ∀ g,
      z (k + 1) g = (1 / (kg G g : ℝ)) * ∑ p ∈ entriesOf G g, x (k + 1) p.1 p.2) := by
  exact @NProof.general_dual n N nl G hG ρ hρ Cf f x z y hrun

