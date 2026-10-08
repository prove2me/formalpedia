-- Prove2me | solution 1 for BoydADMM.Consensus.regularized_z_update_prox
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:26:46.456349+00:00
-- url     : https://prove2.me/submissions/ff9ab289-9747-43dd-9e62-818a6566768e

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

lemma quadratic_block (ρ : ℝ) {n : ℕ} (x y c z : EuclideanSpace ℝ (Fin n)) :
    -⟪y,z⟫_ℝ + ρ/2 * ‖x-z‖^2 =
      (-⟪y,c⟫_ℝ + ρ/2 * ‖x-c‖^2) + ρ/2 * ‖z-c‖^2 +
        ⟪ρ • (c-x)-y,z-c⟫_ℝ := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq, real_inner_comm z c]
  ring

lemma consensus_gap {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    let c := avg x + (1 / ρ) • avg y
    (∑ i, (-⟪y i,z⟫_ℝ + ρ/2 * ‖x i-z‖^2)) =
      (∑ i, (-⟪y i,c⟫_ℝ + ρ/2 * ‖x i-c‖^2)) +
        ((N : ℝ) * ρ/2) * ‖z-c‖^2 := by
  dsimp only
  let c := avg x + (1 / ρ) • avg y
  have hc : avg (fun i => ρ • (c-x i)-y i) = 0 := by
    rw [avg_sub, avg_smul, avg_sub, avg_const hN]
    dsimp [c]
    rw [add_sub_cancel_left, smul_smul]
    simp [ne_of_gt hρ]
  have hs : ∑ i, (ρ • (c-x i)-y i) = 0 := by
    rw [sum_eq_smul_avg hN, hc, smul_zero]
  change (∑ i, _) = (∑ i, (-⟪y i,c⟫_ℝ + ρ/2 * ‖x i-c‖^2)) + _
  simp_rw [quadratic_block ρ (x _) (y _) c z]
  simp only [Finset.sum_add_distrib, ← sum_inner, hs, inner_zero_left, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma regularized_prox {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Cg : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    (z ∈ Cg ∧ ∀ z' ∈ Cg,
        g z + ∑ i, (-⟪y i, z⟫_ℝ + (ρ / 2) * ‖x i - z‖ ^ 2) ≤
          g z' + ∑ i, (-⟪y i, z'⟫_ℝ + (ρ / 2) * ‖x i - z'‖ ^ 2)) ↔
      (z ∈ Cg ∧ ∀ z' ∈ Cg,
        g z + ((N : ℝ) * ρ / 2) * ‖z - avg x - (1 / ρ) • avg y‖ ^ 2 ≤
          g z' + ((N : ℝ) * ρ / 2) * ‖z' - avg x - (1 / ρ) • avg y‖ ^ 2) := by
  constructor <;> rintro ⟨hz, hm⟩ <;> refine ⟨hz, ?_⟩ <;> intro z' hz'
  all_goals
    have h := hm z' hz'
    have h₁ := consensus_gap hN ρ hρ x y z
    have h₂ := consensus_gap hN ρ hρ x y z'
    dsimp only at h₁ h₂
    simp only [sub_sub] at *
    linarith

lemma consensus_average {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    (∀ z' : EuclideanSpace ℝ (Fin n),
        ∑ i, (f i (x i) + ⟪y i, x i - z⟫_ℝ + (ρ / 2) * ‖x i - z‖ ^ 2) ≤
          ∑ i, (f i (x i) + ⟪y i, x i - z'⟫_ℝ + (ρ / 2) * ‖x i - z'‖ ^ 2)) ↔
      z = avg x + (1 / ρ) • avg y := by
  let c := avg x + (1/ρ) • avg y
  have hp : 0 < (N : ℝ) * ρ / 2 := by positivity
  have he (v : EuclideanSpace ℝ (Fin n)) :
      (∑ i, (f i (x i) + ⟪y i, x i-v⟫_ℝ + ρ/2 * ‖x i-v‖^2)) =
        (∑ i, (f i (x i) + ⟪y i, x i⟫_ℝ)) +
          (∑ i, (-⟪y i,c⟫_ℝ + ρ/2 * ‖x i-c‖^2)) +
            ((N : ℝ) * ρ/2) * ‖v-c‖^2 := by
    calc
      _ = (∑ i, (f i (x i)+⟪y i,x i⟫_ℝ)) +
          (∑ i, (-⟪y i,v⟫_ℝ + ρ/2 * ‖x i-v‖^2)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [inner_sub_right]
        ring
      _ = _ := by rw [consensus_gap hN ρ hρ x y]; dsimp [c]; ring
  simp_rw [he]
  constructor
  · intro hm
    have h := hm c
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at h
    have hn : ‖z-c‖^2 ≤ 0 := by nlinarith
    have hz : ‖z-c‖ = 0 := by nlinarith [sq_nonneg ‖z-c‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro hz
    change z = c at hz
    rw [hz]
    intro z'
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    exact le_add_of_nonneg_right (mul_nonneg hp.le (sq_nonneg _))

lemma consensus_dual {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Cf : Fin N → Set (EuclideanSpace ℝ (Fin n))) (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → Fin N → EuclideanSpace ℝ (Fin n)) (z : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → Fin N → EuclideanSpace ℝ (Fin n)) (hrun : IsConsensusADMMRun Cf f ρ x z y) :
    (∀ k, avg (y (k + 1)) = 0) ∧
    (∀ k, 2 ≤ k → z k = avg (x k)) ∧
    (∀ k, 2 ≤ k → ∀ i, ∀ x' ∈ Cf i,
      f i (x (k + 1) i) + ⟪y k i, x (k + 1) i - avg (x k)⟫_ℝ +
          (ρ / 2) * ‖x (k + 1) i - avg (x k)‖ ^ 2 ≤
        f i x' + ⟪y k i, x' - avg (x k)⟫_ℝ + (ρ / 2) * ‖x' - avg (x k)‖ ^ 2) ∧
    (∀ k, 1 ≤ k → ∀ i, y (k + 1) i = y k i + ρ • (x (k + 1) i - avg (x (k + 1)))) := by
  have hz (k : ℕ) : z (k+1) = avg (x (k+1)) + (1/ρ) • avg (y k) := by
    rw [hrun.z_succ]
    change avg (fun i => x (k+1) i + (1/ρ) • y k i) = _
    rw [avg_add, avg_smul]
  have hy (k : ℕ) : avg (y (k+1)) = 0 := by
    have he : y (k+1) = fun i => y k i + ρ • (x (k+1) i-z (k+1)) :=
      funext (hrun.y_succ k)
    rw [he, avg_add, avg_smul, avg_sub, avg_const hN, hz]
    simp [sub_add_eq_sub_sub, smul_neg, smul_smul, ne_of_gt hρ]
  have hz' (k : ℕ) (hk : 2 ≤ k) : z k = avg (x k) := by
    obtain ⟨l, rfl⟩ : ∃ l, k = l+1+1 := ⟨k-2, by omega⟩
    rw [hz, hy]
    simp
  refine ⟨hy, hz', ?_, ?_⟩
  · intro k hk i x' hx'
    simpa only [hz' k hk] using hrun.x_min k i x' hx'
  · intro k hk i
    rw [hrun.y_succ, hz' (k+1) (by omega)]

end NProof


/-- §7.1.1, p. 52: for a regularizer `g` with effective domain `Cg`, the `z`-update (7.4)
`argmin_z (g(z) + ∑_i (−y_i^{kT} z + (ρ/2)‖x_i^{k+1} − z‖²))` has exactly the same
minimizers as the averaging-then-proximal step
`argmin_z (g(z) + (Nρ/2)‖z − x̄^{k+1} − (1/ρ)ȳ^k‖²)`. Here `x`, `y` stand for `x^{k+1}`, `y^k`. -/
theorem solution {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Cg : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    (z ∈ Cg ∧ ∀ z' ∈ Cg,
        g z + ∑ i, (-⟪y i, z⟫_ℝ + (ρ / 2) * ‖x i - z‖ ^ 2) ≤
          g z' + ∑ i, (-⟪y i, z'⟫_ℝ + (ρ / 2) * ‖x i - z'‖ ^ 2)) ↔
      (z ∈ Cg ∧ ∀ z' ∈ Cg,
        g z + ((N : ℝ) * ρ / 2) * ‖z - avg x - (1 / ρ) • avg y‖ ^ 2 ≤
          g z' + ((N : ℝ) * ρ / 2) * ‖z' - avg x - (1 / ρ) • avg y‖ ^ 2) := by
  exact @NProof.regularized_prox n N hN ρ hρ Cg g x y z

