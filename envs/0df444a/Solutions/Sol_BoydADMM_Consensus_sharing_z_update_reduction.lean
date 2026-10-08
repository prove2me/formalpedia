-- Prove2me | solution 1 for BoydADMM.Consensus.sharing_z_update_reduction
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:27:40.616235+00:00
-- url     : https://prove2.me/submissions/97c63aec-a883-443d-91e3-2044438a8e09

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

lemma sharing_lift_obj {n N : ℕ} (hN : 0 < N) (ρ : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin N → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n)) :
    sharingZObj g ρ a (fun i => a i + w - avg a) =
      g ((N : ℝ) • w) + ρ/2 * ∑ _i : Fin N, ‖w-avg a‖^2 := by
  unfold sharingZObj
  rw [sum_eq_smul_avg hN, lift_avg hN]
  have hc (i : Fin N) : a i+w-avg a-a i = w-avg a := by abel
  simp_rw [hc]

lemma sharing_lower {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a z : Fin N → EuclideanSpace ℝ (Fin n)) :
    g ((N : ℝ) • avg z) + ρ/2 * ∑ _i : Fin N, ‖avg z-avg a‖^2 ≤
      sharingZObj g ρ a z := by
  unfold sharingZObj
  rw [sum_eq_smul_avg hN, variance hN a z (avg z) rfl]
  have hs : 0 ≤ ∑ i, ‖z i - (a i+avg z-avg a)‖^2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

lemma sharing_one_iff {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Cg : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (a z : Fin N → EuclideanSpace ℝ (Fin n)) :
      ((∑ i, z i) ∈ Cg ∧ ∀ z' : Fin N → EuclideanSpace ℝ (Fin n), (∑ i, z' i) ∈ Cg →
          sharingZObj g ρ a z ≤ sharingZObj g ρ a z') ↔
        ((N : ℝ) • avg z ∈ Cg ∧
          (∀ w : EuclideanSpace ℝ (Fin n), (N : ℝ) • w ∈ Cg →
            g ((N : ℝ) • avg z) + (ρ / 2) * ∑ _i : Fin N, ‖avg z - avg a‖ ^ 2 ≤
              g ((N : ℝ) • w) + (ρ / 2) * ∑ _i : Fin N, ‖w - avg a‖ ^ 2) ∧
          ∀ i, z i = a i + avg z - avg a) := by
  constructor
  · rintro ⟨hmem, hm⟩
    have hf : ∀ i, z i = a i + avg z - avg a := by
      apply (fixed_average hN a z (avg z)).mp
      refine ⟨rfl, ?_⟩
      intro z' hz'
      have hsum : (∑ i, z' i) = ∑ i, z i := by
        rw [sum_eq_smul_avg hN z', sum_eq_smul_avg hN z, hz']
      have hh := hm z' (hsum.symm ▸ hmem)
      unfold sharingZObj at hh
      rw [hsum] at hh
      nlinarith
    refine ⟨(sum_eq_smul_avg hN z) ▸ hmem, ?_, hf⟩
    intro w hw
    have hc : (∑ i, (a i+w-avg a)) ∈ Cg := by
      rw [sum_eq_smul_avg hN, lift_avg hN]
      exact hw
    have hh := hm (fun i => a i+w-avg a) hc
    rw [sharing_lift_obj hN] at hh
    exact (sharing_lower hN ρ hρ g a z).trans hh
  · rintro ⟨hmem, hm, hf⟩
    refine ⟨(sum_eq_smul_avg hN z).symm ▸ hmem, ?_⟩
    intro z' hz'
    have he : z = (fun i => a i+avg z-avg a) := funext hf
    have hobj : sharingZObj g ρ a z =
        g ((N : ℝ) • avg z) + ρ/2 * ∑ _i : Fin N, ‖avg z-avg a‖^2 := by
      calc
        sharingZObj g ρ a z = sharingZObj g ρ a (fun i => a i+avg z-avg a) := by
          exact congrArg (sharingZObj g ρ a) he
        _ = _ := sharing_lift_obj hN ρ g a (avg z)
    rw [hobj]
    exact (hm (avg z') ((sum_eq_smul_avg hN z') ▸ hz')).trans
      (sharing_lower hN ρ hρ g a z')

lemma sharing_goal {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Cg : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∀ a z : Fin N → EuclideanSpace ℝ (Fin n),
      ((∑ i, z i) ∈ Cg ∧ ∀ z' : Fin N → EuclideanSpace ℝ (Fin n), (∑ i, z' i) ∈ Cg →
          sharingZObj g ρ a z ≤ sharingZObj g ρ a z') ↔
        ((N : ℝ) • avg z ∈ Cg ∧
          (∀ w : EuclideanSpace ℝ (Fin n), (N : ℝ) • w ∈ Cg →
            g ((N : ℝ) • avg z) + (ρ / 2) * ∑ _i : Fin N, ‖avg z - avg a‖ ^ 2 ≤
              g ((N : ℝ) • w) + (ρ / 2) * ∑ _i : Fin N, ‖w - avg a‖ ^ 2) ∧
          ∀ i, z i = a i + avg z - avg a)) ∧
    (∀ (Cf : Fin N → Set (EuclideanSpace ℝ (Fin n))) (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
      (x z u : ℕ → Fin N → EuclideanSpace ℝ (Fin n)),
      IsSharingADMMRun Cf f Cg g ρ x z u →
        ∀ k i, u (k + 1) i = avg (u k) + avg (x (k + 1)) - avg (z (k + 1))) := by
  refine ⟨sharing_one_iff hN ρ hρ Cg g, ?_⟩
  intro Cf f x z u hrun k i
  have hf := ((sharing_one_iff hN ρ hρ Cg g
    (fun j => u k j+x (k+1) j) (z (k+1))).mp ⟨hrun.z_mem k, hrun.z_min k⟩).2.2 i
  rw [hrun.u_succ, hf, avg_add]
  abel

end NProof


/-- §7.3, p. 57 (goal). Let `g` have effective domain `Cg`, `ρ > 0`, `N ≥ 1`.

(1) For any `a_1, …, a_N ∈ ℝⁿ`, `(z_1, …, z_N)` solves the sharing `z`-update
`minimize g(∑_i z_i) + (ρ/2)∑_i ‖z_i − a_i‖²` (over `∑_i z_i ∈ dom g`) iff its average `z̄` solves
the `n`-variable problem `minimize g(N z̄) + (ρ/2)∑_{i=1}^N ‖z̄ − ā‖²` (over `N z̄ ∈ dom g`) and
`z_i = a_i + z̄ − ā` for every `i` (7.13).

(2) Along every run of sharing ADMM, (7.14) holds: `u_i^{k+1} = ū^k + x̄^{k+1} − z̄^{k+1}` for every
`k` and `i`; in particular all `u_i^{k+1}` are equal. -/
theorem solution {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Cg : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∀ a z : Fin N → EuclideanSpace ℝ (Fin n),
      ((∑ i, z i) ∈ Cg ∧ ∀ z' : Fin N → EuclideanSpace ℝ (Fin n), (∑ i, z' i) ∈ Cg →
          sharingZObj g ρ a z ≤ sharingZObj g ρ a z') ↔
        ((N : ℝ) • avg z ∈ Cg ∧
          (∀ w : EuclideanSpace ℝ (Fin n), (N : ℝ) • w ∈ Cg →
            g ((N : ℝ) • avg z) + (ρ / 2) * ∑ _i : Fin N, ‖avg z - avg a‖ ^ 2 ≤
              g ((N : ℝ) • w) + (ρ / 2) * ∑ _i : Fin N, ‖w - avg a‖ ^ 2) ∧
          ∀ i, z i = a i + avg z - avg a)) ∧
    (∀ (Cf : Fin N → Set (EuclideanSpace ℝ (Fin n))) (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
      (x z u : ℕ → Fin N → EuclideanSpace ℝ (Fin n)),
      IsSharingADMMRun Cf f Cg g ρ x z u →
        ∀ k i, u (k + 1) i = avg (u k) + avg (x (k + 1)) - avg (z (k + 1))) := by
  exact @NProof.sharing_goal n N hN ρ hρ Cg g

