-- Prove2me | solution 1 for BBBV.RandomPermutation.piChain_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T06:21:02.323891+00:00
-- url     : https://prove2.me/submissions/9d510dea-c9cb-4595-8cd4-010a448fc58e

import Definitions.Def_BBBV_RandomPermutation_Chain

noncomputable section
open Classical Finset BBBV.RandomPermutation
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace WentaoBBBVUniform

private lemma chain_key {n T : ℕ} (ω : Ω n T) (i : ℕ) :
    piChain ω i (x ω i) = BBBV.RandomOracle.ones n := by
  induction i with
  | zero => exact ω.1.apply_symm_apply _
  | succ i ih =>
    change piChain ω i (Equiv.swap (x ω i) (x ω (i + 1)) (x ω (i + 1))) = _
    simpa using ih

private def relabel {n T : ℕ} (τ : Equiv.Perm (BBBV.RandomOracle.Str n)) : Ω n T ≃ Ω n T :=
  Equiv.prodCongr (Equiv.mulRight τ)
    (Equiv.piCongrRight (fun _ : Fin (T + 1) => τ.symm))

private lemma x_relabel {n T : ℕ} (τ : Equiv.Perm (BBBV.RandomOracle.Str n))
    (ω : Ω n T) (i : ℕ) (hi : i ≤ T + 1) :
    x (relabel τ ω) i = τ.symm (x ω i) := by
  cases i with
  | zero => rfl
  | succ k => simp [relabel, x, show k < T + 1 by omega]

private lemma chain_relabel {n T : ℕ} (τ : Equiv.Perm (BBBV.RandomOracle.Str n))
    (ω : Ω n T) (i : ℕ) (hi : i ≤ T + 1) :
    piChain (relabel τ ω) i = piChain ω i * τ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change piChain (relabel τ ω) i *
      Equiv.swap (x (relabel τ ω) i) (x (relabel τ ω) (i + 1)) =
      (piChain ω i * Equiv.swap (x ω i) (x ω (i + 1))) * τ
    rw [ih (by omega), x_relabel τ ω i (by omega), x_relabel τ ω (i + 1) hi]
    rw [mul_assoc, Equiv.mul_swap_eq_swap_mul]
    simp only [Equiv.apply_symm_apply]
    exact (mul_assoc _ _ _).symm

end WentaoBBBVUniform

open WentaoBBBVUniform

theorem solution {n T : ℕ} (i : ℕ) (hi : i ≤ T + 1)
    (σ : Equiv.Perm (BBBV.RandomOracle.Str n)) :
    (((Finset.univ.filter fun ω : Ω n T => piChain ω i = σ).card : ℝ) /
      (Fintype.card (Ω n T) : ℝ) =
        1 / (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ)) ∧
    (∀ ω : Ω n T, piChain ω i (x ω i) = BBBV.RandomOracle.ones n) := by
  classical
  refine ⟨?_, fun ω => chain_key ω i⟩
  let G := Equiv.Perm (BBBV.RandomOracle.Str n)
  let C : ℕ := (univ.filter fun ω : Ω n T => piChain ω i = σ).card
  have he (τ : G) : (∑ ω : Ω n T, if piChain (relabel τ ω) i = σ then (1 : ℕ) else 0) = C := by
    have h := Equiv.sum_comp (relabel τ) (fun ω : Ω n T =>
      if piChain ω i = σ then (1 : ℕ) else 0)
    simpa [C] using h
  have hinner (π : G) : (∑ τ : G, if π * τ = σ then (1 : ℕ) else 0) = 1 := by
    have h := Equiv.sum_comp (Equiv.mulLeft π) (fun τ : G => if τ = σ then (1 : ℕ) else 0)
    calc
      _ = ∑ τ : G, if τ = σ then (1 : ℕ) else 0 := h
      _ = 1 := by
        rw [sum_eq_single (show G from σ)]
        · simp
        · intro τ _ hτ; simp [hτ]
        · simp
  have hcount : Fintype.card G * C = Fintype.card (Ω n T) := by
    calc
      _ = ∑ τ : G, ∑ ω : Ω n T,
          if piChain (relabel τ ω) i = σ then (1 : ℕ) else 0 := by
        simp [he]
      _ = ∑ ω : Ω n T, ∑ τ : G, if piChain ω i * τ = σ then (1 : ℕ) else 0 := by
        rw [sum_comm]
        simp_rw [chain_relabel _ _ i hi]
      _ = _ := by simp only [hinner, sum_const, card_univ, smul_eq_mul, mul_one]
  have hΩ : (0 : ℝ) < Fintype.card (Ω n T) := by exact_mod_cast Fintype.card_pos
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  change (C : ℝ) / (Fintype.card (Ω n T) : ℝ) = 1 / (Fintype.card G : ℝ)
  apply (div_eq_div_iff hΩ.ne' hG.ne').mpr
  have hcountR : (Fintype.card G : ℝ) * C = Fintype.card (Ω n T) := by
    exact_mod_cast hcount
  simpa [mul_comm] using hcountR
