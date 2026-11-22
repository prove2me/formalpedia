-- Prove2me | solution 1 for FarhiQAOA.Cubic.eq_35_min
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:50:45.993276+00:00
-- url     : https://prove2.me/submissions/928ff7d1-0d3f-4fea-8a3a-b27e496866ed

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace FarhiQAOA.Cubic.Eq35Aux

open QAlgorithms FarhiQAOA.Cubic

/-! ### Part 1: Walsh-Hadamard diagonalization of `qaoaMixer` -/

def walshMat (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => ∏ i : Fin n, if y i && z i then -1 else 1

noncomputable def walshInv (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((2⁻¹ : ℂ) ^ n) • walshMat n

lemma walshMat_mul_walshMat_apply (n : ℕ) (y z : Qubits n) :
    (walshMat n * walshMat n) y z = if y = z then (2 : ℂ) ^ n else 0 := by
  simp only [Matrix.mul_apply, walshMat, Matrix.of_apply, ← Finset.prod_mul_distrib]
  have hps := (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (if y i && b then (-1 : ℂ) else 1) * (if b && z i then (-1 : ℂ) else 1))).symm
  rw [hps]
  have hfactor : ∀ i : Fin n,
      (∑ b : Bool, (if y i && b then (-1 : ℂ) else 1) * (if b && z i then (-1 : ℂ) else 1)) =
        if y i = z i then (2 : ℂ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases y i <;> cases z i <;> norm_num
  simp_rw [hfactor]
  by_cases hyz : y = z
  · subst hyz
    simp
  · rw [if_neg hyz]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hyz
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma walshMat_mul_walshInv (n : ℕ) : walshMat n * walshInv n = 1 := by
  ext y z
  simp only [walshInv, Matrix.mul_smul, Matrix.smul_apply, walshMat_mul_walshMat_apply,
    smul_eq_mul, Matrix.one_apply]
  split_ifs
  · rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
  · ring

lemma walshInv_mul_walshMat (n : ℕ) : walshInv n * walshMat n = 1 := by
  ext y z
  simp only [walshInv, Matrix.smul_mul, Matrix.smul_apply, walshMat_mul_walshMat_apply,
    smul_eq_mul, Matrix.one_apply]
  split_ifs
  · rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
  · ring

noncomputable def walshUnit (n : ℕ) : (Matrix (Qubits n) (Qubits n) ℂ)ˣ :=
  ⟨walshMat n, walshInv n, walshMat_mul_walshInv n, walshInv_mul_walshMat n⟩

lemma pauliX_wire_eq_conj (n : ℕ) (j : Fin n) :
    Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli j Stabilizer.Pauli.X) =
      walshMat n * Matrix.diagonal (fun u : Qubits n => if u j then (-1 : ℂ) else 1) * walshInv n := by
  ext y z
  have h_rhs :
      (walshMat n * Matrix.diagonal (fun u : Qubits n => if u j then (-1 : ℂ) else 1) * walshInv n) y z =
        ∏ i : Fin n, (if i = j then (if y i = z i then (0 : ℂ) else 1) else (if y i = z i then 1 else 0)) := by
    rw [walshInv, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, walshMat, Matrix.of_apply]
    have hterm : ∀ u : Qubits n,
        (∏ i : Fin n, if y i && u i then (-1 : ℂ) else 1) * (if u j then (-1 : ℂ) else 1) *
          (∏ i : Fin n, if u i && z i then (-1 : ℂ) else 1) =
        ∏ i : Fin n, ((if y i && u i then (-1 : ℂ) else 1) *
          (if i = j then (if u i then (-1 : ℂ) else 1) else 1) *
          (if u i && z i then (-1 : ℂ) else 1)) := by
      intro u
      have hj : (if u j then (-1 : ℂ) else 1) =
          ∏ i : Fin n, if i = j then (if u i then (-1 : ℂ) else 1) else 1 := by
        rw [Finset.prod_ite_eq' Finset.univ j (fun i => if u i then (-1 : ℂ) else 1),
          if_pos (Finset.mem_univ j)]
      rw [hj, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp_rw [hterm]
    have hps := (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
      (if y i && b then (-1 : ℂ) else 1) *
        (if i = j then (if b then (-1 : ℂ) else 1) else 1) *
        (if b && z i then (-1 : ℂ) else 1))).symm
    rw [hps]
    have hfactor : ∀ i : Fin n,
        (∑ b : Bool, (if y i && b then (-1 : ℂ) else 1) *
          (if i = j then (if b then (-1 : ℂ) else 1) else 1) *
          (if b && z i then (-1 : ℂ) else 1)) =
        (2 : ℂ) * (if i = j then (if y i = z i then 0 else 1) else (if y i = z i then 1 else 0)) := by
      intro i
      rw [Fintype.sum_bool]
      by_cases hij : i = j <;> cases y i <;> cases z i <;> simp [hij] <;> norm_num
    simp_rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_pow, one_mul]
  rw [h_rhs]
  have hdef : Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli j Stabilizer.Pauli.X) y z =
      if ∀ a : Fin n, a ∉ Set.range (Stabilizer.wire1 j) → y a = z a then
        if y j = z j then (0 : ℂ) else 1
      else 0 := rfl
  have hrange : (∀ a : Fin n, a ∉ Set.range (Stabilizer.wire1 j) → y a = z a) ↔
      (∀ a : Fin n, a ≠ j → y a = z a) := by
    have hset : Set.range (Stabilizer.wire1 j) = {j} := by
      ext a
      simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
    simp [hset]
  rw [hdef, if_congr hrange rfl rfl]
  by_cases hall : ∀ a : Fin n, a ≠ j → y a = z a
  · rw [if_pos hall]
    by_cases hyz : y j = z j
    · rw [if_pos hyz]
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      simp [hyz]
    · rw [if_neg hyz]
      symm
      refine Finset.prod_eq_one fun i _ => ?_
      by_cases hij : i = j
      · subst hij; simp [hyz]
      · simp [hij, hall i hij]
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨a, haj, hyza⟩ := hall
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
    simp [haj, hyza]

noncomputable def mixerEntry (β : ℝ) (a b : Bool) : ℂ :=
  2⁻¹ * ∑ u : Bool,
    (if a && u then (-1 : ℂ) else 1) *
      Complex.exp (-(Complex.I * (β : ℂ)) * (if u then (-1 : ℂ) else 1)) *
      (if u && b then (-1 : ℂ) else 1)

lemma exp_qaoaMixer_apply (n : ℕ) (β : ℝ) (z y : Qubits n) :
    NormedSpace.exp (-(Complex.I * (β : ℂ)) • qaoaMixer n) z y =
      ∏ i : Fin n, mixerEntry β (z i) (y i) := by
  set c : ℂ := -(Complex.I * (β : ℂ))
  have hdiag_sum :
      Matrix.diagonal (fun u : Qubits n => ∑ j : Fin n, c * (if u j then (-1 : ℂ) else 1)) =
        ∑ j : Fin n, c • Matrix.diagonal (fun u : Qubits n => if u j then (-1 : ℂ) else 1) := by
    ext a b
    simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hsum : c • qaoaMixer n =
      (walshUnit n : Matrix (Qubits n) (Qubits n) ℂ) *
        Matrix.diagonal (fun u : Qubits n => ∑ j : Fin n, c * (if u j then (-1 : ℂ) else 1)) *
        (((walshUnit n)⁻¹ : (Matrix (Qubits n) (Qubits n) ℂ)ˣ) : Matrix (Qubits n) (Qubits n) ℂ) := by
    change c • qaoaMixer n =
      walshMat n * Matrix.diagonal (fun u : Qubits n => ∑ j : Fin n, c * (if u j then (-1 : ℂ) else 1)) *
        walshInv n
    rw [hdiag_sum, Matrix.mul_sum, Matrix.sum_mul, qaoaMixer, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pauliX_wire_eq_conj, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsum, Matrix.exp_units_conj, Matrix.exp_diagonal]
  have hunit_mul : ∀ M : Matrix (Qubits n) (Qubits n) ℂ,
      ((walshUnit n : Matrix (Qubits n) (Qubits n) ℂ) * M *
        (((walshUnit n)⁻¹ : (Matrix (Qubits n) (Qubits n) ℂ)ˣ) : Matrix (Qubits n) (Qubits n) ℂ)) =
      ((2⁻¹ : ℂ) ^ n) • (walshMat n * M * walshMat n) := by
    intro M
    change walshMat n * M * walshInv n = ((2⁻¹ : ℂ) ^ n) • (walshMat n * M * walshMat n)
    rw [walshInv, Matrix.mul_smul]
  rw [hunit_mul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp only [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.exp_sum,
    Matrix.mul_diagonal, walshMat, Matrix.of_apply]
  have hterm : ∀ u : Qubits n,
      (∏ i : Fin n, if z i && u i then (-1 : ℂ) else 1) *
        (∏ i : Fin n, Complex.exp (c * (if u i then (-1 : ℂ) else 1))) *
        (∏ i : Fin n, if u i && y i then (-1 : ℂ) else 1) =
      ∏ i : Fin n, ((if z i && u i then (-1 : ℂ) else 1) *
        Complex.exp (c * (if u i then (-1 : ℂ) else 1)) *
        (if u i && y i then (-1 : ℂ) else 1)) := by
    intro u
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp_rw [hterm]
  have hps := (Fintype.prod_sum (fun (i : Fin n) (u : Bool) =>
    (if z i && u then (-1 : ℂ) else 1) *
      Complex.exp (c * (if u then (-1 : ℂ) else 1)) *
      (if u && y i then (-1 : ℂ) else 1))).symm
  rw [hps]
  have hpow : (2⁻¹ : ℂ) ^ n = ∏ _i : Fin n, (2⁻¹ : ℂ) := by simp
  rw [hpow, ← Finset.prod_mul_distrib]
  rfl

lemma exp_problemHamiltonian_apply {n : ℕ} (f : Qubits n → ℝ) (γ : ℝ) :
    NormedSpace.exp (-(Complex.I * (γ : ℂ)) • problemHamiltonian f) =
      Matrix.diagonal (fun y => Complex.exp (-(Complex.I * (γ : ℂ)) * (f y : ℂ))) := by
  have hdiag : -(Complex.I * (γ : ℂ)) • problemHamiltonian f =
      Matrix.diagonal (fun y => -(Complex.I * (γ : ℂ)) * (f y : ℂ)) := by
    ext y z
    simp [problemHamiltonian, Matrix.diagonal_apply]
  rw [hdiag, Matrix.exp_diagonal]
  ext y z
  simp [Matrix.diagonal_apply, Pi.exp_def, ← Complex.exp_eq_exp_ℂ]

lemma qaoaState_p1_apply {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (γ β : ℝ) (z : Qubits n) :
    qaoaState G 1 (fun _ => γ) (fun _ => β) z =
      ((Real.sqrt (2 ^ n))⁻¹ : ℂ) *
        ∑ y : Qubits n,
          (∏ i : Fin n, mixerEntry β (z i) (y i)) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y : ℂ)) := by
  have hU : qaoaUnitary (cutValue G) 1 (fun _ => β) (fun _ => γ) =
      NormedSpace.exp (-(Complex.I * (β : ℂ)) • qaoaMixer n) *
        NormedSpace.exp (-(Complex.I * (γ : ℂ)) • problemHamiltonian (cutValue G)) := by
    simp [qaoaUnitary, orderedProd]
  have hcard : Fintype.card (Qubits n) = 2 ^ n := by simp
  simp only [qaoaState, hU, exp_problemHamiltonian_apply, act, Matrix.mulVec, dotProduct,
    uniformState, hcard, Nat.cast_pow, Nat.cast_ofNat, Matrix.mul_diagonal, exp_qaoaMixer_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-! ### Part 2: Unitarity of `mixerEntry` and local edge reduction -/

lemma star_exp_pm_mul (β : ℝ) (u : Bool) :
    star (Complex.exp (-(Complex.I * (β : ℂ)) * (if u then (-1 : ℂ) else 1))) *
      Complex.exp (-(Complex.I * (β : ℂ)) * (if u then (-1 : ℂ) else 1)) = 1 := by
  rw [RCLike.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero
  cases u <;> simp

lemma sum_star_mixerEntry_mul (β : ℝ) (a b : Bool) :
    (∑ c : Bool, star (mixerEntry β c a) * mixerEntry β c b) = if a = b then 1 else 0 := by
  have h0 : star (Complex.exp (-(Complex.I * (β : ℂ)))) *
      Complex.exp (-(Complex.I * (β : ℂ))) = 1 := by
    simpa using star_exp_pm_mul β false
  have h1 : star (Complex.exp (Complex.I * (β : ℂ))) *
      Complex.exp (Complex.I * (β : ℂ)) = 1 := by
    simpa [mul_neg, neg_neg] using star_exp_pm_mul β true
  have h2 : star (2⁻¹ : ℂ) = 2⁻¹ := by
    rw [RCLike.star_def, map_inv₀, map_ofNat]
  rw [Fintype.sum_bool]
  cases a <;> cases b <;>
    simp only [mixerEntry, Fintype.sum_bool, Bool.and_false, Bool.and_true, Bool.false_and,
      Bool.true_and, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, mul_one, one_mul,
      mul_neg, neg_mul, neg_neg, star_mul, star_add, star_neg, h2]
  · linear_combination (2⁻¹ : ℂ) * h0 + (2⁻¹ : ℂ) * h1
  · linear_combination (2⁻¹ : ℂ) * h0 - (2⁻¹ : ℂ) * h1
  · linear_combination (2⁻¹ : ℂ) * h0 - (2⁻¹ : ℂ) * h1
  · linear_combination (2⁻¹ : ℂ) * h0 + (2⁻¹ : ℂ) * h1

def incCut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j k : Fin n) (y : Qubits n) : ℝ :=
  ∑ u : Fin n, ∑ v : Fin n,
    if (u < v ∧ G.Adj u v) ∧ (u = j ∨ u = k ∨ v = j ∨ v = k) then edgeCut u v y else 0

def restCut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j k : Fin n) (y : Qubits n) : ℝ :=
  ∑ u : Fin n, ∑ v : Fin n,
    if (u < v ∧ G.Adj u v) ∧ ¬(u = j ∨ u = k ∨ v = j ∨ v = k) then edgeCut u v y else 0

lemma cutValue_eq_restCut_add_incCut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (j k : Fin n) (y : Qubits n) :
    cutValue G y = restCut G j k y + incCut G j k y := by
  simp only [cutValue, restCut, incCut, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  by_cases h1 : u < v ∧ G.Adj u v
  · by_cases h2 : u = j ∨ u = k ∨ v = j ∨ v = k <;> simp [h1, h2]
  · simp [h1]

def upd₂ {n : ℕ} (j k : Fin n) (y : Qubits n) (a b : Bool) : Qubits n :=
  Function.update (Function.update y j a) k b

lemma restCut_eq_of_agree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (j k : Fin n) {y₁ y₂ : Qubits n} (h : ∀ i : Fin n, i ≠ j → i ≠ k → y₁ i = y₂ i) :
    restCut G j k y₁ = restCut G j k y₂ := by
  simp only [restCut]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs with huv
  · rcases huv with ⟨_, hnot⟩
    push Not at hnot
    rcases hnot with ⟨huj, huk, hvj, hvk⟩
    simp only [edgeCut, h u huj huk, h v hvj hvk]
  · rfl

lemma agree_upd₂ {n : ℕ} (j k : Fin n) (y : Qubits n) (a b : Bool) :
    ∀ i : Fin n, i ≠ j → i ≠ k → y i = upd₂ j k y a b i := by
  intro i hij hik
  simp [upd₂, Function.update_of_ne hik, Function.update_of_ne hij]

lemma sum_agree_eq_sum_upd₂ {n : ℕ} {j k : Fin n} (hjk : j ≠ k) (y₁ : Qubits n)
    (g : Qubits n → ℂ) :
    (∑ y₂ : Qubits n, if (∀ i : Fin n, i ≠ j → i ≠ k → y₁ i = y₂ i) then g y₂ else 0) =
      ∑ a : Bool, ∑ b : Bool, g (upd₂ j k y₁ a b) := by
  have hpart : ∀ y₂ : Qubits n,
      (if (∀ i : Fin n, i ≠ j → i ≠ k → y₁ i = y₂ i) then g y₂ else 0) =
        ∑ a : Bool, ∑ b : Bool, if y₂ = upd₂ j k y₁ a b then g y₂ else 0 := by
    intro y₂
    by_cases h : ∀ i : Fin n, i ≠ j → i ≠ k → y₁ i = y₂ i
    · rw [if_pos h]
      have heq : y₂ = upd₂ j k y₁ (y₂ j) (y₂ k) := by
        ext i
        by_cases hik : i = k
        · subst hik; simp [upd₂]
        · by_cases hij : i = j
          · subst hij; simp [upd₂, Function.update_of_ne hjk]
          · simp [upd₂, Function.update_of_ne hik, Function.update_of_ne hij, (h i hij hik).symm]
      rw [Fintype.sum_eq_single (y₂ j), Fintype.sum_eq_single (y₂ k)]
      · simp [← heq]
      · intro b hb
        rw [if_neg]
        intro hcontra
        have := congr_fun hcontra k
        simp [upd₂] at this
        exact hb this.symm
      · intro a ha
        rw [Fintype.sum_eq_zero]
        intro b
        rw [if_neg]
        intro hcontra
        have := congr_fun hcontra j
        simp [upd₂, Function.update_of_ne hjk] at this
        exact ha this.symm
    · rw [if_neg h]
      symm
      refine Fintype.sum_eq_zero _ fun a => Fintype.sum_eq_zero _ fun b => ?_
      rw [if_neg]
      rintro rfl
      exact h (agree_upd₂ j k y₁ a b)
  simp_rw [hpart]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp

noncomputable def localEdgeSummand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (γ β : ℝ) (j k : Fin n) (y : Qubits n) : ℂ :=
  ∑ c : Bool, ∑ d : Bool, ∑ a : Bool, ∑ b : Bool,
    (if c = d then (0 : ℂ) else 1) *
      (star (mixerEntry β c (y j)) * mixerEntry β c a *
        (star (mixerEntry β d (y k)) * mixerEntry β d b)) *
      star (Complex.exp (-(Complex.I * (γ : ℂ)) * (incCut G j k y : ℂ))) *
      Complex.exp (-(Complex.I * (γ : ℂ)) * (incCut G j k (upd₂ j k y a b) : ℂ))

lemma edgeCut_complex_eq_sum_prod {n : ℕ} {j k : Fin n} (hjk : j ≠ k) (z : Qubits n) :
    (edgeCut j k z : ℂ) =
      ∑ c : Bool, ∑ d : Bool,
        (if c = d then (0 : ℂ) else 1) *
          ∏ i : Fin n,
            (if i = j then (if z i = c then (1 : ℂ) else 0)
             else if i = k then (if z i = d then (1 : ℂ) else 0)
             else 1) := by
  have hprod : ∀ c d : Bool,
      (∏ i : Fin n,
        (if i = j then (if z i = c then (1 : ℂ) else 0)
         else if i = k then (if z i = d then (1 : ℂ) else 0)
         else 1)) =
      (if z j = c then (1 : ℂ) else 0) * (if z k = d then (1 : ℂ) else 0) := by
    intro c d
    rw [← Finset.prod_subset (Finset.subset_univ ({j, k} : Finset (Fin n)))]
    · rw [Finset.prod_pair hjk]
      simp [hjk.symm]
    · intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [hi.1, hi.2]
  simp_rw [hprod]
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  simp only [edgeCut]
  cases z j <;> cases z k <;> simp

lemma prod_mixer_orthog {n : ℕ} {j k : Fin n} (hjk : j ≠ k) (β : ℝ)
    (c d : Bool) (y₁ y₂ : Qubits n) :
    (∑ z : Qubits n,
      (∏ i : Fin n,
        (if i = j then (if z i = c then (1 : ℂ) else 0)
         else if i = k then (if z i = d then (1 : ℂ) else 0)
         else 1)) *
      (∏ i : Fin n, star (mixerEntry β (z i) (y₁ i))) *
      (∏ i : Fin n, mixerEntry β (z i) (y₂ i))) =
    if (∀ i : Fin n, i ≠ j → i ≠ k → y₁ i = y₂ i) then
      (star (mixerEntry β c (y₁ j)) * mixerEntry β c (y₂ j)) *
        (star (mixerEntry β d (y₁ k)) * mixerEntry β d (y₂ k))
    else 0 := by
  simp_rw [← Finset.prod_mul_distrib]
  have hps := (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (if i = j then (if b = c then (1 : ℂ) else 0)
     else if i = k then (if b = d then (1 : ℂ) else 0)
     else 1) *
    star (mixerEntry β b (y₁ i)) *
    mixerEntry β b (y₂ i))).symm
  rw [hps]
  have hfactor : ∀ i : Fin n,
      (∑ b : Bool,
        (if i = j then (if b = c then (1 : ℂ) else 0)
         else if i = k then (if b = d then (1 : ℂ) else 0)
         else 1) *
        star (mixerEntry β b (y₁ i)) *
        mixerEntry β b (y₂ i)) =
      if i = j then star (mixerEntry β c (y₁ j)) * mixerEntry β c (y₂ j)
      else if i = k then star (mixerEntry β d (y₁ k)) * mixerEntry β d (y₂ k)
      else if y₁ i = y₂ i then 1 else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      rw [Fintype.sum_eq_single c (fun b hb => by simp [hb])]
      simp
    · by_cases hik : i = k
      · subst hik
        simp only [if_neg hij, if_true]
        rw [Fintype.sum_eq_single d (fun b hb => by simp [hb])]
        simp
      · simp only [if_neg hij, if_neg hik, one_mul]
        exact sum_star_mixerEntry_mul β (y₁ i) (y₂ i)
  simp_rw [hfactor]
  by_cases h : ∀ i : Fin n, i ≠ j → i ≠ k → y₁ i = y₂ i
  · rw [if_pos h]
    rw [← Finset.prod_subset (Finset.subset_univ ({j, k} : Finset (Fin n)))]
    · rw [Finset.prod_pair hjk]
      simp [hjk.symm]
    · intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [hi.1, hi.2, h i hi.1 hi.2]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hij, hik, hi⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [hij, hik, hi]

lemma star_exp_rest_add_inc_cancel (γ r x₁ x₂ : ℝ) :
    star (Complex.exp (-(Complex.I * (γ : ℂ)) * ((r + x₁ : ℝ) : ℂ))) *
      Complex.exp (-(Complex.I * (γ : ℂ)) * ((r + x₂ : ℝ) : ℂ)) =
    star (Complex.exp (-(Complex.I * (γ : ℂ)) * (x₁ : ℂ))) *
      Complex.exp (-(Complex.I * (γ : ℂ)) * (x₂ : ℂ)) := by
  push_cast
  rw [mul_add, mul_add, Complex.exp_add, Complex.exp_add, star_mul]
  have h0 : star (Complex.exp (-(Complex.I * (γ : ℂ)) * (r : ℂ))) *
      Complex.exp (-(Complex.I * (γ : ℂ)) * (r : ℂ)) = 1 := by
    rw [RCLike.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    convert Complex.exp_zero
    simp
  linear_combination
    star (Complex.exp (-(Complex.I * (γ : ℂ)) * (x₁ : ℂ))) *
      Complex.exp (-(Complex.I * (γ : ℂ)) * (x₂ : ℂ)) * h0

lemma norm_sq_mul_real_eq_re (w : ℂ) (r : ℝ) :
    ‖w‖ ^ 2 * r = (star w * w * (r : ℂ)).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [RCLike.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma edgeTerm1_eq_local {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (γ β : ℝ) {j k : Fin n} (hjk : j ≠ k) :
    edgeTerm1 G γ β j k =
      ((2⁻¹ : ℂ) ^ n * ∑ y : Qubits n, localEdgeSummand G γ β j k y).re := by
  have hprob : ∀ z : Qubits n,
      prob (qaoaState G 1 (fun _ => γ) (fun _ => β)) z * edgeCut j k z =
        ((star (qaoaState G 1 (fun _ => γ) (fun _ => β) z) : ℂ) *
          (qaoaState G 1 (fun _ => γ) (fun _ => β) z : ℂ) *
          (edgeCut j k z : ℂ)).re := by
    intro z
    simp only [prob, ket, EuclideanSpace.inner_single_left, starRingEnd_apply, star_one, one_mul]
    exact norm_sq_mul_real_eq_re (qaoaState G 1 (fun _ => γ) (fun _ => β) z) (edgeCut j k z)
  simp only [edgeTerm1, edgeTerm, hprob, ← Complex.re_sum]
  congr 1
  have hsqrt : star (((Real.sqrt (2 ^ n))⁻¹ : ℂ)) * ((Real.sqrt (2 ^ n))⁻¹ : ℂ) = (2⁻¹ : ℂ) ^ n := by
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
    have hreal : (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * (Real.sqrt ((2 : ℝ) ^ n))⁻¹ = (2⁻¹ : ℝ) ^ n := by
      rw [← mul_inv, Real.mul_self_sqrt hpos, inv_pow]
    have hcast := congr_arg (algebraMap ℝ ℂ) hreal
    simpa [RCLike.star_def] using hcast
  trans ∑ z : Qubits n,
      (2⁻¹ : ℂ) ^ n *
        ∑ y₁ : Qubits n, ∑ y₂ : Qubits n,
          (∏ i : Fin n, star (mixerEntry β (z i) (y₁ i))) *
            (∏ i : Fin n, mixerEntry β (z i) (y₂ i)) *
            star (Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₁ : ℂ))) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₂ : ℂ)) *
            (edgeCut j k z : ℂ)
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [qaoaState_p1_apply]
    have hmul :
        star (((Real.sqrt (2 ^ n))⁻¹ : ℂ) *
          ∑ y : Qubits n, (∏ i : Fin n, mixerEntry β (z i) (y i)) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y : ℂ))) *
        (((Real.sqrt (2 ^ n))⁻¹ : ℂ) *
          ∑ y : Qubits n, (∏ i : Fin n, mixerEntry β (z i) (y i)) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y : ℂ))) *
        (edgeCut j k z : ℂ) =
        (star (((Real.sqrt (2 ^ n))⁻¹ : ℂ)) * ((Real.sqrt (2 ^ n))⁻¹ : ℂ)) *
        ((∑ y₁ : Qubits n, star ((∏ i : Fin n, mixerEntry β (z i) (y₁ i)) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₁ : ℂ)))) *
          (∑ y₂ : Qubits n, (∏ i : Fin n, mixerEntry β (z i) (y₂ i)) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₂ : ℂ))) *
          (edgeCut j k z : ℂ)) := by
      simp only [star_mul, star_sum]
      ring
    rw [hmul, hsqrt]
    congr 1
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y₂ _ => ?_
    simp only [star_mul, star_prod]
    ring
  · rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y₁ _ => ?_
    simp_rw [edgeCut_complex_eq_sum_prod hjk]
    trans ∑ c : Bool, ∑ d : Bool,
        (if c = d then (0 : ℂ) else 1) *
          ∑ y₂ : Qubits n,
            star (Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₁ : ℂ))) *
              Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₂ : ℂ)) *
              ∑ z : Qubits n,
                (∏ i : Fin n,
                  (if i = j then (if z i = c then (1 : ℂ) else 0)
                   else if i = k then (if z i = d then (1 : ℂ) else 0)
                   else 1)) *
                (∏ i : Fin n, star (mixerEntry β (z i) (y₁ i))) *
                (∏ i : Fin n, mixerEntry β (z i) (y₂ i))
    · rw [Finset.sum_comm]
      trans ∑ y₂ : Qubits n, ∑ c : Bool, ∑ d : Bool,
          (if c = d then (0 : ℂ) else 1) *
            (star (Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₁ : ℂ))) *
              Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₂ : ℂ)) *
              ∑ z : Qubits n,
                (∏ i : Fin n,
                  (if i = j then (if z i = c then (1 : ℂ) else 0)
                   else if i = k then (if z i = d then (1 : ℂ) else 0)
                   else 1)) *
                (∏ i : Fin n, star (mixerEntry β (z i) (y₁ i))) *
                (∏ i : Fin n, mixerEntry β (z i) (y₂ i)))
      · refine Finset.sum_congr rfl fun y₂ _ => ?_
        trans ∑ z : Qubits n, ∑ c : Bool, ∑ d : Bool,
            (if c = d then (0 : ℂ) else 1) *
              (star (Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₁ : ℂ))) *
                Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₂ : ℂ)) *
                ((∏ i : Fin n,
                    (if i = j then (if z i = c then (1 : ℂ) else 0)
                     else if i = k then (if z i = d then (1 : ℂ) else 0)
                     else 1)) *
                  (∏ i : Fin n, star (mixerEntry β (z i) (y₁ i))) *
                  (∏ i : Fin n, mixerEntry β (z i) (y₂ i))))
        · refine Finset.sum_congr rfl fun z _ => ?_
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
          ring
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
    · simp_rw [prod_mixer_orthog hjk β]
      simp only [localEdgeSummand]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      have hite : ∀ y₂ : Qubits n,
          star (Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₁ : ℂ))) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₂ : ℂ)) *
            (if ∀ i : Fin n, i ≠ j → i ≠ k → y₁ i = y₂ i then
              (star (mixerEntry β c (y₁ j)) * mixerEntry β c (y₂ j)) *
                (star (mixerEntry β d (y₁ k)) * mixerEntry β d (y₂ k))
             else 0) =
          if ∀ i : Fin n, i ≠ j → i ≠ k → y₁ i = y₂ i then
            (star (mixerEntry β c (y₁ j)) * mixerEntry β c (y₂ j) *
              (star (mixerEntry β d (y₁ k)) * mixerEntry β d (y₂ k))) *
            star (Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₁ : ℂ))) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₂ : ℂ))
          else 0 := by
        intro y₂
        split_ifs <;> ring
      simp_rw [hite]
      rw [sum_agree_eq_sum_upd₂ hjk y₁, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hupd_j : upd₂ j k y₁ a b j = a := by simp [upd₂, Function.update_of_ne hjk]
      have hupd_k : upd₂ j k y₁ a b k = b := by simp [upd₂]
      have hrest : restCut G j k (upd₂ j k y₁ a b) = restCut G j k y₁ :=
        (restCut_eq_of_agree G j k (agree_upd₂ j k y₁ a b)).symm
      have hphase :
          star (Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G y₁ : ℂ))) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (cutValue G (upd₂ j k y₁ a b) : ℂ)) =
          star (Complex.exp (-(Complex.I * (γ : ℂ)) * (incCut G j k y₁ : ℂ))) *
            Complex.exp (-(Complex.I * (γ : ℂ)) * (incCut G j k (upd₂ j k y₁ a b) : ℂ)) := by
        rw [cutValue_eq_restCut_add_incCut G j k y₁,
          cutValue_eq_restCut_add_incCut G j k (upd₂ j k y₁ a b), hrest]
        exact star_exp_rest_add_inc_cancel γ (restCut G j k y₁) (incCut G j k y₁)
          (incCut G j k (upd₂ j k y₁ a b))
      rw [hupd_j, hupd_k]
      linear_combination
        (if c = d then (0 : ℂ) else 1) *
          (star (mixerEntry β c (y₁ j)) * mixerEntry β c a *
            (star (mixerEntry β d (y₁ k)) * mixerEntry β d b)) * hphase


/-! ### Part 3: Closed-form formulas for `fg4`, `fg5`, `fg6` and the witness `(arcsin (1/√3), π/8)` -/

lemma mixerEntry_eq (β : ℝ) (a b : Bool) :
    mixerEntry β a b = if a = b then (Real.cos β : ℂ) else -(Complex.I * (Real.sin β : ℂ)) := by
  have hcos : (Real.cos β : ℂ) = 2⁻¹ * (Complex.exp (-(Complex.I * (β : ℂ))) + Complex.exp (Complex.I * (β : ℂ))) := by
    rw [Complex.ofReal_cos, Complex.cos]
    have : (β : ℂ) * Complex.I = Complex.I * (β : ℂ) := mul_comm _ _
    rw [this]; ring
  have hsin : -(Complex.I * (Real.sin β : ℂ)) = 2⁻¹ * (Complex.exp (-(Complex.I * (β : ℂ))) - Complex.exp (Complex.I * (β : ℂ))) := by
    rw [Complex.ofReal_sin, Complex.sin, mul_comm (β : ℂ) Complex.I]
    ring_nf
    rw [Complex.I_sq]
    ring
  cases a <;> cases b <;>
    simp only [mixerEntry, Fintype.sum_bool, Bool.and_false, Bool.and_true, Bool.false_and,
      Bool.true_and, if_true, if_false, mul_one, one_mul, mul_neg, neg_mul, neg_neg,
      Bool.false_eq_true, Bool.true_eq_false]
  · rw [hcos]; ring
  · rw [hsin]; ring
  · rw [hsin]; ring
  · rw [hcos]; ring

lemma star_exp_mul_exp (γ u v : ℝ) :
    star (Complex.exp (-(Complex.I * (γ : ℂ)) * (u : ℂ))) *
      Complex.exp (-(Complex.I * (γ : ℂ)) * (v : ℂ)) =
    Complex.exp (Complex.I * (γ : ℂ) * ((u - v : ℝ) : ℂ)) := by
  rw [RCLike.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

def bcut (x y : Bool) : ℝ := if x = y then 0 else 1

lemma sum_bool_private (γ : ℝ) (x a : Bool) :
    (∑ w : Bool, Complex.exp (Complex.I * (γ : ℂ) * ((bcut x w - bcut a w : ℝ) : ℂ))) =
      if x = a then (2 : ℂ) else (2 : ℂ) * (Real.cos γ : ℂ) := by
  have hcos : Complex.exp (Complex.I * (γ : ℂ)) + Complex.exp (-(Complex.I * (γ : ℂ))) =
      (2 : ℂ) * Complex.cos (γ : ℂ) := by
    rw [Complex.cos, mul_comm (γ : ℂ) Complex.I]; ring
  rw [Fintype.sum_bool]
  cases x <;> cases a <;> simp [bcut]
  all_goals first | exact hcos | (rw [add_comm]; exact hcos) | (norm_num; done)

lemma sum_bool_common (γ : ℝ) (x y a b : Bool) :
    (∑ w : Bool, Complex.exp (Complex.I * (γ : ℂ) *
      (((bcut x w + bcut y w) - (bcut a w + bcut b w) : ℝ) : ℂ))) =
      if x = a ∧ y = b then (2 : ℂ)
      else if x ≠ a ∧ y ≠ b then
        (if x = y then (2 : ℂ) * (Real.cos (2 * γ) : ℂ) else (2 : ℂ))
      else (2 : ℂ) * (Real.cos γ : ℂ) := by
  have hcos1 : Complex.exp (Complex.I * (γ : ℂ)) + Complex.exp (-(Complex.I * (γ : ℂ))) =
      (2 : ℂ) * Complex.cos (γ : ℂ) := by
    rw [Complex.cos, mul_comm (γ : ℂ) Complex.I]; ring
  have hcos2 : Complex.exp (Complex.I * (γ : ℂ) * 2) + Complex.exp (-(Complex.I * (γ : ℂ) * 2)) =
      (2 : ℂ) * Complex.cos (2 * (γ : ℂ)) := by
    rw [Complex.cos]
    have h1 : Complex.I * (γ : ℂ) * 2 = (2 * (γ : ℂ)) * Complex.I := by ring
    rw [h1]; ring
  have h11 : (1 : ℂ) + 1 = 2 := by norm_num
  have hm11 : (-1 : ℂ) + -1 = -2 := by norm_num
  rw [Fintype.sum_bool]
  cases x <;> cases y <;> cases a <;> cases b <;> simp [bcut, Complex.ofReal_mul, h11, hm11]
  all_goals first
    | (norm_num; done)
    | exact hcos1
    | (rw [add_comm]; exact hcos1)
    | exact hcos2
    | (rw [add_comm]; exact hcos2)

lemma incCut_gFour (y : Qubits 4) :
    incCut gFour 0 1 y =
      bcut (y 0) (y 1) + (bcut (y 0) (y 2) + bcut (y 1) (y 2)) +
      (bcut (y 0) (y 3) + bcut (y 1) (y 3)) := by
  have h : ∀ u v : Fin 4,
      ((u < v ∧ gFour.Adj u v) ∧ (u = 0 ∨ u = 1 ∨ v = 0 ∨ v = 1)) ↔
        (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 0 ∧ v = 3) ∨
        (u = 1 ∧ v = 2) ∨ (u = 1 ∧ v = 3) := by decide
  simp only [incCut, h, Fin.sum_univ_four, edgeCut, bcut]
  simp only [Fin.isValue, Fin.reduceEq, and_false, and_true, false_and, or_false, or_true,
    if_true, if_false]
  ring

lemma incCut_gFive (y : Qubits 5) :
    incCut gFive 0 1 y =
      bcut (y 0) (y 1) + (bcut (y 0) (y 2) + bcut (y 1) (y 2)) +
      bcut (y 0) (y 3) + bcut (y 1) (y 4) := by
  have h : ∀ u v : Fin 5,
      ((u < v ∧ gFive.Adj u v) ∧ (u = 0 ∨ u = 1 ∨ v = 0 ∨ v = 1)) ↔
        (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 0 ∧ v = 3) ∨
        (u = 1 ∧ v = 2) ∨ (u = 1 ∧ v = 4) := by decide
  simp only [incCut, h, Fin.sum_univ_five, edgeCut, bcut]
  simp only [Fin.isValue, Fin.reduceEq, and_false, and_true, false_and, or_false, or_true,
    if_true, if_false]
  ring

lemma incCut_gSix (y : Qubits 6) :
    incCut gSix 0 1 y =
      bcut (y 0) (y 1) + bcut (y 0) (y 2) + bcut (y 0) (y 3) +
      bcut (y 1) (y 4) + bcut (y 1) (y 5) := by
  have h : ∀ u v : Fin 6,
      ((u < v ∧ gSix.Adj u v) ∧ (u = 0 ∨ u = 1 ∨ v = 0 ∨ v = 1)) ↔
        (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 0 ∧ v = 3) ∨
        (u = 1 ∧ v = 4) ∨ (u = 1 ∧ v = 5) := by decide
  simp only [incCut, h, Fin.sum_univ_six, edgeCut, bcut]
  simp only [Fin.isValue, Fin.reduceEq, and_false, and_true, false_and, or_false, or_true,
    if_true, if_false]
  ring

noncomputable def mixerWeight (β : ℝ) (y0 y1 a b : Bool) : ℂ :=
  ∑ c : Bool, ∑ d : Bool,
    (if c = d then (0 : ℂ) else 1) *
      (star (mixerEntry β c y0) * mixerEntry β c a *
        (star (mixerEntry β d y1) * mixerEntry β d b))

noncomputable def nbrFactor (c_common : ℕ) (γ : ℝ) (y0 y1 a b : Bool) : ℂ :=
  if y0 = a ∧ y1 = b then 1
  else if y0 ≠ a ∧ y1 ≠ b then
    (if y0 = y1 then (Real.cos (2 * γ) : ℂ) ^ c_common * (Real.cos γ : ℂ) ^ (4 - 2 * c_common)
     else (Real.cos γ : ℂ) ^ (4 - 2 * c_common))
  else (Real.cos γ : ℂ) ^ 2

lemma re_master_formula (c_common : ℕ) (hc : c_common ≤ 2) (γ β : ℝ) :
    ((2⁻¹ : ℂ) ^ 2 * ∑ y0 : Bool, ∑ y1 : Bool, ∑ a : Bool, ∑ b : Bool,
      mixerWeight β y0 y1 a b *
        Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
        nbrFactor c_common γ y0 y1 a b).re =
    1 / 2 + 1 / 2 * Real.sin (4 * β) * Real.sin γ * Real.cos γ ^ 2 -
      (c_common : ℝ) / 2 * Real.sin (2 * β) ^ 2 * Real.sin γ ^ 2 * Real.cos γ ^ 2 := by
  have hcos2g : Real.cos (2 * γ) = 2 * Real.cos γ ^ 2 - 1 := Real.cos_two_mul γ
  have hsin2g : Real.sin γ ^ 2 + Real.cos γ ^ 2 = 1 := Real.sin_sq_add_cos_sq γ
  have hsin4b : Real.sin (4 * β) = 4 * Real.sin β * Real.cos β * (Real.cos β ^ 2 - Real.sin β ^ 2) := by
    have : 4 * β = 2 * (2 * β) := by ring
    rw [this, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul']
    ring
  have hsin2b : Real.sin (2 * β) = 2 * Real.sin β * Real.cos β := Real.sin_two_mul β
  have hscb : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have hexp : ∀ r : ℝ, Complex.exp (Complex.I * (γ : ℂ) * (r : ℂ)) =
      (Real.cos (γ * r) : ℂ) + Complex.I * (Real.sin (γ * r) : ℂ) := by
    intro r
    have : Complex.I * (γ : ℂ) * (r : ℂ) = ((γ * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  have h1 : Complex.exp (Complex.I * (γ : ℂ)) = (Real.cos γ : ℂ) + Complex.I * (Real.sin γ : ℂ) := by
    simpa using hexp 1
  have hm1 : Complex.exp (-(Complex.I * (γ : ℂ))) = (Real.cos γ : ℂ) - Complex.I * (Real.sin γ : ℂ) := by
    have h := hexp (-1)
    simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one, Real.cos_neg, Real.sin_neg] at h
    rw [h]; ring
  have hsin2_eq : Real.sin γ ^ 2 = 1 - Real.cos γ ^ 2 := by linarith
  have hsinb_eq : Real.sin β ^ 2 = 1 - Real.cos β ^ 2 := by linarith
  have hpow4 : Real.sin β ^ 4 = (1 - Real.cos β ^ 2) ^ 2 := by
    calc Real.sin β ^ 4 = (Real.sin β ^ 2) ^ 2 := by ring
      _ = (1 - Real.cos β ^ 2) ^ 2 := by rw [hsinb_eq]
  have hpow3 : Real.sin β ^ 3 = Real.sin β * (1 - Real.cos β ^ 2) := by
    calc Real.sin β ^ 3 = Real.sin β * Real.sin β ^ 2 := by ring
      _ = Real.sin β * (1 - Real.cos β ^ 2) := by rw [hsinb_eq]
  interval_cases c_common <;> (
    simp only [Fintype.sum_bool, mixerWeight, mixerEntry_eq, nbrFactor, bcut,
      if_true, if_false, Bool.false_eq_true, Bool.true_eq_false, ne_eq, not_false_eq_true,
      not_true_eq_false, and_true, and_false, and_self, sub_self, sub_zero, zero_sub,
      Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg, mul_zero, mul_one, mul_neg,
      Complex.exp_zero, pow_zero, pow_one, one_mul, zero_mul, add_zero, zero_add,
      RCLike.star_def, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, neg_neg,
      Nat.reduceMul, Nat.reduceSub, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [h1, hm1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
      Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
      Complex.inv_re, Complex.inv_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, pow_succ, pow_zero,
      Complex.normSq_ofNat]
    simp only [hcos2g, hsin4b, hsin2b]
    ring_nf
    simp only [hsin2_eq, hpow4, hpow3, hsinb_eq]
    ring)

lemma sum_bool_swap12 (f : Bool → Bool → Bool → ℂ) :
    (∑ y : Bool, ∑ a : Bool, ∑ b : Bool, f y a b) =
    ∑ a : Bool, ∑ b : Bool, ∑ y : Bool, f y a b := by
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _ => Finset.sum_comm

lemma sum_bool_swap22 (f : Bool → Bool → Bool → Bool → ℂ) :
    (∑ x : Bool, ∑ y : Bool, ∑ a : Bool, ∑ b : Bool, f x y a b) =
    ∑ a : Bool, ∑ b : Bool, ∑ x : Bool, ∑ y : Bool, f x y a b := by
  trans ∑ x : Bool, ∑ a : Bool, ∑ b : Bool, ∑ y : Bool, f x y a b
  · exact Finset.sum_congr rfl fun x _ => sum_bool_swap12 (f x)
  · exact sum_bool_swap12 (fun x a b => ∑ y : Bool, f x y a b)

lemma sum_bool_swap32 (f : Bool → Bool → Bool → Bool → Bool → ℂ) :
    (∑ w : Bool, ∑ x : Bool, ∑ y : Bool, ∑ a : Bool, ∑ b : Bool, f w x y a b) =
    ∑ a : Bool, ∑ b : Bool, ∑ w : Bool, ∑ x : Bool, ∑ y : Bool, f w x y a b := by
  trans ∑ w : Bool, ∑ a : Bool, ∑ b : Bool, ∑ x : Bool, ∑ y : Bool, f w x y a b
  · exact Finset.sum_congr rfl fun w _ => sum_bool_swap22 (f w)
  · exact sum_bool_swap12 (fun w a b => ∑ x : Bool, ∑ y : Bool, f w x y a b)

lemma localEdgeSummand_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (γ β : ℝ) (j k : Fin n) (y : Qubits n) :
    localEdgeSummand G γ β j k y =
      ∑ a : Bool, ∑ b : Bool,
        mixerWeight β (y j) (y k) a b *
          Complex.exp (Complex.I * (γ : ℂ) *
            ((incCut G j k y - incCut G j k (upd₂ j k y a b) : ℝ) : ℂ)) := by
  unfold localEdgeSummand mixerWeight
  have hterm : ∀ c d a b : Bool,
      (if c = d then (0 : ℂ) else 1) *
        (star (mixerEntry β c (y j)) * mixerEntry β c a *
          (star (mixerEntry β d (y k)) * mixerEntry β d b)) *
        star (Complex.exp (-(Complex.I * (γ : ℂ)) * (incCut G j k y : ℂ))) *
        Complex.exp (-(Complex.I * (γ : ℂ)) * (incCut G j k (upd₂ j k y a b) : ℂ)) =
      (if c = d then (0 : ℂ) else 1) *
        (star (mixerEntry β c (y j)) * mixerEntry β c a *
          (star (mixerEntry β d (y k)) * mixerEntry β d b)) *
        Complex.exp (Complex.I * (γ : ℂ) *
          ((incCut G j k y - incCut G j k (upd₂ j k y a b) : ℝ) : ℂ)) := by
    intro c d a b
    rw [mul_assoc _ (star (Complex.exp _)), star_exp_mul_exp]
  simp_rw [hterm, Finset.sum_mul]
  exact sum_bool_swap22 _

lemma fg4_formula (γ β : ℝ) :
    fg4 γ β = 1 / 2 + 1 / 2 * Real.sin (4 * β) * Real.sin γ * Real.cos γ ^ 2 -
      Real.sin (2 * β) ^ 2 * Real.sin γ ^ 2 * Real.cos γ ^ 2 := by
  have h1 := edgeTerm1_eq_local gFour γ β (by decide : (0 : Fin 4) ≠ 1)
  rw [fg4, h1]
  have hre := re_master_formula 2 (le_refl 2) γ β
  rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num, one_mul] at hre
  rw [← hre]
  congr 1
  simp_rw [localEdgeSummand_eq]
  let e : (Bool × Bool × Bool × Bool) ≃ Qubits 4 :=
    { toFun := fun ⟨y0, y1, y2, y3⟩ i => match i with | 0 => y0 | 1 => y1 | 2 => y2 | 3 => y3
      invFun := fun y => (y 0, y 1, y 2, y 3)
      left_inv := by rintro ⟨y0, y1, y2, y3⟩; rfl
      right_inv := by intro y; ext i; fin_cases i <;> rfl }
  rw [← Fintype.sum_equiv e _ _ (fun _ => rfl)]
  simp only [Fintype.sum_prod_type]
  have heval : ∀ y0 y1 y2 y3 a b : Bool,
      let y := e (y0, y1, y2, y3)
      y 0 = y0 ∧ y 1 = y1 ∧
      incCut gFour 0 1 y - incCut gFour 0 1 (upd₂ 0 1 y a b) =
        (bcut y0 y1 - bcut a b) +
        ((bcut y0 y2 + bcut y1 y2) - (bcut a y2 + bcut b y2)) +
        ((bcut y0 y3 + bcut y1 y3) - (bcut a y3 + bcut b y3)) := by
    intro y0 y1 y2 y3 a b
    refine ⟨rfl, rfl, ?_⟩
    rw [incCut_gFour, incCut_gFour]
    have h0 : upd₂ 0 1 (e (y0, y1, y2, y3)) a b 0 = a := by simp [upd₂, Function.update_of_ne]
    have h1 : upd₂ 0 1 (e (y0, y1, y2, y3)) a b 1 = b := by simp [upd₂]
    have h2 : upd₂ 0 1 (e (y0, y1, y2, y3)) a b 2 = y2 := by
      simp [upd₂, Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
        Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0), e]
    have h3 : upd₂ 0 1 (e (y0, y1, y2, y3)) a b 3 = y3 := by
      simp [upd₂, Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1),
        Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0), e]
    rw [h0, h1, h2, h3]
    change bcut y0 y1 + (bcut y0 y2 + bcut y1 y2) + (bcut y0 y3 + bcut y1 y3) -
        (bcut a b + (bcut a y2 + bcut b y2) + (bcut a y3 + bcut b y3)) = _
    ring
  have hinner : ∀ y0 y1 : Bool,
      (∑ y2 : Bool, ∑ y3 : Bool, ∑ a : Bool, ∑ b : Bool,
        mixerWeight β (e (y0, y1, y2, y3) 0) (e (y0, y1, y2, y3) 1) a b *
          Complex.exp (Complex.I * (γ : ℂ) *
            ((incCut gFour 0 1 (e (y0, y1, y2, y3)) -
              incCut gFour 0 1 (upd₂ 0 1 (e (y0, y1, y2, y3)) a b) : ℝ) : ℂ))) =
      4 * ∑ a : Bool, ∑ b : Bool,
        mixerWeight β y0 y1 a b *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
          nbrFactor 2 γ y0 y1 a b := by
    intro y0 y1
    trans ∑ y2 : Bool, ∑ y3 : Bool, ∑ a : Bool, ∑ b : Bool,
        mixerWeight β y0 y1 a b *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (γ : ℂ) *
            (((bcut y0 y2 + bcut y1 y2) - (bcut a y2 + bcut b y2) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (γ : ℂ) *
            (((bcut y0 y3 + bcut y1 y3) - (bcut a y3 + bcut b y3) : ℝ) : ℂ))
    · refine Finset.sum_congr rfl fun y2 _ => Finset.sum_congr rfl fun y3 _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      obtain ⟨h0, h1, hdiff⟩ := heval y0 y1 y2 y3 a b
      rw [h0, h1, hdiff]
      push_cast
      rw [mul_add, mul_add, Complex.exp_add, Complex.exp_add]
      ring
    · trans ∑ a : Bool, ∑ b : Bool,
          mixerWeight β y0 y1 a b *
            Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
            (∑ y2 : Bool, Complex.exp (Complex.I * (γ : ℂ) *
              (((bcut y0 y2 + bcut y1 y2) - (bcut a y2 + bcut b y2) : ℝ) : ℂ))) *
            (∑ y3 : Bool, Complex.exp (Complex.I * (γ : ℂ) *
              (((bcut y0 y3 + bcut y1 y3) - (bcut a y3 + bcut b y3) : ℝ) : ℂ)))
      · rw [sum_bool_swap22]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
      · simp only [sum_bool_common, nbrFactor, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        cases y0 <;> cases y1 <;> cases a <;> cases b <;> simp <;> ring
  simp_rw [hinner, ← Finset.mul_sum]
  ring

lemma fg5_formula (γ β : ℝ) :
    fg5 γ β = 1 / 2 + 1 / 2 * Real.sin (4 * β) * Real.sin γ * Real.cos γ ^ 2 -
      1 / 2 * Real.sin (2 * β) ^ 2 * Real.sin γ ^ 2 * Real.cos γ ^ 2 := by
  have h1 := edgeTerm1_eq_local gFive γ β (by decide : (0 : Fin 5) ≠ 1)
  rw [fg5, h1]
  have hre := re_master_formula 1 (by decide) γ β
  rw [Nat.cast_one] at hre
  rw [← hre]
  congr 1
  simp_rw [localEdgeSummand_eq]
  let e : (Bool × Bool × Bool × Bool × Bool) ≃ Qubits 5 :=
    { toFun := fun ⟨y0, y1, y2, y3, y4⟩ i => match i with
        | 0 => y0 | 1 => y1 | 2 => y2 | 3 => y3 | 4 => y4
      invFun := fun y => (y 0, y 1, y 2, y 3, y 4)
      left_inv := by rintro ⟨y0, y1, y2, y3, y4⟩; rfl
      right_inv := by intro y; ext i; fin_cases i <;> rfl }
  rw [← Fintype.sum_equiv e _ _ (fun _ => rfl)]
  simp only [Fintype.sum_prod_type]
  have heval : ∀ y0 y1 y2 y3 y4 a b : Bool,
      let y := e (y0, y1, y2, y3, y4)
      y 0 = y0 ∧ y 1 = y1 ∧
      incCut gFive 0 1 y - incCut gFive 0 1 (upd₂ 0 1 y a b) =
        (bcut y0 y1 - bcut a b) +
        ((bcut y0 y2 + bcut y1 y2) - (bcut a y2 + bcut b y2)) +
        (bcut y0 y3 - bcut a y3) + (bcut y1 y4 - bcut b y4) := by
    intro y0 y1 y2 y3 y4 a b
    refine ⟨rfl, rfl, ?_⟩
    rw [incCut_gFive, incCut_gFive]
    have h0 : upd₂ 0 1 (e (y0, y1, y2, y3, y4)) a b 0 = a := by simp [upd₂, Function.update_of_ne]
    have h1 : upd₂ 0 1 (e (y0, y1, y2, y3, y4)) a b 1 = b := by simp [upd₂]
    have h2 : upd₂ 0 1 (e (y0, y1, y2, y3, y4)) a b 2 = y2 := by
      simp [upd₂, Function.update_of_ne (by decide : (2 : Fin 5) ≠ 1),
        Function.update_of_ne (by decide : (2 : Fin 5) ≠ 0), e]
    have h3 : upd₂ 0 1 (e (y0, y1, y2, y3, y4)) a b 3 = y3 := by
      simp [upd₂, Function.update_of_ne (by decide : (3 : Fin 5) ≠ 1),
        Function.update_of_ne (by decide : (3 : Fin 5) ≠ 0), e]
    have h4 : upd₂ 0 1 (e (y0, y1, y2, y3, y4)) a b 4 = y4 := by
      simp [upd₂, Function.update_of_ne (by decide : (4 : Fin 5) ≠ 1),
        Function.update_of_ne (by decide : (4 : Fin 5) ≠ 0), e]
    rw [h0, h1, h2, h3, h4]
    change bcut y0 y1 + (bcut y0 y2 + bcut y1 y2) + bcut y0 y3 + bcut y1 y4 -
        (bcut a b + (bcut a y2 + bcut b y2) + bcut a y3 + bcut b y4) = _
    ring
  have hinner : ∀ y0 y1 : Bool,
      (∑ y2 : Bool, ∑ y3 : Bool, ∑ y4 : Bool, ∑ a : Bool, ∑ b : Bool,
        mixerWeight β (e (y0, y1, y2, y3, y4) 0) (e (y0, y1, y2, y3, y4) 1) a b *
          Complex.exp (Complex.I * (γ : ℂ) *
            ((incCut gFive 0 1 (e (y0, y1, y2, y3, y4)) -
              incCut gFive 0 1 (upd₂ 0 1 (e (y0, y1, y2, y3, y4)) a b) : ℝ) : ℂ))) =
      8 * ∑ a : Bool, ∑ b : Bool,
        mixerWeight β y0 y1 a b *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
          nbrFactor 1 γ y0 y1 a b := by
    intro y0 y1
    trans ∑ y2 : Bool, ∑ y3 : Bool, ∑ y4 : Bool, ∑ a : Bool, ∑ b : Bool,
        mixerWeight β y0 y1 a b *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (γ : ℂ) *
            (((bcut y0 y2 + bcut y1 y2) - (bcut a y2 + bcut b y2) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y3 - bcut a y3 : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y1 y4 - bcut b y4 : ℝ) : ℂ))
    · refine Finset.sum_congr rfl fun y2 _ => Finset.sum_congr rfl fun y3 _ =>
        Finset.sum_congr rfl fun y4 _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      obtain ⟨h0, h1, hdiff⟩ := heval y0 y1 y2 y3 y4 a b
      rw [h0, h1, hdiff]
      push_cast
      rw [mul_add, mul_add, mul_add, Complex.exp_add, Complex.exp_add, Complex.exp_add]
      ring
    · trans ∑ a : Bool, ∑ b : Bool,
          mixerWeight β y0 y1 a b *
            Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
            (∑ y2 : Bool, Complex.exp (Complex.I * (γ : ℂ) *
              (((bcut y0 y2 + bcut y1 y2) - (bcut a y2 + bcut b y2) : ℝ) : ℂ))) *
            (∑ y3 : Bool, Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y3 - bcut a y3 : ℝ) : ℂ))) *
            (∑ y4 : Bool, Complex.exp (Complex.I * (γ : ℂ) * ((bcut y1 y4 - bcut b y4 : ℝ) : ℂ)))
      · rw [sum_bool_swap32]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
      · simp only [sum_bool_common, sum_bool_private, nbrFactor, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        cases y0 <;> cases y1 <;> cases a <;> cases b <;> simp <;> ring
  simp_rw [hinner, ← Finset.mul_sum]
  ring

lemma fg6_formula (γ β : ℝ) :
    fg6 γ β = 1 / 2 + 1 / 2 * Real.sin (4 * β) * Real.sin γ * Real.cos γ ^ 2 := by
  have h1 := edgeTerm1_eq_local gSix γ β (by decide : (0 : Fin 6) ≠ 1)
  rw [fg6, h1]
  have hre := re_master_formula 0 (by decide) γ β
  rw [Nat.cast_zero, zero_div, zero_mul, zero_mul, zero_mul, sub_zero] at hre
  rw [← hre]
  congr 1
  simp_rw [localEdgeSummand_eq]
  let e : (Bool × Bool × Bool × Bool × Bool × Bool) ≃ Qubits 6 :=
    { toFun := fun ⟨y0, y1, y2, y3, y4, y5⟩ i => match i with
        | 0 => y0 | 1 => y1 | 2 => y2 | 3 => y3 | 4 => y4 | 5 => y5
      invFun := fun y => (y 0, y 1, y 2, y 3, y 4, y 5)
      left_inv := by rintro ⟨y0, y1, y2, y3, y4, y5⟩; rfl
      right_inv := by intro y; ext i; fin_cases i <;> rfl }
  rw [← Fintype.sum_equiv e _ _ (fun _ => rfl)]
  simp only [Fintype.sum_prod_type]
  have heval : ∀ y0 y1 y2 y3 y4 y5 a b : Bool,
      let y := e (y0, y1, y2, y3, y4, y5)
      y 0 = y0 ∧ y 1 = y1 ∧
      incCut gSix 0 1 y - incCut gSix 0 1 (upd₂ 0 1 y a b) =
        (bcut y0 y1 - bcut a b) +
        (bcut y0 y2 - bcut a y2) + (bcut y0 y3 - bcut a y3) +
        (bcut y1 y4 - bcut b y4) + (bcut y1 y5 - bcut b y5) := by
    intro y0 y1 y2 y3 y4 y5 a b
    refine ⟨rfl, rfl, ?_⟩
    rw [incCut_gSix, incCut_gSix]
    have h0 : upd₂ 0 1 (e (y0, y1, y2, y3, y4, y5)) a b 0 = a := by simp [upd₂, Function.update_of_ne]
    have h1 : upd₂ 0 1 (e (y0, y1, y2, y3, y4, y5)) a b 1 = b := by simp [upd₂]
    have h2 : upd₂ 0 1 (e (y0, y1, y2, y3, y4, y5)) a b 2 = y2 := by
      simp [upd₂, Function.update_of_ne (by decide : (2 : Fin 6) ≠ 1),
        Function.update_of_ne (by decide : (2 : Fin 6) ≠ 0), e]
    have h3 : upd₂ 0 1 (e (y0, y1, y2, y3, y4, y5)) a b 3 = y3 := by
      simp [upd₂, Function.update_of_ne (by decide : (3 : Fin 6) ≠ 1),
        Function.update_of_ne (by decide : (3 : Fin 6) ≠ 0), e]
    have h4 : upd₂ 0 1 (e (y0, y1, y2, y3, y4, y5)) a b 4 = y4 := by
      simp [upd₂, Function.update_of_ne (by decide : (4 : Fin 6) ≠ 1),
        Function.update_of_ne (by decide : (4 : Fin 6) ≠ 0), e]
    have h5 : upd₂ 0 1 (e (y0, y1, y2, y3, y4, y5)) a b 5 = y5 := by
      simp [upd₂, Function.update_of_ne (by decide : (5 : Fin 6) ≠ 1),
        Function.update_of_ne (by decide : (5 : Fin 6) ≠ 0), e]
    rw [h0, h1, h2, h3, h4, h5]
    change bcut y0 y1 + bcut y0 y2 + bcut y0 y3 + bcut y1 y4 + bcut y1 y5 -
        (bcut a b + bcut a y2 + bcut a y3 + bcut b y4 + bcut b y5) = _
    ring
  have hinner : ∀ y0 y1 : Bool,
      (∑ y2 : Bool, ∑ y3 : Bool, ∑ y4 : Bool, ∑ y5 : Bool, ∑ a : Bool, ∑ b : Bool,
        mixerWeight β (e (y0, y1, y2, y3, y4, y5) 0) (e (y0, y1, y2, y3, y4, y5) 1) a b *
          Complex.exp (Complex.I * (γ : ℂ) *
            ((incCut gSix 0 1 (e (y0, y1, y2, y3, y4, y5)) -
              incCut gSix 0 1 (upd₂ 0 1 (e (y0, y1, y2, y3, y4, y5)) a b) : ℝ) : ℂ))) =
      16 * ∑ a : Bool, ∑ b : Bool,
        mixerWeight β y0 y1 a b *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
          nbrFactor 0 γ y0 y1 a b := by
    intro y0 y1
    trans ∑ y2 : Bool, ∑ y3 : Bool, ∑ y4 : Bool, ∑ y5 : Bool, ∑ a : Bool, ∑ b : Bool,
        mixerWeight β y0 y1 a b *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y2 - bcut a y2 : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y3 - bcut a y3 : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y1 y4 - bcut b y4 : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (γ : ℂ) * ((bcut y1 y5 - bcut b y5 : ℝ) : ℂ))
    · refine Finset.sum_congr rfl fun y2 _ => Finset.sum_congr rfl fun y3 _ =>
        Finset.sum_congr rfl fun y4 _ => Finset.sum_congr rfl fun y5 _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      obtain ⟨h0, h1, hdiff⟩ := heval y0 y1 y2 y3 y4 y5 a b
      rw [h0, h1, hdiff]
      push_cast
      rw [mul_add, mul_add, mul_add, mul_add, Complex.exp_add, Complex.exp_add,
        Complex.exp_add, Complex.exp_add]
      ring
    · trans ∑ a : Bool, ∑ b : Bool,
          mixerWeight β y0 y1 a b *
            Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)) *
            (∑ y2 : Bool, Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y2 - bcut a y2 : ℝ) : ℂ))) *
            (∑ y3 : Bool, Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y3 - bcut a y3 : ℝ) : ℂ))) *
            (∑ y4 : Bool, Complex.exp (Complex.I * (γ : ℂ) * ((bcut y1 y4 - bcut b y4 : ℝ) : ℂ))) *
            (∑ y5 : Bool, Complex.exp (Complex.I * (γ : ℂ) * ((bcut y1 y5 - bcut b y5 : ℝ) : ℂ)))
      · have pull : ∀ (A : Bool → Bool → ℂ) (B C D E : Bool → Bool → Bool → ℂ),
            (∑ y2 : Bool, ∑ y3 : Bool, ∑ y4 : Bool, ∑ y5 : Bool, ∑ a : Bool, ∑ b : Bool,
              A a b * B a b y2 * C a b y3 * D a b y4 * E a b y5) =
            ∑ a : Bool, ∑ b : Bool,
              A a b * (∑ y2 : Bool, B a b y2) * (∑ y3 : Bool, C a b y3) *
                (∑ y4 : Bool, D a b y4) * (∑ y5 : Bool, E a b y5) := by
          intro A B C D E
          trans ∑ y2 : Bool, ∑ a : Bool, ∑ b : Bool, ∑ y3 : Bool, ∑ y4 : Bool, ∑ y5 : Bool,
              A a b * B a b y2 * C a b y3 * D a b y4 * E a b y5
          · exact Finset.sum_congr rfl fun y2 _ => sum_bool_swap32 (fun y3 y4 y5 a b =>
              A a b * B a b y2 * C a b y3 * D a b y4 * E a b y5)
          · rw [sum_bool_swap12]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            simp only [← Finset.mul_sum, ← Finset.sum_mul]
        exact pull (fun a b => mixerWeight β y0 y1 a b *
            Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y1 - bcut a b : ℝ) : ℂ)))
          (fun a _ y2 => Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y2 - bcut a y2 : ℝ) : ℂ)))
          (fun a _ y3 => Complex.exp (Complex.I * (γ : ℂ) * ((bcut y0 y3 - bcut a y3 : ℝ) : ℂ)))
          (fun _ b y4 => Complex.exp (Complex.I * (γ : ℂ) * ((bcut y1 y4 - bcut b y4 : ℝ) : ℂ)))
          (fun _ b y5 => Complex.exp (Complex.I * (γ : ℂ) * ((bcut y1 y5 - bcut b y5 : ℝ) : ℂ)))
      · simp only [sum_bool_private, nbrFactor, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        cases y0 <;> cases y1 <;> cases a <;> cases b <;> simp <;> ring
  simp_rw [hinner, ← Finset.mul_sum]
  ring

end FarhiQAOA.Cubic.Eq35Aux

open QAlgorithms FarhiQAOA.Cubic

theorem solution (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : 4 * s + 3 * t ≤ 1) :
    ∃ γ β : ℝ, γ ∈ Set.Icc 0 (2 * Real.pi) ∧ β ∈ Set.Icc 0 Real.pi ∧
      (1731 / 2500 : ℝ) * (3 / 2 - s - t) ≤
        s * fg4 γ β + (4 * s + 3 * t) * fg5 γ β + (3 / 2 - 5 * s - 3 * t) * fg6 γ β := by
  let γ : ℝ := Real.arcsin (1 / Real.sqrt 3)
  let β : ℝ := Real.pi / 8
  refine ⟨γ, β, ?_, ?_, ?_⟩
  · constructor
    · exact Real.arcsin_nonneg.mpr (by positivity)
    · have h1 : γ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
      linarith [Real.pi_pos]
  · change 0 ≤ Real.pi / 8 ∧ Real.pi / 8 ≤ Real.pi
    constructor <;> linarith [Real.pi_pos]
  · rw [FarhiQAOA.Cubic.Eq35Aux.fg4_formula, FarhiQAOA.Cubic.Eq35Aux.fg5_formula,
        FarhiQAOA.Cubic.Eq35Aux.fg6_formula]
    have hsq3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hsq3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hle1 : (1 : ℝ) / Real.sqrt 3 ≤ 1 := by
      rw [div_le_one hsq3_pos]
      nlinarith [hsq3_sq]
    have hge_m1 : (-1 : ℝ) ≤ 1 / Real.sqrt 3 := by linarith [div_nonneg zero_le_one hsq3_pos.le]
    have hsing : Real.sin γ = 1 / Real.sqrt 3 := Real.sin_arcsin hge_m1 hle1
    have hcosg2 : Real.cos γ ^ 2 = 2 / 3 := by
      have hsc := Real.sin_sq_add_cos_sq γ
      rw [hsing, div_pow, one_pow, hsq3_sq] at hsc
      linarith
    have hsing2 : Real.sin γ ^ 2 = 1 / 3 := by
      rw [hsing, div_pow, one_pow, hsq3_sq]
    have hsin4b : Real.sin (4 * β) = 1 := by
      have : 4 * β = Real.pi / 2 := by ring
      rw [this, Real.sin_pi_div_two]
    have hsin2b2 : Real.sin (2 * β) ^ 2 = 1 / 2 := by
      have : 2 * β = Real.pi / 4 := by ring
      rw [this, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [hsin4b, hsin2b2, hcosg2, hsing2, hsing]
    have hsqrt_bound : (1 : ℝ) / (3 * Real.sqrt 3) ≥ 481 / 2500 := by
      have hpos : (0 : ℝ) < 3 * Real.sqrt 3 := by positivity
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hpos]
      nlinarith [hsq3_sq, hsq3_pos]
    have hcomb :
        s * (1 / 2 + 1 / 2 * 1 * (1 / Real.sqrt 3) * (2 / 3) - 1 / 2 * (1 / 3) * (2 / 3)) +
        (4 * s + 3 * t) * (1 / 2 + 1 / 2 * 1 * (1 / Real.sqrt 3) * (2 / 3) - 1 / 2 * (1 / 2) * (1 / 3) * (2 / 3)) +
        (3 / 2 - 5 * s - 3 * t) * (1 / 2 + 1 / 2 * 1 * (1 / Real.sqrt 3) * (2 / 3)) =
        3 / 4 + 1 / (2 * Real.sqrt 3) - 1 / 3 * s - 1 / 6 * t := by
      field_simp
      ring
    rw [hcomb]
    have h32 : (1 : ℝ) / (2 * Real.sqrt 3) = (3 / 2 : ℝ) * (1 / (3 * Real.sqrt 3)) := by
      field_simp
    linarith [h32, hsqrt_bound]
