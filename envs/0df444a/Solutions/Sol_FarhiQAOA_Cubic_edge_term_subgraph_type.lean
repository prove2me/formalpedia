-- Prove2me | solution 1 for FarhiQAOA.Cubic.edge_term_subgraph_type
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:10:39.667647+00:00
-- url     : https://prove2.me/submissions/90b1ad05-1d37-4b80-a4e4-7fa055ed8e5c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic.SubgraphTypeAux

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

/-! ### Part 3: Restriction along an embedding `e : Fin m ↪ Fin n` -/

def incCutSym {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j k : Fin n) (y : Qubits n) : ℝ :=
  ∑ u : Fin n, ∑ v : Fin n,
    if G.Adj u v ∧ (u = j ∨ u = k ∨ v = j ∨ v = k) then edgeCut u v y else 0

lemma incCut_eq_half_incCutSym {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (j k : Fin n) (y : Qubits n) :
    incCut G j k y = (1 / 2 : ℝ) * incCutSym G j k y := by
  have hsplit : incCutSym G j k y =
      incCut G j k y +
        ∑ u : Fin n, ∑ v : Fin n,
          if (v < u ∧ G.Adj u v) ∧ (u = j ∨ u = k ∨ v = j ∨ v = k) then edgeCut u v y else 0 := by
    simp only [incCutSym, incCut, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases hadj : G.Adj u v
    · rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
      · have hnot : ¬(v < u) := not_lt_of_gt hlt
        by_cases hjk : u = j ∨ u = k ∨ v = j ∨ v = k <;> simp [hadj, hlt, hnot, hjk]
      · have hnot : ¬(u < v) := not_lt_of_gt hgt
        by_cases hjk : u = j ∨ u = k ∨ v = j ∨ v = k <;> simp [hadj, hgt, hnot, hjk]
    · simp [hadj]
  have hswap :
      (∑ u : Fin n, ∑ v : Fin n,
        if (v < u ∧ G.Adj u v) ∧ (u = j ∨ u = k ∨ v = j ∨ v = k) then edgeCut u v y else 0) =
      incCut G j k y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
    have hadj : G.Adj u v ↔ G.Adj v u := G.adj_comm u v
    have hjk : (u = j ∨ u = k ∨ v = j ∨ v = k) ↔ (v = j ∨ v = k ∨ u = j ∨ u = k) := by tauto
    have hcut : edgeCut u v y = edgeCut v u y := by simp [edgeCut, eq_comm]
    simp only [hadj, hjk, hcut]
  linarith

lemma incCut_comp_embedding {m n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (j k : Fin n) (j₀ k₀ : Fin m) (e : Fin m ↪ Fin n)
    (hj : e j₀ = j) (hk : e k₀ = k)
    (hcov : ∀ v : Fin n, G.Adj j v ∨ G.Adj k v → v ∈ Finset.univ.map e)
    (hadj_j : ∀ r : Fin m, G.Adj j (e r) ↔ H.Adj j₀ r)
    (hadj_k : ∀ r : Fin m, G.Adj k (e r) ↔ H.Adj k₀ r)
    (y : Qubits n) :
    incCut G j k y = incCut H j₀ k₀ (y ∘ e) := by
  rw [incCut_eq_half_incCutSym G j k y, incCut_eq_half_incCutSym H j₀ k₀ (y ∘ e)]
  congr 1
  simp only [incCutSym]
  have hmem_of_cond : ∀ u v : Fin n,
      G.Adj u v ∧ (u = j ∨ u = k ∨ v = j ∨ v = k) →
        u ∈ Finset.univ.map e ∧ v ∈ Finset.univ.map e := by
    intro u v ⟨huv, hjk⟩
    have hj_mem : j ∈ Finset.univ.map e := hj ▸ Finset.mem_map_of_mem e (Finset.mem_univ j₀)
    have hk_mem : k ∈ Finset.univ.map e := hk ▸ Finset.mem_map_of_mem e (Finset.mem_univ k₀)
    rcases hjk with rfl | rfl | rfl | rfl
    · exact ⟨hj_mem, hcov v (Or.inl huv)⟩
    · exact ⟨hk_mem, hcov v (Or.inr huv)⟩
    · exact ⟨hcov u (Or.inl huv.symm), hj_mem⟩
    · exact ⟨hcov u (Or.inr huv.symm), hk_mem⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun s _ => ?_
      have he_jk : (e r = j ∨ e r = k ∨ e s = j ∨ e s = k) ↔
          (r = j₀ ∨ r = k₀ ∨ s = j₀ ∨ s = k₀) := by
        rw [← hj, ← hk]
        simp [e.injective.eq_iff]
      by_cases hcond : r = j₀ ∨ r = k₀ ∨ s = j₀ ∨ s = k₀
      · have hadj_eq : G.Adj (e r) (e s) ↔ H.Adj r s := by
          rcases hcond with rfl | rfl | rfl | rfl
          · rw [hj, hadj_j s]
          · rw [hk, hadj_k s]
          · rw [hj, G.adj_comm, H.adj_comm, hadj_j r]
          · rw [hk, G.adj_comm, H.adj_comm, hadj_k r]
        by_cases hadj : H.Adj r s
        · rw [if_pos ⟨hadj_eq.mpr hadj, he_jk.mpr hcond⟩, if_pos ⟨hadj, hcond⟩]
          rfl
        · have hnotG : ¬(G.Adj (e r) (e s) ∧ (e r = j ∨ e r = k ∨ e s = j ∨ e s = k)) :=
            fun h => hadj (hadj_eq.mp h.1)
          have hnotH : ¬(H.Adj r s ∧ (r = j₀ ∨ r = k₀ ∨ s = j₀ ∨ s = k₀)) :=
            fun h => hadj h.1
          rw [if_neg hnotG, if_neg hnotH]
      · have hnotG : ¬(G.Adj (e r) (e s) ∧ (e r = j ∨ e r = k ∨ e s = j ∨ e s = k)) :=
          fun h => hcond (he_jk.mp h.2)
        have hnotH : ¬(H.Adj r s ∧ (r = j₀ ∨ r = k₀ ∨ s = j₀ ∨ s = k₀)) :=
          fun h => hcond h.2
        rw [if_neg hnotG, if_neg hnotH]
    · intro v _ hv
      rw [if_neg]
      intro h
      exact hv (hmem_of_cond (e r) v h).2
  · intro u _ hu
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [if_neg]
    intro h
    exact hu (hmem_of_cond u v h).1

lemma upd₂_comp_embedding {m n : ℕ} (j k : Fin n) (j₀ k₀ : Fin m)
    (e : Fin m ↪ Fin n) (hj : e j₀ = j) (hk : e k₀ = k)
    (y : Qubits n) (a b : Bool) :
    (upd₂ j k y a b) ∘ e = upd₂ j₀ k₀ (y ∘ e) a b := by
  ext r
  simp only [Function.comp_apply, upd₂]
  by_cases hrk : r = k₀
  · subst hrk; simp [hk]
  · have herk : e r ≠ k := by rw [← hk]; exact e.injective.ne hrk
    by_cases hrj : r = j₀
    · subst hrj
      have hjk : j ≠ k := hj ▸ herk
      rw [hj, Function.update_of_ne hjk, Function.update_self,
        Function.update_of_ne hrk, Function.update_self]
    · have herj : e r ≠ j := by rw [← hj]; exact e.injective.ne hrj
      simp [hrk, hrj, herk, herj]

lemma sum_comp_embedding {m n : ℕ} (e : Fin m ↪ Fin n) (F : Qubits m → ℂ) :
    (2⁻¹ : ℂ) ^ n * ∑ y : Qubits n, F (y ∘ e) =
      (2⁻¹ : ℂ) ^ m * ∑ x : Qubits m, F x := by
  let Ce : ℂ := ∏ i : Fin n, if ∃ r : Fin m, e r = i then (1 : ℂ) else 2
  have hfiber : ∀ x : Qubits m,
      (∑ y : Qubits n, if y ∘ e = x then (1 : ℂ) else 0) = Ce := by
    intro x
    have hprod : ∀ y : Qubits n,
        (if y ∘ e = x then (1 : ℂ) else 0) =
          ∏ i : Fin n, if ∀ r : Fin m, e r = i → y i = x r then (1 : ℂ) else 0 := by
      intro y
      by_cases hyx : y ∘ e = x
      · rw [if_pos hyx]
        symm
        refine Finset.prod_eq_one fun i _ => ?_
        rw [if_pos]
        intro r hr
        subst hr
        exact congr_fun hyx r
      · rw [if_neg hyx]
        obtain ⟨r, hr⟩ := Function.ne_iff.mp hyx
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ (e r)) ?_
        rw [if_neg]
        intro hall
        exact hr (hall r rfl)
    simp_rw [hprod]
    have hps := (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
      if ∀ r : Fin m, e r = i → b = x r then (1 : ℂ) else 0)).symm
    rw [hps]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : ∃ r : Fin m, e r = i
    · rw [if_pos hi]
      obtain ⟨r₀, rfl⟩ := hi
      have heq : ∀ b : Bool, (∀ r : Fin m, e r = e r₀ → b = x r) ↔ b = x r₀ := by
        intro b
        refine ⟨fun h => h r₀ rfl, fun hb r hr => ?_⟩
        rw [e.injective hr]
        exact hb
      simp_rw [heq]
      rw [Fintype.sum_bool]
      cases x r₀ <;> norm_num
    · rw [if_neg hi]
      have h1 : ∀ b : Bool, (∀ r : Fin m, e r = i → b = x r) ↔ True :=
        fun _ => iff_true_intro fun r hr => False.elim (hi ⟨r, hr⟩)
      simp_rw [h1, if_true]
      rw [Fintype.sum_bool]
      norm_num
  have hsum_F : ∀ Gf : Qubits m → ℂ,
      (∑ y : Qubits n, Gf (y ∘ e)) = Ce * ∑ x : Qubits m, Gf x := by
    intro Gf
    trans ∑ y : Qubits n, ∑ x : Qubits m, if y ∘ e = x then Gf x else 0
    · refine Finset.sum_congr rfl fun y _ => ?_
      simp
    · rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hmul : ∀ y : Qubits n,
          (if y ∘ e = x then Gf x else 0) = (if y ∘ e = x then (1 : ℂ) else 0) * Gf x := by
        intro y; split_ifs <;> ring
      simp_rw [hmul, ← Finset.sum_mul, hfiber x]
  have h1 := hsum_F (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at h1
  have hCe : (2⁻¹ : ℂ) ^ n * Ce = (2⁻¹ : ℂ) ^ m := by
    have h2m_ne : ((2 : ℂ) ^ m) ≠ 0 := pow_ne_zero m (by norm_num)
    apply mul_right_cancel₀ h2m_ne
    calc (2⁻¹ : ℂ) ^ n * Ce * (2 : ℂ) ^ m
        = (2⁻¹ : ℂ) ^ n * (Ce * (2 : ℂ) ^ m) := by ring
      _ = (2⁻¹ : ℂ) ^ n * (2 : ℂ) ^ n := by rw [← h1]
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
      _ = (2⁻¹ : ℂ) ^ m * (2 : ℂ) ^ m := by rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
  rw [hsum_F F, ← mul_assoc, hCe]

lemma edgeTerm1_eq_of_embedding {m n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    {j k : Fin n} (hjk : j ≠ k) {j₀ k₀ : Fin m} (hjk₀ : j₀ ≠ k₀)
    (e : Fin m ↪ Fin n) (hj : e j₀ = j) (hk : e k₀ = k)
    (hcov : ∀ v : Fin n, G.Adj j v ∨ G.Adj k v → v ∈ Finset.univ.map e)
    (hadj_j : ∀ r : Fin m, G.Adj j (e r) ↔ H.Adj j₀ r)
    (hadj_k : ∀ r : Fin m, G.Adj k (e r) ↔ H.Adj k₀ r)
    (γ β : ℝ) :
    edgeTerm1 G γ β j k = edgeTerm1 H γ β j₀ k₀ := by
  rw [edgeTerm1_eq_local G γ β hjk, edgeTerm1_eq_local H γ β hjk₀]
  congr 1
  have hlocal : ∀ y : Qubits n,
      localEdgeSummand G γ β j k y = localEdgeSummand H γ β j₀ k₀ (y ∘ e) := by
    intro y
    simp only [localEdgeSummand]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hyj : y j = (y ∘ e) j₀ := by simp [hj]
    have hyk : y k = (y ∘ e) k₀ := by simp [hk]
    have hinc1 := incCut_comp_embedding G H j k j₀ k₀ e hj hk hcov hadj_j hadj_k y
    have hinc2 := incCut_comp_embedding G H j k j₀ k₀ e hj hk hcov hadj_j hadj_k (upd₂ j k y a b)
    rw [upd₂_comp_embedding j k j₀ k₀ e hj hk y a b] at hinc2
    rw [hyj, hyk, hinc1, hinc2]
  simp_rw [hlocal]
  exact sum_comp_embedding e (localEdgeSummand H γ β j₀ k₀)

/-! ### Part 4: Neighborhood decomposition in a 3-regular graph -/

lemma mem_neighborFinset_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : v ∈ G.neighborFinset u ↔ G.Adj u v := by
  simp [SimpleGraph.mem_neighborFinset]

lemma card_erase_neighborFinset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {u v : Fin n} (huv : G.Adj u v) :
    ((G.neighborFinset u).erase v).card = 2 := by
  have hv : v ∈ G.neighborFinset u := (mem_neighborFinset_iff G u v).mpr huv
  rw [Finset.card_erase_of_mem hv, SimpleGraph.card_neighborFinset_eq_degree, h3 u]

lemma inter_erase_neighborFinset_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (j k : Fin n) :
    ((G.neighborFinset j).erase k) ∩ ((G.neighborFinset k).erase j) =
      Finset.univ.filter fun u => G.Adj j u ∧ G.Adj k u := by
  ext u
  simp only [Finset.mem_inter, Finset.mem_erase, SimpleGraph.mem_neighborFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨⟨_, hju⟩, ⟨_, hku⟩⟩ => ⟨hju, hku⟩,
    fun ⟨hju, hku⟩ => ⟨⟨(G.ne_of_adj hku).symm, hju⟩, ⟨(G.ne_of_adj hju).symm, hku⟩⟩⟩

lemma gFour_adj_zero (r : Fin 4) : gFour.Adj 0 r ↔ r = 1 ∨ r = 2 ∨ r = 3 := by
  fin_cases r <;> decide

lemma gFour_adj_one (r : Fin 4) : gFour.Adj 1 r ↔ r = 0 ∨ r = 2 ∨ r = 3 := by
  fin_cases r <;> decide

lemma gFive_adj_zero (r : Fin 5) : gFive.Adj 0 r ↔ r = 1 ∨ r = 2 ∨ r = 3 := by
  fin_cases r <;> decide

lemma gFive_adj_one (r : Fin 5) : gFive.Adj 1 r ↔ r = 0 ∨ r = 2 ∨ r = 4 := by
  fin_cases r <;> decide

lemma gSix_adj_zero (r : Fin 6) : gSix.Adj 0 r ↔ r = 1 ∨ r = 2 ∨ r = 3 := by
  fin_cases r <;> decide

lemma gSix_adj_one (r : Fin 6) : gSix.Adj 1 r ↔ r = 0 ∨ r = 4 ∨ r = 5 := by
  fin_cases r <;> decide

lemma case_commonNbrCount_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {j k : Fin n} (hjk : G.Adj j k)
    (hc : commonNbrCount G j k = 2) (γ β : ℝ) :
    edgeTerm1 G γ β j k = fg4 γ β := by
  let Nj := (G.neighborFinset j).erase k
  let Nk := (G.neighborFinset k).erase j
  have hNj_card : Nj.card = 2 := card_erase_neighborFinset G h3 hjk
  have hNk_card : Nk.card = 2 := card_erase_neighborFinset G h3 hjk.symm
  have hinter_card : (Nj ∩ Nk).card = 2 := by
    rw [inter_erase_neighborFinset_eq]
    exact hc
  have hNj_eq : Nj ∩ Nk = Nj :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hNk_eq : Nj ∩ Nk = Nk :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  obtain ⟨u, v, huv, huv_set⟩ := Finset.card_eq_two.mp hinter_card
  have hNj_uv : Nj = {u, v} := hNj_eq.symm.trans huv_set
  have hNk_uv : Nk = {u, v} := hNk_eq.symm.trans huv_set
  have hu_mem : u ∈ Nj := by rw [hNj_uv]; simp
  have hv_mem : v ∈ Nj := by rw [hNj_uv]; simp
  have hu_k : u ∈ Nk := by rw [hNk_uv]; simp
  have hv_k : v ∈ Nk := by rw [hNk_uv]; simp
  have hju : G.Adj j u := ((mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hu_mem))
  have hjv : G.Adj j v := ((mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hv_mem))
  have hku : G.Adj k u := ((mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hu_k))
  have hkv : G.Adj k v := ((mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hv_k))
  have hjk_ne : j ≠ k := G.ne_of_adj hjk
  have hju_ne : j ≠ u := G.ne_of_adj hju
  have hjv_ne : j ≠ v := G.ne_of_adj hjv
  have hku_ne : k ≠ u := G.ne_of_adj hku
  have hkv_ne : k ≠ v := G.ne_of_adj hkv
  let f : Fin 4 → Fin n := ![j, k, u, v]
  have hf_inj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [f] at hab ⊢ <;>
      first | exact False.elim (hjk_ne hab) | exact False.elim (hjk_ne hab.symm)
            | exact False.elim (hju_ne hab) | exact False.elim (hju_ne hab.symm)
            | exact False.elim (hjv_ne hab) | exact False.elim (hjv_ne hab.symm)
            | exact False.elim (hku_ne hab) | exact False.elim (hku_ne hab.symm)
            | exact False.elim (hkv_ne hab) | exact False.elim (hkv_ne hab.symm)
            | exact False.elim (huv hab) | exact False.elim (huv hab.symm)
  let e : Fin 4 ↪ Fin n := ⟨f, hf_inj⟩
  refine edgeTerm1_eq_of_embedding G gFour hjk_ne (by decide : (0 : Fin 4) ≠ 1)
    e rfl rfl ?_ ?_ ?_ γ β
  · intro w hw
    rw [Finset.mem_map]
    rcases hw with hjw | hkw
    · by_cases hwk : w = k
      · exact ⟨1, Finset.mem_univ _, hwk.symm⟩
      · have hwNj : w ∈ Nj := Finset.mem_erase.mpr ⟨hwk, (mem_neighborFinset_iff G _ _).mpr hjw⟩
        rw [hNj_uv, Finset.mem_insert, Finset.mem_singleton] at hwNj
        rcases hwNj with rfl | rfl
        · exact ⟨2, Finset.mem_univ _, rfl⟩
        · exact ⟨3, Finset.mem_univ _, rfl⟩
    · by_cases hwj : w = j
      · exact ⟨0, Finset.mem_univ _, hwj.symm⟩
      · have hwNk : w ∈ Nk := Finset.mem_erase.mpr ⟨hwj, (mem_neighborFinset_iff G _ _).mpr hkw⟩
        rw [hNk_uv, Finset.mem_insert, Finset.mem_singleton] at hwNk
        rcases hwNk with rfl | rfl
        · exact ⟨2, Finset.mem_univ _, rfl⟩
        · exact ⟨3, Finset.mem_univ _, rfl⟩
  · intro r
    rw [gFour_adj_zero]
    fin_cases r <;> simp [e, f, G.loopless.irrefl j, hjk, hju, hjv]
  · intro r
    rw [gFour_adj_one]
    fin_cases r <;> simp [e, f, G.loopless.irrefl k, hjk.symm, hku, hkv]

lemma case_commonNbrCount_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {j k : Fin n} (hjk : G.Adj j k)
    (hc : commonNbrCount G j k = 1) (γ β : ℝ) :
    edgeTerm1 G γ β j k = fg5 γ β := by
  let Nj := (G.neighborFinset j).erase k
  let Nk := (G.neighborFinset k).erase j
  have hNj_card : Nj.card = 2 := card_erase_neighborFinset G h3 hjk
  have hNk_card : Nk.card = 2 := card_erase_neighborFinset G h3 hjk.symm
  have hinter_card : (Nj ∩ Nk).card = 1 := by
    rw [inter_erase_neighborFinset_eq]
    exact hc
  obtain ⟨u, hu_set⟩ := Finset.card_eq_one.mp hinter_card
  have hu_inter : u ∈ Nj ∩ Nk := by rw [hu_set]; simp
  have hu_Nj : u ∈ Nj := Finset.mem_of_mem_inter_left hu_inter
  have hu_Nk : u ∈ Nk := Finset.mem_of_mem_inter_right hu_inter
  have hNj_erase_card : (Nj.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem hu_Nj, hNj_card]
  have hNk_erase_card : (Nk.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem hu_Nk, hNk_card]
  obtain ⟨v, hv_set⟩ := Finset.card_eq_one.mp hNj_erase_card
  obtain ⟨w, hw_set⟩ := Finset.card_eq_one.mp hNk_erase_card
  have hv_mem_erase : v ∈ Nj.erase u := by rw [hv_set]; simp
  have hw_mem_erase : w ∈ Nk.erase u := by rw [hw_set]; simp
  have hvu : v ≠ u := (Finset.mem_erase.mp hv_mem_erase).1
  have hv_Nj : v ∈ Nj := (Finset.mem_erase.mp hv_mem_erase).2
  have hwu : w ≠ u := (Finset.mem_erase.mp hw_mem_erase).1
  have hw_Nk : w ∈ Nk := (Finset.mem_erase.mp hw_mem_erase).2
  have hNj_uv : Nj = {u, v} := by
    ext x
    by_cases hxu : x = u
    · subst hxu; simp [hu_Nj]
    · have : x ∈ Nj ↔ x ∈ Nj.erase u := ⟨fun hx => Finset.mem_erase.mpr ⟨hxu, hx⟩, Finset.mem_of_mem_erase⟩
      rw [this, hv_set]
      simp [hxu]
  have hNk_uw : Nk = {u, w} := by
    ext x
    by_cases hxu : x = u
    · subst hxu; simp [hu_Nk]
    · have : x ∈ Nk ↔ x ∈ Nk.erase u := ⟨fun hx => Finset.mem_erase.mpr ⟨hxu, hx⟩, Finset.mem_of_mem_erase⟩
      rw [this, hw_set]
      simp [hxu]
  have hv_not_Nk : v ∉ Nk := by
    intro hvNk
    have hv_inter : v ∈ Nj ∩ Nk := Finset.mem_inter.mpr ⟨hv_Nj, hvNk⟩
    rw [hu_set, Finset.mem_singleton] at hv_inter
    exact hvu hv_inter
  have hw_not_Nj : w ∉ Nj := by
    intro hwNj
    have hw_inter : w ∈ Nj ∩ Nk := Finset.mem_inter.mpr ⟨hwNj, hw_Nk⟩
    rw [hu_set, Finset.mem_singleton] at hw_inter
    exact hwu hw_inter
  have hvw : v ≠ w := by
    rintro rfl
    exact hv_not_Nk hw_Nk
  have hju : G.Adj j u := (mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hu_Nj)
  have hjv : G.Adj j v := (mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hv_Nj)
  have hku : G.Adj k u := (mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hu_Nk)
  have hkw : G.Adj k w := (mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hw_Nk)
  have hjk_ne : j ≠ k := G.ne_of_adj hjk
  have hju_ne : j ≠ u := G.ne_of_adj hju
  have hjv_ne : j ≠ v := G.ne_of_adj hjv
  have hku_ne : k ≠ u := G.ne_of_adj hku
  have hkw_ne : k ≠ w := G.ne_of_adj hkw
  have hkv_ne : k ≠ v := (Finset.mem_erase.mp hv_Nj).1.symm
  have hjw_ne : j ≠ w := (Finset.mem_erase.mp hw_Nk).1.symm
  have hnot_jw : ¬G.Adj j w := by
    intro hjw
    exact hw_not_Nj (Finset.mem_erase.mpr ⟨hkw_ne.symm, (mem_neighborFinset_iff G _ _).mpr hjw⟩)
  have hnot_kv : ¬G.Adj k v := by
    intro hkv
    exact hv_not_Nk (Finset.mem_erase.mpr ⟨hjv_ne.symm, (mem_neighborFinset_iff G _ _).mpr hkv⟩)
  let f : Fin 5 → Fin n := ![j, k, u, v, w]
  have hf_inj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [f] at hab ⊢ <;>
      first | exact False.elim (hjk_ne hab) | exact False.elim (hjk_ne hab.symm)
            | exact False.elim (hju_ne hab) | exact False.elim (hju_ne hab.symm)
            | exact False.elim (hjv_ne hab) | exact False.elim (hjv_ne hab.symm)
            | exact False.elim (hjw_ne hab) | exact False.elim (hjw_ne hab.symm)
            | exact False.elim (hku_ne hab) | exact False.elim (hku_ne hab.symm)
            | exact False.elim (hkv_ne hab) | exact False.elim (hkv_ne hab.symm)
            | exact False.elim (hkw_ne hab) | exact False.elim (hkw_ne hab.symm)
            | exact False.elim (hvu hab) | exact False.elim (hvu hab.symm)
            | exact False.elim (hwu hab) | exact False.elim (hwu hab.symm)
            | exact False.elim (hvw hab) | exact False.elim (hvw hab.symm)
  let e : Fin 5 ↪ Fin n := ⟨f, hf_inj⟩
  refine edgeTerm1_eq_of_embedding G gFive hjk_ne (by decide : (0 : Fin 5) ≠ 1)
    e rfl rfl ?_ ?_ ?_ γ β
  · intro x hx
    rw [Finset.mem_map]
    rcases hx with hjx | hkx
    · by_cases hxk : x = k
      · exact ⟨1, Finset.mem_univ _, hxk.symm⟩
      · have hxNj : x ∈ Nj := Finset.mem_erase.mpr ⟨hxk, (mem_neighborFinset_iff G _ _).mpr hjx⟩
        rw [hNj_uv, Finset.mem_insert, Finset.mem_singleton] at hxNj
        rcases hxNj with rfl | rfl
        · exact ⟨2, Finset.mem_univ _, rfl⟩
        · exact ⟨3, Finset.mem_univ _, rfl⟩
    · by_cases hxj : x = j
      · exact ⟨0, Finset.mem_univ _, hxj.symm⟩
      · have hxNk : x ∈ Nk := Finset.mem_erase.mpr ⟨hxj, (mem_neighborFinset_iff G _ _).mpr hkx⟩
        rw [hNk_uw, Finset.mem_insert, Finset.mem_singleton] at hxNk
        rcases hxNk with rfl | rfl
        · exact ⟨2, Finset.mem_univ _, rfl⟩
        · exact ⟨4, Finset.mem_univ _, rfl⟩
  · intro r
    rw [gFive_adj_zero]
    fin_cases r <;> simp [e, f, G.loopless.irrefl j, hjk, hju, hjv, hnot_jw]
  · intro r
    rw [gFive_adj_one]
    fin_cases r <;> simp [e, f, G.loopless.irrefl k, hjk.symm, hku, hnot_kv, hkw]

lemma case_commonNbrCount_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {j k : Fin n} (hjk : G.Adj j k)
    (hc : commonNbrCount G j k = 0) (γ β : ℝ) :
    edgeTerm1 G γ β j k = fg6 γ β := by
  let Nj := (G.neighborFinset j).erase k
  let Nk := (G.neighborFinset k).erase j
  have hNj_card : Nj.card = 2 := card_erase_neighborFinset G h3 hjk
  have hNk_card : Nk.card = 2 := card_erase_neighborFinset G h3 hjk.symm
  have hinter_empty : Nj ∩ Nk = ∅ := by
    rw [← Finset.card_eq_zero, inter_erase_neighborFinset_eq]
    exact hc
  obtain ⟨u₁, u₂, hu12, hNj_u⟩ := Finset.card_eq_two.mp hNj_card
  obtain ⟨v₁, v₂, hv12, hNk_v⟩ := Finset.card_eq_two.mp hNk_card
  have hu1_Nj : u₁ ∈ Nj := by rw [hNj_u]; simp
  have hu2_Nj : u₂ ∈ Nj := by rw [hNj_u]; simp
  have hv1_Nk : v₁ ∈ Nk := by rw [hNk_v]; simp
  have hv2_Nk : v₂ ∈ Nk := by rw [hNk_v]; simp
  have hnot_Nk_of_Nj : ∀ x ∈ Nj, x ∉ Nk := by
    intro x hxNj hxNk
    have : x ∈ Nj ∩ Nk := Finset.mem_inter.mpr ⟨hxNj, hxNk⟩
    rw [hinter_empty] at this
    exact Finset.notMem_empty x this
  have hu1_not_Nk : u₁ ∉ Nk := hnot_Nk_of_Nj u₁ hu1_Nj
  have hu2_not_Nk : u₂ ∉ Nk := hnot_Nk_of_Nj u₂ hu2_Nj
  have hv1_not_Nj : v₁ ∉ Nj := fun h => hnot_Nk_of_Nj v₁ h hv1_Nk
  have hv2_not_Nj : v₂ ∉ Nj := fun h => hnot_Nk_of_Nj v₂ h hv2_Nk
  have hju1 : G.Adj j u₁ := (mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hu1_Nj)
  have hju2 : G.Adj j u₂ := (mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hu2_Nj)
  have hkv1 : G.Adj k v₁ := (mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hv1_Nk)
  have hkv2 : G.Adj k v₂ := (mem_neighborFinset_iff G _ _).mp (Finset.mem_of_mem_erase hv2_Nk)
  have hjk_ne : j ≠ k := G.ne_of_adj hjk
  have hju1_ne : j ≠ u₁ := G.ne_of_adj hju1
  have hju2_ne : j ≠ u₂ := G.ne_of_adj hju2
  have hku1_ne : k ≠ u₁ := (Finset.mem_erase.mp hu1_Nj).1.symm
  have hku2_ne : k ≠ u₂ := (Finset.mem_erase.mp hu2_Nj).1.symm
  have hjv1_ne : j ≠ v₁ := (Finset.mem_erase.mp hv1_Nk).1.symm
  have hjv2_ne : j ≠ v₂ := (Finset.mem_erase.mp hv2_Nk).1.symm
  have hkv1_ne : k ≠ v₁ := G.ne_of_adj hkv1
  have hkv2_ne : k ≠ v₂ := G.ne_of_adj hkv2
  have hu1v1 : u₁ ≠ v₁ := by rintro rfl; exact hu1_not_Nk hv1_Nk
  have hu1v2 : u₁ ≠ v₂ := by rintro rfl; exact hu1_not_Nk hv2_Nk
  have hu2v1 : u₂ ≠ v₁ := by rintro rfl; exact hu2_not_Nk hv1_Nk
  have hu2v2 : u₂ ≠ v₂ := by rintro rfl; exact hu2_not_Nk hv2_Nk
  have hnot_jv1 : ¬G.Adj j v₁ := fun h =>
    hv1_not_Nj (Finset.mem_erase.mpr ⟨hkv1_ne.symm, (mem_neighborFinset_iff G _ _).mpr h⟩)
  have hnot_jv2 : ¬G.Adj j v₂ := fun h =>
    hv2_not_Nj (Finset.mem_erase.mpr ⟨hkv2_ne.symm, (mem_neighborFinset_iff G _ _).mpr h⟩)
  have hnot_ku1 : ¬G.Adj k u₁ := fun h =>
    hu1_not_Nk (Finset.mem_erase.mpr ⟨hju1_ne.symm, (mem_neighborFinset_iff G _ _).mpr h⟩)
  have hnot_ku2 : ¬G.Adj k u₂ := fun h =>
    hu2_not_Nk (Finset.mem_erase.mpr ⟨hju2_ne.symm, (mem_neighborFinset_iff G _ _).mpr h⟩)
  let f : Fin 6 → Fin n := ![j, k, u₁, u₂, v₁, v₂]
  have hf_inj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [f] at hab ⊢ <;>
      first | exact False.elim (hjk_ne hab) | exact False.elim (hjk_ne hab.symm)
            | exact False.elim (hju1_ne hab) | exact False.elim (hju1_ne hab.symm)
            | exact False.elim (hju2_ne hab) | exact False.elim (hju2_ne hab.symm)
            | exact False.elim (hjv1_ne hab) | exact False.elim (hjv1_ne hab.symm)
            | exact False.elim (hjv2_ne hab) | exact False.elim (hjv2_ne hab.symm)
            | exact False.elim (hku1_ne hab) | exact False.elim (hku1_ne hab.symm)
            | exact False.elim (hku2_ne hab) | exact False.elim (hku2_ne hab.symm)
            | exact False.elim (hkv1_ne hab) | exact False.elim (hkv1_ne hab.symm)
            | exact False.elim (hkv2_ne hab) | exact False.elim (hkv2_ne hab.symm)
            | exact False.elim (hu12 hab) | exact False.elim (hu12 hab.symm)
            | exact False.elim (hv12 hab) | exact False.elim (hv12 hab.symm)
            | exact False.elim (hu1v1 hab) | exact False.elim (hu1v1 hab.symm)
            | exact False.elim (hu1v2 hab) | exact False.elim (hu1v2 hab.symm)
            | exact False.elim (hu2v1 hab) | exact False.elim (hu2v1 hab.symm)
            | exact False.elim (hu2v2 hab) | exact False.elim (hu2v2 hab.symm)
  let e : Fin 6 ↪ Fin n := ⟨f, hf_inj⟩
  refine edgeTerm1_eq_of_embedding G gSix hjk_ne (by decide : (0 : Fin 6) ≠ 1)
    e rfl rfl ?_ ?_ ?_ γ β
  · intro x hx
    rw [Finset.mem_map]
    rcases hx with hjx | hkx
    · by_cases hxk : x = k
      · exact ⟨1, Finset.mem_univ _, hxk.symm⟩
      · have hxNj : x ∈ Nj := Finset.mem_erase.mpr ⟨hxk, (mem_neighborFinset_iff G _ _).mpr hjx⟩
        rw [hNj_u, Finset.mem_insert, Finset.mem_singleton] at hxNj
        rcases hxNj with rfl | rfl
        · exact ⟨2, Finset.mem_univ _, rfl⟩
        · exact ⟨3, Finset.mem_univ _, rfl⟩
    · by_cases hxj : x = j
      · exact ⟨0, Finset.mem_univ _, hxj.symm⟩
      · have hxNk : x ∈ Nk := Finset.mem_erase.mpr ⟨hxj, (mem_neighborFinset_iff G _ _).mpr hkx⟩
        rw [hNk_v, Finset.mem_insert, Finset.mem_singleton] at hxNk
        rcases hxNk with rfl | rfl
        · exact ⟨4, Finset.mem_univ _, rfl⟩
        · exact ⟨5, Finset.mem_univ _, rfl⟩
  · intro r
    rw [gSix_adj_zero]
    fin_cases r <;> simp [e, f, G.loopless.irrefl j, hjk, hju1, hju2, hnot_jv1, hnot_jv2]
  · intro r
    rw [gSix_adj_one]
    fin_cases r <;> simp [e, f, G.loopless.irrefl k, hjk.symm, hnot_ku1, hnot_ku2, hkv1, hkv2]

end FarhiQAOA.Cubic.SubgraphTypeAux

open QAlgorithms FarhiQAOA.Cubic FarhiQAOA.Cubic.SubgraphTypeAux in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (j k : Fin n) (hjk : G.Adj j k) (γ β : ℝ) :
    (commonNbrCount G j k = 2 → edgeTerm1 G γ β j k = fg4 γ β) ∧
      (commonNbrCount G j k = 1 → edgeTerm1 G γ β j k = fg5 γ β) ∧
      (commonNbrCount G j k = 0 → edgeTerm1 G γ β j k = fg6 γ β) :=
  ⟨fun hc => case_commonNbrCount_two G h3 hjk hc γ β,
   fun hc => case_commonNbrCount_one G h3 hjk hc γ β,
   fun hc => case_commonNbrCount_zero G h3 hjk hc γ β⟩
