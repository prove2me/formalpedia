-- Prove2me | solution 1 for CuttingStock63.Fractional.fractional_edge_criterion
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T05:10:33.014355+00:00
-- url     : https://prove2.me/submissions/f28441f4-72b3-4dd3-999a-bfb5574b246e

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional
import Definitions.Def_MatousekLP_BFS_EquationalForm
import Definitions.Def_CuttingStock63_Fractional_Edge
open scoped BigOperators Classical
open Matrix DermanSeqDecisions.LinProg CuttingStock63.Fractional

namespace CuttingFractionalProof
end CuttingFractionalProof

open scoped BigOperators Classical
open Module Matrix DermanSeqDecisions.LinProg CuttingStock63.Fractional

namespace CuttingFractionalProof

variable {m n : ℕ}

noncomputable def columnBasis (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n))
    (hB : MatousekLP.BFS.IsBasis A B) : Basis B ℝ (Fin m → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' (fun j : B => fun i => A i j) hB.2
    (by simpa using hB.1)

@[simp] theorem columnBasis_apply (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Finset (Fin n)) (hB : MatousekLP.BFS.IsBasis A B) (j : B) :
    columnBasis A B hB j = fun i => A i j := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℝ)
    (fun j : B => fun i => A i j) hB.2 (by simpa using hB.1)) j

noncomputable def basisLift (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n))
    (hB : MatousekLP.BFS.IsBasis A B) (u : Fin m → ℝ) : Fin n → ℝ :=
  fun k => if hk : k ∈ B then (columnBasis A B hB).repr u ⟨k, hk⟩ else 0

@[simp] theorem basisLift_outside (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Finset (Fin n)) (hB : MatousekLP.BFS.IsBasis A B) (u : Fin m → ℝ)
    (k : Fin n) (hk : k ∉ B) : basisLift A B hB u k = 0 := by
  simp [basisLift, hk]

 theorem supported_sum (B : Finset (Fin n)) (f : Fin n → ℝ)
    (hf : ∀ k, k ∉ B → f k = 0) : (∑ k, f k) = ∑ k : B, f k := by
  rw [← Finset.sum_subtype B (by simp) f]
  exact (Finset.sum_subset B.subset_univ (by intro k _ hk; exact hf k hk)).symm

 theorem basisLift_mulVec (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n))
    (hB : MatousekLP.BFS.IsBasis A B) (u : Fin m → ℝ) :
    A *ᵥ basisLift A B hB u = u := by
  funext i
  change (∑ k, A i k * basisLift A B hB u k) = u i
  rw [supported_sum B _ (by intro k hk; simp [hk])]
  have h := congrFun ((columnBasis A B hB).sum_repr u) i
  simpa [basisLift, Finset.sum_apply, mul_comm] using h

 theorem supported_kernel_zero (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Finset (Fin n)) (hB : MatousekLP.BFS.IsBasis A B) (z : Fin n → ℝ)
    (hz : ∀ k, k ∉ B → z k = 0) (hAz : A *ᵥ z = 0) : z = 0 := by
  have hs : (∑ k : B, z k • (fun i => A i k)) = (0 : Fin m → ℝ) := by
    funext i
    have h := congrFun hAz i
    change (∑ k, A i k * z k) = 0 at h
    rw [supported_sum B _ (by intro k hk; simp [hz k hk])] at h
    simpa [Finset.sum_apply, mul_comm] using h
  have hc := (Fintype.linearIndependent_iff.mp hB.2) (fun k : B => z k) hs
  funext k
  by_cases hk : k ∈ B
  · exact hc ⟨k, hk⟩
  · exact hz k hk

noncomputable def basisEdge (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n))
    (hB : MatousekLP.BFS.IsBasis A B) (j : Fin n) : Fin n → ℝ :=
  Pi.single j 1 - basisLift A B hB (fun i => A i j)

 theorem basisEdge_spec (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n))
    (hB : MatousekLP.BFS.IsBasis A B) (j : Fin n) (hj : j ∉ B) :
    IsEdgeDirection A B j (basisEdge A B hB j) := by
  refine ⟨hj, ?_, ?_, ?_⟩
  · rw [basisEdge, mulVec_sub, basisLift_mulVec, mulVec_single_one]
    exact sub_self _
  · simp [basisEdge, hj]
  · intro k hk hkj
    simp [basisEdge, hk, hkj]

 theorem edge_decomposition (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (B : Finset (Fin n)) (xbar x : Fin n → ℝ)
    (hxbar : IsBasicFeasibleFor A b B xbar) (hx : IsFeasible11 A b x) :
    ∃ v : {j : Fin n // j ∉ B} → (Fin n → ℝ),
      (∀ j, IsEdgeDirection A B j.1 (v j)) ∧
      x - xbar = ∑ j, x j.1 • v j := by
  let v : {j : Fin n // j ∉ B} → (Fin n → ℝ) :=
    fun j => basisEdge A B hxbar.2.1 j
  have hv (j : {j : Fin n // j ∉ B}) : IsEdgeDirection A B j.1 (v j) :=
    basisEdge_spec A B hxbar.2.1 j j.2
  refine ⟨v, hv, ?_⟩
  have hs : ∀ k, k ∉ B → (∑ j, x j.1 • v j) k = x k := by
    intro k hk
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (⟨k, hk⟩ : {j : Fin n // j ∉ B})]
    · simp [(hv ⟨k, hk⟩).2.2.1]
    · intro j _ hj
      have hkj : k ≠ j.1 := by
        intro he
        apply hj
        exact Subtype.ext he.symm
      rw [(hv j).2.2.2 k hk hkj, mul_zero]
    · simp
  have hxA : A *ᵥ x = b := funext hx.2
  have hbA : A *ᵥ xbar = b := funext hxbar.1.2
  have hz := supported_kernel_zero A B hxbar.2.1
    (x - xbar - ∑ j, x j.1 • v j)
    (by intro k hk; simp [hs k hk, hxbar.2.2 k hk])
    (by simp [mulVec_sub, mulVec_sum, mulVec_smul, hxA, hbA, (hv _).2.1])
  exact sub_eq_zero.mp hz

end CuttingFractionalProof

open DermanSeqDecisions.LinProg
open scoped BigOperators

namespace CuttingFractionalProof

noncomputable def linearValue {n : ℕ} (c x : Fin n → ℝ) : ℝ := ∑ i, c i * x i

noncomputable def reduced {n : ℕ} (c d x v : Fin n → ℝ) : ℝ :=
  linearValue d x * linearValue c v - linearValue c x * linearValue d v

lemma linearValue_add {n : ℕ} (c x y : Fin n → ℝ) :
    linearValue c (x+y) = linearValue c x + linearValue c y := by
  simp [linearValue, mul_add, Finset.sum_add_distrib]

lemma linearValue_sub {n : ℕ} (c x y : Fin n → ℝ) :
    linearValue c (x-y) = linearValue c x - linearValue c y := by
  simp [linearValue, mul_sub, Finset.sum_sub_distrib]

lemma linearValue_smul {n : ℕ} (c x : Fin n → ℝ) (a : ℝ) :
    linearValue c (a • x) = a * linearValue c x := by
  simp only [linearValue, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma linearValue_sum {n : ℕ} {J : Type*} [Fintype J] (c : Fin n → ℝ)
    (x : J → Fin n → ℝ) : linearValue c (∑ j, x j) = ∑ j, linearValue c (x j) := by
  simp only [linearValue, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma reduced_sub {n : ℕ} (c d x u v : Fin n → ℝ) :
    reduced c d x (u-v) = reduced c d x u - reduced c d x v := by
  simp only [reduced, linearValue_sub]
  ring

lemma reduced_self {n : ℕ} (c d x : Fin n → ℝ) : reduced c d x x = 0 := by
  unfold reduced
  ring

lemma reduced_smul {n : ℕ} (c d x v : Fin n → ℝ) (a : ℝ) :
    reduced c d x (a • v) = a * reduced c d x v := by
  simp only [reduced, linearValue_smul]
  ring

lemma reduced_sum {n : ℕ} {J : Type*} [Fintype J] (c d x : Fin n → ℝ)
    (v : J → Fin n → ℝ) : reduced c d x (∑ j, v j) = ∑ j, reduced c d x (v j) := by
  simp only [reduced, linearValue_sum, Finset.mul_sum, Finset.sum_sub_distrib]

lemma quotient_deriv {n : ℕ} (c d x v : Fin n → ℝ) (hd : linearValue d x ≠ 0) :
    deriv (fun τ : ℝ => fracObj c d (x + τ • v)) 0 =
      reduced c d x v / (linearValue d x)^2 := by
  have hc : HasDerivAt (fun τ : ℝ => linearValue c x + τ * linearValue c v)
      (linearValue c v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (linearValue c v)).const_add (linearValue c x)
  have hd' : HasDerivAt (fun τ : ℝ => linearValue d x + τ * linearValue d v)
      (linearValue d v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (linearValue d v)).const_add (linearValue d x)
  have hq := (hc.fun_div hd' (by simpa using hd)).deriv
  have he : (fun τ : ℝ => fracObj c d (x + τ • v)) =
      (fun τ : ℝ => (linearValue c x + τ * linearValue c v) /
        (linearValue d x + τ * linearValue d v)) := by
    funext τ
    change linearValue c (x+τ•v) / linearValue d (x+τ•v) = _
    rw [linearValue_add, linearValue_add, linearValue_smul, linearValue_smul]
  rw [he]
  simpa [reduced, mul_comm] using hq

lemma reduced_nonneg_of_deriv_nonneg {n : ℕ} (c d x v : Fin n → ℝ)
    (hd : 0 < linearValue d x)
    (h : 0 ≤ deriv (fun τ : ℝ => fracObj c d (x + τ • v)) 0) :
    0 ≤ reduced c d x v := by
  rw [quotient_deriv c d x v hd.ne'] at h
  simpa using (le_div_iff₀ (sq_pos_of_pos hd)).mp h

lemma ratio_le_of_reduced_nonneg {n : ℕ} (c d x y : Fin n → ℝ)
    (hx : 0 < linearValue d x) (hy : 0 < linearValue d y)
    (h : 0 ≤ reduced c d x (y-x)) : fracObj c d x ≤ fracObj c d y := by
  rw [reduced_sub, reduced_self, sub_zero] at h
  change linearValue c x / linearValue d x ≤ linearValue c y / linearValue d y
  apply (div_le_div_iff₀ hx hy).2
  unfold reduced at h
  nlinarith

end CuttingFractionalProof

open scoped BigOperators

namespace CuttingStock63.Fractional
open DermanSeqDecisions.LinProg
theorem fractional_edge_criterion {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c d : Fin n → ℝ) (B : Finset (Fin n)) (xbar : Fin n → ℝ)
    (hden : ∀ x, IsFeasible11 A b x → 0 < ∑ i, d i * x i)
    (hxbar : IsBasicFeasibleFor A b B xbar)
    (hedge : ∀ j, j ∉ B → ∀ v, IsEdgeDirection A B j v →
      0 ≤ deriv (fun τ : ℝ => fracObj c d (xbar + τ • v)) 0) :
    ∀ x, IsFeasible11 A b x → fracObj c d xbar ≤ fracObj c d x := by
  classical
  intro x hx
  obtain ⟨v, hv, he⟩ := CuttingFractionalProof.edge_decomposition A b B xbar x hxbar hx
  apply CuttingFractionalProof.ratio_le_of_reduced_nonneg c d xbar x
    (hden xbar hxbar.1) (hden x hx)
  rw [he, CuttingFractionalProof.reduced_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [CuttingFractionalProof.reduced_smul]
  apply mul_nonneg (hx.1 j.1)
  exact CuttingFractionalProof.reduced_nonneg_of_deriv_nonneg c d xbar (v j)
    (hden xbar hxbar.1) (hedge j.1 j.2 (v j) (hv j))
end CuttingStock63.Fractional

open DermanSeqDecisions.LinProg CuttingStock63.Fractional

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c d : Fin n → ℝ) (B : Finset (Fin n)) (xbar : Fin n → ℝ)
    (hden : ∀ x, IsFeasible11 A b x → 0 < ∑ i, d i * x i)
    (hxbar : IsBasicFeasibleFor A b B xbar)
    (hedge : ∀ j, j ∉ B → ∀ v, IsEdgeDirection A B j v →
      0 ≤ deriv (fun τ : ℝ => fracObj c d (xbar + τ • v)) 0) :
    ∀ x, IsFeasible11 A b x → fracObj c d xbar ≤ fracObj c d x := by
  exact CuttingStock63.Fractional.fractional_edge_criterion A b c d B xbar hden hxbar hedge
