-- Prove2me | solution 1 for Chi2QEC.photonLoss_hamming_bound
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T13:48:27.467071+00:00
-- url     : https://prove2.me/submissions/b3447a50-453d-4d1d-82a9-d88006ef9d68

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Definitions.Def_Chi2QEC_pumpSubspace
import Definitions.Def_Chi2QEC_lossError
import Definitions.Def_Chi2QEC_SatisfiesKL
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


set_option autoImplicit false

namespace Chi2QEC

/-- A pump index is determined by its signal occupation in each qudit. -/
theorem pumpIndex_signal_injective (n q : ℕ) :
    Function.Injective (fun x : pumpIndex n q => fun l : Fin n => x.1 l 0) := by
  intro x y h
  apply Subtype.ext
  funext l k
  have hs : x.1 l 0 = y.1 l 0 := congrFun h l
  have hx := x.2 l
  have hy := y.2 l
  fin_cases k
  · exact hs
  · exact hx.1.symm.trans (hs.trans hy.1)
  · apply Fin.ext
    change (x.1 l 2 : ℕ) = (y.1 l 2 : ℕ)
    have hsn := congrArg Fin.val hs
    have hx2 := hx.2
    have hy2 := hy.2
    omega

/-- The pump subspace has at most one basis vector for each choice of signal occupations. -/
theorem pumpSubspace_finrank_le (n q : ℕ) :
    Module.finrank ℂ (pumpSubspace n q) ≤ q ^ n := by
  classical
  letI : Fintype (pumpIndex n q) := Fintype.ofFinite _
  have hcard : Fintype.card (pumpIndex n q) ≤ q ^ n := by
    calc
      Fintype.card (pumpIndex n q) ≤ Fintype.card (Fin n → Fin q) :=
        Fintype.card_le_of_injective _ (pumpIndex_signal_injective n q)
      _ = q ^ n := by simp
  have hspan : pumpSubspace n q = Submodule.span ℂ
      (Set.range (fun x : pumpIndex n q => EuclideanSpace.single x.1 (1 : ℂ))) := by
    unfold pumpSubspace
    congr 1
    exact Set.image_eq_range _ _
  rw [hspan]
  exact (finrank_range_le_card (R := ℂ) _).trans hcard

end Chi2QEC

set_option autoImplicit false

namespace Chi2QEC

noncomputable section

private def uniformPump (n q j : ℕ) (hj : j < q) : FockIdx n q :=
  fun _ k => if k = 2 then ⟨q - 1 - j, by omega⟩ else ⟨j, hj⟩

private theorem uniformPump_mem (n q j : ℕ) (hj : j < q) :
    uniformPump n q j hj ∈ pumpIndex n q := by
  intro ℓ
  constructor
  · simp [uniformPump]
  · simp only [uniformPump, show (0 : Fin 3) ≠ 2 by decide, ↓reduceIte]
    omega

private theorem uniformPump_single_mem (n q j : ℕ) (hj : j < q) :
    EuclideanSpace.single (uniformPump n q j hj) (1 : ℂ) ∈ pumpSubspace n q := by
  apply Submodule.subset_span
  exact ⟨uniformPump n q j hj, uniformPump_mem n q j hj, rfl⟩

private theorem matrix_single_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (x y : ι) :
    (Matrix.toEuclideanLin M (EuclideanSpace.single y (1 : ℂ))) x = M x y := by
  simp [Matrix.toLpLin_apply, Matrix.col_apply]

private theorem annihilation_single_zero (n q : ℕ) (ℓ : Fin n) (k : Fin 3)
    (y : FockIdx n q) (hy : (y ℓ k : ℕ) = 0) :
    Matrix.toEuclideanLin (annihilation n q ℓ k)
      (EuclideanSpace.single y (1 : ℂ)) = 0 := by
  ext x
  rw [matrix_single_apply]
  simp [annihilation, hy]

/-- The full pump space has a zero-loss state and a nonzero-loss state for the same
signal mode, so its diagonal Knill--Laflamme scalar cannot be constant. -/
theorem pump_not_satisfiesKL (n q : ℕ) (hn : 0 < n) (hq : 2 ≤ q) :
    ¬ SatisfiesKL (pumpSubspace n q) (lossError n q) := by
  classical
  let ℓ : Fin n := ⟨0, hn⟩
  let y0 := uniformPump n q 0 (by omega)
  let y1 := uniformPump n q 1 (by omega)
  let x : FockIdx n q := Function.update y1 ℓ (Function.update (y1 ℓ) 0 ⟨0, by omega⟩)
  have hy0 : (y0 ℓ 0 : ℕ) = 0 := by simp [y0, uniformPump]
  have hy1 : (y1 ℓ 0 : ℕ) = 1 := by simp [y1, uniformPump]
  have hoff : ∀ ℓ' k', (ℓ', k') ≠ (ℓ, (0 : Fin 3)) → x ℓ' k' = y1 ℓ' k' := by
    intro ℓ' k' hne
    by_cases hℓ : ℓ' = ℓ
    · subst ℓ'
      have hk : k' ≠ 0 := by
        intro hk
        subst k'
        exact hne rfl
      simp [x, hk]
    · simp [x, hℓ]
  have hval : (x ℓ 0 : ℕ) + 1 = (y1 ℓ 0 : ℕ) := by simp [x, hy1]
  have hentry : annihilation n q ℓ 0 x y1 = 1 := by
    unfold annihilation
    rw [if_pos ⟨hoff, hval⟩]
    simp [hy1]
  have hm0 : EuclideanSpace.single y0 (1 : ℂ) ∈ pumpSubspace n q :=
    uniformPump_single_mem n q 0 (by omega)
  have hm1 : EuclideanSpace.single y1 (1 : ℂ) ∈ pumpSubspace n q :=
    uniformPump_single_mem n q 1 (by omega)
  have hzero := annihilation_single_zero n q ℓ 0 y0 hy0
  rintro ⟨α, hα⟩
  have hα0 := hα (some (ℓ, 0)) (some (ℓ, 0)) _ hm0 _ hm0
  have hscalar : α (some (ℓ, 0)) (some (ℓ, 0)) = 0 := by
    simpa [lossError, hzero, EuclideanSpace.inner_single_left] using hα0.symm
  have hα1 := hα (some (ℓ, 0)) (some (ℓ, 0)) _ hm1 _ hm1
  have hz : Matrix.toEuclideanLin (annihilation n q ℓ 0)
      (EuclideanSpace.single y1 (1 : ℂ)) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa [lossError, hscalar] using hα1
  have hzentry := congrArg (fun v : EuclideanSpace ℂ (FockIdx n q) => v x) hz
  rw [matrix_single_apply, hentry] at hzentry
  simp at hzentry

end

end Chi2QEC

namespace Chi2QEC

/-- A correctable code is a proper subspace whenever the whole pump space is
not correctable. Finite dimensionality then turns proper inclusion into a strict
dimension bound. -/
theorem code_finrank_lt_pump (n q : ℕ)
    (C : Submodule ℂ (EuclideanSpace ℂ (FockIdx n q)))
    (hC : C ≤ pumpSubspace n q)
    (hKL : SatisfiesKL C (lossError n q))
    (hpump : ¬ SatisfiesKL (pumpSubspace n q) (lossError n q)) :
    Module.finrank ℂ C < Module.finrank ℂ (pumpSubspace n q) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne hC ?_
  intro heq
  exact hpump (heq ▸ hKL)

end Chi2QEC

set_option autoImplicit false

namespace Chi2QEC

/-- The numerical dimension estimate propagates to the next tensor power. -/
theorem hamming_arithmetic_step (n q : ℕ) (hn : 1 ≤ n) (hq : 2 ≤ q)
    (h : (1 + 3 * n) * q ^ n ≤ (4 * q - 3) ^ n) :
    (1 + 3 * (n + 1)) * q ^ (n + 1) ≤ (4 * q - 3) ^ (n + 1) := by
  have hcoeff : (1 + 3 * (n + 1)) * q ≤ (1 + 3 * n) * (4 * q - 3) := by
    calc
      (1 + 3 * (n + 1)) * q ≤ (2 * (1 + 3 * n)) * q :=
        Nat.mul_le_mul_right _ (by omega)
      _ = (1 + 3 * n) * (2 * q) := by ring
      _ ≤ (1 + 3 * n) * (4 * q - 3) := Nat.mul_le_mul_left _ (by omega)
  calc
    (1 + 3 * (n + 1)) * q ^ (n + 1) =
        ((1 + 3 * (n + 1)) * q) * q ^ n := by rw [pow_succ]; ring
    _ ≤ ((1 + 3 * n) * (4 * q - 3)) * q ^ n := Nat.mul_le_mul_right _ hcoeff
    _ = ((1 + 3 * n) * q ^ n) * (4 * q - 3) := by ring
    _ ≤ (4 * q - 3) ^ n * (4 * q - 3) := Nat.mul_le_mul_right _ h
    _ = (4 * q - 3) ^ (n + 1) := (pow_succ _ _).symm

/-- Two pump factors suffice for the crude dimension bound when `q ≥ 3`. -/
theorem hamming_arithmetic_large_q (n q : ℕ) (hn : 2 ≤ n) (hq : 3 ≤ q) :
    (1 + 3 * n) * q ^ n ≤ (4 * q - 3) ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      calc
        (1 + 3 * 2) * q ^ 2 ≤ (3 * q) ^ 2 := by nlinarith
        _ ≤ (4 * q - 3) ^ 2 := by gcongr; omega
  | succ n hn ih => exact hamming_arithmetic_step n q (by omega) (by omega) ih

/-- Three binary pump factors suffice for the crude dimension bound. -/
theorem hamming_arithmetic_binary (n : ℕ) (hn : 3 ≤ n) :
    (1 + 3 * n) * 2 ^ n ≤ (4 * 2 - 3) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => exact hamming_arithmetic_step n 2 (by omega) (by omega) ih

/-- A proper code subspace of the pump space satisfies the desired numerical bound. -/
theorem hamming_arithmetic_of_strict (n q d : ℕ) (hn : 0 < n) (hq : 2 ≤ q)
    (hd : d < q ^ n) : (1 + 3 * n) * d ≤ (4 * q - 3) ^ n := by
  by_cases hn1 : n = 1
  · subst n
    simp only [pow_one] at hd ⊢
    omega
  by_cases hq2 : q = 2
  · subst q
    by_cases hn2 : n = 2
    · subst n
      norm_num at hd ⊢
      omega
    · exact (Nat.mul_le_mul_left _ (Nat.le_of_lt hd)).trans
        (hamming_arithmetic_binary n (by omega))
  · exact (Nat.mul_le_mul_left _ (Nat.le_of_lt hd)).trans
      (hamming_arithmetic_large_q n q (by omega) (by omega))

/-- The empty tensor power has dimension at most one. -/
theorem hamming_arithmetic_zero (q d : ℕ) (hd : d ≤ 1) :
    (1 + 3 * 0) * d ≤ (4 * q - 3) ^ 0 := by simpa using hd

end Chi2QEC


open Chi2QEC

/-- The unchanged full photon-loss Hamming bound. -/
theorem solution (n q b k : ℕ) (hq : 2 ≤ q)
    (C : Submodule ℂ (EuclideanSpace ℂ (FockIdx n q))) (hC : C ≤ pumpSubspace n q)
    (hdim : Module.finrank ℂ C = b ^ k) (hKL : SatisfiesKL C (lossError n q)) :
    (1 + 3 * n) * b ^ k ≤ (4 * q - 3) ^ n := by
  rw [← hdim]
  have hpump := pumpSubspace_finrank_le n q
  by_cases hn : n = 0
  · subst n
    simpa using (Submodule.finrank_mono hC).trans hpump
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    exact hamming_arithmetic_of_strict n q (Module.finrank ℂ C) hnpos hq
      ((code_finrank_lt_pump n q C hC hKL (pump_not_satisfiesKL n q hnpos hq)).trans_le hpump)

#print axioms solution
#check @solution
