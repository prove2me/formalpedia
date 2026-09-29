-- Prove2me | solution 1 for ClassicalSchur.not_coveredBySumFree_blockSums
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:26:32.419991+00:00
-- url     : https://prove2.me/submissions/f94976e6-d76e-4d47-8c94-97d2afe3a336

-- Generated from lean/ClassicalSchur/Ramsey.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 2 file-scoped / sub-threshold helper(s)
--   rename  : not_coveredBySumFree_blockSums -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Mathlib



namespace ClassicalSchur

/-- Prefix sums are monotone in the index. -/
theorem prefixSum_mono (A : List ℕ) {i j : ℕ} (hij : i ≤ j) :
    (A.take i).sum ≤ (A.take j).sum := by
  have h1 : (A.take j).take i = A.take i := by simp [List.take_take, Nat.min_eq_left hij]
  have h2 := List.sum_take_add_sum_drop (A.take j) i
  rw [h1] at h2
  omega

/-- A difference of two prefix sums is a block sum (ER Proposition 2.7,
one direction). -/
theorem sub_mem_blockSums (A : List ℕ) {i j : ℕ} (hij : i < j) (hj : j ≤ A.length) :
    (A.take j).sum - (A.take i).sum ∈ blockSums A := by
  refine ⟨(A.take j).drop i, ?_, ?_, ?_⟩
  · exact (List.drop_suffix i (A.take j)).isInfix.trans (List.take_prefix j A).isInfix
  · intro h
    have h' := congrArg List.length h
    simp at h'
    omega
  · have h1 : (A.take j).take i = A.take i := by simp [List.take_take, Nat.min_eq_left hij.le]
    have h2 := List.sum_take_add_sum_drop (A.take j) i
    rw [h1] at h2
    omega

end ClassicalSchur

open ClassicalSchur in
theorem solution {k N : ℕ} (hR : TriangleRamsey k N)
    {A : List ℕ} (hA : N ≤ A.length + 1) {q : ℕ} (hq : q ≤ k) :
    ¬ CoveredBySumFree (blockSums A) q := by
  classical
  rintro ⟨C, hC, hcov⟩
  have hmem : ∀ p : {p : ℕ × ℕ // p.1 < p.2 ∧ p.2 ≤ A.length},
      ∃ t : Fin q, (A.take p.1.2).sum - (A.take p.1.1).sum ∈ C t := fun p =>
    Set.mem_iUnion.mp (hcov (sub_mem_blockSums A p.2.1 p.2.2))
  choose f hf using hmem
  let col : ℕ → ℕ → ℕ := fun x y =>
    if h : x < y ∧ y ≤ A.length then (f ⟨(x, y), h⟩).val else 0
  have hcol : ∀ x y (h : x < y ∧ y ≤ A.length), col x y = (f ⟨(x, y), h⟩).val :=
    fun x y h => dif_pos h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, h1, h2⟩ :=
    hR (Finset.range (A.length + 1)) (Finset.range q) col (by simpa using hq)
      (by simpa using hA)
      (fun x _ y hy hxy => by
        rw [Finset.mem_range] at hy
        rw [hcol x y ⟨hxy, by omega⟩, Finset.mem_range]
        exact (f _).isLt)
  rw [Finset.mem_range] at hx hy hz
  have hxy' : x < y ∧ y ≤ A.length := ⟨hxy, by omega⟩
  have hyz' : y < z ∧ z ≤ A.length := ⟨hyz, by omega⟩
  have hxz' : x < z ∧ z ≤ A.length := ⟨hxy.trans hyz, by omega⟩
  rw [hcol x y hxy', hcol y z hyz'] at h1
  rw [hcol x y hxy', hcol x z hxz'] at h2
  have m1 := hf ⟨(x, y), hxy'⟩
  have m2 := hf ⟨(y, z), hyz'⟩
  have m3 := hf ⟨(x, z), hxz'⟩
  rw [show f ⟨(y, z), hyz'⟩ = f ⟨(x, y), hxy'⟩ from Fin.ext h1.symm] at m2
  rw [show f ⟨(x, z), hxz'⟩ = f ⟨(x, y), hxy'⟩ from Fin.ext h2.symm] at m3
  have p1 := prefixSum_mono A hxy.le
  have p2 := prefixSum_mono A hyz.le
  refine hC _ _ m1 _ m2 ?_
  convert m3 using 1
  dsimp only
  omega
