-- Prove2me | solution 2 for Conway99.srg_lambda_one_mu_two_degree_mem
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T17:49:30.254433+00:00
-- url     : https://prove2.me/submissions/0675cd31-a459-4fa2-b366-9260a20df4fb

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Theorems.Thm_Conway99_srg_lambda_one_mu_two_card

open SimpleGraph Matrix

namespace Conway99Aux

/-- The trace of an idempotent real matrix is a natural number (its rank). -/
theorem trace_eq_nat_of_idem {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ)
    (h : P * P = P) : ∃ d : ℕ, P.trace = (d : ℝ) := by
  classical
  set f : (V → ℝ) →ₗ[ℝ] (V → ℝ) := Matrix.toLin' P with hf
  have hidem : ∀ x, f (f x) = f x := by intro x; simp [hf, h]
  have hproj : LinearMap.IsProj (LinearMap.range f) f := by
    constructor
    · intro x; exact ⟨x, rfl⟩
    · rintro x ⟨y, rfl⟩; exact hidem y
  refine ⟨Module.finrank ℝ (LinearMap.range f), ?_⟩
  rw [← hproj.trace]
  simp [hf, LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ V)]

set_option maxHeartbeats 1000000 in
/-- Eigenvalue multiplicities of a matrix `B` satisfying `B * B = m • 1 + 8 • J`,
`B * J = J * B = c • J`, `J * J = nn • J`, where `t` is a square root of `m`. -/
theorem multiplicities {V : Type*} [Fintype V] [DecidableEq V]
    (B J : Matrix V V ℝ) (nn c m t : ℝ) (hn : nn ≠ 0) (ht : 0 < t)
    (htm : t ^ 2 = m)
    (hBB : B * B = m • (1 : Matrix V V ℝ) + (8:ℝ) • J)
    (hBJ : B * J = c • J) (hJB : J * B = c • J) (hJJ : J * J = nn • J)
    (hcm : c ^ 2 - m = 8 * nn)
    (htrB : B.trace = nn) (htrJ : J.trace = nn) (hcard : (Fintype.card V : ℝ) = nn) :
    ∃ f g : ℕ, (f:ℝ) + g = nn - 1 ∧ c + t * f - t * g = nn := by
  set Q : Matrix V V ℝ := 1 - (1/nn) • J with hQ
  set C : Matrix V V ℝ := B - (c/nn) • J with hC
  have hQQ : Q * Q = Q := by
    simp only [hQ, sub_mul, mul_sub, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, hJJ,
      smul_smul]
    match_scalars <;> field_simp <;> ring
  have hCC : C * C = m • Q := by
    simp only [hC, hQ, sub_mul, mul_sub, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, hBB,
      hBJ, hJB, hJJ, smul_smul]
    match_scalars <;> field_simp <;> ring_nf <;> nlinarith [hcm]
  have hCQ : C * Q = C := by
    simp only [hC, hQ, sub_mul, mul_sub, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, hBJ,
      hJJ, smul_smul]
    match_scalars <;> field_simp <;> ring
  have hQC : Q * C = C := by
    simp only [hC, hQ, sub_mul, mul_sub, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, hJB,
      hJJ, smul_smul]
    match_scalars <;> field_simp <;> ring
  have ht0 : t ≠ 0 := ne_of_gt ht
  set P1 : Matrix V V ℝ := (1/(2*t)) • (C + t • Q) with hP1
  set P2 : Matrix V V ℝ := (1/(2*t)) • (t • Q - C) with hP2
  have hP1P1 : P1 * P1 = P1 := by
    simp only [hP1, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_smul, hCC, hCQ, hQC,
      hQQ, smul_add]
    match_scalars <;> field_simp <;> nlinarith [htm]
  have hP2P2 : P2 * P2 = P2 := by
    simp only [hP2, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_smul, hCC, hCQ, hQC,
      hQQ, smul_sub]
    match_scalars <;> field_simp <;> nlinarith [htm]
  obtain ⟨f, hf⟩ := trace_eq_nat_of_idem P1 hP1P1
  obtain ⟨g, hg⟩ := trace_eq_nat_of_idem P2 hP2P2
  have htrQ : Q.trace = nn - 1 := by
    rw [hQ, Matrix.trace_sub, Matrix.trace_smul, htrJ, Matrix.trace_one, hcard, smul_eq_mul]
    field_simp
  have htrC : C.trace = nn - c := by
    rw [hC, Matrix.trace_sub, Matrix.trace_smul, htrJ, htrB, smul_eq_mul]
    field_simp
  rw [hP1, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, htrQ, htrC, smul_eq_mul,
    smul_eq_mul] at hf
  rw [hP2, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, htrQ, htrC, smul_eq_mul,
    smul_eq_mul] at hg
  refine ⟨f, g, ?_, ?_⟩
  · rw [← hf, ← hg]; field_simp; ring
  · rw [← hf, ← hg]; field_simp; ring

/-- If `M * d ^ 2 = N ^ 2` with `d ≠ 0`, then `M` is a square `s ^ 2` and `s ∣ N`. -/
theorem sq_of_mul_sq_eq_sq {M N d : ℤ} (hd : d ≠ 0) (h : M * d^2 = N^2) :
    ∃ s : ℕ, (s:ℤ)^2 = M ∧ (s:ℤ) ∣ N := by
  have hdvd : d^2 ∣ N^2 := ⟨M, by linarith [h]⟩
  have hdN : d ∣ N := (Int.pow_dvd_pow_iff (by norm_num)).mp hdvd
  obtain ⟨q, rfl⟩ := hdN
  have hq : M = q^2 := by
    have h2 : d^2 * M = d^2 * q^2 := by ring_nf; ring_nf at h; linarith
    exact mul_left_cancel₀ (pow_ne_zero 2 hd) h2
  exact ⟨q.natAbs, by rw [hq]; simp, Dvd.dvd.mul_left (Int.natAbs_dvd.mpr dvd_rfl) d⟩

/-- Endgame: `4 * k - 7 = s ^ 2` together with `s ∣ n - 2 * k - 1` forces `s ∣ 63`,
hence one of the six degrees. -/
theorem degree_of_sqrt_dvd (k n : ℕ) (hcount : 2*n = k^2+2) (s : ℕ)
    (hs : (s:ℤ)^2 = 4*(k:ℤ)-7) (hdvd : (s:ℤ) ∣ (n:ℤ) - (2*(k:ℤ)+1)) :
    k = 2 ∨ k = 4 ∨ k = 14 ∨ k = 22 ∨ k = 112 ∨ k = 994 := by
  have hcz : 2*(n:ℤ) = (k:ℤ)^2 + 2 := by exact_mod_cast hcount
  have h32 : 32*((n:ℤ)-(2*(k:ℤ)+1)) = (s:ℤ)^4 - 2*(s:ℤ)^2 - 63 := by
    have h4 : (s:ℤ)^4 = (4*(k:ℤ)-7)^2 := by rw [show ((s:ℤ))^4 = ((s:ℤ)^2)^2 by ring, hs]
    rw [h4, hs]; linarith
  have hd63 : (s:ℤ) ∣ 63 := by
    have h1 : (s:ℤ) ∣ 32*((n:ℤ)-(2*(k:ℤ)+1)) := hdvd.mul_left 32
    rw [h32] at h1
    have h2 : (s:ℤ) ∣ (s:ℤ)^4 - 2*(s:ℤ)^2 := ⟨(s:ℤ)^3 - 2*(s:ℤ), by ring⟩
    simpa using dvd_sub h2 h1
  have hd63n : s ∣ 63 := by exact_mod_cast hd63
  have hsmem : s ∈ Nat.divisors 63 := Nat.mem_divisors.mpr ⟨hd63n, by norm_num⟩
  have hs' : (s:ℤ)^2 = 4*(k:ℤ)-7 := hs
  fin_cases hsmem <;> · norm_num at hs' ⊢; omega

end Conway99Aux

open Conway99Aux

theorem solution {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] {n k : ℕ} (h : g.IsSRGWith n k 1 2) (hn : 1 < n) :
    k = 2 ∨ k = 4 ∨ k = 14 ∨ k = 22 ∨ k = 112 ∨ k = 994 := by
  classical
  have hcount : 2 * n = k ^ 2 + 2 := Conway99.srg_lambda_one_mu_two_card h (by omega)
  have hk2 : 2 ≤ k := by nlinarith
  have hcard : Fintype.card V = n := h.card
  set A : Matrix V V ℝ := g.adjMatrix ℝ with hA
  set J : Matrix V V ℝ := Matrix.of (fun _ _ => (1:ℝ)) with hJdef
  set B : Matrix V V ℝ := (2:ℝ) • A + 1 with hB
  have hA2 : A * A + A = ((k:ℝ) - 2) • (1 : Matrix V V ℝ) + (2:ℝ) • J := by
    have hm := h.matrix_eq (α := ℝ)
    have hc : (gᶜ.adjMatrix ℝ) = J - 1 - A := by
      ext i j
      by_cases hij : i = j <;> by_cases hadj : g.Adj i j <;>
        simp [hJdef, hA, hij, hadj, SimpleGraph.adjMatrix_apply]
    rw [hc, pow_two] at hm
    rw [hA, hm, ← Nat.cast_smul_eq_nsmul ℝ k, ← Nat.cast_smul_eq_nsmul ℝ 1,
      ← Nat.cast_smul_eq_nsmul ℝ 2]
    push_cast
    module
  have hAJ : A * J = (k:ℝ) • J := by
    ext i j
    have hdeg : g.degree i = k := h.regular i
    simp only [hA, hJdef, Matrix.mul_apply, SimpleGraph.adjMatrix_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, mul_one, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    rw [show (Finset.univ.filter fun x => g.Adj i x) = g.neighborFinset i by
      ext x; simp [SimpleGraph.mem_neighborFinset]]
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    simp [hdeg]
  have hJA : J * A = (k:ℝ) • J := by
    ext i j
    have hdeg : g.degree j = k := h.regular j
    simp only [hA, hJdef, Matrix.mul_apply, SimpleGraph.adjMatrix_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, one_mul, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    rw [show (Finset.univ.filter fun x => g.Adj x j) = g.neighborFinset j by
      ext x; simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]]
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    simp [hdeg]
  have hJJ : J * J = (n:ℝ) • J := by
    ext i j
    simp [hJdef, Matrix.mul_apply, hcard]
  set m : ℝ := 4*(k:ℝ) - 7 with hm
  set c : ℝ := 2*(k:ℝ) + 1 with hc
  have hkR : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  have hmpos : 0 < m := by simp only [hm]; linarith
  set t : ℝ := Real.sqrt m with ht
  have htm : t ^ 2 = m := Real.sq_sqrt hmpos.le
  have htpos : 0 < t := Real.sqrt_pos.mpr hmpos
  have hBB : B * B = m • (1 : Matrix V V ℝ) + (8:ℝ) • J := by
    have hexp : B * B = (4:ℝ) • (A * A + A) + 1 := by
      simp only [hB, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one]
      module
    rw [hexp, hA2, hm]
    module
  have hBJ : B * J = c • J := by
    rw [hB, add_mul, smul_mul_assoc, hAJ, one_mul, hc, smul_smul]
    module
  have hJB : J * B = c • J := by
    rw [hB, mul_add, mul_smul_comm, hJA, mul_one, hc, smul_smul]
    module
  have hcountR : 2 * (n:ℝ) = (k:ℝ)^2 + 2 := by exact_mod_cast hcount
  have hcm : c ^ 2 - m = 8 * (n:ℝ) := by simp only [hc, hm]; nlinarith [hcountR]
  have htrB : B.trace = (n:ℝ) := by
    rw [hB, Matrix.trace_add, Matrix.trace_smul, hA, SimpleGraph.trace_adjMatrix,
      Matrix.trace_one, hcard]
    simp
  have htrJ : J.trace = (n:ℝ) := by simp [hJdef, Matrix.trace, Matrix.diag, hcard]
  have hnne : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcardR : (Fintype.card V : ℝ) = (n:ℝ) := by exact_mod_cast hcard
  obtain ⟨f, gg, hfg1, hfg2⟩ :=
    multiplicities B J (n:ℝ) c m t hnne htpos htm hBB hBJ hJB hJJ hcm htrB htrJ hcardR
  by_cases hfe : f = gg
  · -- the conference case: `n = 2k+1`, forcing `k = 4`
    subst hfe
    have hnc : (n:ℝ) = 2*(k:ℝ)+1 := by simp only [hc] at hfg2; linarith
    have hnk : n = 2*k+1 := by exact_mod_cast hnc
    have hkk : k * k = 4 * k := by
      have : 2*(2*k+1) = k^2+2 := by rw [← hnk]; exact hcount
      nlinarith [this]
    have : k = 4 := by
      have hkpos : 0 < k := by omega
      exact Nat.eq_of_mul_eq_mul_right hkpos hkk
    tauto
  · -- the integral case
    have hkey : t * ((f:ℝ) - gg) = (n:ℝ) - c := by ring_nf; ring_nf at hfg2; linarith
    have hsq : m * ((f:ℝ) - gg)^2 = ((n:ℝ) - c)^2 := by
      rw [← hkey, mul_pow, ← htm]
    have hZ : (4*(k:ℤ)-7) * ((f:ℤ) - gg)^2 = ((n:ℤ) - (2*(k:ℤ)+1))^2 := by
      have : ((4*(k:ℤ)-7 : ℤ) : ℝ) * ((((f:ℤ) - gg : ℤ)) : ℝ)^2
          = ((((n:ℤ) - (2*(k:ℤ)+1) : ℤ)) : ℝ)^2 := by
        push_cast
        simpa [hm, hc] using hsq
      exact_mod_cast this
    have hdne : ((f:ℤ) - gg) ≠ 0 := by
      simp only [sub_ne_zero]
      exact_mod_cast fun hcon => hfe (by exact_mod_cast hcon)
    obtain ⟨s, hs1, hs2⟩ := sq_of_mul_sq_eq_sq hdne hZ
    exact degree_of_sqrt_dvd k n hcount s hs1 hs2
