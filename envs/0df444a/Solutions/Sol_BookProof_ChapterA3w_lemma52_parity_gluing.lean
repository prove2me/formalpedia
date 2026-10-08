-- Prove2me | solution 1 for BookProof.ChapterA3w.lemma52_parity_gluing
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:32:24.544014+00:00
-- url     : https://prove2.me/submissions/cbe2026a-84de-4192-b124-587afad1b37f

-- Generated from ChapterA3w.lean — theorem BookProof.ChapterA3w.lemma52_parity_gluing
import Definitions.Def_ChapterA3q
import Mathlib
import Definitions.Def_ChapterA3w
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3k
open BookProof.ChapterA3
open BookProof.ChapterA3j
open BookProof.ChapterA3k
open BookProof.ChapterA3w


open Matrix


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3q
open scoped Kronecker

private theorem chir_parity_anticomm_local :
    chir * mgamma 0 = -(mgamma 0 * chir) := by
  have hz : mgamma5Z * mgammaZ 0 = -(mgammaZ 0 * mgamma5Z) := by
    decide
  change ((Int.castRingHom ℂ).mapMatrix mgamma5Z) *
      ((Int.castRingHom ℂ).mapMatrix (mgammaZ 0)) =
        -(((Int.castRingHom ℂ).mapMatrix (mgammaZ 0)) *
          ((Int.castRingHom ℂ).mapMatrix mgamma5Z))
  simpa only [map_mul, map_neg] using
    congrArg ((Int.castRingHom ℂ).mapMatrix) hz

private theorem scaled_chir_parity_anticomm_local :
    (Complex.I • chir) * mgamma 0 = -(mgamma 0 * (Complex.I • chir)) := by
  calc
    (Complex.I • chir) * mgamma 0 = Complex.I • (chir * mgamma 0) := by
      rw [smul_mul_assoc]
    _ = Complex.I • (-(mgamma 0 * chir)) := by
      rw [chir_parity_anticomm_local]
    _ = -(Complex.I • (mgamma 0 * chir)) := by simp
    _ = -(mgamma 0 * (Complex.I • chir)) := by
      rw [← mul_smul_comm]

private theorem chir_parity_numerator_left_local :
    (1 - Complex.I • chir) * mgamma 0 =
      mgamma 0 * (1 + Complex.I • chir) := by
  calc
    (1 - Complex.I • chir) * mgamma 0 =
        mgamma 0 - (Complex.I • chir) * mgamma 0 := by
      simp only [sub_mul, one_mul]
    _ = mgamma 0 + mgamma 0 * (Complex.I • chir) := by
      rw [scaled_chir_parity_anticomm_local]
      abel
    _ = mgamma 0 * (1 + Complex.I • chir) := by
      rw [mul_add, mul_one]

private theorem swap_local : projChirL * mgamma 0 = mgamma 0 * projChirR := by
  let a : ℂ := (2 : ℂ)⁻¹
  let u : Matrix (Fin 4) (Fin 4) ℂ := Complex.I • chir
  have hnum : (1 - u) * mgamma 0 = mgamma 0 * (1 + u) := by
    simpa [u] using chir_parity_numerator_left_local
  change (a • (1 - u)) * mgamma 0 = mgamma 0 * (a • (1 + u))
  calc
    (a • (1 - u)) * mgamma 0 = a • ((1 - u) * mgamma 0) := by
      rw [smul_mul_assoc]
    _ = a • (mgamma 0 * (1 + u)) := by rw [hnum]
    _ = mgamma 0 * (a • (1 + u)) := by rw [← mul_smul_comm]


private theorem projChirL_parity_commutator_local :
    projChirL * mgamma 0 - mgamma 0 * projChirL =
      Complex.I • (mgamma 0 * chir) := by
  let a : ℂ := (2 : ℂ)⁻¹
  let u : Matrix (Fin 4) (Fin 4) ℂ := Complex.I • chir
  let g : Matrix (Fin 4) (Fin 4) ℂ := mgamma 0
  have hanti : u * g = -(g * u) := by
    dsimp [u, g]
    exact scaled_chir_parity_anticomm_local
  have hnum : (1 - u) * g = g * (1 + u) := by
    calc
      (1 - u) * g = g - u * g := by rw [sub_mul, one_mul]
      _ = g + g * u := by rw [hanti]; abel
      _ = g * (1 + u) := by rw [mul_add, mul_one]
  have hswap : (a • (1 - u)) * g = g * (a • (1 + u)) := by
    calc
      (a • (1 - u)) * g = a • ((1 - u) * g) := by rw [smul_mul_assoc]
      _ = a • (g * (1 + u)) := by rw [hnum]
      _ = g * (a • (1 + u)) := by rw [← mul_smul_comm]
  have ha : a * (2 : ℂ) = 1 := by
    dsimp [a]
    norm_num
  have hinner : (1 + u) - (1 - u) = (2 : ℂ) • u := by
    calc
      (1 + u) - (1 - u) = u + u := by abel
      _ = (2 : ℂ) • u := by rw [two_smul]
  have hdiff : a • (1 + u) - a • (1 - u) = u := by
    rw [← smul_sub]
    rw [hinner, smul_smul, ha]
    simp
  change (a • (1 - u)) * g - g * (a • (1 - u)) =
    Complex.I • (g * chir)
  calc
    (a • (1 - u)) * g - g * (a • (1 - u)) =
        g * (a • (1 + u)) - g * (a • (1 - u)) := by rw [hswap]
    _ = g * (a • (1 + u) - a • (1 - u)) := by rw [mul_sub]
    _ = g * u := by rw [hdiff]
    _ = Complex.I • (g * chir) := by
      dsimp [u]
      rw [mul_smul_comm]

private theorem noncomm_local : projChirL * mgamma 0 ≠ mgamma 0 * projChirL := by
  intro h
  have hcomm := projChirL_parity_commutator_local
  have hzero : Complex.I • (mgamma 0 * chir) = 0 := by
    calc
      Complex.I • (mgamma 0 * chir) =
          projChirL * mgamma 0 - mgamma 0 * projChirL := hcomm.symm
      _ = 0 := by rw [h]; simp
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 3) hzero
  norm_num [Matrix.smul_apply, Matrix.mul_apply, mgamma, chir, mgamma5,
    mgammaZ, mgamma5Z, Fin.sum_univ_succ] at hentry
  simp at hentry


private theorem noncomm2_local : parityDiag * projLL ≠ projLL * parityDiag := by
  intro h
  simp only [parityDiag, projLL, ← Matrix.mul_kronecker_mul] at h
  have he := congrArg (fun M : M2 => M (0, 0) (2, 3)) h
  norm_num [Matrix.kronecker_apply, Matrix.mul_apply, projChirL,
    Matrix.smul_apply, mgamma, mgammaZ, chir, mgamma5, mgamma5Z,
    Fin.sum_univ_succ, Matrix.one_apply, Fin.reduceFinMk] at he
  simp at he
  have hi := congrArg Complex.im he
  norm_num at hi


theorem solution :
    (projChirL * mgamma 0 ≠ mgamma 0 * projChirL) ∧
    (projChirL * mgamma 0 = mgamma 0 * projChirR) ∧
    (parityDiag * projLL ≠ projLL * parityDiag) ∧
    (parityDiag * projRR = projLL * parityDiag) := by
  refine ⟨noncomm_local, swap_local, noncomm2_local, ?_⟩
  simp only [parityDiag, projRR, projLL, ← Matrix.mul_kronecker_mul, ← swap_local]

#print axioms solution

