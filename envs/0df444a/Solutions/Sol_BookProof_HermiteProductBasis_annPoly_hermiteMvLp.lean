-- Prove2me | solution 1 for BookProof.HermiteProductBasis.annPoly_hermiteMvLp
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:23:25.467115+00:00
-- url     : https://prove2.me/submissions/2c900f0a-7720-4e45-9f7f-d385f4eee937

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0. https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean -/
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
set_option maxHeartbeats 4000000
set_option autoImplicit false
noncomputable section
namespace BookProof.HermiteProductBasis
open scoped ENNReal
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore
open BookProof.HermiteCore
variable {d : ℕ}
@[simp] theorem hermiteMvBasis_apply (a : Fin d →₀ ℕ) :
    hermiteMvBasis a = hermiteMvLp (d := d) a := by
  rw [hermiteMvBasis, HilbertBasis.coe_mk]

theorem pderiv_aeval_self (i : Fin d) (q : Polynomial ℂ) :
    pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q)
      = Polynomial.aeval (X i) (Polynomial.derivative q) := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, map_mul,
        Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [mul_comm, mul_assoc, algebraMap_eq]

theorem pderiv_aeval_other {i j : Fin d} (h : j ≠ i) (q : Polynomial ℂ) :
    pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q) = 0 := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [h, algebraMap_eq]

theorem pderiv_hermiteFactor_self (i : Fin d) (n : ℕ) :
    pderiv i (hermiteFactor i n) = (n : ℂ) • hermiteFactor i (n - 1) := by
  cases n with
  | zero => simp [hermiteFactor, hermiteCx_zero]
  | succ m =>
      rw [hermiteFactor, pderiv_aeval_self]
      have h : Polynomial.derivative (hermiteCx (m + 1)) = ((m : ℂ) + 1) • hermiteCx m := by
        have hm := congrArg (Polynomial.map (Int.castRingHom ℂ)) (derivative_hermiteZ m)
        simpa [hermiteCx, Polynomial.derivative_map, Polynomial.smul_eq_C_mul,
          Polynomial.map_mul] using hm
      rw [h]
      simp [hermiteFactor, map_smul]

theorem pderiv_hermiteFactor_other {i j : Fin d} (h : j ≠ i) (n : ℕ) :
    pderiv j (hermiteFactor i n) = 0 := pderiv_aeval_other h _

theorem pderiv_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    pderiv i (hermiteMv a) = ((a i : ℂ)) • hermiteMv (a - Finsupp.single i 1) := by
  classical
  have hrest : ∀ b : Fin d →₀ ℕ, (∀ j : Fin d, j ≠ i → b j = a j) →
      ∏ j ∈ Finset.univ.erase i, hermiteFactor j (b j)
        = ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) :=
    fun b hb => Finset.prod_congr rfl fun j hj => by rw [hb j (Finset.ne_of_mem_erase hj)]
  have hsub : ∀ j : Fin d, j ≠ i → (a - Finsupp.single i 1 : Fin d →₀ ℕ) j = a j := by
    intro j hj; simp [Finsupp.tsub_apply, hj]
  have hsi : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 := by simp [Finsupp.tsub_apply]
  have hzero : pderiv i (∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j)) = 0 := by
    refine Finset.prod_induction _ (fun p => pderiv i p = 0) ?_ (by simp) ?_
    · intro p q hp hq
      rw [Derivation.leibniz, hp, hq]; simp
    · intro j hj
      exact pderiv_aeval_other (Finset.ne_of_mem_erase hj).symm _
  rw [hermiteMv_erase i a, hermiteMv_erase i (a - Finsupp.single i 1), hrest _ hsub, hsi,
    Derivation.leibniz, hzero, pderiv_hermiteFactor_self]
  simp [mul_comm]

@[simp] theorem annPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    annPoly i p = pderiv i p := rfl

@[simp] theorem crePoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    crePoly i p = X i * p - pderiv i p := rfl

theorem crePoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    crePoly i (hermiteMv a) = hermiteMv (a + Finsupp.single i 1) := by
  rw [crePoly_apply, hermiteMv_X_mul, pderiv_hermiteMv]
  abel

theorem hermiteNorm_succ (n : ℕ) :
    hermiteNorm (n + 1) = hermiteNorm n * Real.sqrt ((n : ℝ) + 1) := by
  have hfac : ((n + 1).factorial : ℝ) * Real.sqrt (2 * Real.pi)
      = ((n : ℝ) + 1) * ((n.factorial : ℝ) * Real.sqrt (2 * Real.pi)) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hermiteNorm, hermiteNorm, hfac, Real.sqrt_mul (by positivity), mul_comm]

theorem hermiteMvNorm_add_single (i : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMvNorm (a + Finsupp.single i 1) = hermiteMvNorm a * Real.sqrt ((a i : ℝ) + 1) := by
  classical
  have hsplit : ∀ b : Fin d →₀ ℕ, hermiteMvNorm b
      = hermiteNorm (b i) * ∏ j ∈ Finset.univ.erase i, hermiteNorm (b j) := by
    intro b
    rw [hermiteMvNorm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, hermiteNorm ((a + Finsupp.single i 1 : Fin d →₀ ℕ) j)
      = ∏ j ∈ Finset.univ.erase i, hermiteNorm (a j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [show (a + Finsupp.single i 1 : Fin d →₀ ℕ) j = a j by
        simp [Finset.ne_of_mem_erase hj]]
  have hai : (a + Finsupp.single i 1 : Fin d →₀ ℕ) i = a i + 1 := by simp
  rw [hsplit (a + Finsupp.single i 1), hrest, hai, hermiteNorm_succ, hsplit a]
  ring

theorem hermiteMvNorm_sub_single {i : Fin d} {a : Fin d →₀ ℕ} (h : 1 ≤ a i) :
    hermiteMvNorm a = hermiteMvNorm (a - Finsupp.single i 1) * Real.sqrt ((a i : ℝ)) := by
  classical
  have hb : a = (a - Finsupp.single i 1) + Finsupp.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]
  have hbi : ((a - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℝ) + 1 = (a i : ℝ) := by
    rw [show (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 by simp [Finsupp.tsub_apply]]
    have : ((a i - 1 : ℕ) : ℝ) = (a i : ℝ) - 1 := by
      push_cast [Nat.cast_sub h]
      ring
    rw [this]
    ring
  calc hermiteMvNorm a
      = hermiteMvNorm ((a - Finsupp.single i 1) + Finsupp.single i 1) := by rw [← hb]
    _ = hermiteMvNorm (a - Finsupp.single i 1)
          * Real.sqrt (((a - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℝ) + 1) :=
        hermiteMvNorm_add_single i _
    _ = hermiteMvNorm (a - Finsupp.single i 1) * Real.sqrt ((a i : ℝ)) := by rw [hbi]

theorem pgMap_apply (p : MvPolynomial (Fin d) ℂ) : pgMap p = pgLp p := rfl

theorem crePoly_hermiteMvLp (i : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (crePoly i (hermiteMv a))
      = ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (a + Finsupp.single i 1) := by
  rw [crePoly_hermiteMv, pgLp_hermiteMv_eq (a + Finsupp.single i 1), smul_smul,
    hermiteMvNorm_add_single]
  congr 1
  have hne : ((hermiteMvNorm a : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero a
  push_cast
  field_simp

theorem annPoly_hermiteMvLp (i : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (annPoly i (hermiteMv a))
      = ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (a - Finsupp.single i 1) := by
  rw [annPoly_apply, pderiv_hermiteMv, ← pgMap_apply, map_smul, pgMap_apply,
    pgLp_hermiteMv_eq (a - Finsupp.single i 1), smul_smul, smul_smul]
  rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
  · rw [h0]
    simp
  · congr 1
    have hnorm := hermiteMvNorm_sub_single (i := i) (a := a) hpos
    have hsub_pos := hermiteMvNorm_pos (a - Finsupp.single i 1)
    have hai : (0 : ℝ) < (a i : ℝ) := by exact_mod_cast hpos
    have hsqrt_pos : 0 < Real.sqrt ((a i : ℝ)) := Real.sqrt_pos.mpr hai
    have hsqrt : Real.sqrt ((a i : ℝ)) * Real.sqrt ((a i : ℝ)) = (a i : ℝ) :=
      Real.mul_self_sqrt hai.le
    have hreal : (hermiteMvNorm a)⁻¹ * ((a i : ℝ) * hermiteMvNorm (a - Finsupp.single i 1))
        = Real.sqrt ((a i : ℝ)) := by
      rw [hnorm]
      field_simp
      nlinarith [hsqrt, hsub_pos, hsqrt_pos]
    have := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hreal
    push_cast at this ⊢
    linear_combination this
end BookProof.HermiteProductBasis

open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore BookProof.HermiteProductBasis
variable {d : ℕ}
theorem solution (i : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (annPoly i (hermiteMv a))
      = ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (a - Finsupp.single i 1) := by
  exact BookProof.HermiteProductBasis.annPoly_hermiteMvLp i a
#print axioms solution
