-- Prove2me | solution 1 for BookProof.NsLagrangianDet.hasDerivAt_dispField
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:17.574337+00:00
-- url     : https://prove2.me/submissions/4c5d14dd-9e55-4c83-8160-74ca57182e96

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.hasDerivAt_dispField
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ)
    (r c : Fin 3) :
    HasDerivAt (fun t : ℝ => dispField kv y (a + t • (Pi.single c (1 : ℝ) : Fin 3 → ℝ)) r)
      (dispGrad kv y a r c) 0 := by

  unfold dispField dispGrad
  simp only [Matrix.of_apply]
  apply HasDerivAt.fun_sum
  intro m _
  have hlin : ∀ t : ℝ, (∑ c', wv kv m c' * (a + t • (Pi.single c (1 : ℝ) : Fin 3 → ℝ)) c')
      = (∑ c', wv kv m c' * a c') + t * wv kv m c := by
    intro t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ c) h)]
    simp
    ring
  have hphase : HasDerivAt
      (fun t : ℝ => phase (wv kv m) (a + t • (Pi.single c (1 : ℝ) : Fin 3 → ℝ)))
      (Complex.I * ((wv kv m c : ℝ) : ℂ) * phase (wv kv m) a) 0 := by
    have hin : HasDerivAt (fun t : ℝ => Complex.I * ((((∑ c', wv kv m c' * a c')
        + t * wv kv m c : ℝ)) : ℂ)) (Complex.I * ((wv kv m c : ℝ) : ℂ)) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (((∑ c', wv kv m c' * a c') + t * wv kv m c : ℝ)))
          (wv kv m c) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (wv kv m c)).const_add
          (∑ c', wv kv m c' * a c')
      simpa using (h1.ofReal_comp).const_mul Complex.I
    have := hin.cexp
    simp only [zero_mul, add_zero] at this
    convert this using 1
    · funext t
      rw [phase, hlin t]
    · rw [phase]; ring
  have := hphase.const_mul (ev y (scoef m r))
  convert this using 1 <;>
    (first
      | rfl
      | rw [gradCoef, MvPolynomial.smul_eq_C_mul, map_mul]; simp [ev]; ring)
