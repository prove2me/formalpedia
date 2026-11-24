-- Prove2me | solution 1 for EpAlgSmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:26:48.272244+00:00
-- url     : https://prove2.me/submissions/bc99618d-3cd0-4014-a60d-e7c1b3c66a35

module
public import Definitions.Def_PHarmonicPoly_EpAlg
public import Definitions.Def_PHarmonicPoly_EpAlgSmul

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} (p c : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    EpAlg p (c • P) = c ^ 3 • EpAlg p P := by
  have hCc : (c • P) = C c * P := MvPolynomial.smul_eq_C_mul P c
  have hd : ∀ i : Fin n, pderiv i (c • P) = C c * pderiv i P := by
    intro i; rw [hCc, pderiv_C_mul]
  have hd2 : ∀ i j : Fin n, pderiv i (pderiv j (c • P)) = C c * pderiv i (pderiv j P) := by
    intro i j; rw [hd j, pderiv_C_mul]
  have e1 : (∑ i : Fin n, (pderiv i (c • P)) ^ 2)
      = C c ^ 2 * ∑ i : Fin n, (pderiv i P) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hd i, mul_pow])
  have e2 : (∑ i : Fin n, pderiv i (pderiv i (c • P)))
      = C c * ∑ i : Fin n, pderiv i (pderiv i P) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hd2 i i)
  have e3 : (∑ i : Fin n, ∑ j : Fin n,
        pderiv i (pderiv j (c • P)) * pderiv i (c • P) * pderiv j (c • P))
      = C c ^ 3 * ∑ i : Fin n, ∑ j : Fin n,
        pderiv i (pderiv j P) * pderiv i P * pderiv j P := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hd2 i j, hd i, hd j]; ring
  rw [EpAlg, EpAlg, e1, e2, e3, MvPolynomial.smul_eq_C_mul, C_pow]
  ring
