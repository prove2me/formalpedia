-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.fourierChar_inner_eq_prod_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:15:02.273981+00:00
-- url     : https://prove2.me/submissions/f05a8a80-6914-42bf-893c-65cc17dbc2db

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_inner_dualLattice_eq_sum

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution (w : dualLattice L) (x : V) :
    ((𝐞 (⟪x, (w : V)⟫) : Circle) : ℂ)
      = ∏ i, fourier (dualLatticeEquiv L b w i)
          ((torusEquiv L b (x : V ⧸ L.toAddSubgroup)) i) := by
  classical
  set n := dualLatticeEquiv L b w with hn
  -- Right-hand side: each factor is `exp (2π · (n i · Φ x i) · I)`.
  have hR : ∀ i,
      fourier (n i) ((torusEquiv L b (x : V ⧸ L.toAddSubgroup)) i)
        = Complex.exp (2 * Real.pi * ((n i : ℝ) * latticeEquivFun L b x i) * Complex.I) := by
    intro i
    simp only [torusEquiv_mk, fourier_coe_apply]
    push_cast
    ring_nf
  rw [Finset.prod_congr rfl (fun i _ => hR i)]
  rw [← Complex.exp_sum]
  -- Left-hand side: `𝐞 (∑ ...) = exp (2π · (∑ ...) · I)`, split the exponent.
  rw [inner_dualLattice_eq_sum L b w x, Real.fourierChar_apply]
  congr 1
  push_cast [Finset.mul_sum]
  rw [Finset.sum_mul]
end DedekindZeta.PoissonSummation
