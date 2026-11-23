-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.inner_dualLattice_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:00.496833+00:00
-- url     : https://prove2.me/submissions/b9b5cda3-64d8-4daf-a3da-d10d9fb5ec8f

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_inner_dualBasisR
import Theorems.Thm_DedekindZeta_PoissonSummation_dualLatticeEquiv_symm_repr

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
    (⟪x, (w : V)⟫ : ℝ)
      = ∑ i, ((dualLatticeEquiv L b w i : ℤ) : ℝ) * latticeEquivFun L b x i := by
  conv_lhs => rw [dualLatticeEquiv_symm_repr L b w]
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, inner_dualBasisR]
end DedekindZeta.PoissonSummation
