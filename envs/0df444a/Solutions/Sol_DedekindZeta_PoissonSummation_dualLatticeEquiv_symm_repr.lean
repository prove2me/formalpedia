-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.dualLatticeEquiv_symm_repr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:09:53.397671+00:00
-- url     : https://prove2.me/submissions/0acbd0dd-4ce5-4ed0-a2f9-428079bf8dba

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_dualLatticeBasis_coe
import Theorems.Thm_DedekindZeta_PoissonSummation_dualLatticeEquiv_apply

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution (w : dualLattice L) :
    (w : V) = ∑ i, ((dualLatticeEquiv L b w i : ℤ) : ℝ) • dualBasisR L b i := by
  have h := (dualLatticeBasis L b).sum_repr w
  have hcoe : (w : V)
      = ((∑ i, ((dualLatticeBasis L b).repr w i) • (dualLatticeBasis L b i)
          : dualLattice L) : V) := by rw [h]
  rw [hcoe, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SetLike.val_smul, dualLatticeBasis_coe, ← Int.cast_smul_eq_zsmul ℝ, dualLatticeEquiv_apply]
end DedekindZeta.PoissonSummation
