-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.inner_dualBasisR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:04:51.386992+00:00
-- url     : https://prove2.me/submissions/288710c2-c0dd-4b18-a36a-eeb1457731aa

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution (x : V) (i : Fin d) :
    (⟪x, dualBasisR L b i⟫ : ℝ) = latticeEquivFun L b x i := by
  classical
  rw [latticeEquivFun_apply]
  set P := b.ofZLatticeBasis ℝ L with hP
  have hkron : ∀ j, (⟪P j, dualBasisR L b i⟫ : ℝ) = (if j = i then (1 : ℝ) else 0) := by
    intro j
    rw [real_inner_comm]
    have hd := LinearMap.BilinForm.apply_dualBasis_left innerₗ_nondegenerate P i j
    rw [innerₗ_apply_apply] at hd
    exact hd
  have hx : x = ∑ j, P.repr x j • P j := (P.sum_repr x).symm
  conv_lhs => rw [hx]
  rw [sum_inner]
  have : ∀ j, (⟪P.repr x j • P j, dualBasisR L b i⟫ : ℝ)
      = P.repr x j * (if j = i then (1 : ℝ) else 0) := by
    intro j; rw [real_inner_smul_left, hkron j]
  rw [Finset.sum_congr rfl (fun j _ => this j)]
  simp [Finset.sum_ite_eq']
end DedekindZeta.PoissonSummation
