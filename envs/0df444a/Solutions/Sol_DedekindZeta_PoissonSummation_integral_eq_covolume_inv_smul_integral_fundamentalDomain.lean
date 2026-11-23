-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.integral_eq_covolume_inv_smul_integral_fundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:12:25.050335+00:00
-- url     : https://prove2.me/submissions/89cb9bfa-3e13-400a-9cf4-ff03cc5d69fc

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_integral_prod_torus_eq_integral_box
import Theorems.Thm_DedekindZeta_PoissonSummation_integral_box_eq_covolume_inv_smul_integral_fundamentalDomain

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_908
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ θ, g θ)
      = (ZLattice.covolume L)⁻¹ •
          ∫ x in D, g (torusEquiv L b (x : V ⧸ L.toAddSubgroup)) := by
  -- Convert the `torusEquiv` pullback to the explicit coordinatewise form `red ∘ Φ`,
  -- then chain Step 1 (torus = box) and Step 2 (box = covolume⁻¹ • domain).
  simp only [torusEquiv_mk]
  rw [integral_prod_torus_eq_integral_box hg]
  exact integral_box_eq_covolume_inv_smul_integral_fundamentalDomain L b hD hg
end DedekindZeta.PoissonSummation
