-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.integral_box_eq_covolume_inv_smul_integral_fundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:10:04.518038+00:00
-- url     : https://prove2.me/submissions/74f29bd3-6bcf-4101-930c-0bffa0226a45

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_integral_box_eq_integral_image_fundamentalDomain
import Theorems.Thm_DedekindZeta_PoissonSummation_integral_image_fundamentalDomain_eq_covolume_inv_smul

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
    (∫ y in Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1),
        g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))
      = (ZLattice.covolume L)⁻¹ •
          ∫ x in D, g (fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ))) := by
  rw [integral_box_eq_integral_image_fundamentalDomain L b hD hg,
    integral_image_fundamentalDomain_eq_covolume_inv_smul L b hD hg]
end DedekindZeta.PoissonSummation
