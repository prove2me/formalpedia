-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.integral_image_fundamentalDomain_eq_covolume_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:56.259606+00:00
-- url     : https://prove2.me/submissions/f89856f1-d2c6-40c8-973e-e477611df3e9

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_latticeEquivFun_map_volume

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
    (∫ y in (latticeEquivFun L b) '' D,
        g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))))
      = (ZLattice.covolume L)⁻¹ •
          ∫ x in D, g (fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ))) := by
  classical
  -- `Φ = latticeEquivFun L b` and the common integrand `F = g ∘ red`.
  set Φ := latticeEquivFun L b with hΦ
  set F : (Fin d → ℝ) → ℂ :=
    fun y => g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) with hFdef
  -- `Φ` is a continuous linear equiv, hence a measurable embedding.
  have hemb : MeasurableEmbedding (Φ : V → (Fin d → ℝ)) := by
    have := Φ.toHomeomorph.measurableEmbedding
    rwa [ContinuousLinearEquiv.coe_toHomeomorph] at this
  -- Change of variables `y = Φ x` over `Φ '' D` (no integrability needed): the
  -- measurable-embedding set-integral pushforward, then the Jacobian
  -- `latticeEquivFun_map_volume` (`map Φ volume = ofReal (covolume L) • volume`).
  have key : (∫ x in D, F (Φ x))
      = ZLattice.covolume L • ∫ y in Φ '' D, F y := by
    have hmap := hemb.setIntegral_map (μ := (volume : Measure V)) F (Φ '' D)
    rw [Set.preimage_image_eq D hemb.injective] at hmap
    -- `hmap : ∫ y in Φ '' D, F y ∂(map Φ volume) = ∫ x in D, F (Φ x)`.
    rw [← hmap, latticeEquivFun_map_volume L b, Measure.restrict_smul,
      integral_smul_measure, ENNReal.toReal_ofReal (ZLattice.covolume_pos L volume).le]
  -- Invert the `covolume` factor.
  rw [key, smul_smul, inv_mul_cancel₀ (ZLattice.covolume_pos L volume).ne', one_smul]
end DedekindZeta.PoissonSummation
