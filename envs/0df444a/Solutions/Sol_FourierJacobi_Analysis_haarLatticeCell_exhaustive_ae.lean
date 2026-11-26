-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_exhaustive_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:46.623147+00:00
-- url     : https://prove2.me/submissions/0513178b-c357-4d41-814a-861b3185acc7

import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Valuations_KernelShells
import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_existsUnique
import Theorems.Thm_FourierJacobi_Measure_coordinates_determinant_ae_with_parameter
import Theorems.Thm_FourierJacobi_Measure_localField_haar_nullSingletonClass


set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter ValuativeRel
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_9fc63f53e5_126
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_9fc63f53e5_127
namespace FourierJacobi.Analysis
theorem _root_.solution (μ : Measure K) [μ.IsAddHaarMeasure]
    (ν : Measure Kˣ) (r : ℤ) (z : K) (hz : CentralRepresentative K r z) :
    ∀ᵐ p : HaarPoint K ∂ν.prod (μ.prod μ),
      ∃! i : LatticeIndex, p ∈ haarLatticeCell K r z i := by
  let : NullSingletonClass μ := FourierJacobi.Measure.localField_haar_nullSingletonClass K μ
  filter_upwards [FourierJacobi.Measure.coordinates_determinant_ae_with_parameter μ μ ν z]
    with p hp
  exact haarLatticeCell_existsUnique K r z hz p hp
end FourierJacobi.Analysis
