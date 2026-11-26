-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:31.975172+00:00
-- url     : https://prove2.me/submissions/e65dc161-16d7-4b28-b65e-ea520abf9538

import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Valuations_KernelShells
import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_disjoint
import Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_exhaustive

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
omit [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Analysis
theorem _root_.solution (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (p : HaarPoint K) (hp : p.2.1≠0 ∧ p.2.2≠0 ∧ p.2.2^2-p.2.1*z≠0) :
    ∃! i : LatticeIndex, p ∈ haarLatticeCell K r z i := by
  obtain ⟨i,hi⟩ := haarLatticeCell_exhaustive K r z hz p hp
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hji
  exact (Set.disjoint_left.mp (haarLatticeCell_disjoint K r z hji)) hj hi
end FourierJacobi.Analysis
