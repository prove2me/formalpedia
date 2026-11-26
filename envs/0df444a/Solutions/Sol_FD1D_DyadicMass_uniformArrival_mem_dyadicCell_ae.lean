-- Prove2me | solution 1 for FD1D.DyadicMass.uniformArrival_mem_dyadicCell_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:06.715213+00:00
-- url     : https://prove2.me/submissions/db64ce11-accf-407e-ad9f-4d00578db854

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_UniformArrival
import Theorems.Thm_FD1D_DyadicMass_uniformArrival_mem_dyadicCell

set_option autoImplicit true
open FD1D
noncomputable section
open Set MeasureTheory
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution (L : ℕ) :
    ∀ᵐ u ∂uniformDemand,
      u ∈ dyadicCell (uniformArrivalLeaf L u) := by
  rw [uniformDemand, ae_restrict_iff' measurableSet_Icc]
  filter_upwards with u hu
  exact uniformArrival_mem_dyadicCell L hu
end FD1D.DyadicMass
