-- Prove2me | solution 1 for ChromaticReconstruction.phi_uniformLeafExt_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:57.83985+00:00
-- url     : https://prove2.me/submissions/16e06dc9-80cf-4340-91bb-2466be7c6e50

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Theorem2
import Definitions.Def_RequestProject_ProperTree
import Definitions.Def_RequestProject_CountingLimit
import Definitions.Def_RequestProject_TauBound
import Definitions.Def_RequestProject_MainTheorems
import Theorems.Thm_P2M_ChromaticReconstruction_phi_uniformLeafExt_eq_iff__849a9106dfc6


set_option autoImplicit true
open MvPolynomial Finset Filter Topology
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {V W : Type*} [Fintype V] [Fintype W] (q : ℕ) (hq : 2 ≤ q)
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : G.Connected) (hH : H.Connected) :
    phi (uniformLeafExt q G) = phi (uniformLeafExt q H) ↔ chromSymm G = chromSymm H :=
  phi_uniformLeafExt_eq_iff' hq G H hG hH
end ChromaticReconstruction
