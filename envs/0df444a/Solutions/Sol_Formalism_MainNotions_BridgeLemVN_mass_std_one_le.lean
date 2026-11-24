-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVN.mass_std_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:46.654954+00:00
-- url     : https://prove2.me/submissions/23798fca-9b8a-4040-8562-480910d9811a

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN
import Theorems.Thm_Formalism_MainNotions_BridgeLemVN_mass_le
import Theorems.Thm_Formalism_MainNotions_BridgeLemVN_isLattice_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_exists_model
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mass_eq_of_lattices
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finiteDimensional_of_ortho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finrank_of_ortho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isLattice_of_ortho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isTotPosDef_of_ortho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_stdForm_isSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_stdLat_isOrtho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVN
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVN
theorem _root_.solution (hK : IsCMUnram K) :
    mass (stdForm K 1) (stdLat K 1) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  have hs := stdForm_isSymm K 1
  have ho := stdLat_isOrtho K 1
  have := finiteDimensional_of_ortho ho
  obtain ⟨h', A, hn, hA, hex, e⟩ := exists_model hs (isTotPosDef_of_ortho hK hs ho) (finrank_of_ortho ho)
    (isLattice_of_ortho ho)
  rw [← e, ← mass_eq_of_lattices hn hn hA isLattice_one hex]
  exact mass_le hK h' hn
end Formalism.MainNotions.BridgeLemVN
