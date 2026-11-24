-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.zhat_section_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:10.130817+00:00
-- url     : https://prove2.me/submissions/3fca8dfd-d0bc-47ca-8bb7-2c393097db93

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_N_sub_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_UW_sub_S
import Theorems.Thm_Formalism_QuantumDeterminants_symmetric_group_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6 C2x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.ZhatSectionOfParts := by
  intro hZE hUM hTM _ k r z z' γ hstd n0 hn0 v hv h hh s' hs'
  have hz := hstd.2.1
  have hz' := hstd.2.2
  obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
  have hSg := symmetric_group_holds k r z hz.1
  have hn0S : n0 ∈ Sset k r z := N_sub_S hn0.1
  have hτS : C2.tauM k r z v ∈ Sset k r z := N_sub_S hτN
  have hhS : h ∈ Sset k r z := UW_sub_S hh
  have hs1 : n0 * C2.tauM k r z v ∈ Sset k r z := hSg.2.1 _ hn0S _ hτS
  have hs : n0 * C2.tauM k r z v * h ∈ Sset k r z := hSg.2.1 _ hs1 _ hhS
  have hU := hUM k r z hz
  have hu : C2.uMap k r z (n0 * C2.tauM k r z v * h) = v := by
    rw [(hU.1 _ hs1).2.2 h hhS, (hU.1 _ hn0S).2.2 _ hτS, hn0.2, hτu, hU.2 h hh, Matrix.one_mul,
      Matrix.mul_one]
  rw [hZE k r z z' hz hz' _ hs s' hs' γ, hu]
end Formalism.FourierDecayAlt.P
