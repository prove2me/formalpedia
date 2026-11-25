-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedA.radRedInj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:14:55.164068+00:00
-- url     : https://prove2.me/submissions/c0fe41ce-c595-4c56-b12b-4a6b1e8d1a9d

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_mem_domR
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_decomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace Formalism.FourierDecayAlt.P.NFRadRedA
theorem _root_.solution : NF.RadRedInj := by
  intro Wp Wq _ _ _ _ k r z z' μsec π π' hB Φ hΦ Ψ hΨ hR
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, -, he⟩ := hΦ
  obtain ⟨h0', -, he'⟩ := hΨ
  funext x g
  by_cases hx : (x, g) ∈ DomR k r z z'
  · obtain ⟨hxO, hg, hG⟩ := hx
    obtain ⟨h, hh, h', hh', hd⟩ := decomp hk hz hz' hT hT' hsec hg hG
    have hq : (x, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z' := by
      refine ⟨hxO, ?_⟩
      have h2 := hG
      unfold GGl at h2
      linarith
    have hD := mem_domR hz hz' hsec hq
    have e1 := he _ hD h hh h' hh'
    have e2 := he' _ hD h hh h' hh'
    have hr := congrFun hR (x, zetaL k r z z' (Fin.last r) g)
    simp only [radR, Set.indicator_of_mem hq] at hr
    simp only at e1 e2 hd
    rw [hd, e1, e2, hr]
  · exact (h0 (x, g) hx).trans (h0' (x, g) hx).symm
end Formalism.FourierDecayAlt.P.NFRadRedA
