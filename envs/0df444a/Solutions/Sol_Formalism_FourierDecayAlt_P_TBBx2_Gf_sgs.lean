-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Gf_sgs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:20:06.969433+00:00
-- url     : https://prove2.me/submissions/8dd3bc21-b1c4-455b-adae-902acba09872

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_one_mem_UW
import Theorems.Thm_Formalism_QuantumDeterminants_gInv
import Theorems.Thm_Formalism_QuantumDeterminants_nSubgroup
import Theorems.Thm_Formalism_QuantumDeterminants_sGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx2
theorem _root_.solution {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : B.RealPlaceData k r Wp Wq) (q : B.SS k r)
    (hq : Ds.inSS q) (g : B.Mat k r) :
    Gf k r Ds.z Ds.z' (B.sgs q g) = Gf k r Ds.z Ds.z' g := by
  obtain ⟨hh, hn, hh', hn'⟩ := hq
  have SG := sGroup k r Ds.z Ds.z_mem
  have SG' := sGroup k r Ds.z' Ds.z'_mem
  have hS1 : Matrix.of q.1.1 ∈ Sset k r Ds.z := ⟨_, hh, 1, (nSubgroup k r).1, by simp⟩
  have hS2 : Matrix.of q.1.2 ∈ Sset k r Ds.z := ⟨1, one_mem_UW _ _ _, _, hn, by simp⟩
  have hS3 : Matrix.of q.2.1 ∈ Sset k r Ds.z' := ⟨_, hh', 1, (nSubgroup k r).1, by simp⟩
  have hS4 : Matrix.of q.2.2 ∈ Sset k r Ds.z' := ⟨1, one_mem_UW _ _ _, _, hn', by simp⟩
  have hs : (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ ∈ Sset k r Ds.z :=
    SG.2.1 _ (SG.2.2 _ hS1) _ (SG.2.2 _ hS2)
  have hs' : Matrix.of q.2.2 * Matrix.of q.2.1 ∈ Sset k r Ds.z' := SG'.2.1 _ hS4 _ hS3
  have e : B.sgs q g = ((Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1) := by
    unfold B.sgs; simp only [mul_assoc]
  rw [e]
  exact gInv k r Ds.z Ds.z' Ds.z_mem Ds.z'_mem _ hs _ hs' g
end Formalism.FourierDecayAlt.P.TBBx2
