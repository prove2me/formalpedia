-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.fold_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:37:57.411611+00:00
-- url     : https://prove2.me/submissions/e8510970-53ba-4b35-bed0-9c11fa720da2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_eh
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_mulY
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_polyFam_monomial
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_good
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_opF_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f)
    (L : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) :
    PolyFam k r i D L.length (fun Y x => (L.map (opF k r i Y)).foldr (fun T h => T h) f x -
      Y ^ L.length • ((L.map (dl k r i)).prod • f x)) := by
  induction L with
  | nil =>
    refine ⟨fun _ _ => 0, fun _ => smooth_zero, fun Y x _ => ?_⟩
    simp
  | cons e L ih =>
    have hG : PolyFam k r i D (L.length + 1) (fun Y => (L.map (opF k r i Y)).foldr (fun T h => T h) f) :=
      (ih.succ.add (polyFam_monomial (smooth_smul hf (L.map (dl k r i)).prod) L.length)).congr
        fun Y x _ => by simp
    have hE := hG.good (good_eh hD e.2.1 e.2.2)
    have hA := ih.mulY.smul (dl k r i e)
    have hB := ih.succ.smul (dl k r i e * e.1)
    have hC := polyFam_monomial (smooth_smul hf (dl k r i e * e.1 * (L.map (dl k r i)).prod)) L.length
    refine (((hA.add hB).add hC).add hE).congr fun Y x _ => ?_
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, List.length_cons]
    rw [opF_apply]
    module
end Formalism.FourierDecayAlt.P.Qx2
