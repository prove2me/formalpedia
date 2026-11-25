-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.chat_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:26:44.103396+00:00
-- url     : https://prove2.me/submissions/de096481-d81d-4fd1-b57e-64430627888e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_polyAt_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_qminor_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_lc_skip1

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
theorem _root_.solution (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) (a β : Mx k r → Fin (mdim k r i) → ℂ) (s : ℂ) :
    PolyAt (mdim k r i - 1) (fun Y => chatL (EH k r) (posL k r i) (Y + s) a β f x -
      Y ^ (mdim k r i - 1) • ((∑ j, β x j * a x j) • f x)) := by
  have H : PolyAt (mdim k r i - 1) (fun Y => ∑ p : Fin (mdim k r i), ∑ q : Fin (mdim k r i),
      ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β x p * a x q) •
        (qminorOp (EH k r) (posL k r i ∘ skip1 p) (posL k r i ∘ skip1 q) (Y + s) f x -
          Y ^ (mdim k r i - 1) • (lc k r i (skip1 p) (skip1 q) • f x))) :=
    polyAt_sum _ _ fun p _ => polyAt_sum _ _ fun q _ => (qminor_poly hD hf hx (skip1 p) (skip1 q) s).smul _
  have hc : ∀ p : Fin (mdim k r i), (-1 : ℂ) ^ ((p : ℕ) + (p : ℕ)) = 1 := fun p => Even.neg_one_pow ⟨p, rfl⟩
  have key : ∀ Y : ℂ, (∑ p : Fin (mdim k r i), ∑ q : Fin (mdim k r i),
      ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * β x p * a x q) •
        (Y ^ (mdim k r i - 1) • (lc k r i (skip1 p) (skip1 q) • f x))) =
      Y ^ (mdim k r i - 1) • ((∑ j, β x j * a x j) • f x) := fun Y => by
    simp only [lc_skip1, ite_smul, one_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, hc, one_mul]
    rw [Finset.sum_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun p _ => smul_comm _ _ _
  refine H.congr fun Y => ?_
  rw [← key Y]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rfl
end Formalism.FourierDecayAlt.P.Qx2
