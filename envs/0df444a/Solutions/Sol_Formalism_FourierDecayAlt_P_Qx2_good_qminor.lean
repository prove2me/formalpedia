-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.good_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:40:09.815348+00:00
-- url     : https://prove2.me/submissions/bfbc7429-a41c-44c1-90fd-e5716bea503f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_foldr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_sum

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
theorem _root_.solution (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    Good k r i D (fun f : Mx k r → E => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u f) := by
  have key : ∀ σ : Equiv.Perm (Fin t), Good k r i D (fun f : Mx k r → E =>
      (List.ofFn fun l : Fin t => QuantumDeterminants.Top (EH k r) (u - ((l : ℕ) : ℂ)) ((posL k r i ∘ a) (σ l))
        ((posL k r i ∘ b) l)).foldr (fun T h => T h) f) := fun σ =>
    good_foldr _ fun T hT => by
      rw [List.mem_ofFn] at hT
      obtain ⟨l, rfl⟩ := hT
      exact good_top hD _ _ _
  have h := good_sum Finset.univ (fun σ : Equiv.Perm (Fin t) => ((Equiv.Perm.sign σ : ℤ) : ℂ)) _
    (fun σ _ => key σ)
  convert h using 2 with f
  funext x
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
end Formalism.FourierDecayAlt.P.Qx2
