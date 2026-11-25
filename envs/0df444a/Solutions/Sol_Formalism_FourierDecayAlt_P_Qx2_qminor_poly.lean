-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.qminor_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:56:37.543222+00:00
-- url     : https://prove2.me/submissions/0f8e3f40-b923-45e5-aa2a-5dd1d4065765

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_fold_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_polyAt_sum

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
    (hx : x ∈ Glev k r i ∩ D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (s : ℂ) :
    PolyAt t (fun Y => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) (Y + s) f x -
      Y ^ t • (lc k r i a b • f x)) := by
  have key : ∀ σ : Equiv.Perm (Fin t), PolyAt t (fun Y =>
      (List.ofFn fun l : Fin t => QuantumDeterminants.Top (EH k r) (Y + s - ((l : ℕ) : ℂ)) ((posL k r i ∘ a) (σ l))
        ((posL k r i ∘ b) l)).foldr (fun T h => T h) f x -
      Y ^ t • ((∏ l : Fin t, if posL k r i (a (σ l)) = posL k r i (b l) then (1 : ℂ) else 0) • f x)) := by
    intro σ
    have h := (fold_poly hD hf (List.ofFn fun l : Fin t => (s - ((l : ℕ) : ℂ), a (σ l), b l))).at hx
    simp only [List.length_ofFn, List.map_ofFn, List.prod_ofFn] at h
    refine h.congr fun Y => ?_
    have e : (List.ofFn fun l : Fin t => QuantumDeterminants.Top (E := E) (EH k r) (Y + s - ((l : ℕ) : ℂ))
        ((posL k r i ∘ a) (σ l)) ((posL k r i ∘ b) l)) =
        List.ofFn (opF k r i Y ∘ fun l : Fin t => (s - ((l : ℕ) : ℂ), a (σ l), b l)) := by
      congr 1
      funext l
      simp only [Function.comp, opF, add_sub_assoc]
    rw [e]
    rfl
  refine (polyAt_sum Finset.univ _ fun σ _ => (key σ).smul ((Equiv.Perm.sign σ : ℤ) : ℂ)).congr fun Y => ?_
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, lc, Finset.sum_smul, Finset.smul_sum, smul_sub,
    Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  module
end Formalism.FourierDecayAlt.P.Qx2
