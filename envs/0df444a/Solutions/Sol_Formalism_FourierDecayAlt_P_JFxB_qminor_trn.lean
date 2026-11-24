-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.qminor_trn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:18.908661+00:00
-- url     : https://prove2.me/submissions/36c1990d-f90e-44e4-9e39-a83ad39f64e6

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_fold_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E') → (Mat k r → E'))
    (Eop' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hI : ∀ c d (f : Mat k r → E), CkOn ((1 : ℕ) : ℕ∞) (GV k r) f →
      ∀ g ∈ GV k r, Eop c d (trn L a b f) g = trn L a b (Eop' c d f) g)
    (hC : ∀ c d (f f₂ : Mat k r → E'), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop c d f g = Eop c d f₂ g)
    (hS' : ∀ c d (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f →
      CkOn (m : ℕ∞) (GV k r) (Eop' c d f))
    {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E)
    (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, qminorOp Eop p q u (trn L a b f) g = trn L a b (qminorOp Eop' p q u f) g := by
  intro g hg
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, trn, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : ∀ (F : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E') → (Mat k r → E')),
      (List.ofFn fun j : Fin t => Top F (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)) =
        (List.ofFn fun j : Fin t => ((u - ((j : ℕ) : ℂ)), p (σ j), q j)).map
          (fun t => Top F t.1 t.2.1 t.2.2) := by
    intro F; rw [List.map_ofFn]; rfl
  have e2 : ∀ (F : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)),
      (List.ofFn fun j : Fin t => Top F (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)) =
        (List.ofFn fun j : Fin t => ((u - ((j : ℕ) : ℂ)), p (σ j), q j)).map
          (fun t => Top F t.1 t.2.1 t.2.2) := by
    intro F; rw [List.map_ofFn]; rfl
  rw [e1, e2]
  have := fold_trn L ha hb Eop Eop' hI hC hS'
    (List.ofFn fun j : Fin t => ((u - ((j : ℕ) : ℂ)), p (σ j), q j)) f (by simpa using hf) g hg
  simpa [trn] using this
end Formalism.FourierDecayAlt.P.JFxB
