-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.limit_ident
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:48.5538+00:00
-- url     : https://prove2.me/submissions/df410e76-4eb8-4215-b314-439982ad97f0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_stepD
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_allLie_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {a : ℝ} {mm : ℕ} (Fs : ℕ → Mat k r → E)
    (hC : ∀ n, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (Fs n))
    (K : List (Mat k r) → List (Mat k r) → Mat k r → E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ n (u w : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, ‖dLR u w (Fs n) g - K u w g‖ ≤ gN g ^ (-a) * ε n) :
    ∀ u w : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, dLR u w (K [] []) g = K u w g := by
  have hck : ∀ n (u w : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length + 1 ≤ mm → CkOn ((1 : ℕ) : ℕ∞) (GV k r) (dLR u w (Fs n)) := by
    intro n u w hu hw hl
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr hu hw) 1 (ckOn_mono (by rw [length_lr]; omega) (hC n))
  have base : ∀ w : List (Mat k r), (∀ X ∈ w, unitLie k r X) → w.length ≤ mm →
      ∀ g ∈ GV k r, dLR [] w (K [] []) g = K [] w g := by
    intro w
    induction w with
    | nil => intro _ _ g _; rfl
    | cons X w ih =>
      intro hw hl g hg
      have hw' : ∀ Y ∈ w, unitLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
      have hX := hw X List.mem_cons_self
      have hl' : w.length + 1 ≤ mm := by simpa using hl
      show op false X (dLR [] w (K [] [])) g = K [] (X :: w) g
      rw [op_congr false hX.1 (ih hw' (by omega)) g hg]
      exact stepD hX.1 hg a (fun n => dLR [] w (Fs n)) (K [] w) (K [] (X :: w)) ε hε
        (fun n => hck n [] w (by simp) hw' (by simpa using hl'))
        (fun n h hh => hb n [] w (by simp) hw' (by simp; omega) h hh)
        (fun n h hh => hb n [] (X :: w) (by simp) hw (by simpa using hl) h hh)
  intro u
  induction u with
  | nil => intro w _ hw hl; exact base w hw (by simpa using hl)
  | cons X u ih =>
    intro w hu hw hl g hg
    have hu' : ∀ Y ∈ u, unitLie k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX := hu X List.mem_cons_self
    have hl' : u.length + w.length + 1 ≤ mm := by simp at hl; omega
    show op true X (dLR u w (K [] [])) g = K (X :: u) w g
    rw [op_congr true hX.1 (ih w hu' hw (by omega)) g hg]
    exact stepD hX.1 hg a (fun n => dLR u w (Fs n)) (K u w) (K (X :: u) w) ε hε
      (fun n => hck n u w hu' hw hl')
      (fun n h hh => hb n u w hu' hw (by omega) h hh)
      (fun n h hh => hb n (X :: u) w hu hw hl h hh)
end Formalism.FourierDecayAlt.P.Ux1
