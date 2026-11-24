-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.exch_dLR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:37.205848+00:00
-- url     : https://prove2.me/submissions/60309d14-7220-4f80-aa81-4af4fb872c41

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_meas_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_step_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_allLie_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [CompleteSpace E]
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1) (hψm : AEStronglyMeasurable ψ μ) (h : α → Mat k r → E) (mm : ℕ)
    (hh : ∀ ξ, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (h ξ))
    (hm : ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => h ξ g) μ) (β : α → ℝ) (hβ : Integrable β μ)
    (hbd : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ mm →
      ∀ g ∈ GV k r, ∀ ξ, ‖dLR u v (h ξ) g‖ ≤ β ξ) :
    ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ mm →
      ∀ g ∈ GV k r, dLR u v (fun g' => ∫ ξ, ψ ξ • h ξ g' ∂μ) g = ∫ ξ, ψ ξ • dLR u v (h ξ) g ∂μ := by
  have hC : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length + 1 ≤ mm → ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (dLR u v (h ξ)) := by
    intro u v hu hv hl ξ
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr hu hv) 1 (ckOn_mono (by rw [length_lr]; omega) (hh ξ))
  have hM : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ mm → ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => dLR u v (h ξ) g) μ := by
    intro u v hu hv hl g hg
    simp_rw [dLR_eq]
    exact meas_alt hh hm _ (allLie_lr hu hv) (by rw [length_lr]; exact hl) g hg
  have base : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ mm →
      ∀ g ∈ GV k r, dLR [] v (fun g' => ∫ ξ, ψ ξ • h ξ g' ∂μ) g = ∫ ξ, ψ ξ • dLR [] v (h ξ) g ∂μ := by
    intro v
    induction v with
    | nil => intro _ _ g _; rfl
    | cons X v ih =>
      intro hv hl g hg
      have hv' : ∀ Y ∈ v, unitLie k r Y := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
      have hX := hv X List.mem_cons_self
      have hl' : v.length + 1 ≤ mm := by simpa using hl
      show op false X (dLR [] v (fun g' => ∫ ξ, ψ ξ • h ξ g' ∂μ)) g = ∫ ξ, ψ ξ • op false X (dLR [] v (h ξ)) g ∂μ
      exact step_int (b := false) hX.1 ψ hψ hψm (fun ξ => dLR [] v (h ξ)) (hC [] v (by simp) hv' (by simpa using hl'))
        (hM [] v (by simp) hv' (by simp; omega)) β hβ (hbd [] v (by simp) hv' (by simp; omega))
        (hbd [] (X :: v) (by simp) hv (by simpa using hl)) _ (ih hv' (by omega)) g hg
  intro u
  induction u with
  | nil => intro v _ hv hl; exact base v hv (by simpa using hl)
  | cons X u ih =>
    intro v hu hv hl g hg
    have hu' : ∀ Y ∈ u, unitLie k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX := hu X List.mem_cons_self
    have hl' : u.length + v.length + 1 ≤ mm := by simp at hl; omega
    show op true X (dLR u v (fun g' => ∫ ξ, ψ ξ • h ξ g' ∂μ)) g = ∫ ξ, ψ ξ • op true X (dLR u v (h ξ)) g ∂μ
    exact step_int (b := true) hX.1 ψ hψ hψm (fun ξ => dLR u v (h ξ)) (hC u v hu' hv hl')
      (hM u v hu' hv (by omega)) β hβ (hbd u v hu' hv (by omega)) (hbd (X :: u) v hu hv hl) _
      (ih v hu' hv (by omega)) g hg
end Formalism.FourierDecayAlt.P.Ux10
