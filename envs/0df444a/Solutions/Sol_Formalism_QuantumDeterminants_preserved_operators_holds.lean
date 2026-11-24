-- Prove2me | solution 1 for Formalism.QuantumDeterminants.preserved_operators_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:50.571392+00:00
-- url     : https://prove2.me/submissions/be5ad73f-ee00-410a-8503-3345990bb78b

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Theorems.Thm_Formalism_QuantumDeterminants_WRPres_coord_contDiff
import Theorems.Thm_Formalism_QuantumDeterminants_WRPres_conjCoord_contDiff
import Theorems.Thm_Formalism_QuantumDeterminants_WRPres_wirt_contDiffOn
import Theorems.Thm_Formalism_QuantumDeterminants_WRPres_wirtBar_contDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open WRPres
namespace Formalism.QuantumDeterminants
theorem _root_.solution : PresOps := by
  intro m E _ _ l i f hf
  have hc : ContDiffOn ℝ ∞ f (OmX m) := hf.1
  have hz : ∀ x ∉ OmX m, f x = 0 := hf.2
  have hcoord : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => x l) (OmX m) := (coord_contDiff l).contDiffOn
  have hconj : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => star (x l)) (OmX m) :=
    (conjCoord_contDiff l).contDiffOn
  have hne : ∀ x ∈ OmX m, x l ≠ 0 := fun x hx => hx l
  have hinv : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (x l)⁻¹) (OmX m) := hcoord.inv hne
  have hinvc : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (star (x l))⁻¹) (OmX m) :=
    hconj.inv fun x hx => by simpa using hne x hx
  show ContDiffOn ℝ ∞ (opL l i f) (OmX m) ∧ ∀ x ∉ OmX m, opL l i f x = 0
  fin_cases i
  · exact ⟨(hcoord.smul (wirt_contDiffOn hc l)).congr fun x hx => by simp [opL, pOp, hx],
      fun x hx => by simp [opL, pOp, hx]⟩
  · exact ⟨(hcoord.smul hc).congr fun x hx => by simp [opL, cOp],
      fun x hx => by simp [opL, cOp, hz x hx]⟩
  · exact ⟨(hinv.smul hc).congr fun x hx => by simp [opL, ciOp],
      fun x hx => by simp [opL, ciOp, hz x hx]⟩
  · exact ⟨(hconj.smul (wirtBar_contDiffOn hc l)).congr fun x hx => by simp [opL, pbOp, hx],
      fun x hx => by simp [opL, pbOp, hx]⟩
  · exact ⟨(hconj.smul hc).congr fun x hx => by simp [opL, cbOp],
      fun x hx => by simp [opL, cbOp, hz x hx]⟩
  · exact ⟨(hinvc.smul hc).congr fun x hx => by simp [opL, cbiOp],
      fun x hx => by simp [opL, cbiOp, hz x hx]⟩
end Formalism.QuantumDeterminants
