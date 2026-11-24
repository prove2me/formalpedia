-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_trn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:38:41.213858+00:00
-- url     : https://prove2.me/submissions/67b50b13-d66f-4bc3-80d2-b3f79c68b561

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_trn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) (v : List (Mat k r))
    (hv : ∀ X ∈ v, inLie k r X) {f : Mat k r → E} (hf : CkOn v.length (GV k r) f) :
    ∀ g ∈ GV k r, Rw v (trn L a b f) g = trn L a b (Rw (v.map fun X => b⁻¹ * X * b) f) g := by
  induction v with
  | nil => intro g _; rfl
  | cons X v ih =>
    intro g hg
    have hX : inLie k r X := hv X (by simp)
    have hv' : ∀ Y ∈ v, inLie k r Y := fun Y hY => hv Y (by simp [hY])
    have hle : ((v.length : ℕ) : ℕ∞) ≤ (((X :: v).length : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.le_succ v.length
    have hfv : CkOn v.length (GV k r) f := sCkOn_mono hle hf
    have hw : ∀ x ∈ wR (v.map fun Z => b⁻¹ * Z * b), inLie k r x.2 := by
      intro x hx
      simp only [wR, List.mem_map] at hx
      obtain ⟨Y, ⟨Z, hZ, rfl⟩, rfl⟩ := hx
      exact lie_conj (hv' Z hZ) hb
    have e1 : (((X :: v).length : ℕ) : ℕ∞) =
        1 + ((wR (v.map fun Z => b⁻¹ * Z * b)).length : ℕ∞) := by
      simp only [wR, List.length_map, List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    have hc1 : CkOn 1 (GV k r) (Rw (v.map fun Z => b⁻¹ * Z * b) f) := by
      rw [← Dw_wR]; exact CkOn_Dw hw (by rw [← e1]; exact hf)
    show Dx (false, X) (Rw v (trn L a b f)) g =
      trn L a b (Dx (false, b⁻¹ * X * b) (Rw (v.map fun Z => b⁻¹ * Z * b) f)) g
    rw [Dx_congr (x := (false, X)) hX (f := Rw v (trn L a b f)) (f₂ := trn L a b (Rw (v.map fun Z => b⁻¹ * Z * b) f))
      (ih hv' hfv) g hg]
    exact Dx_trn L ha hb hX hc1 g hg
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
