-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.fold_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:44.698828+00:00
-- url     : https://prove2.me/submissions/cdada19a-2499-4cec-aaaa-8ab94a15e2ad

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution : ∀ (L : List (Module.End ℂ (Wsm (E := E) U₀) × ((Mat k r → E) → (Mat k r → E)))),
    (∀ p ∈ L, ∀ (h : Wsm (E := E) U₀), ∀ g ∈ U₀, g ∈ GV k r → (p.1 h).1 g = p.2 h.1 g) →
    (∀ p ∈ L, ∀ (h₁ h₂ : Mat k r → E), (∀ x ∈ U₀, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ g ∈ U₀, g ∈ GV k r → p.2 h₁ g = p.2 h₂ g) →
    ∀ (f : Wsm (E := E) U₀), ∀ g ∈ U₀, g ∈ GV k r →
      ((L.map Prod.fst).prod f).1 g = (L.map Prod.snd).foldr (fun T h => T h) f.1 g
  | [], _, _, f, g, _, _ => by simp
  | p :: L, hA, hC, f, g, hg, hgG => by
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply]
    rw [hA p (by simp) _ g hg hgG]
    apply hC p (by simp) _ _ _ g hg hgG
    intro x hx hxG
    exact solution L (fun q hq => hA q (by simp [hq])) (fun q hq => hC q (by simp [hq])) f x hx hxG
end Formalism.FourierDecayAlt.P.PBG
