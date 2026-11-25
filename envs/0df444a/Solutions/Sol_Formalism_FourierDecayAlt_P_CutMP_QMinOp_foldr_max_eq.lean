-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.QMinOp.foldr_max_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:00:18.449075+00:00
-- url     : https://prove2.me/submissions/002ead12-d4f3-4138-af0e-fccf98346dbc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatQMinOp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp
open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section terms
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
private theorem foldr_max_le_lemma (t : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ t) → l.foldr max 0 ≤ t := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))
private theorem le_foldr_max_lemma_2 : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih x hx) (le_max_right _ _)
end terms
section basic₂
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end basic₂
end
end Formalism.FourierDecayAlt.P.CutMP.QMinOp
end

set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.QMinOp
open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp
theorem _root_.solution (t : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ t) → t ∈ l → l.foldr max 0 = t := by
  intro l hl ht
  exact le_antisymm (foldr_max_le_lemma t l hl) (le_foldr_max_lemma_2 l t ht)
end Formalism.FourierDecayAlt.P.CutMP.QMinOp
