-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.blk_cl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:20.543075+00:00
-- url     : https://prove2.me/submissions/65f31de8-d137-4a54-8f76-43c65fb7f51a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P.StandardCharacterExists
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]
end Formalism.FourierDecayAlt.P.StandardCharacterExists
