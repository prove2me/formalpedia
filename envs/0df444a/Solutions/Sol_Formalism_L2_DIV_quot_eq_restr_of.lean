-- Prove2me | solution 1 for Formalism.L2.DIV.quot_eq_restr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:31.551784+00:00
-- url     : https://prove2.me/submissions/6185f7c7-5fdd-4225-87af-0c4ba217955f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_P2M_Formalism_L2_DIV_map_one__d0eedca16a10
import Theorems.Thm_P2M_Formalism_L2_DIV_map_conjTranspose__e871e98cff26
import Theorems.Thm_Formalism_L2_DIV_quotEqRestrC
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K)
    {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : (H.map v.embedding).PosDef)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (hE : ∀ i a, v.embedding (star (E i a)) = starRingEnd ℂ (v.embedding (E i a)))
    (hP : IsOrthProj H E Pr) : quotFrame Pr H v = restrFrame E H v := by
  have h1 : Pr.map v.embedding * E.map v.embedding = 1 := by
    rw [← Matrix.map_mul, hP.1, map_one']
  have h2 : (E.map v.embedding)ᴴ * H.map v.embedding *
      (1 - E.map v.embedding * Pr.map v.embedding) = 0 := by
    have := congrArg (fun M => M.map v.embedding) hP.2
    simp only [Matrix.map_mul, Matrix.map_sub _ (map_sub v.embedding), map_one',
      map_conjTranspose' v.embedding E hE] at this
    rw [this]
    exact Matrix.map_zero _ (map_zero _)
  rw [quotFrame, restrFrame, quotEqRestrC n d _ hH _ _ h1 h2]
end Formalism.L2.DIV
