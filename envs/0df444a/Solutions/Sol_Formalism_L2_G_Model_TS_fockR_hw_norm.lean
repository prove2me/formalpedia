-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_hw_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:44.502465+00:00
-- url     : https://prove2.me/submissions/876ff1d5-fdb3-42e8-b15e-36d3463c8ce4

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_map
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_int_self_pos
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_hw_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) : ∃ N : ℕ, 0 < N ∧
    ∀ (R : Type) [CommRing R], fockR (hw R hn ν) (hw R hn ν) = (N : R) := by
  have pos : 0 < fockR (hw ℤ hn ν) (hw ℤ hn ν) := fockR_int_self_pos _ (hwNe ℤ r n hn ν)
  refine ⟨(fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat, by omega, fun R _ => ?_⟩
  rw [← lclosedeq_hw_map (Int.castRingHom R) hn ν, fockR_map]
  have e : (((fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat : ℕ) : ℤ) = fockR (hw ℤ hn ν) (hw ℤ hn ν) :=
    Int.toNat_of_nonneg pos.le
  calc (Int.castRingHom R) (fockR (hw ℤ hn ν) (hw ℤ hn ν))
      = (Int.castRingHom R) (((fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat : ℕ) : ℤ) := by rw [e]
    _ = _ := by rw [eq_intCast, Int.cast_natCast]
end Formalism.L2.G.Model.TS
