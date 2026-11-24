-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.hw_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:29.212082+00:00
-- url     : https://prove2.me/submissions/f042da05-4ef1-4e92-b056-8fa1c6bbbecd

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingHighestWeightProof
import Theorems.Thm_Formalism_L2_G_Model_TS_hw_dom
import Theorems.Thm_Formalism_GradedWeylDivisibility_highestWeightCount_self_eq_succ_of_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_rowDiv_shift
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_weight_P
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_weight_rowW
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable


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
theorem _root_.solution {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) B) (hG : G ∈ dualWeyl B r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv B a b k G = 0 := by
  classical
  have hGp : IsWeightedHomogeneous (lehwP a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro m hm
    rw [lehw_weight_P]
    have hm' := hGh hm
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hm']
  have hsh := lehw_rowDiv_shift B (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp
  have hmem := rowDivStable B r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have h1 := hsh hm
  rw [lehw_weight_P] at h1
  have h2 := hw_dom ν hn _ hmem m (mem_support_iff.mpr hm) (a.val + 1)
  have h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [h1] at h3
  linarith
end Formalism.L2.G.Model.TS
