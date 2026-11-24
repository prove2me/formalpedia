-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:28.436856+00:00
-- url     : https://prove2.me/submissions/3a36eb3e-4768-43ba-bf7c-b5e86be5d5c4

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_L2_G_Model_sw_dom
import Theorems.Thm_Formalism_GradedWeylDivisibility_highestWeightCount_self_eq_succ_of_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_rowDiv_shift
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_weight_P
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_weight_rowW
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowNuSum


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
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) (hG : G ∈ dualWeyl R r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv R a b k G = 0 := by
  classical
  have hGp : IsWeightedHomogeneous (lehwP a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro m hm
    rw [lehw_weight_P]
    have hm' := hGh hm
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hm']
  have hsh := lehw_rowDiv_shift R (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp
  have hmem := rowDivStable R r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have h1 := hsh hm
  rw [lehw_weight_P] at h1
  have h2 := sw_dom R ν _ hmem m (mem_support_iff.mpr hm) (a.val + 1)
  rw [← rowNuSum r n ν hn] at h2
  have h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [h1] at h3
  linarith
end Formalism.L2.G.Model
