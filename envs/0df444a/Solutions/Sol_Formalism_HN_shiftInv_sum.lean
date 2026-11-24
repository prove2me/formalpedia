-- Prove2me | solution 1 for Formalism.HN.shiftInv_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:30.248625+00:00
-- url     : https://prove2.me/submissions/0fdedc50-c03f-402c-a04b-60365720ad35

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Theorems.Thm_Formalism_HN_shiftInv_count
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
universe u v w w₂
private theorem sum_fin_ite_lt_const_eq_mul_min (c : ℝ) (k n : ℕ) :
    (∑ j : Fin n, if (j : ℕ) < k then c else 0) = c * ((min k n : ℕ) : ℝ) :=
  (Fin.sum_univ_eq_sum_range (fun i => if i < k then c else 0) n).trans (shiftInv_count c k n)
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w w₂
namespace Formalism.HN
theorem _root_.solution {n m : ℕ} (h : m = n) (f : Fin n → ℝ) (g : Fin m → ℝ) (c : ℝ) (k : ℕ)
    (hfg : ∀ (j : ℕ) (h1 : j < m) (h2 : j < n), g ⟨j, h1⟩ = f ⟨j, h2⟩ + c) :
    (∑ j : Fin m, if (j : ℕ) < k then g j else 0) =
      (∑ j : Fin n, if (j : ℕ) < k then f j else 0) + c * ((min k n : ℕ) : ℝ) := by
  subst h
  rw [← sum_fin_ite_lt_const_eq_mul_min c k, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact hfg j.1 j.2 j.2
  · simp
end Formalism.HN
