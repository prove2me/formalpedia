-- Prove2me | solution 1 for Formalism.HN.sum_ite_val_lt_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:03.59996+00:00
-- url     : https://prove2.me/submissions/a24b4e46-5706-4239-a097-57dc623ec82d

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Theorems.Thm_Formalism_HN_sum_ite_val_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (n m : ℕ) (hm : m ≤ n) (x : Fin n → ℝ) (a : ℝ) :
    (∑ j : Fin n, if (j : ℕ) < m then x j else 0) - a * m =
      ∑ j : Fin n, if (j : ℕ) < m then x j - a else 0 := by
  have h : ∀ j : Fin n, (if (j : ℕ) < m then x j - a else 0) =
      (if (j : ℕ) < m then x j else 0) - a * (if (j : ℕ) < m then (1 : ℝ) else 0) := by
    intro j
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_ite_val_lt_one n m hm]
end Formalism.HN
