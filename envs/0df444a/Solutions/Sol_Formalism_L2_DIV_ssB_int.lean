-- Prove2me | solution 1 for Formalism.L2.DIV.ssB_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:56:16.870809+00:00
-- url     : https://prove2.me/submissions/655f64a0-40b5-486f-8475-f9bac1763a35

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Theorems.Thm_Formalism_L2_DIV_fk_map_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution (K : Type) [Field K] {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℤ, ssB K ν m = map (Int.castRingHom K) P := by
  obtain ⟨k, sz, hsz, I, -, -, h⟩ := ((Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose_spec.2 m).2.2
  exact ⟨Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I, by rw [fk_map_bidet]; exact h⟩
end Formalism.L2.DIV
