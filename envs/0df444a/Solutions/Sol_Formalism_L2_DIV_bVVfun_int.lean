-- Prove2me | solution 1 for Formalism.L2.DIV.bVVfun_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:10:39.290832+00:00
-- url     : https://prove2.me/submissions/7b974b87-8309-4cf7-9be6-33de68ea9d34

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Theorems.Thm_Formalism_L2_DIV_ssB_int
import Theorems.Thm_Formalism_L2_DIV_fk_map_blockEmb

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
theorem _root_.solution (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (i : VVIdx lam) :
    ∃ P : MvPolynomial (ι × Fin n × Fin n) ℤ, bVVfun K lam i = MvPolynomial.map (Int.castRingHom K) P := by
  choose Q hQ using fun τ => ssB_int K (lam τ).natW (i τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℤ τ (Q τ), ?_⟩
  rw [map_prod]
  unfold bVVfun ten
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [fk_map_blockEmb]
  exact congrArg _ (hQ τ)
end Formalism.L2.DIV
