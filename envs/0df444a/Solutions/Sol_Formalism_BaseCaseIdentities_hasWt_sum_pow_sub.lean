-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.hasWt_sum_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:51.687134+00:00
-- url     : https://prove2.me/submissions/02e23396-4ec8-46c8-a8dd-9c759a91dd41

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_add
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_add_pow_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}
namespace Formalism.BaseCaseIdentities
theorem _root_.solution {ι : Type*} {l e : ℕ} (hl : l.Prime) (hv : v (l : k) = 1) (_he : 1 ≤ e)
    (s : Finset ι) {F : ι → MvPowerSeries Z k} (h : ∀ i ∈ s, HasWt v r w (F i)) :
    HasWt v r (1 + ((l ^ e : ℕ) : ℝ) * w) ((∑ i ∈ s, F i) ^ (l ^ e) - ∑ i ∈ s, (F i) ^ (l ^ e)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : l ^ e ≠ 0 := pow_ne_zero _ hl.ne_zero
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow this, sub_zero]
    exact HasWt.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h1 := hasWt_add_pow_sub (e := e) hl hv le_rfl (h i (Finset.mem_insert_self i s))
      (HasWt.sum s fun j hj => h j (Finset.mem_insert_of_mem hj))
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h3 := (h1.mono (w' := 1 + ((l ^ e : ℕ) : ℝ) * w) (by linarith)).add h2
    convert h3 using 1
    ring
end Formalism.BaseCaseIdentities
