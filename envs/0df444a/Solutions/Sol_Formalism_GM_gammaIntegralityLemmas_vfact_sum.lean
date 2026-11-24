-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.vfact_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:25.146816+00:00
-- url     : https://prove2.me/submissions/01dc0bfd-fe18-4fdf-b202-d8acb4092dc8

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vfact_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution {ι : Type} (s : Finset ι) (α : ι → ℕ) {T B : ℕ} (h : ∑ i ∈ s, α i ≤ T)
    (hB : Nat.log p T ≤ B) :
    padicValNat p (∑ i ∈ s, α i).factorial ≤ ∑ i ∈ s, padicValNat p (α i).factorial + s.card * B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha] at h ⊢
    rw [sum_insert ha, card_insert_of_notMem ha]
    have h1 := vfact_split (p := p) h hB
    have h2 := ih (by omega)
    nlinarith
end Formalism.GM.gammaIntegralityLemmas
