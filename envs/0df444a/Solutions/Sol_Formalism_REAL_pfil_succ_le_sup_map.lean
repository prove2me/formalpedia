-- Prove2me | solution 1 for Formalism.REAL.pfil_succ_le_sup_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:08.111061+00:00
-- url     : https://prove2.me/submissions/b439a05f-ed84-466b-acf6-3b2264a72943

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_ew_cons
import Theorems.Thm_Formalism_REAL_word_action_mem_pfil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution (j : ℕ) : pfil ε E u (j + 1) ≤
    pfil ε E u j ⊔ ⨆ p : Fin n × Fin n, (pfil ε E u j).map (E p.1 p.2) := by
  apply Submodule.span_le.mpr
  rintro z ⟨w, hw, hnc, y, hy, rfl⟩
  rw [SetLike.mem_coe]
  cases w with
  | nil => exact Submodule.mem_sup_left (word_action_mem_pfil ε E u j [] (Nat.zero_le _) hnc y hy)
  | cons p w =>
    have hlen : w.length ≤ j := by
      have h' := hw
      simp only [List.length_cons] at h'
      omega
    have hmem : ew E w y ∈ pfil ε E u j :=
      word_action_mem_pfil ε E u j w hlen (fun q hq => hnc q (List.mem_cons.mpr (Or.inr hq))) y hy
    rw [ew_cons]
    apply Submodule.mem_sup_right
    apply Submodule.mem_iSup_of_mem p
    exact Submodule.mem_map_of_mem hmem
end Formalism.REAL
