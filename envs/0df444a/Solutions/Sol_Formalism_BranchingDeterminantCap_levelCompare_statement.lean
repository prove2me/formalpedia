-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.levelCompare_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:37.339661+00:00
-- url     : https://prove2.me/submissions/43223a5f-b0c3-456a-8dfb-b091ff16dd32

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_nPl_pos
import Theorems.Thm_Formalism_BranchingDeterminantCap_scale_sandwich_bound
import Theorems.Thm_Formalism_HN_twist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : LevelCompare := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX R R' h hR hR'0 hh hle hhR
  have hR0 : R ≠ ⊥ := fun e => hR'0 (le_bot_iff.mp (e ▸ hle))
  have hR'fg : R'.FG := by
    have : IsNoetherian (𝓞 K) R := isNoetherian_of_fg_of_noetherian R hR
    exact (isNoetherian_submodule.1 this) R' hle
  obtain ⟨-, h1, h2, h3, h4⟩ := scale_sandwich_bound K V ι b X hX R R' h hR hR0 hh hle hhR
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh'
  have htw := twist K V ι b X (fun _ => Real.sqrt h) hX (fun _ => hs) R' hR'fg
  obtain ⟨e1, e2, -⟩ := htw.2.2.1 hR'0
  have hf : (0 : ℝ) < nPl K := by exact_mod_cast ms_nPl_pos
  have ht : 2 * ((1 / (nPl K : ℝ)) * ∑ _v : InfinitePlace K, Real.log (Real.sqrt h)) =
      Real.log h := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_sqrt hh'.le]
    unfold nPl at hf ⊢
    field_simp
  have e1' : muDef b (scaleFrame (Real.sqrt h) X) R' = muDef b X R' + Real.log h := by
    rw [← ht]; exact e1
  have e2' : muMaxDef b (scaleFrame (Real.sqrt h) X) R' = muMaxDef b X R' + Real.log h := by
    rw [← ht]; exact e2
  rw [e1', e2']
  constructor <;> rw [abs_le] <;> constructor <;> linarith
end Formalism.BranchingDeterminantCap
