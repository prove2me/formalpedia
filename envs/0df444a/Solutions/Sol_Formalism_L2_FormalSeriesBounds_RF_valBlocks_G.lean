-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valBlocks_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:16.49783+00:00
-- url     : https://prove2.me/submissions/d3be791a-d974-4639-a47d-4524afd25f9d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_val_lists
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ)
variable {X n}
variable (X n)
variable {X n}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
    (hM : BlockMembership X n F FFimg Z ga) (hA : BlockAdmissible X F Z ga) : ValBlocks X F Z n ga ν := by
  intro L hatt hrows hwt
  set L' : Orb → List (GlobalTheory d × ℝ) := fun o => if o ∈ Z then L o else [] with hL'
  have hLZ : ∀ o ∈ Z, L' o = L o := fun o ho => by simp [hL', ho]
  have hLn : ∀ o, o ∉ Z → L' o = [] := fun o ho => by simp [hL', ho]
  have hwt' : ∀ o ∈ Z, ∀ g a k, ((L' o).map fun q => q.1.wt (X o) g a k).sum = ga o g a k := by
    intro o ho g a k
    rw [hLZ o ho]
    exact hwt o ho g a k
  have hOK : ∀ o, ∀ q ∈ L' o, q.1.AttainsOK (X o) (F o) q.2 := by
    intro o q hq
    by_cases ho : o ∈ Z
    · exact hA L' hwt' o ho q hq (hatt o ho q (by rwa [hLZ o ho] at hq))
    · rw [hLn o ho] at hq
      exact absurd hq (by simp)
  have hsum : ∀ f : Orb → List (GlobalTheory d × ℝ) → ℕ, (∀ o, f o [] = 0) → ∑ o, f o (L' o) = ∑ o ∈ Z, f o (L o) := by
    intro f hf
    rw [← Finset.sum_subset (Finset.subset_univ Z)]
    · exact Finset.sum_congr rfl fun o ho => by rw [hLZ o ho]
    · intro o _ ho
      rw [hLn o ho, hf]
  have hsumR : ∑ o, ((L' o).map Prod.snd).sum = ∑ o ∈ Z, ((L o).map Prod.snd).sum := by
    rw [← Finset.sum_subset (Finset.subset_univ Z)]
    · exact Finset.sum_congr rfl fun o ho => by rw [hLZ o ho]
    · intro o _ ho
      rw [hLn o ho]
      simp
  rw [← hsumR]
  refine val_lists hV hJ F L' hOK ?_ (hM L' hLn hwt')
  rw [hsum (fun o l => (l.map fun q => q.1.what₂ (X o).n).sum) (fun o => by simp)]
  exact hrows
end Formalism.L2.FormalSeriesBounds.RF
