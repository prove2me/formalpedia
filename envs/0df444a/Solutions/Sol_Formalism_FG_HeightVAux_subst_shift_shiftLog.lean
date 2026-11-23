-- Prove2me | solution 1 for Formalism.FG.HeightVAux.subst_shift_shiftLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:56.090156+00:00
-- url     : https://prove2.me/submissions/89fcf547-f00e-4c74-bd4f-6c8e74c03729

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
import Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog_single
import Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.HeightVAux
open MvPowerSeries Formalism.G Formalism.LT
variable {K : Type*} [Field K] {l m : ℕ} [NeZero m]
namespace Formalism.FG.HeightVAux
theorem _root_.solution (hl : 2 ≤ l) (j : ZMod m) :
    subst (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) K)) (shiftLog K l m j) =
      shiftLog K l m (j - 1) := by
  classical
  set e : ZMod m ↪ ZMod m := (Equiv.subRight (1 : ZMod m)).toEmbedding with he
  have hs : ∀ a : ZMod m, e a = a - 1 := fun a => by simp [he]
  have hX : (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) K)) = X ∘ ⇑e := by
    funext k; simp [hs]
  rw [hX, ← rename_eq_subst]
  ext n
  obtain ⟨x, rfl⟩ : ∃ x, Finsupp.embDomain e x = n :=
    ⟨n.comapDomain e e.injective.injOn, Finsupp.embDomain_comapDomain (by
      intro a _; exact ⟨a + 1, by simp [hs]⟩)⟩
  rw [coeff_embDomain_rename]
  by_cases hA : ∃ t : ℕ, x = Finsupp.single (j - (t : ZMod m)) ((l ^ 2) ^ t)
  · obtain ⟨t, rfl⟩ := hA
    rw [Finsupp.embDomain_single, hs, ShiftFEAux.coeff_shiftLog_single hl]
    have : j - (t : ZMod m) - 1 = j - 1 - (t : ZMod m) := by ring
    rw [this, ShiftFEAux.coeff_shiftLog_single hl]
  · push Not at hA
    rw [ShiftFEAux.coeff_shiftLog_zero j x hA, ShiftFEAux.coeff_shiftLog_zero]
    intro t ht
    apply hA t
    have : Finsupp.single (j - 1 - (t : ZMod m)) ((l ^ 2) ^ t) =
        Finsupp.embDomain e (Finsupp.single (j - (t : ZMod m)) ((l ^ 2) ^ t)) := by
      rw [Finsupp.embDomain_single, hs]; congr 1; ring
    rw [this] at ht
    exact Finsupp.embDomain_inj.mp ht
end Formalism.FG.HeightVAux
