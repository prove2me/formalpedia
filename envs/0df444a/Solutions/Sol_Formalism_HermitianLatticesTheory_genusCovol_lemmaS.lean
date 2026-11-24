-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_lemmaS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:45.845573+00:00
-- url     : https://prove2.me/submissions/28b01199-45ee-4785-a20b-95ad336df7e0

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_locS_mono
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_le_of_loc
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_claimB
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_ri_peel
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_loc_eq_of_le_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : ∀ (n : ℕ) (X Y X' Y' : Submodule R W), X ≤ Y → X' ≤ Y' →
    X.toAddSubgroup.relIndex Y.toAddSubgroup = n → n ≠ 0 →
    X'.toAddSubgroup.relIndex Y'.toAddSubgroup ≠ 0 →
    (∀ (P : Ideal R) [P.IsMaximal], ∃ f : W →+ W, Function.Injective f ∧
      (locS P.primeCompl X).toAddSubgroup.map f = (locS P.primeCompl X').toAddSubgroup ∧
      (locS P.primeCompl Y).toAddSubgroup.map f = (locS P.primeCompl Y').toAddSubgroup) →
    X'.toAddSubgroup.relIndex Y'.toAddSubgroup = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y X' Y' hXY hXY' hn hn0 hfin' hloc
  have hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := hn ▸ hn0
  by_cases hall : ∀ (P : Ideal R) [P.IsMaximal], Y ≤ locS P.primeCompl X
  · have h1 : Y ≤ X := genusCovol_le_of_loc hall
    have h1' : Y' ≤ X' := by
      apply genusCovol_le_of_loc
      intro P _
      obtain ⟨f, _, hfX, hfY⟩ := hloc P
      have hYX : locS P.primeCompl Y ≤ locS P.primeCompl X :=
        (genusCovol_locS_mono _ (hall P)).trans (genusCovol_locS_idem _ X)
      have : (locS P.primeCompl Y').toAddSubgroup ≤ (locS P.primeCompl X').toAddSubgroup := by
        rw [← hfX, ← hfY]
        exact AddSubgroup.map_mono ((Submodule.toAddSubgroup_le _ _).mpr hYX)
      exact (genusCovol_le_locS _ Y').trans ((Submodule.toAddSubgroup_le _ _).mp this)
    rw [← hn, AddSubgroup.relIndex_eq_one.mpr ((Submodule.toAddSubgroup_le _ _).mpr h1),
      AddSubgroup.relIndex_eq_one.mpr ((Submodule.toAddSubgroup_le _ _).mpr h1')]
  · push Not at hall
    obtain ⟨P, hP, hY⟩ := hall
    obtain ⟨f, hfi, hfX, hfY⟩ := hloc P
    set Z := Y ⊓ locS P.primeCompl X with hZ
    set Z' := Y' ⊓ locS P.primeCompl X' with hZ'
    have hXZ : X ≤ Z := le_inf hXY (genusCovol_le_locS _ X)
    have hXZ' : X' ≤ Z' := le_inf hXY' (genusCovol_le_locS _ X')
    have hm := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXZ)
      ((Submodule.toAddSubgroup_le _ _).mpr (inf_le_left : Z ≤ Y))
    have hm' := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXZ')
      ((Submodule.toAddSubgroup_le _ _).mpr (inf_le_left : Z' ≤ Y'))
    have hp := genusCovol_ri_peel P.primeCompl hXY hfin
    have hp' := genusCovol_ri_peel P.primeCompl hXY' hfin'
    rw [← hfX, ← hfY, AddSubgroup.relIndex_map_map_of_injective _ _ hfi] at hp'
    have hne1 : Z.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 1 := by
      intro h
      exact hY (((Submodule.toAddSubgroup_le _ _).mp (AddSubgroup.relIndex_eq_one.mp h)).trans
        inf_le_right)
    have hlt : X.toAddSubgroup.relIndex Z.toAddSubgroup < n := by
      rw [← hn, ← hm]
      have h0 : X.toAddSubgroup.relIndex Z.toAddSubgroup ≠ 0 := by
        intro h; rw [← hm, h, zero_mul] at hfin; exact hfin rfl
      have h2 : Z.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := by
        intro h; rw [← hm, h, mul_zero] at hfin; exact hfin rfl
      have : 2 ≤ Z.toAddSubgroup.relIndex Y.toAddSubgroup := by omega
      have h4 := Nat.pos_of_ne_zero h0
      nlinarith
    have hfinZ' : X'.toAddSubgroup.relIndex Z'.toAddSubgroup ≠ 0 := by
      intro h; rw [← hm', h, zero_mul] at hfin'; exact hfin' rfl
    have hIH := ih _ hlt X Z X' Z' hXZ hXZ' rfl
      (by intro h; rw [← hm, h, zero_mul] at hfin; exact hfin rfl) hfinZ' (by
        intro Q _
        by_cases hQ : Q = P
        · subst hQ
          refine ⟨f, hfi, hfX, ?_⟩
          rw [genusCovol_loc_eq_of_le_of_le _ hXZ inf_le_right,
            genusCovol_loc_eq_of_le_of_le _ hXZ' inf_le_right, hfX]
        · obtain ⟨g, hgi, hgX, hgY⟩ := hloc Q
          have hPQ : ¬ P ≤ Q := fun h =>
            hQ ((Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsMaximal.ne_top inferInstance) h).symm)
          obtain ⟨a, haP, haQ⟩ := Set.not_subset.mp hPQ
          have e1 : locS Q.primeCompl Z = locS Q.primeCompl Y :=
            le_antisymm (genusCovol_locS_mono _ inf_le_left) (genusCovol_claimB P Q haP haQ hfin)
          have e2 : locS Q.primeCompl Z' = locS Q.primeCompl Y' :=
            le_antisymm (genusCovol_locS_mono _ inf_le_left) (genusCovol_claimB P Q haP haQ hfin')
          exact ⟨g, hgi, hgX, by rw [e1, e2, hgY]⟩)
    rw [← hm', hIH, hp', ← hp, hm, hn]
end Formalism.HermitianLatticesTheory
