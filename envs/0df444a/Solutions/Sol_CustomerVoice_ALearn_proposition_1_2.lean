-- Prove2me | solution 2 for CustomerVoice.ALearn.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:04:22.587025+00:00
-- url     : https://prove2.me/submissions/66dcb793-e4c7-431f-933f-0c658bc1135c

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting
import Theorems.Thm_CustomerVoice_ALearn_ich_iff_threshold
import Theorems.Thm_CustomerVoice_ALearn_icl_iff_threshold
import Theorems.Thm_CustomerVoice_ALearn_optimal_design

-- carved verbatim out of submission 177c8c84-6227-40b9-9115-df7ee9f76b23, lines 173-182

section
open CustomerVoice.ALearn

theorem CustomerResearch.equilibrium_iff_ic (M : Model) (hM : M.Standing) :
    M.InformativeEq ↔ M.ICH ∧ M.ICL := by
  have hopt := CustomerVoice.ALearn.optimal_design M hM
  constructor
  · rintro ⟨m,bel,d,hinj,hbel,hsel,hbuy⟩
    have hd (x : Msg) : d x = M.qOpt (M.θ (bel x)) :=
      (hopt (bel x)).2 (d x) (hsel x).1 (hsel x).2
    constructor
    · have h := hbuy BType.H (m BType.L)
      simpa only [hd, hbel, Model.θ, Model.u, Model.ICH] using h
    · have h := hbuy BType.L (m BType.H)
      simpa only [hd, hbel, Model.θ, Model.u, Model.ICL] using h
  · rintro ⟨hH,hL⟩
    let m : BType → Msg | .H => .mH | .L => .mL
    let bel : Msg → BType | .mH => .H | .mL => .L
    refine ⟨m,bel,fun x => M.qOpt (M.θ (bel x)), ?_⟩
    refine ⟨by decide, ?_, ?_, ?_⟩
    · intro t; cases t <;> rfl
    · intro x; exact (hopt (bel x)).1
    · intro t x
      cases t <;> cases x <;>
        simp_all [m,bel,Model.θ,Model.ICH,Model.ICL,Model.u]

theorem solution (M : Model) (hM : M.Standing) :
    M.InformativeEq ↔ M.θH / M.θL ≥ M.Delta := by
  rw [CustomerResearch.equilibrium_iff_ic M hM,
    CustomerVoice.ALearn.ich_iff_threshold M hM, CustomerVoice.ALearn.icl_iff_threshold M hM]
  change (M.DeltaH ≤ M.θH/M.θL ∧ M.DeltaL ≤ M.θH/M.θL) ↔
    max M.DeltaH M.DeltaL ≤ M.θH/M.θL
  exact max_le_iff.symm

end
