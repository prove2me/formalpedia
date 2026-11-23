-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.tail_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:57.274386+00:00
-- url     : https://prove2.me/submissions/f1cf02ff-d1ac-483c-a2a9-168ceacb8e3e

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Theorems.Thm_Formalism_FG_InvIntVAux_low_one
import Theorems.Thm_Formalism_FG_InvIntVAux_eq_single_of_degree_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
namespace Formalism.FG.InvIntVAux
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → MvPowerSeries ι K)
    (hf : IsIdMod2 f) (j : ι) : Low 2 (f j - MvPowerSeries.X j) := by
  intro d hd
  obtain h0 | h1 : d.degree = 0 ∨ d.degree = 1 := by omega
  · have hL : Low 1 (f j - MvPowerSeries.X j) := low_one (by simp [hf.1 j])
    exact hL d (by omega)
  · obtain ⟨i, rfl⟩ := eq_single_of_degree_eq_one d h1
    rw [map_sub, hf.2 j i, MvPowerSeries.coeff_X]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : Finsupp.single i 1 ≠ Finsupp.single j 1 := by
        intro heq
        exact hij (Finsupp.single_left_injective one_ne_zero heq)
      rw [if_neg hij, if_neg hne, sub_zero]
end Formalism.FG.InvIntVAux
