-- Prove2me | solution 1 for CohnElkies.saddleLogRadius_covers_Ici
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/c31d179a-3dfe-49d5-a1a2-5e6e9acfdaa3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleLogRadius_continuousOn_Ici

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {d : ℕ} (hd : 0 < d)
    {u₀ : ℝ} (hu₀ : -1 < u₀)
    (htop : Tendsto (saddleLogRadius ε d) atTop atTop)
    {r : ℝ}
    (hr : Real.exp (saddleLogRadius ε d u₀) ≤ r) :
    ∃ u : ℝ, u₀ ≤ u ∧
      saddleLogRadius ε d u = Real.log r := by
  have hrpositive : 0 < r :=
    (Real.exp_pos _).trans_le hr
  have hlog :
      saddleLogRadius ε d u₀ ≤ Real.log r := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hrpositive]
    exact hr
  have hfilter :
      (atTop : Filter ℝ) ≤ 𝓟 (Ici u₀) :=
    Filter.le_principal_iff.mpr
      (eventually_ge_atTop u₀)
  have himage :
      Ici (saddleLogRadius ε d u₀) ⊆
        saddleLogRadius ε d '' Ici u₀ :=
    (isPreconnected_Ici : IsPreconnected (Ici u₀)).intermediate_value_Ici
      (show u₀ ∈ Ici u₀ from Set.mem_Ici.mpr (le_refl u₀))
      hfilter
      (saddleLogRadius_continuousOn_Ici
        hε horder hd hu₀)
      htop
  obtain ⟨u, hu, heq⟩ := himage hlog
  exact ⟨u, hu, heq⟩
end CohnElkies
