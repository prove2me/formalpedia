-- Prove2me | solution 1 for EnvyFreeCake104.Divide.splitCell_preserves_records__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T01:51:50.692133+00:00
-- url     : https://prove2.me/submissions/1db129ac-9d6f-47b6-8752-cadc110d85b9

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
import Theorems.Thm_EnvyFreeCake104_Divide_split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) :
    ∀ (t : Rec ι), t.Valid V N →
      ∀ (c y : ℝ), c ∈ t.pts → c < y → y < t.nextPt c →
      ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((splitCell N c y).run t) tr₀ = some (((), t'), tr) ∧
        t'.Valid V N ∧ t'.pts = insert y t.pts := by
  intro t ht c y hc hcy hyn o tr₀
  obtain ⟨tr, hrun⟩ := EnvyFreeCake104.Divide.splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
    V N t c y o tr₀
  refine ⟨_, tr, hrun, ?_, rfl⟩
  exact EnvyFreeCake104.Divide.split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
    V N t ht c y hc hcy hyn
