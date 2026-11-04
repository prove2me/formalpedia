-- Prove2me | solution 1 for FiniteEnergyPlane.hasZeroIndex_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T11:59:31.158341+00:00
-- url     : https://prove2.me/submissions/52fe681b-2598-4629-8fd0-8850a981c4b4

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique

open Metric

namespace FiniteEnergyPlane

theorem hasZeroIndex_unique_aux {f : ℂ → ℂ} {z₀ : ℂ} {k m : ℤ} (hk : HasZeroIndex f z₀ k)
    (hm : HasZeroIndex f z₀ m) : k = m := by
  obtain ⟨-, r, hr, -, hkw⟩ := hk
  obtain ⟨-, r', hr', -, hmw⟩ := hm
  have hρ : min r r' / 2 ∈ Set.Ioo 0 r :=
    ⟨by positivity, by linarith [min_le_left r r', lt_min hr hr']⟩
  have hρ' : min r r' / 2 ∈ Set.Ioo 0 r' :=
    ⟨by positivity, by linarith [min_le_right r r', lt_min hr hr']⟩
  exact hasLoopWind_unique (hkw _ hρ) (hmw _ hρ')

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {f : ℂ → ℂ} {z₀ : ℂ} {k m : ℤ} (hk : HasZeroIndex f z₀ k)
    (hm : HasZeroIndex f z₀ m) : k = m :=
  hasZeroIndex_unique_aux hk hm
