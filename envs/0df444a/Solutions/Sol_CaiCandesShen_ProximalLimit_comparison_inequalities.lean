-- Prove2me | solution 1 for CaiCandesShen.ProximalLimit.comparison_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:40:03.059371+00:00
-- url     : https://prove2.me/submissions/437b3c83-50bb-442a-b9fe-436fb3e51c58

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems

namespace CaiCandesShen.ProximalLimit

theorem aux_cci_main {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (τ : ℝ) (hτ : 0 < τ) (Xτ : Mat n₁ n₂) (hXτ : IsProximalSolution f τ Xτ) :
    nuclearNorm Xτ + 1 / (2 * τ) * frobNorm Xτ ^ 2 ≤
        nuclearNorm Xinf + 1 / (2 * τ) * frobNorm Xinf ^ 2 ∧
      nuclearNorm Xinf ≤ nuclearNorm Xτ := by
  refine ⟨?_, hXinf.1.2 Xτ hXτ.1⟩
  have h := hXτ.2 Xinf hXinf.1.1
  unfold fτ at h
  have e1 : nuclearNorm Xτ + 1 / (2 * τ) * frobNorm Xτ ^ 2
      = (τ * nuclearNorm Xτ + 1 / 2 * frobNorm Xτ ^ 2) / τ := by
    field_simp
  have e2 : nuclearNorm Xinf + 1 / (2 * τ) * frobNorm Xinf ^ 2
      = (τ * nuclearNorm Xinf + 1 / 2 * frobNorm Xinf ^ 2) / τ := by
    field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right h hτ.le

end CaiCandesShen.ProximalLimit

open Filter Topology
open CaiCandesShen.ProximalLimit

theorem solution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (τ : ℝ) (hτ : 0 < τ) (Xτ : Mat n₁ n₂) (hXτ : IsProximalSolution f τ Xτ) :
    nuclearNorm Xτ + 1 / (2 * τ) * frobNorm Xτ ^ 2 ≤
        nuclearNorm Xinf + 1 / (2 * τ) * frobNorm Xinf ^ 2 ∧
      nuclearNorm Xinf ≤ nuclearNorm Xτ :=
  aux_cci_main f Xinf hXinf τ hτ Xτ hXτ
