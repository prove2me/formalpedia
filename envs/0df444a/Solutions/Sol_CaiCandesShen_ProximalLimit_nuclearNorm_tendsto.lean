-- Prove2me | solution 1 for CaiCandesShen.ProximalLimit.nuclearNorm_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:13:58.496816+00:00
-- url     : https://prove2.me/submissions/ecdbc028-4f93-4986-bb9b-b3b50aeda714

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

theorem aux_nnt_upper (N0 N1 a b τ : ℝ) (hτ : 0 < τ)
    (h : τ * N1 + 1 / 2 * a ^ 2 ≤ τ * N0 + 1 / 2 * b ^ 2) :
    N1 ≤ N0 + b ^ 2 / (2 * τ) := by
  rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg a]

end CaiCandesShen.ProximalLimit

open CaiCandesShen.ProximalLimit

theorem solution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    Tendsto (fun τ => nuclearNorm (Xτ τ)) atTop (𝓝 (nuclearNorm Xinf)) := by
  obtain ⟨⟨hfeas, hmin⟩, _⟩ := hXinf
  have hlow : ∀ᶠ τ in atTop, nuclearNorm Xinf ≤ nuclearNorm (Xτ τ) := by
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    exact hmin _ (hXτ τ hτ).1
  have hup : ∀ᶠ τ in atTop,
      nuclearNorm (Xτ τ) ≤ nuclearNorm Xinf + frobNorm Xinf ^ 2 / (2 * τ) := by
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    have h := (hXτ τ hτ).2 Xinf hfeas
    unfold fτ at h
    exact aux_nnt_upper _ _ _ _ τ hτ h
  have hlim : Tendsto (fun τ : ℝ => nuclearNorm Xinf + frobNorm Xinf ^ 2 / (2 * τ)) atTop
      (𝓝 (nuclearNorm Xinf)) := by
    have h2 : Tendsto (fun τ : ℝ => frobNorm Xinf ^ 2 / (2 * τ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop two_pos)
    simpa using (tendsto_const_nhds (x := nuclearNorm Xinf)).add h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hlow hup
