-- Prove2me | solution 1 for CaiCandesShen.ProximalLimit.frobNorm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:40:27.773923+00:00
-- url     : https://prove2.me/submissions/ef8b26d4-9978-4d68-95db-c5d78e56a412

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems

namespace CaiCandesShen.ProximalLimit

end CaiCandesShen.ProximalLimit

open Filter Topology
open CaiCandesShen.ProximalLimit

theorem solution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    ∀ τ, 0 < τ → frobNorm (Xτ τ) ^ 2 ≤ frobNorm Xinf ^ 2 := by
  intro τ hτ
  obtain ⟨hfeas, hmin⟩ := hXτ τ hτ
  have h1 : fτ τ (Xτ τ) ≤ fτ τ Xinf := hmin Xinf hXinf.1.1
  have h2 : nuclearNorm Xinf ≤ nuclearNorm (Xτ τ) := hXinf.1.2 (Xτ τ) hfeas
  have h3 : τ * nuclearNorm Xinf ≤ τ * nuclearNorm (Xτ τ) :=
    mul_le_mul_of_nonneg_left h2 hτ.le
  unfold fτ at h1
  linarith
