-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.idxE_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T04:51:04.904407+00:00
-- url     : https://prove2.me/submissions/35bf9e49-784a-4134-a778-d95971705783

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge

theorem solution : Function.Injective (fun q : Fin 4 × Fin 4 => idxE q.1 q.2) := by
  intro ⟨μ, a⟩ ⟨ν, b⟩ h
  have hval : (4 + 4 * μ.val + a.val : Nat) = 4 + 4 * ν.val + b.val := by
    have := congrArg Fin.val h
    simpa [idxE] using this
  have hμ : μ.val = ν.val := by omega
  have ha : a.val = b.val := by omega
  apply Prod.ext
  · exact Fin.ext hμ
  · exact Fin.ext ha
