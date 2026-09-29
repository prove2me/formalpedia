-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.idxDE_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T04:51:05.674511+00:00
-- url     : https://prove2.me/submissions/b3d2c877-2af0-46ed-b738-975239ba2336

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge

theorem solution :
    Function.Injective (fun q : Fin 4 × Fin 4 × Fin 4 => idxDE q.1 q.2.1 q.2.2) := by
  intro ⟨μ, ν, a⟩ ⟨μ', ν', a'⟩ h
  have hval : (20 + 16 * μ.val + 4 * ν.val + a.val : Nat) =
      20 + 16 * μ'.val + 4 * ν'.val + a'.val := by
    have := congrArg Fin.val h
    simpa [idxDE] using this
  have hμ : μ.val = μ'.val := by omega
  have hν : ν.val = ν'.val := by omega
  have ha : a.val = a'.val := by omega
  apply Prod.ext
  · exact Fin.ext hμ
  · apply Prod.ext
    · exact Fin.ext hν
    · exact Fin.ext ha
