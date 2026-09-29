-- Prove2me | solution 1 for Freiman.middleRepair_cert_uniform_family
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:53:12.874529+00:00
-- url     : https://prove2.me/submissions/324f08f1-1c5d-4454-8d8c-4c3dd5cd199f

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c → middleRatio c < (19/5:ℝ) → ∃ f : Fin 11, 9≤f.val ∧ middleRepairCertDomain c f.val := by
  intro c hc hr
  by_cases hp : (middleNormalized c).left.length % 2 = (middleNormalized c).right.length % 2
  · refine ⟨⟨9, by decide⟩, by decide, hc, ?_⟩
    simpa [middleCertParity, hp] using hr
  · refine ⟨⟨10, by decide⟩, by decide, hc, ?_⟩
    simpa [middleCertParity, hp] using hr

#print axioms solution
