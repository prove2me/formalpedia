-- Prove2me | solution 1 for Freiman.middleRepair_cert_record_from_proof
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:52:51.380127+00:00
-- url     : https://prove2.me/submissions/f023d4bb-94ca-4755-83e0-f074e449f809

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem solution :
    (∀ (C : MiddleCertCatalog) (p : MiddleCertProof), middleCertWitnessesValid C → middleCertProofValid C p → middleCertProofSound C p) → ∀ (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect) (rec : MiddleCertRecord) (parent : ℤ), middleCertWitnessesValid C → middleRepairRecordValid C redirects rec parent → ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s → ¬ middleCertHolds (middleRepairCertConditions C rec parent) r s q := by
  intro hs C redirects rec parent hw hv r s q hr hh
  apply hs C (middleRepairEffectiveProof C redirects rec parent) hw hv.1 r s q hr
  intro p hp
  exact ⟨hh _ (hv.2 p hp).1, hh _ (hv.2 p hp).2⟩

#print axioms solution
