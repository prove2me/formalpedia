-- Prove2me | solution 1 for Freiman.middleRepair_cert_family_from_records
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:54:14.914658+00:00
-- url     : https://prove2.me/submissions/7a83648c-ce36-47d9-9475-825f6c422949

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

private theorem complement_iff (b : CertBound) (r s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬certBoundHolds b r s q := by
  rcases b with ⟨lo, st, th⟩
  cases lo <;> cases st <;> simp [lowerHistoryComplement, certBoundHolds]

private theorem snd_branch (C : MiddleCertCatalog) (g : MiddleCertGoal)
    (h : (middleRepairCertGoalBranches C g).map Prod.snd =
      (middleCertGoalBranches C g).map Prod.snd) (j : ℕ) :
    (middleRepairCertBranch C g j).2 = (middleCertBranch C g j).2 := by
  have he := congrArg (fun xs => xs[j]?) h
  clear h
  simp only [List.getElem?_map] at he
  unfold middleRepairCertBranch middleCertBranch
  cases h1 : (middleRepairCertGoalBranches C g)[j]? <;>
    cases h2 : (middleCertGoalBranches C g)[j]? <;>
    simp_all only [Option.map_none, Option.map_some,
      Option.getD_none, Option.getD_some, Option.some.injEq]
  all_goals cases he

theorem solution :
    (∀ (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect) (rec : MiddleCertRecord) (parent : ℤ), middleCertWitnessesValid C → middleRepairRecordValid C redirects rec parent → ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s → ¬ middleCertHolds (middleRepairCertConditions C rec parent) r s q) → ∀ (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect) (f : ℕ), middleCertWitnessesValid C → middleCertFamilyValid C f → middleRepairBranchIdentity C → middleRepairLedgerValid C redirects → middleRepairCertFamilySound C f := by
  intro hs C redirects f hw hf hi hl i hit hif r s q hr _hq hp hh j hj hb
  have hil : i < C.goals.length := List.mem_range.mp hit
  have hgm : middleCertGoal C (i+1) ∈ C.goals := by
    simp only [middleCertGoal, Nat.add_sub_cancel, List.getElem?_eq_getElem hil,
      Option.getD_some]
    exact List.getElem_mem hil
  have hmap := hi.1 _ hgm
  have hlen : (middleRepairCertGoalBranches C (middleCertGoal C (i+1))).length =
      (middleCertGoalBranches C (middleCertGoal C (i+1))).length := by
    simpa only [List.length_map] using congrArg List.length hmap
  have hbranch := snd_branch C _ hmap j
  have hjold : j ∈ List.range (middleCertGoalBranches C (middleCertGoal C (i+1))).length := by
    simpa only [hlen] using hj
  have hcov := hf.2.2 i hit hif j hjold
  by_contra hn
  have fail_holds : middleCertHolds
      (match (middleRepairCertBranch C (middleCertGoal C (i+1)) j).2 with
       | .bound t => [lowerHistoryComplement t] | _ => []) r s q := by
    cases he : (middleRepairCertBranch C (middleCertGoal C (i+1)) j).2 with
    | automatic => simp [he, middleCertComparisonHolds] at hn
    | impossible => simp [middleCertHolds]
    | bound b =>
      simp only [he, middleCertComparisonHolds] at hn
      simpa only [middleCertHolds, List.mem_singleton, forall_eq] using
        (complement_iff b r s q).mpr hn
  have contradiction (p : ℤ)
      (hparent : middleCertHolds
        (if p < 0 then [] else
          (middleRepairCertParents (middleCertParity f))[p.toNat]?.getD []) r s q)
      (hrecord : middleCertRecorded C (i+1) j p) : False := by
    rcases hrecord with ⟨rec, hrec, hg, hbrec, hprec⟩
    apply hs C redirects rec p hw (hl.2 rec hrec p hprec) r s q hr
    unfold middleRepairCertConditions
    rw [hg, hbrec]
    intro b hm
    simp only [List.mem_append] at hm
    rcases hm with ((hm | hm) | hm) | hm
    · exact hh b hm
    · exact hb b hm
    · rw [hif] at hm
      exact hparent b hm
    · exact fail_holds b hm
  rcases hcov with hauto | hdirect | hparents
  · apply hn
    simp only [hbranch, hauto, middleCertComparisonHolds]
  · exact contradiction (-1) (by simp [middleCertHolds]) hdirect
  · obtain ⟨hf9, hparents⟩ := hparents
    simp only [middleRepairCertParentHolds, hf9, ↓reduceIte] at hp
    obtain ⟨bs, hbs, hholds⟩ := hp
    obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hbs
    have hkold : k ∈ List.range (C.parents (middleCertParity f)).length := by
      rw [List.mem_range, ← hi.2 (middleCertParity f)]
      exact hk
    apply contradiction (k : ℤ) _ (hparents k hkold)
    simpa only [Int.natCast_nonneg, not_lt.mpr (Int.natCast_nonneg k),
      ↓reduceIte, Int.toNat_natCast, List.getElem?_eq_getElem hk, Option.getD_some, heq] using hholds

#print axioms solution
