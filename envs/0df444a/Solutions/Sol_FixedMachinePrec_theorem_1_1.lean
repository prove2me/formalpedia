-- Prove2me | solution 1 for FixedMachinePrec.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:07:37.058293+00:00
-- url     : https://prove2.me/submissions/76e27cb3-1e76-4ff8-8802-d6621632b13d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_FixedMachinePrec_theorem_5_12
import Theorems.Thm_FixedMachinePrec_theorem_6_4
import Theorems.Thm_FixedMachinePrec_proposition_6_5

open FixedMachinePrec

theorem solution :
    ∃ (Popt Pdl : List RAMInstr) (Mopt Mdl : Turing.TM2ComputableAux Bool Bool) (c : ℕ),
      ∀ m : ℕ, 3 ≤ m → ∀ G : Instance, G.Acyclic → G.arcs.Nodup → 2 ≤ G.n →
        (∀ W : ℕ, c * m ^ 2 * (Nat.log2 (m * G.n) + 1) ≤ W →
          ∃ (out : List Bool) (t : ℕ), RAMOutputs W Popt (encInput m G) out t ∧
            IsOptimumOutput m G out ∧
            t ≤ c * (encInput m G).length +
              m ^ (c * m ^ 2) * G.n ^ (6 * m ^ 2 + 13 * m + 1) * Nat.log2 G.n ∧
            t ≤ c * (encInput m G).length + m ^ (c * m ^ 2) * G.n ^ (11 * m ^ 2)) ∧
        (∀ T W : ℕ, c * m ^ 2 * (Nat.log2 (m * G.n) + 1) ≤ W →
          ∃ (out : List Bool) (t : ℕ), RAMOutputs W Pdl (encDeadlineInput m G T) out t ∧
            IsDeadlineOutput m G T out ∧
            t ≤ c * (encDeadlineInput m G T).length +
              m ^ (c * m ^ 2) * G.n ^ (6 * m ^ 2 + 13 * m + 1)) ∧
        (∃ (out : List Bool) (t : ℕ), HMBinPacking.OutputsWithin Mopt (encInput m G) out t ∧
            IsOptimumOutput m G out ∧
            t ≤ c * (encInput m G).length +
              m ^ (c * m ^ 2) * G.n ^ (12 * m ^ 2 + 26 * m + 2) * Nat.log2 G.n ^ 3) ∧
        (∀ T : ℕ, ∃ (out : List Bool) (t : ℕ), HMBinPacking.OutputsWithin Mdl (encDeadlineInput m G T) out t ∧
            IsDeadlineOutput m G T out ∧
            t ≤ c * (encDeadlineInput m G T).length +
              m ^ (c * m ^ 2) * G.n ^ (12 * m ^ 2 + 26 * m + 2) * Nat.log2 G.n ^ 2) := by
  obtain ⟨Pdl, Popt, a, ram⟩ := theorem_6_4
  obtain ⟨Mopt, Mdl, b, tm⟩ := proposition_6_5
  let c := max a b
  have ha : a ≤ c := le_max_left _ _
  have hb : b ≤ c := le_max_right _ _
  refine ⟨Popt, Pdl, Mopt, Mdl, c, ?_⟩
  intro m hm G hG harcs _hn
  obtain ⟨hdeadline, ρ, hreal, hopt, _⟩ := theorem_5_12 m hm G hG
  have optOK : IsOptimumOutput m G (encSchedule (optimum G m).2) :=
    ⟨_, rfl, ρ, hreal, hopt⟩
  have dlOK (T : ℕ) : IsDeadlineOutput m G T (encDeadlineResult (deadline G m T)) := by
    cases h : deadline G m T with
    | none => exact Or.inl ⟨rfl, (hdeadline T).1.mp h⟩
    | some σ => exact Or.inr ⟨σ, rfl, (hdeadline T).2 σ h⟩
  have word (W : ℕ) (hw : c * m ^ 2 * (Nat.log2 (m * G.n) + 1) ≤ W) :
      a * m ^ 2 * (Nat.log2 (m * G.n) + 1) ≤ W :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ha)) hw
  obtain ⟨tmOpt, tmDl⟩ := tm m hm G hG harcs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hw
    obtain ⟨t, run, h₁, h₂⟩ := (ram m hm G hG harcs W (word W hw)).2
    refine ⟨_, t, run, optOK, h₁.trans ?_, h₂.trans ?_⟩ <;> gcongr <;> omega
  · intro T W hw
    obtain ⟨t, run, ht⟩ := (ram m hm G hG harcs W (word W hw)).1 T
    refine ⟨_, t, run, dlOK T, ht.trans ?_⟩ <;> gcongr <;> omega
  · obtain ⟨t, run, ht⟩ := tmOpt
    refine ⟨_, t, run, optOK, ht.trans ?_⟩ <;> gcongr <;> omega
  · intro T
    obtain ⟨t, run, ht⟩ := tmDl T
    refine ⟨_, t, run, dlOK T, ht.trans ?_⟩ <;> gcongr <;> omega
