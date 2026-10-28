-- Prove2me | solution 1 for CountingMatroid.Bridge.mainTheorem_of_explicit_machine_realization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:23:15.187609+00:00
-- url     : https://prove2.me/submissions/1bd6eb8a-91a2-4397-bc4a-b5714d2c14b7

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Definitions.Def_CountingMatroid_Bridge_MachineRealization
import Theorems.Thm_CountingMatroid_Bridge_finite_experiment_fpras_explicit
import Theorems.Thm_CountingMatroid_Bridge_finite_good_card_of_bad_bound
import Theorems.Thm_CountingMatroid_Bridge_clock_event_card

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations CountingMatroid.Model.Subroutines
open CountingMatroid.Bridge

/-- Completing the explicit machine implementation closes the original,
unmodified mission statement. Finite probability, signs, zero cases and
the exact target endpoint are discharged here rather than assumed. -/
theorem solution
    (implementation : ExplicitMachineRealization) : OAI.CommonBasesFPRAS.MainTheorem := by
  obtain ⟨k, s, P, C, d, hC, himpl⟩ := implementation
  obtain ⟨Cs, ds, _, hsource⟩ := finite_experiment_fpras_explicit
  refine ⟨k, s, P, C, d, hC, ?_⟩
  intro n r M₁ M₂ O ε δ hE₁ hE₂ hr₁ hr₂ hO hε hε1 hδ hδ1
  let p : InputParams := ⟨ε, δ, hε, hε1, hδ, hδ1⟩
  let K := (CountingMatroid.Program.schedule n p).val.repetitions * blockLength n r p
  let B := OAI.CommonBasesFPRAS.resourceBound C d n r ε δ
  let Z := OAI.CommonBasesFPRAS.commonBaseCount M₁ M₂
  let E := fun xs => (presampledOutcome Analysis.IntersectionSearch.intersectionSolver
    n r (O false) (O true) p xs).1
  let good := fun xs => OAI.CommonBasesFPRAS.relativeAccuracy ε Z (E xs)
  obtain ⟨positions, hrun⟩ := himpl n r M₁ M₂ O p hE₁ hE₂ hr₁ hr₂ hO
  obtain ⟨_, hbad, hsign⟩ := hsource n r M₁ M₂ O p hE₁ hE₂ hr₁ hr₂ hO
  have hg : (1-δ)*(2:ℚ)^K ≤ Nat.card {bits : Fin K → Bool // good (List.ofFn bits)} := by
    apply finite_good_card_of_bad_bound K δ hδ.le good
    simpa only [good, E, OAI.CommonBasesFPRAS.relativeAccuracy, not_and_or, not_le] using hbad
  have hKB : K ≤ B := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective positions positions.injective
  constructor
  · intro bits
    obtain ⟨hout, hc, hb⟩ := hrun bits
    refine ⟨?_, hc, hb, ?_⟩
    · rw [hout]; rfl
    · intro z hz
      have he : E (List.ofFn (fun i => bits (positions i).val)) = z := Option.some.inj (hout.symm.trans hz)
      obtain ⟨hnonneg, hzero, _, _⟩ := hsign (List.ofFn (fun i => bits (positions i).val)) (List.length_ofFn ..)
      exact he ▸ ⟨hnonneg, hzero⟩
  · have hout (bits : Fin B → Bool) :
        (OAI.CommonBasesFPRAS.execution P O
          (OAI.CommonBasesFPRAS.initialConfig k s n r ε δ)
          (OAI.CommonBasesFPRAS.finiteBits bits) B).output =
        some (E (List.ofFn (fun i => bits (positions i)))) := by
      have hsamp : (fun i : Fin K => OAI.CommonBasesFPRAS.finiteBits bits (positions i).val) =
          (fun i => bits (positions i)) := by
        funext i
        exact dif_pos (positions i).isLt
      exact (hrun (OAI.CommonBasesFPRAS.finiteBits bits)).1.trans
        (congrArg (fun f : Fin K → Bool => some (E (List.ofFn f))) hsamp)
    have hevent (bits : Fin B → Bool) :
        (∃ z, (OAI.CommonBasesFPRAS.execution P O
          (OAI.CommonBasesFPRAS.initialConfig k s n r ε δ)
          (OAI.CommonBasesFPRAS.finiteBits bits) B).output = some z ∧
          OAI.CommonBasesFPRAS.relativeAccuracy ε Z z) ↔
        good (List.ofFn (fun i => bits (positions i))) := by
      rw [hout]
      constructor
      · rintro ⟨z, hz, hzgood⟩
        rcases Option.some.inj hz with rfl
        exact hzgood
      · intro h
        exact ⟨_, rfl, h⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hevent), clock_event_card positions (fun bits => good (List.ofFn bits))]
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hpow : (2:ℚ)^B = (2:ℚ)^K * 2^(B-K) := by
      rw [← pow_add, Nat.add_sub_of_le hKB]
    rw [hpow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hg (by positivity)
