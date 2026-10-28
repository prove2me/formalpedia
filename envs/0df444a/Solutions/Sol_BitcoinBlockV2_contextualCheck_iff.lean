-- Prove2me | solution 1 for BitcoinBlockV2.contextualCheck_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:13:07.228579+00:00
-- url     : https://prove2.me/submissions/ce8ccc87-7172-40b6-b640-24bf9f14b1b8

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

open BitcoinBlockV2 in
theorem solution (S : ChainState) (b : BitcoinSer.Block)
    (hne : b.vtx ≠ []) (hvin : ∀ tx ∈ b.vtx, tx.vin ≠ []) :
    BitcoinBlockV2.contextualCheckBlock S b = true ↔ BitcoinBlockV2.ContextSpec S b := by
  unfold contextualCheckBlock ContextSpec
  cases hv : b.vtx with
  | nil => exact absurd hv hne
  | cons t0 rest =>
    have h0 : t0.vin ≠ [] := hvin t0 (by simp [hv])
    cases hi : t0.vin with
    | nil => exact absurd hi h0
    | cons i0 is =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        List.headD_cons, hi, List.take_succ_cons, List.take_zero, List.mem_singleton, forall_eq,
        List.all_eq_true]
      constructor
      · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
        refine ⟨a, ?_, c, d⟩
        intro hh
        rcases b with b | b
        · rw [hh] at b; cases b
        · exact b
      · rintro ⟨a, b, c, d⟩
        refine ⟨⟨⟨a, ?_⟩, c⟩, d⟩
        cases hh : BitcoinActivation.activeAfter S.tipHeight .heightInCB
        · exact Or.inl rfl
        · exact Or.inr (b hh)
