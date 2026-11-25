-- Prove2me | solution 1 for DetDLP.w1d_fp_exponent_readback
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T02:03:20.713423+00:00
-- url     : https://prove2.me/submissions/c88a4ceb-51d2-482e-afba-05625cfeea0b

import Definitions.Def_DetDLP_W3_DriverReadback
import Theorems.Thm_DetDLP_w3_native_seed_coverage
import Theorems.Thm_DetDLP_w3_driver_trace_certificate

set_option autoImplicit false
open DetDLP

/-- Converts an actual exponent and its machine postcondition into both Stage II certificates.
The native blocks are existential certificate data, not inputs to the machine. -/
theorem solution (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ) (gen : orderOf h = p-1)
    (accepts : ℕ → Prop) (u : ℕ) (hu : u < p-1) (powEq : h^u = a) (ok : accepts u) :
    w3_scanOutput (p-1) (Additive.ofMul h) (Additive.ofMul a) accepts ∧
    (∀ hg : w3_large p (p-1), letI : NeZero (p-1) := ⟨by have := hg.2.1; omega⟩
      ∀ F : Fin (blockCount (bitLen p)) → List (ZMod p)ˣ,
        ∃ (seed : FpSeed p (blockCount (bitLen p))) (B : Fin (blockCount (bitLen p)) → List (ZMod p)ˣ),
          (∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (hashThreshold p (p-1) (blockCount (bitLen p)) (p-1)) seed i) ∧
          w3_traceOutput (w3_fpFB F) (w3_fpFB B) (p-1) (Additive.ofMul h) (Additive.ofMul a) accepts) := by
  have he : u • Additive.ofMul h = Additive.ofMul a := congrArg Additive.ofMul powEq
  have ho : addOrderOf (Additive.ofMul h) = p-1 := gen
  refine ⟨w3_scanOutput_of_exponent ho hu he ok, ?_⟩
  intro hg
  letI : NeZero (p-1) := ⟨by have := hg.2.1; omega⟩
  intro F
  obtain ⟨seed, B, hB, cover⟩ := w3_native_seed_coverage.1 p hg
  refine ⟨seed, B, hB, ?_⟩
  have hc : Nat.card (Additive (ZMod p)ˣ) = p-1 := by
    change Nat.card (ZMod p)ˣ = p-1
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)]
  apply (w3_driver_trace_certificate (le_max_left 2 _) (by have := hg.2.1; omega) hc
    (Additive.ofMul h) (Additive.ofMul a) ho (w3_fpFB F) (w3_fpFB B) cover accepts).2
  exact ⟨u, hu, he, ok⟩
