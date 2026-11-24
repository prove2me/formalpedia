-- Prove2me | solution 1 for Formalism.L2.Th1.D.UnramifiedCompletion.exists_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:24:34.558112+00:00
-- url     : https://prove2.me/submissions/5c6dbccd-c63d-467b-822b-8f910e97b1a3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_pow_pow_fix
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_castL_nonunit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.L2.Th1.D.UnramifiedCompletion
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
namespace Formalism.L2.Th1.D.UnramifiedCompletion
theorem _root_.solution {x : ℂ_[l]} (hx : x ∈ ringA l) :
    ∃ f : ℕ, 0 < f ∧
      (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ringA l)}) ⟨x, hx⟩) ^ (l ^ f)
        = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ringA l)}) ⟨x, hx⟩ := by
  have : CharP (ringA l ⧸ Ideal.span {((l : ℕ) : ringA l)}) l := CharP.quotient _ l castL_nonunit
  set mk := Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ringA l)}) with hmk
  have key : ∀ (a b : ringA l ⧸ Ideal.span {((l : ℕ) : ringA l)}) (f g : ℕ), a ^ (l ^ f) = a →
      b ^ (l ^ g) = b → a ^ (l ^ (f * g)) = a ∧ b ^ (l ^ (f * g)) = b := by
    intro a b f g ha hb
    constructor
    · rw [pow_mul]; exact pow_pow_fix a _ ha g
    · rw [mul_comm, pow_mul]; exact pow_pow_fix b _ hb f
  refine Subring.closure_induction
    (p := fun x hx => ∃ f : ℕ, 0 < f ∧ (mk ⟨x, hx⟩) ^ (l ^ f) = mk ⟨x, hx⟩) ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro z hz
    obtain ⟨n, hn, hln, h⟩ := hz
    have hcop : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl.out).2 hln
    refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
    have h1 : l ^ n.totient ≡ 1 [MOD n] := Nat.ModEq.pow_totient hcop
    have h2 : z ^ (l ^ n.totient) = z := by
      have h3 : z ^ (l ^ n.totient) = z ^ 1 := by
        rw [← Nat.div_add_mod (l ^ n.totient) n, ← Nat.div_add_mod 1 n, h1, pow_add, pow_add, pow_mul,
          pow_mul, h]
        simp
      simpa using h3
    rw [← map_pow]
    congr 1
    exact Subtype.ext h2
  · exact ⟨1, one_pos, by
      have : (⟨0, zero_mem _⟩ : ringA l) = 0 := rfl
      rw [this, map_zero, zero_pow (pow_ne_zero _ hl.out.ne_zero)]⟩
  · exact ⟨1, one_pos, by
      have : (⟨1, one_mem _⟩ : ringA l) = 1 := rfl
      rw [this, map_one, one_pow]⟩
  · rintro x y hx hy ⟨f, hf, h1⟩ ⟨g, hg, h2⟩
    obtain ⟨k1, k2⟩ := key _ _ f g h1 h2
    refine ⟨f * g, Nat.mul_pos hf hg, ?_⟩
    have : (⟨x + y, add_mem hx hy⟩ : ringA l) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, add_pow_char_pow, k1, k2]
  · rintro x hx ⟨f, hf, h1⟩
    refine ⟨f, hf, ?_⟩
    have : (⟨-x, neg_mem hx⟩ : ringA l) = -⟨x, hx⟩ := rfl
    rw [this, map_neg]
    have h0 := map_neg (iterateFrobenius (ringA l ⧸ Ideal.span {((l : ℕ) : ringA l)}) l f) (mk ⟨x, hx⟩)
    rw [iterateFrobenius_def, iterateFrobenius_def, h1] at h0
    exact h0
  · rintro x y hx hy ⟨f, hf, h1⟩ ⟨g, hg, h2⟩
    obtain ⟨k1, k2⟩ := key _ _ f g h1 h2
    refine ⟨f * g, Nat.mul_pos hf hg, ?_⟩
    have : (⟨x * y, mul_mem hx hy⟩ : ringA l) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, mul_pow, k1, k2]
end Formalism.L2.Th1.D.UnramifiedCompletion
