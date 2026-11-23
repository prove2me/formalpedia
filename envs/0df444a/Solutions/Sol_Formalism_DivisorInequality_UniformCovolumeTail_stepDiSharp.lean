-- Prove2me | solution 1 for Formalism.DivisorInequality.UniformCovolumeTail.stepDiSharp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:09.370615+00:00
-- url     : https://prove2.me/submissions/31142dca-51bd-404f-90f1-76dee57dcde6

import Mathlib
import Definitions.Def_Formalism_DivisorInequality_DivIneqTopAnchorU
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_BaseLevelBoundsWithCovolumeHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_EvenDegreeWeightBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder
open Formalism Formalism.DivisorInequality
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisorInequality.UniformCovolumeTail
set_option maxHeartbeats 800000
namespace Formalism.DivisorInequality.UniformCovolumeTail
theorem _root_.solution (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' hK : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 Ce Ch : ℝ)
    (h32 : ∀ j s, logK j s ≤
      (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s +
      ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
        (logh j + logh' j)))
    (hmean : ∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ))
    (hOm : ∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm)
    (hSK : ∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT) + Ce * f * N ^ 2 * logg)
    (hth : (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L)
    (hh : ∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg))
    (hh' : ∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg))
    (hcard : (Fintype.card Pl : ℝ) ≤ f) (hg0 : ∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2)
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hL : 0 ≤ L) (hLLa : L ≤ La) (hLa1 : 1 ≤ La)
    (h5 : ∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La)
    (h6 : ∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La)
    (hT : logT ≤ C7 * m * L) (hg : logg ≤ C8 * L)
    (p2 : 0 ≤ C2) (p3 : 0 ≤ C3) (p4 : 0 ≤ C4) (p5 : 0 ≤ c5) (p6 : 0 ≤ c6) (p7 : 0 ≤ C7) (p8 : 0 ≤ C8)
    (pe : 0 ≤ Ce)
    (kA : C3 + c5 + 2 * c6 + 1 + 2 * C4 + 2 * Ce * C8 ≤ Ch) (kB : 2 * (C2 + C4) * (C7 + C8) ≤ Ch) :
    ∀ j, hK j ≤ ∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm) +
      Ch * f * N ^ 2 * (La + m ^ 3 * L) := by
  intro j
  have hn : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hc0 : 0 ≤ (Fintype.card Pl : ℝ) * g0 j := mul_nonneg (Nat.cast_nonneg _) (hg0 j).1
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hcard
  have hLa0 : 0 ≤ La := by linarith
  have hN2 : 1 ≤ N ^ 2 := by
    have := mul_le_mul hN hN zero_le_one (by linarith)
    linarith only [this]
  have hF0 : 0 ≤ f * N ^ 2 := mul_nonneg hf0 (sq_nonneg N)
  have hcF : (Fintype.card Pl : ℝ) * g0 j ≤ f * N ^ 2 := mul_le_mul hcard (hg0 j).2 (hg0 j).1 hf0

  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 =
      (Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT) + Ce * f * N ^ 2 * logg) +
        (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) + (logh j + logh' j) := ⟨_, rfl⟩
  have hpt : ∀ s, logK j s ≤ (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s + K0 := by
    intro s
    have a1 := h32 j s
    have a2 := hSK j s
    linarith
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset Emb)) => hpt s)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum

  have hX : ∑ s, (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) =
      (Fintype.card Emb : ℝ) * ∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    have e := hOm τ
    rw [div_eq_iff hn.ne'] at e
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, e]
    ring
  rw [hX] at hsum

  have hZ : (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) ≤
      f * (1 + 2 * N ^ 2 * (c6 * La)) := by
    calc (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2)))
        ≤ ∑ _τ : Pl, (1 + 2 * N ^ 2 * (c6 * La)) := by
          apply Finset.sum_le_sum
          intro τ _
          have a1 := mul_le_mul_of_nonneg_left (h6 j τ) (hg0 j).1
          have a2 := mul_le_mul_of_nonneg_right (hg0 j).2 (mul_nonneg p6 hLa0)
          linarith
      _ = (Fintype.card Pl : ℝ) * (1 + 2 * N ^ 2 * (c6 * La)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ f * (1 + 2 * N ^ 2 * (c6 * La)) :=
          mul_le_mul_of_nonneg_right hcard
            (add_nonneg zero_le_one (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg N)) (mul_nonneg p6 hLa0)))

  have hscal : K0 + (Fintype.card Pl : ℝ) * g0 j * (C3 * L) ≤ Ch * f * N ^ 2 * (La + m ^ 3 * L) := by
    have b1 := mul_le_mul_of_nonneg_left (h5 j) hc0
    have b2 := mul_le_mul_of_nonneg_right hcF (mul_nonneg p5 hLa0)
    have b3 := mul_le_mul_of_nonneg_right hcF (mul_nonneg p3 hL)
    have b4 : C2 * f * m ^ 2 * N ^ 2 * (logg + logT) ≤ C2 * f * m ^ 2 * N ^ 2 * (C8 * L + C7 * m * L) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (mul_nonneg (mul_nonneg p2 hf0) (sq_nonneg m)) (sq_nonneg N))
    have b5 : Ce * f * N ^ 2 * logg ≤ Ce * f * N ^ 2 * (C8 * L) :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg (mul_nonneg pe hf0) (sq_nonneg N))
    have b6 := hh j
    have b7 := hh' j
    have b8 : 2 * C4 * (f * N ^ 2) * (L + logT + logg) ≤ 2 * C4 * (f * N ^ 2) * (L + C7 * m * L + C8 * L) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg zero_le_two p4) hF0)
    have q1 : (1 : ℝ) * 1 ≤ N ^ 2 * La := mul_le_mul hN2 hLa1 zero_le_one (sq_nonneg N)
    have q2 := mul_le_mul_of_nonneg_left q1 hf0
    have hm1 : 1 ≤ m ^ 2 := by
      have := mul_le_mul hm hm zero_le_one (by linarith)
      linarith only [this]
    have hm2 : m ^ 2 ≤ m ^ 3 := by
      have := mul_le_mul_of_nonneg_left hm (sq_nonneg m)
      linarith only [this]
    have hm3 : m ≤ m ^ 3 := by
      have := mul_le_mul_of_nonneg_left hm1 (by linarith : (0 : ℝ) ≤ m)
      linarith only [this]
    have hm4 : 1 ≤ m ^ 3 := le_trans hm hm3
    have e1 : 0 ≤ f * N ^ 2 * C3 * (La - L) := mul_nonneg (mul_nonneg hF0 p3) (by linarith)
    have e2 : 0 ≤ f * N ^ 2 * C4 * (La - L) := mul_nonneg (mul_nonneg hF0 p4) (by linarith)
    have e3 : 0 ≤ f * N ^ 2 * (Ce * C8) * (La - L) :=
      mul_nonneg (mul_nonneg hF0 (mul_nonneg pe p8)) (by linarith)
    have e5 : 0 ≤ f * N ^ 2 * (C2 * C8) * ((m ^ 3 - m ^ 2) * L) :=
      mul_nonneg (mul_nonneg hF0 (mul_nonneg p2 p8)) (mul_nonneg (by linarith) hL)
    have e6 : 0 ≤ f * N ^ 2 * (C4 * C7) * ((m ^ 3 - m) * L) :=
      mul_nonneg (mul_nonneg hF0 (mul_nonneg p4 p7)) (mul_nonneg (by linarith) hL)
    have e7 : 0 ≤ f * N ^ 2 * (C4 * C8) * ((m ^ 3 - 1) * L) :=
      mul_nonneg (mul_nonneg hF0 (mul_nonneg p4 p8)) (mul_nonneg (by linarith) hL)
    have e8 : f * N ^ 2 * ((C3 + c5 + 2 * c6 + 1 + 2 * C4 + 2 * Ce * C8) * La) ≤ f * N ^ 2 * (Ch * La) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right kA hLa0) hF0
    have e9 : f * N ^ 2 * ((2 * (C2 + C4) * (C7 + C8)) * (m ^ 3 * L)) ≤ f * N ^ 2 * (Ch * (m ^ 3 * L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right kB (mul_nonneg (by linarith) hL)) hF0
    rw [hK0]
    linarith
  rw [hmean j, div_le_iff₀ hn]
  have hth' := (div_le_iff₀ hn).mp hth
  have t1 := mul_le_mul_of_nonneg_left hth' hc0
  have t2 := mul_le_mul_of_nonneg_left hscal hn.le
  linarith
end Formalism.DivisorInequality.UniformCovolumeTail
