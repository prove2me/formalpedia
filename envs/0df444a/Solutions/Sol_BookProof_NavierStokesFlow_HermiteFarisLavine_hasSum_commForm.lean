-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_commForm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:02:58.717874+00:00
-- url     : https://prove2.me/submissions/b581b203-7ec8-4244-880f-d118720edd61

import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_commForm
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}
theorem h44_term (X : ℕ → ℂ) (m : ℕ) :
    -2 * (inner ℂ (hFun κ X m) ((oscSymbol κ m : ℂ) * X m)).im
      = shift2 (fun n => 2 * amp κ n * oscSymbol κ (n + 2)
          * ((starRingEnd ℂ) (X n) * X (n + 2)).re) m
        - 2 * amp κ m * oscSymbol κ m * ((starRingEnd ℂ) (X m) * X (m + 2)).re := by
  rcases m with _ | _ | k <;>
    simp [hFun, shift2, Complex.mul_re, Complex.mul_im] <;> ring

theorem h44_summQ (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    Summable (fun m => 2 * amp κ m * oscSymbol κ m
      * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) m) * ((x : L2I ℕ) : ℕ → ℂ) (m + 2)).re) := by
  set X : ℕ → ℂ := ((x : L2I ℕ) : ℕ → ℂ) with hX
  have h1 := (hasSum_normSq (diagMax (oscSymbol κ) x : L2I ℕ)).summable
  have h2 : Summable (fun m => (ampSeq κ X (m + 2)) ^ 2) :=
    (summable_nat_add_iff 2).mpr (summable_ampSeq_sq hκ x)
  refine Summable.of_norm_bounded (h1.add h2) (fun m => ?_)
  rw [norm_diagMax_coe hκ x m]
  simp only [ampSeq]
  have ha := amp_nonneg hκ m
  have ha2 := amp_le_amp_add_two hκ m
  have hw := oscSymbol_nonneg hκ m
  have hre : |((starRingEnd ℂ) (X m) * X (m + 2)).re| ≤ ‖X m‖ * ‖X (m + 2)‖ := by
    have := Complex.abs_re_le_norm ((starRingEnd ℂ) (X m) * X (m + 2))
    simpa [norm_mul] using this
  have hn1 := norm_nonneg (X m)
  have hn2 := norm_nonneg (X (m + 2))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * amp κ m * oscSymbol κ m)]
  have hb : 2 * amp κ m * oscSymbol κ m * (‖X m‖ * ‖X (m + 2)‖)
      ≤ 2 * (oscSymbol κ m * ‖X m‖) * (amp κ (m + 2) * ‖X (m + 2)‖) := by
    have : amp κ m * ‖X (m + 2)‖ ≤ amp κ (m + 2) * ‖X (m + 2)‖ :=
      mul_le_mul_of_nonneg_right ha2 hn2
    nlinarith [mul_nonneg hw hn1]
  have hc : 2 * amp κ m * oscSymbol κ m * |((starRingEnd ℂ) (X m) * X (m + 2)).re|
      ≤ 2 * amp κ m * oscSymbol κ m * (‖X m‖ * ‖X (m + 2)‖) :=
    mul_le_mul_of_nonneg_left hre (by positivity)
  nlinarith [sq_nonneg (oscSymbol κ m * ‖X m‖ - amp κ (m + 2) * ‖X (m + 2)‖)]

theorem h44_hasSum (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    HasSum (fun n => 8 * κ * (amp κ n
        * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n) * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re))
      (commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x) := by
  set X : ℕ → ℂ := ((x : L2I ℕ) : ℕ → ℂ) with hX
  have hz := lp.hasSum_inner (𝕜 := ℂ) (nsH κ hκ x) (diagMax (oscSymbol κ) x)
  have hc : commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x
      = -2 * (inner ℂ (nsH κ hκ x) (diagMax (oscSymbol κ) x)).im := by
    unfold commForm
    rw [← inner_conj_symm (𝕜 := ℂ) (diagMax (oscSymbol κ) x : L2I ℕ) (nsH κ hκ x : L2I ℕ)]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.conj_im]
    ring
  have hf : HasSum (fun m => -2 * (inner ℂ (hFun κ X m) ((oscSymbol κ m : ℂ) * X m)).im)
      (commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x) := by
    rw [hc]
    exact (Complex.imCLM.hasSum hz).mul_left (-2)
  simp only [h44_term] at hf
  have hQ := h44_summQ hκ x
  rw [← hX] at hQ
  have hP := hf.add hQ.hasSum
  simp only [sub_add_cancel] at hP
  have hP' := (hasSum_shift2_iff.mp hP).sub hQ.hasSum
  simp only [add_sub_cancel_right] at hP'
  convert hP' using 1
  all_goals first
    | rfl
    | (funext n; rw [oscSymbol_step]; ring)

theorem solution (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    HasSum (fun n => 8 * κ * (amp κ n
        * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n) * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re))
      (commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x) := by
  exact h44_hasSum hκ x

