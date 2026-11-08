-- Prove2me | solution 1 for FowlerLSQC.GateDistance.gateDist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:51:24.436746+00:00
-- url     : https://prove2.me/submissions/e2e8423b-78a5-4736-a36b-c3fd0be3ea24

import Mathlib
import Definitions.Def_FowlerLSQC_GateDistance_gateDist

namespace Aux_FLGD

open scoped Matrix ComplexConjugate

variable {m : ℕ}

noncomputable def L (A : Matrix (Fin m) (Fin m) ℂ) : EuclideanSpace ℂ (Fin m × Fin m) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

theorem inner_L (A B : Matrix (Fin m) (Fin m) ℂ) :
    inner ℂ (L A) (L B) = (Aᴴ * B).trace := by
  simp only [L, PiLp.inner_apply, RCLike.inner_apply', Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem norm_L_sq (U : Matrix.unitaryGroup (Fin m) ℂ) : ‖L (U : Matrix (Fin m) (Fin m) ℂ)‖ ^ 2 = m := by
  have h := (@norm_sq_eq_re_inner ℂ _ _ _ _ (L (U : Matrix (Fin m) (Fin m) ℂ)))
  rw [h, inner_L]
  have hU : (U : Matrix (Fin m) (Fin m) ℂ)ᴴ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp U.2
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [hU, Matrix.trace_one]
  simp

theorem expand (U V : Matrix.unitaryGroup (Fin m) ℂ) (c : ℂ) (hc : ‖c‖ = 1) :
    ‖L (U : Matrix (Fin m) (Fin m) ℂ) - c • L (V : Matrix (Fin m) (Fin m) ℂ)‖ ^ 2 =
      2 * m - 2 * (c * ((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * V).trace).re := by
  rw [@norm_sub_sq ℂ, inner_smul_right, inner_L, norm_smul, hc, one_mul, norm_L_sq, norm_L_sq]
  simp only [RCLike.re_to_complex]
  ring

theorem lower (U V : Matrix.unitaryGroup (Fin m) ℂ) (c : ℂ) (hc : ‖c‖ = 1) :
    2 * m - 2 * ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * V).trace‖ ≤
      ‖L (U : Matrix (Fin m) (Fin m) ℂ) - c • L (V : Matrix (Fin m) (Fin m) ℂ)‖ ^ 2 := by
  rw [expand U V c hc]
  have h1 : (c * ((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * V).trace).re ≤
      ‖c * ((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * V).trace‖ := Complex.re_le_norm _
  rw [norm_mul, hc, one_mul] at h1
  linarith

theorem attain (U V : Matrix.unitaryGroup (Fin m) ℂ) : ∃ c : ℂ, ‖c‖ = 1 ∧
    ‖L (U : Matrix (Fin m) (Fin m) ℂ) - c • L (V : Matrix (Fin m) (Fin m) ℂ)‖ ^ 2 =
      2 * m - 2 * ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * V).trace‖ := by
  set t := ((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * V).trace with ht
  by_cases h0 : t = 0
  · refine ⟨1, by simp, ?_⟩
    rw [expand U V 1 (by simp), ← ht, h0]
    simp
  · have hn : (‖t‖ : ℂ) ≠ 0 := by
      simp [h0]
    refine ⟨conj t / (‖t‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj]
      simp [h0]
    · rw [expand U V _ (by rw [norm_div, Complex.norm_conj]; simp [h0]), ← ht]
      have : conj t / (‖t‖ : ℂ) * t = (‖t‖ : ℂ) := by
        rw [div_mul_eq_mul_div, Complex.conj_mul', sq]
        field_simp
      rw [this]
      simp

theorem sqrt_eq (U V : Matrix.unitaryGroup (Fin m) ℂ) (hm : 0 < m) :
    Real.sqrt (2 * m) * FowlerLSQC.GateDistance.gateDist U V =
      Real.sqrt (2 * m - 2 * ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * V).trace‖) := by
  unfold FowlerLSQC.GateDistance.gateDist
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp <;> ring

end Aux_FLGD

open scoped Matrix in
open Aux_FLGD in
theorem solution {m : ℕ} (hm : 0 < m) (U V W : Matrix.unitaryGroup (Fin m) ℂ) :
    FowlerLSQC.GateDistance.gateDist U W ≤
      FowlerLSQC.GateDistance.gateDist U V + FowlerLSQC.GateDistance.gateDist V W := by
  obtain ⟨c1, hc1, h1⟩ := attain U V
  obtain ⟨c2, hc2, h2⟩ := attain V W
  have hs : 0 < Real.sqrt (2 * m) := Real.sqrt_pos.mpr (by positivity)
  have e1 : ‖L (U : Matrix (Fin m) (Fin m) ℂ) - c1 • L (V : Matrix (Fin m) (Fin m) ℂ)‖ =
      Real.sqrt (2 * m) * FowlerLSQC.GateDistance.gateDist U V := by
    rw [sqrt_eq U V hm, ← h1, Real.sqrt_sq (norm_nonneg _)]
  have e2 : ‖L (V : Matrix (Fin m) (Fin m) ℂ) - c2 • L (W : Matrix (Fin m) (Fin m) ℂ)‖ =
      Real.sqrt (2 * m) * FowlerLSQC.GateDistance.gateDist V W := by
    rw [sqrt_eq V W hm, ← h2, Real.sqrt_sq (norm_nonneg _)]
  have hc : ‖c1 * c2‖ = 1 := by rw [norm_mul, hc1, hc2, one_mul]
  have e3 : Real.sqrt (2 * m) * FowlerLSQC.GateDistance.gateDist U W ≤
      ‖L (U : Matrix (Fin m) (Fin m) ℂ) - (c1 * c2) • L (W : Matrix (Fin m) (Fin m) ℂ)‖ := by
    rw [sqrt_eq U W hm]
    calc Real.sqrt (2 * m - 2 * ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * W).trace‖)
        ≤ Real.sqrt (‖L (U : Matrix (Fin m) (Fin m) ℂ) -
            (c1 * c2) • L (W : Matrix (Fin m) (Fin m) ℂ)‖ ^ 2) :=
          Real.sqrt_le_sqrt (lower U W _ hc)
      _ = _ := Real.sqrt_sq (norm_nonneg _)
  have htri : ‖L (U : Matrix (Fin m) (Fin m) ℂ) - (c1 * c2) • L (W : Matrix (Fin m) (Fin m) ℂ)‖ ≤
      ‖L (U : Matrix (Fin m) (Fin m) ℂ) - c1 • L (V : Matrix (Fin m) (Fin m) ℂ)‖ +
        ‖L (V : Matrix (Fin m) (Fin m) ℂ) - c2 • L (W : Matrix (Fin m) (Fin m) ℂ)‖ := by
    have : L (U : Matrix (Fin m) (Fin m) ℂ) - (c1 * c2) • L (W : Matrix (Fin m) (Fin m) ℂ) =
        (L (U : Matrix (Fin m) (Fin m) ℂ) - c1 • L (V : Matrix (Fin m) (Fin m) ℂ)) +
          c1 • (L (V : Matrix (Fin m) (Fin m) ℂ) - c2 • L (W : Matrix (Fin m) (Fin m) ℂ)) := by
      rw [smul_sub, smul_smul]; abel
    rw [this]
    calc _ ≤ _ + ‖c1 • (L (V : Matrix (Fin m) (Fin m) ℂ) - c2 • L (W : Matrix (Fin m) (Fin m) ℂ))‖ :=
          norm_add_le _ _
      _ = _ := by rw [norm_smul, hc1, one_mul]
  rw [e1, e2] at htri
  have := e3.trans htri
  rw [← mul_add] at this
  exact le_of_mul_le_mul_left this hs
