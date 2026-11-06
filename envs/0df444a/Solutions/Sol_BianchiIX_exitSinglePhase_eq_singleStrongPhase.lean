-- Prove2me | solution 1 for BianchiIX.exitSinglePhase_eq_singleStrongPhase
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:00:02.065466+00:00
-- url     : https://prove2.me/submissions/ffeef33e-9c98-4316-a145-435b632ec537

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_TerminalConeData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycleDenom_wall_split (m u v w : ℝ) :
    axisCycleDenom m u v w = (m + 1) ^ 2 + v ^ 2 + (u - w) ^ 2 - 2 * v * (u + w) := by
  unfold axisCycleDenom curvature
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleStrongRoot_relations {I : ℝ} (hI : 2 < I) :
    1 < singleStrongUpperRoot I ∧ 0 < singleStrongLowerRoot I ∧ singleStrongLowerRoot I < 1 ∧
      singleStrongLowerRoot I + singleStrongUpperRoot I = I ∧
      singleStrongLowerRoot I * singleStrongUpperRoot I = 1 := by
  have hD : 0 < I ^ 2 - 4 := by nlinarith
  have hS := Real.sqrt_nonneg (I ^ 2 - 4)
  have hsq := Real.sq_sqrt hD.le
  have hSI : Real.sqrt (I ^ 2 - 4) < I := by nlinarith
  have hSlo : I - 2 < Real.sqrt (I ^ 2 - 4) := by nlinarith
  dsimp [singleStrongLowerRoot, singleStrongUpperRoot]
  refine ⟨by linarith, by linarith, by linarith, by ring, ?_⟩
  nlinarith only [hsq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleStrongUpperRoot_unique {I q : ℝ} (hI : 2 < I) (hq : 1 < q)
    (hpoly : q ^ 2 - I * q + 1 = 0) : q = singleStrongUpperRoot I := by
  obtain ⟨_, _, hl, hsum, hprod⟩ := singleStrongRoot_relations hI
  have hfactor : (q - singleStrongLowerRoot I) * (q - singleStrongUpperRoot I) = 0 := by
    nlinarith only [hpoly, hprod, congrArg (fun z : ℝ => z * q) hsum]
  rcases mul_eq_zero.mp hfactor with h | h
  · have H := sub_eq_zero.mp h
    linarith
  · exact sub_eq_zero.mp h

end
end

private theorem BianchiIX.exitSingleDenom_eq (R u v w : ℝ) :
    axisCycleDenom (1 - exitTailGap R v) u v w = exitSingleBase R v + exitSingleDefect u v w := by
  rw [axisCycleDenom_wall_split]
  dsimp only [exitSingleBase, exitSingleDefect]
  ring

private theorem BianchiIX.exitSingleNumerator_eq {R v : ℝ} (hv : v ^ 2 ≤ R ^ 2) (u w : ℝ) :
    exitSingleBase R v + exitSingleDefect u v w - 4 * (2 - exitTailGap R v) =
      R ^ 2 - 4 + exitSingleDefect u v w := by
  have H := exitTailGap_sq hv
  dsimp only [exitSingleBase]
  nlinarith only [H]

private theorem BianchiIX.exitSingleSquare_eq {R v : ℝ} (hH : exitSingleBase R v ≠ 0) (u w : ℝ) :
    R ^ 2 + exitSingleError R u v w =
      4 + (exitSingleBase R v + exitSingleDefect u v w) *
        (R ^ 2 - 4 + exitSingleDefect u v w) / exitSingleBase R v := by
  dsimp only [exitSingleError]
  field_simp
  ring

private theorem BianchiIX.singleStrongPhase_of_invariant {m u X : ℝ} (hX : 2 < X)
    (hI : singleStrongInvariant m u = 2 + 16 / (X ^ 2 - 4)) :
    singleStrongPhase m u = (X - 2) / 2 := by
  have hXm : 0 < X - 2 := sub_pos.mpr hX
  have hXsq : 0 < X ^ 2 - 4 := by nlinarith only [hX]
  have Hq : singleStrongUpperRoot (singleStrongInvariant m u) = (X + 2) / (X - 2) := by
    symm
    apply singleStrongUpperRoot_unique
      (by rw [hI]; linarith only [div_pos (by norm_num : (0 : ℝ) < 16) hXsq])
      ((lt_div_iff₀ hXm).mpr (by linarith only [hX]))
    rw [hI]
    field_simp
    ring
  rw [singleStrongPhase, Hq]
  field_simp
  ring


/-- The explicit terminal phase is the single-strong-wall phase of the actual cyclic coordinates. -/
theorem solution {R u v w : ℝ}
    (hv : v ^ 2 ≤ R ^ 2) (hH₀ : 0 < exitSingleBase R v)
    (hH : 0 < exitSingleBase R v + exitSingleDefect u v w)
    (hN : 0 < R ^ 2 - 4 + exitSingleDefect u v w) :
    let H := axisCycleDenom (1 - exitTailGap R v) u v w
    exitSinglePhase R u v w = singleStrongPhase (1 - 4 * (2 - exitTailGap R v) / H) (4 * v / H) := by
  intro H
  let N := R ^ 2 - 4 + exitSingleDefect u v w
  have hHpos : 0 < H := by dsimp only [H]; rwa [exitSingleDenom_eq]
  have hNpos : 0 < N := hN
  have hNeq : N = H - 4 * (2 - exitTailGap R v) := by
    dsimp only [N, H]
    rw [exitSingleDenom_eq]
    exact (exitSingleNumerator_eq hv u w).symm
  have hm : 1 - 4 * (2 - exitTailGap R v) / H = N / H := by
    rw [hNeq]
    field_simp
  have HI : singleStrongInvariant (1 - 4 * (2 - exitTailGap R v) / H) (4 * v / H) =
      2 + 16 * exitSingleBase R v / (H * N) := by
    rw [hm, singleStrongInvariant]
    have Hpoly : H ^ 2 + N ^ 2 + 16 * v ^ 2 = 2 * H * N + 16 * exitSingleBase R v := by
      rw [hNeq]
      dsimp only [exitSingleBase]
      ring
    field_simp
    nlinarith only [Hpoly]
  let X := Real.sqrt (R ^ 2 + exitSingleError R u v w)
  have HX : R ^ 2 + exitSingleError R u v w = 4 + H * N / exitSingleBase R v := by
    rw [exitSingleSquare_eq hH₀.ne' u w]
    dsimp only [H, N]
    rw [exitSingleDenom_eq]
  have Hpos : 4 < R ^ 2 + exitSingleError R u v w := by
    rw [HX]
    linarith only [div_pos (mul_pos hHpos hNpos) hH₀]
  have hX : 2 < X := (Real.lt_sqrt (by norm_num)).mpr (by norm_num at Hpos ⊢; exact Hpos)
  have hXsq : X ^ 2 = 4 + H * N / exitSingleBase R v := by
    rw [Real.sq_sqrt (by linarith only [Hpos])]
    exact HX
  have HIX : singleStrongInvariant (1 - 4 * (2 - exitTailGap R v) / H) (4 * v / H) =
      2 + 16 / (X ^ 2 - 4) := by
    rw [HI, hXsq]
    field_simp
    ring
  exact (singleStrongPhase_of_invariant hX HIX).symm
