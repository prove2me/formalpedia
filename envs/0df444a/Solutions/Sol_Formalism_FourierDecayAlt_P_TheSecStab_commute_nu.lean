-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSecStab.commute_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:48.002054+00:00
-- url     : https://prove2.me/submissions/e95531a1-897d-4c2d-ad51-943974a6c02e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
section block
variable {k : ℕ}
private theorem col_lemma_2 {h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {i : Fin (k + 1)}
    (hi : h *ᵥ Pi.single i 1 = Pi.single i 1) (l : Fin (k + 1)) : h l i = if l = i then 1 else 0 := by
  have e := congrFun hi l
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using e
private theorem row_lemma_3 {h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hh : h ∈ UH (Hb k)) {i : Fin (k + 1)}
    (hi : h *ᵥ Pi.single i 1 = Pi.single i 1) (j : Fin (k + 1)) : h i j = if i = j then 1 else 0 := by
  have hU : hᴴ * Hb k * h = Hb k := hh
  have e := congrFun (congrFun hU i) j
  rw [Matrix.mul_apply] at e
  simp only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    col_lemma_2 hi] at e
  rw [Fintype.sum_eq_single i (by intro x hx; simp [hx])] at e
  by_cases hil : i = Fin.last k <;> by_cases hij : i = j <;> simp_all
private theorem vec_lemma_4 {h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hh : h ∈ UH (Hb k))
    {i : Fin (k + 1)} (hi : h *ᵥ Pi.single i 1 = Pi.single i 1) : Pi.single i 1 ᵥ* h = Pi.single i 1 := by
  funext j
  have e : (Pi.single i 1 ᵥ* h) j = h i j := by
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  rw [e, row_lemma_3 hh hi j]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Pi.single_apply, Ne.symm hij]
end block
section block2
variable {k : ℕ}
end block2
section full
variable {k r : ℕ}
end full
end Formalism.FourierDecayAlt.P.TheSecStab
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
variable {k : ℕ}
namespace Formalism.FourierDecayAlt.P.TheSecStab
theorem _root_.solution {h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hh : h ∈ UH (Hb k))
    (h0 : h *ᵥ Pi.single 0 1 = Pi.single 0 1) (hl : h *ᵥ Pi.single (Fin.last k) 1 = Pi.single (Fin.last k) 1)
    (w s : ℂ) : h * nu k w s = nu k w s * h := by
  have hu : ∀ a b : ℂ, h *ᵥ (a • Pi.single 0 1 + b • Pi.single (Fin.last k) 1) =
      a • Pi.single 0 1 + b • Pi.single (Fin.last k) 1 := by
    intro a b
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h0, hl]
  unfold nu
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    hu, hu, vec_lemma_4 hh h0, vec_lemma_4 hh hl]
end Formalism.FourierDecayAlt.P.TheSecStab
