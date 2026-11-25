-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameEntries.regular_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:44.546854+00:00
-- url     : https://prove2.me/submissions/518f9728-3fb6-429b-859a-88b3ae7557f1

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_poly_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace FrameEntries
section Hom
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Hom
section Grp
variable {k r : ℕ}
private theorem Hpk_mul_self_eq_one (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.2
  have hj := j.2
  let p : ℕ → ℕ := fun a => if a < r ∨ r + k < a then 2 * r + k - a else a
  have hp : ∀ a < 2 * r + k + 1, p a < 2 * r + k + 1 := by
    intro a ha
    simp only [p]
    split_ifs <;> omega
  have hent : ∀ a b : Fin (2 * r + k + 1),
      Hpk k r a b = if (b : ℕ) = p a then (if (a : ℕ) = r + k then -1 else 1) else 0 := by
    intro a b
    have := a.2
    have := b.2
    simp only [Hpk, p, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  rw [Finset.sum_eq_single ⟨p i, hp i hi⟩]
  · rw [hent, hent]
    simp only [p, Fin.ext_iff]
    split_ifs <;> first | omega | norm_num
  · intro b _ hb
    rw [hent i b]
    have hb' : (b : ℕ) ≠ p i := fun h => hb (Fin.ext h)
    simp [hb']
  · intro h
    exact absurd (Finset.mem_univ _) h
end Grp
section Main
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Main
end FrameEntries
namespace FrameEntries
section Reg
variable {k r : ℕ}
end Reg
end FrameEntries
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FrameEntries
theorem _root_.solution {f : Mx k r → ℂ} (hf : IsRegular k r f) (i : Fin (r + 1)) (D : Set (Mx k r)) :
    SmoothLev k r i D f := by
  obtain ⟨p, hp⟩ := hf
  intro g₀ _
  refine ⟨Set.univ, _, isOpen_univ, Set.mem_univ _, (poly_contDiff p).contDiffOn, fun g _ hg => ?_⟩
  have hU : gᴴ * Hpk k r * g = Hpk k r := by
    simp only [Glev, UH, Set.mem_setOf_eq] at hg
    exact hg.1
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Hpk_mul_self_eq_one]
  rw [hp g]
  simp only [Matrix.inv_eq_left_inv hl]
end Formalism.FourierDecayAlt.P.FrameEntries
