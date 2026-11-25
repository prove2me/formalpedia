-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliCoordinates.unitB_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:32:06.687614+00:00
-- url     : https://prove2.me/submissions/08e23a38-62f5-485d-a224-109e62e9b6ec

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
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
namespace CapelliCoordinates
section Parts
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Parts
section Sup
variable {k r : ℕ} {i : Fin (r + 1)}
end Sup
section Lin
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Lin
end CapelliCoordinates
namespace CapelliCoordinates
section Cap
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
private theorem apply_eq_zero_of_inWb_not_inV {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) {p : Fin (2 * r + k + 1)}
    (hp : ¬ Qx2.inV k r (Fin.last r) p) : v p = 0 := by
  apply hv
  unfold Qx2.inV at hp
  simp only [Fin.val_last] at hp
  omega
private theorem herm_bvec_eq_zero_of_not_inV {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) {p : Fin (2 * r + k + 1)}
    (hp : ¬ Qx2.inV k r (Fin.last r) p) : herm (Hpk k r) (bvec p) v = 0 := by
  have hcol : ∀ q, (Hpk k r *ᵥ bvec p) q = Hpk k r q p := by
    intro q
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold Qx2.inV at hp
  simp only [Fin.val_last] at hp
  unfold herm
  simp only [dotProduct, hcol]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q.val < r ∨ r + k < q.val
  · simp [hv q hq]
  · have hp' : p.val < r ∨ r + k < p.val := by omega
    have hne : q ≠ p := fun h => by subst h; omega
    have h0 : Hpk k r q p = 0 := by
      simp only [Hpk, hne, and_false, ↓reduceIte]
      rw [if_neg (by omega), if_neg (by omega)]
    rw [h0, mul_zero]
private theorem unitB_eq_sum_single_of_inWb {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hB : ∀ a, inWb k r (Bs a)) (a b : Fin m) :
    unitB (Hpk k r) Bs a b = ∑ c, ∑ d, (Bs a (posL k r (Fin.last r) c) *
      herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) •
        Matrix.single (posL k r (Fin.last r) c) (posL k r (Fin.last r) d) (1 : ℂ) := by
  have hinj : ∀ c c' : Fin (mdim k r (Fin.last r)), posL k r (Fin.last r) c = posL k r (Fin.last r) c' → c = c' := by
    intro c c' h
    ext
    simp only [posL, Fin.ext_iff] at h
    omega
  have hlast' : ∀ c : Fin (mdim k r (Fin.last r)), Qx2.inV k r (Fin.last r) (posL k r (Fin.last r) c) := by
    intro c
    have hc := c.isLt
    simp only [Qx2.inV, posL, mdim, Fin.val_last] at hc ⊢
    omega
  have hsurj : ∀ p, Qx2.inV k r (Fin.last r) p → ∃ c, posL k r (Fin.last r) c = p := by
    intro p hp
    simp only [Qx2.inV, Fin.val_last] at hp
    refine ⟨⟨p.val - r, ?_⟩, ?_⟩
    · simp only [mdim, Fin.val_last]
      omega
    · ext
      simp only [posL, Fin.val_last]
      omega
  ext p q
  simp only [unitB, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases hp : Qx2.inV k r (Fin.last r) p
  · by_cases hq : Qx2.inV k r (Fin.last r) q
    · obtain ⟨c0, rfl⟩ := hsurj p hp
      obtain ⟨d0, rfl⟩ := hsurj q hq
      rw [Fintype.sum_eq_single c0, Fintype.sum_eq_single d0]
      · simp
      · intro d hd
        have hne : posL k r (Fin.last r) d ≠ posL k r (Fin.last r) d0 := fun h => hd (hinj _ _ h)
        simp [hne]
      · intro c hc
        have hne : posL k r (Fin.last r) c ≠ posL k r (Fin.last r) c0 := fun h => hc (hinj _ _ h)
        apply Finset.sum_eq_zero
        intro d _
        simp [hne]
    · rw [herm_bvec_eq_zero_of_not_inV (hB b) hq, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro c _
      apply Finset.sum_eq_zero
      intro d _
      have hne : posL k r (Fin.last r) d ≠ q := fun h => hq (h ▸ hlast' d)
      simp [hne]
  · rw [apply_eq_zero_of_inWb_not_inV (hB a) hp, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro d _
    have hne : posL k r (Fin.last r) c ≠ p := fun h => hp (h ▸ hlast' c)
    simp [hne]
end Cap
end CapelliCoordinates
namespace CapelliCoordinates
section Frame
variable {k r : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}
end Frame
end CapelliCoordinates
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
open Formalism.FourierDecayAlt.P.CapelliCoordinates
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.CapelliCoordinates
theorem _root_.solution {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hB : ∀ a, inWb k r (Bs a)) (a b : Fin m) :
    unitB (Hpk k r) Bs a b = ∑ c, ∑ d, (Bs a (posL k r (Fin.last r) c) *
      herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) •
        Matrix.single (posL k r (Fin.last r) c) (posL k r (Fin.last r) d) (1 : ℂ) := unitB_eq_sum_single_of_inWb Bs hB a b
end Formalism.FourierDecayAlt.P.CapelliCoordinates
