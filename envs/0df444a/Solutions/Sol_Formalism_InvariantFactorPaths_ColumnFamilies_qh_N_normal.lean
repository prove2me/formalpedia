-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_N_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:06:15.478988+00:00
-- url     : https://prove2.me/submissions/79b8278a-f5a5-4aca-b5eb-a954c75356ef

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) :
    ∃ (ε : R) (S : {S : Finset (Fin n) // S.card = s}),
      qhN R s hs J = ε • qhN R s hs (fun q => S.1.orderEmbOfFin S.2 q) := by
  classical
  by_cases hJ : Function.Injective J
  · obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin n), S = Finset.univ.image J := ⟨_, rfl⟩
    have hS : S.card = s := by
      rw [hSdef, Finset.card_image_of_injective _ hJ, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ q, J q ∈ S := by
      intro q
      rw [hSdef]
      exact Finset.mem_image_of_mem J (Finset.mem_univ q)
    let τ : Fin s → Fin s := fun q => (S.orderIsoOfFin hS).symm ⟨J q, hmem q⟩
    have hτ : ∀ q, S.orderEmbOfFin hS (τ q) = J q := by
      intro q
      rw [← Finset.coe_orderIsoOfFin_apply]
      show (((S.orderIsoOfFin hS) ((S.orderIsoOfFin hS).symm ⟨J q, hmem q⟩)) : Fin n) = J q
      rw [OrderIso.apply_symm_apply]
    have hτinj : Function.Injective τ := by
      intro a b hab
      apply hJ
      rw [← hτ a, ← hτ b, hab]
    let σ : Equiv.Perm (Fin s) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
    have hσ : ∀ q, S.orderEmbOfFin hS (σ q) = J q := fun q => hτ q
    refine ⟨((Equiv.Perm.sign σ : ℤ) : R), ⟨S, hS⟩, ?_⟩
    have hM : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q)) =
        (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (S.orderEmbOfFin hS q)).submatrix id σ := by
      ext p q
      simp only [Matrix.submatrix_apply, Matrix.of_apply, id, hσ]
    have hdet : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q)).det =
        ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n × Fin n) R) *
          (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (S.orderEmbOfFin hS q)).det := by
      rw [hM]
      first
        | exact Matrix.det_permute' σ _
        | rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.det_permute, Matrix.det_transpose]
    unfold qhN
    rw [hdet]
    first
      | (simp only [map_mul, map_intCast, Algebra.smul_def]; done)
      | (simp only [map_mul, map_intCast, Algebra.smul_def]; rfl)
      | (rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]; try rfl; done)
      | simp [Algebra.smul_def]
  · have hex : ∃ a b, J a = J b ∧ a ≠ b := by
      by_contra hcon
      push_neg at hcon
      exact hJ (fun a b h => hcon a b h)
    obtain ⟨a, b, hab, hne⟩ := hex
    refine ⟨0, ⟨(Finset.univ : Finset (Fin s)).map (Fin.castLEEmb hs), by simp⟩, ?_⟩
    have h0 : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q)).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.of_apply, hab])
    first
      | (rw [zero_smul]; unfold qhN; rw [h0, map_zero])
      | (simp only [zero_smul]; unfold qhN; rw [h0, map_zero])
end Formalism.InvariantFactorPaths.ColumnFamilies
