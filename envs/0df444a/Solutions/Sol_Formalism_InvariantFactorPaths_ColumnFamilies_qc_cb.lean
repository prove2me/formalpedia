-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:46.276701+00:00
-- url     : https://prove2.me/submissions/66c58a86-54e0-4364-8e05-af2979de0247

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_det_mul_fun
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_par_bij

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin N) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  rw [qc_det_mul_fun]
  set F : (Fin i → Fin N) → R := fun f => (∏ a, A a (f a)) * (B.submatrix f id).det with hF
  have h1 : ∑ f : Fin i → Fin N, F f = ∑ f : Fin i ↪ Fin N, F f := by
    have h0 : ∀ f : Fin i → Fin N, ¬ Function.Injective f → F f = 0 := by
      intro f hf
      simp only [Function.Injective, not_forall] at hf
      obtain ⟨a, b, hab, hne⟩ := hf
      have : (B.submatrix f id).det = 0 :=
        Matrix.det_zero_of_row_eq hne (by funext c; simp [Matrix.submatrix_apply, hab])
      simp [hF, this]
    rw [← Finset.sum_filter_of_ne (p := Function.Injective) (s := univ) (f := F)
      (fun f _ hne => by by_contra hc; exact hne (h0 f hc))]
    symm
    apply Finset.sum_bij (fun (f : Fin i ↪ Fin N) _ => (f : Fin i → Fin N))
    · intro f _; simp [f.injective]
    · intro f _ g _ h; exact DFunLike.coe_injective h
    · intro f hf
      exact ⟨⟨f, (Finset.mem_filter.mp hf).2⟩, Finset.mem_univ _, rfl⟩
    · intro f _; rfl
  rw [h1, ← Function.Bijective.sum_comp qc_par_bij (fun f => F f), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  rintro ⟨S, hS⟩ _
  set e := S.orderEmbOfFin hS with he
  have h2 : ∀ σ : Equiv.Perm (Fin i), F (qc_par ⟨⟨S, hS⟩, σ⟩) =
      (Equiv.Perm.sign σ : R) * (∏ a, A a (e (σ a))) * (B.submatrix e id).det := by
    intro σ
    have h3 : (B.submatrix (fun a => e (σ a)) id).det = (Equiv.Perm.sign σ : R) * (B.submatrix e id).det := by
      have := Matrix.det_permute σ (B.submatrix e id)
      rw [← this]; rfl
    show (∏ a, A a (e (σ a))) * (B.submatrix (fun a => e (σ a)) id).det = _
    rw [h3]; ring
  simp_rw [h2]
  rw [← Finset.sum_mul]
  congr 1
  rw [Matrix.det_apply', ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin i)))]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Matrix.submatrix_apply, id]
  congr 1
  rw [← Equiv.prod_comp σ]
  simp
end Formalism.InvariantFactorPaths.ColumnFamilies
