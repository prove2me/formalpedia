-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.par_dec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:05.30414+00:00
-- url     : https://prove2.me/submissions/c88a862a-bc32-4890-bb19-e7285633a573

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_blk_eta
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_blk_inj
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_hypJ_eq
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_hform_eq
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_gram_blk
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_nim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (hs : ∀ x, s (s x) = x) {g : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hg : cT s g * hypJ J * g = hypJ J)
    (h0 : ∀ i : Fin (M + 1), g i.succ 0 = 0) :
    ∃ (w : Fin M → K) (z : K) (U : Matrix (Fin M) (Fin M) K) (a : Kˣ), z + s z + hform s J w w = 0 ∧
      cT s U * J * U = J ∧ g = nM s J w z * pm 1 0 0 1 0 U * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 := by
  have e := blk_eta g
  rw [show g 1 0 = 0 from h0 0, show (fun i : Fin M => g i.succ.succ 0) = 0 from funext fun i => h0 i.succ] at e
  generalize g 0 0 = a, g 0 1 = b, (fun j : Fin M => g 0 j.succ.succ) = r, g 1 1 = d,
    (fun j : Fin M => g 1 j.succ.succ) = t, (fun i : Fin M => g i.succ.succ 1) = w,
    (Matrix.of fun i j : Fin M => g i.succ.succ j.succ.succ) = U at e
  subst e
  rw [gram_blk, hypJ_eq] at hg
  obtain ⟨-, h1, h2, h3, h4, h5, -, -, h6⟩ := blk_inj hg
  have ht : t = 0 := by rw [← one_smul K t, ← h1, mul_comm, mul_smul, h2, smul_zero]
  subst ht
  have z0 : (s : K → K) ∘ (0 : Fin M → K) = 0 := funext fun _ => map_zero s
  have e : (s : K → K) ∘ (s a • w) = a • (s ∘ w) := by funext i; simp [hs]
  refine ⟨s a • w, b * s a, U, ⟨a, s d, by rw [mul_comm, h3], h3⟩, ?_, by simpa [z0] using h6, ?_⟩
  · rw [hform_eq, e, smul_vecMul, smul_dotProduct, dotProduct_smul, map_mul, hs, smul_eq_mul, smul_eq_mul]
    linear_combination (a * s a) * h4 - (b * s a) * h3 - (a * s b) * h1
  · rw [nim, e, smul_vecMul, smul_vecMul]
    simp only [Units.inv_mk, hs, pm]
    congr 1
    · linear_combination (-b) * h1
    · rw [smul_zero, add_zero, add_eq_zero_iff_eq_neg] at h5
      rw [← smul_neg, ← h5, smul_smul, mul_comm, h3, one_smul]
    · rw [smul_smul, mul_comm, h1, one_smul]
end CompanionTheory.PlacePermOperatorBicommutantSpan
