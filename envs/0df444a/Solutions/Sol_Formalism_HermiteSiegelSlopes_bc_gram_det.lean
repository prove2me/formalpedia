-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.bc_gram_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:24.660623+00:00
-- url     : https://prove2.me/submissions/ff30a21e-14eb-40be-880f-aac6c211ad3f

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_hermitian_polarization_eq
import Theorems.Thm_Formalism_HermiteSiegelSlopes_hermitianForm_add_left
import Theorems.Thm_Formalism_HermiteSiegelSlopes_hermitianForm_add_right
import Theorems.Thm_Formalism_HermiteSiegelSlopes_hermitianForm_smul_right
import Theorems.Thm_Formalism_HermiteSiegelSlopes_hermitianForm_smul_left
import Theorems.Thm_Formalism_HermiteSiegelSlopes_hermitianForm_self_eq_norm_sq
import Theorems.Thm_P2M_Formalism_HermiteSiegelSlopes_bcMap_add__91b38c6a39a2
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_smul_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]
variable [StarRing F] [StarRing E]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution [IsTotallyComplex F]
    (XF : InfinitePlace F → Matrix ι ι ℂ) (XE : InfinitePlace E → Matrix ι ι ℂ)
    (hn : ∀ (w : InfinitePlace E) (x : ι → F),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun E ι) XE w (fun i => algebraMap F E (x i)) =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun F ι) XF (w.comap (algebraMap F E)) x)
    (w : InfinitePlace E) {j : ℕ} (e : Fin j → ι → F) :
    (gramPl (Pi.basisFun E ι) XE w (fun a => bcMap (E := E) (e a))).det =
      (gramPl (Pi.basisFun F ι) XF (w.comap (algebraMap F E)) e).det := by
  set v := w.comap (algebraMap F E) with hv
  have : w.LiesOver v := ⟨rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0 : F, starRingEnd ℂ (v.embedding s0) ≠ v.embedding s0 := by
    have h1 := InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex v)
    rw [ComplexEmbedding.isReal_iff] at h1
    by_contra hc
    push Not at hc
    exact h1 (RingHom.ext fun s => by rw [ComplexEmbedding.conjugate_coe_eq]; exact hc s)
  let τ : F →+* ℂ := w.embedding.comp (algebraMap F E)
  let H1 : (ι → F) → (ι → F) → ℂ := fun x y =>
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun E ι) XE w (bcMap (E := E) x) (bcMap (E := E) y)
  have a1 : ∀ x y z, H1 (x + y) z = H1 x z + H1 y z := fun x y z => by
    simp only [H1, bcMap_add', hermitianForm_add_left]
  have b1 : ∀ x y z, H1 x (y + z) = H1 x y + H1 x z := fun x y z => by
    simp only [H1, bcMap_add', hermitianForm_add_right]
  have r1 : ∀ s x y, H1 x (s • y) = τ s * H1 x y := fun s x y => by
    simp only [H1, baseChangeMap_smul_scalar, hermitianForm_smul_right]; rfl
  have l1 : ∀ s x y, H1 (s • x) y = starRingEnd ℂ (τ s) * H1 x y := fun s x y => by
    simp only [H1, baseChangeMap_smul_scalar, hermitianForm_smul_left]; rfl
  have hN : ∀ x, H1 x x = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun F ι) XF v x x := fun x => by
    simp only [H1, hermitianForm_self_eq_norm_sq]
    have := hn w x
    rw [show bcMap (E := E) x = fun i => algebraMap F E (x i) from rfl, this]
  rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with h | h
  · have hτ : ∀ s, v.embedding s = τ s := fun s => by rw [← h]
    have hH := hermitian_polarization_eq H1 (fun x y => Formalism.HermitianLatticesTheory.majAt (Pi.basisFun F ι) XF v x y) τ a1 b1 r1 l1
      (fun x y z => hermitianForm_add_left _ _ _ _ _ _) (fun x y z => hermitianForm_add_right _ _ _ _ _ _)
      (fun s x y => by rw [hermitianForm_smul_right, hτ]) (fun s x y => by rw [hermitianForm_smul_left, hτ])
      hN s0 (by rw [← hτ]; exact hs0)
    congr 1
    ext a c
    exact hH (e a) (e c)
  · have hτ : ∀ s, v.embedding s = starRingEnd ℂ (τ s) := fun s => by
      rw [← h]; rfl
    have hH := hermitian_polarization_eq H1 (fun x y => Formalism.HermitianLatticesTheory.majAt (Pi.basisFun F ι) XF v y x) τ a1 b1 r1 l1
      (fun x y z => hermitianForm_add_right _ _ _ _ _ _) (fun x y z => hermitianForm_add_left _ _ _ _ _ _)
      (fun s x y => by rw [hermitianForm_smul_left, hτ, Complex.conj_conj])
      (fun s x y => by rw [hermitianForm_smul_right, hτ])
      hN s0 (by
        intro hc
        apply hs0
        rw [hτ, Complex.conj_conj, hc])
    rw [← Matrix.det_transpose (gramPl (Pi.basisFun F ι) XF v e)]
    congr 1
    ext a c
    exact hH (e a) (e c)
end Formalism.HermiteSiegelSlopes
