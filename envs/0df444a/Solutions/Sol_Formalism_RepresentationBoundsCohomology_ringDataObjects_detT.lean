-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.detT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:15:20.779017+00:00
-- url     : https://prove2.me/submissions/94b22087-814f-4329-860a-52ebb97bc0da

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RingDataObjects
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_C_mem_polyT
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_det_poly_statement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Classical Polynomial
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
section
variable {O : Type} [CommRing O] {Xs : Type} (T : Subalgebra O (Xs → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (Xs → Matrix d d O))
private theorem matrix_charpolyRev_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix d d R) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]
end
end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
variable {O : Type} [CommRing O] {Xs : Type} (T : Subalgebra O (Xs → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (Xs → Matrix d d O))
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution (hG1 : ∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T)
    (M : Xs → Matrix d d O[X]) (hM : M ∈ tSpan (polyT T) (rPoly r)) (k : ℕ) :
    (fun x => (M x).det.coeff k) ∈ T := by
  have h1 : ∀ (g : G) (k : ℕ), FromT (polyT T) (fun x => (Matrix.charpolyRev (rPoly r g x)).coeff k) := by
    intro g k
    refine ⟨fun x => C ((Matrix.charpolyRev (r g x)).coeff k), C_mem_polyT T (hG1 g k), fun x => ?_⟩
    have hx : rPoly r g x = (r g x).map C := rfl
    dsimp only
    rw [hx, matrix_charpolyRev_map, Polynomial.coeff_map]
    rfl
  obtain ⟨u, hu, hux⟩ := det_poly_statement O[X] O[X] Xs G d (polyT T) (rPoly r) h1 1 (fun _ => M)
    (fun _ => hM) (Finsupp.single 0 (Fintype.card d))
  have key : ∀ x, u x = (M x).det := by
    intro x
    have hx := hux x
    dsimp only at hx
    rw [Fin.sum_univ_one, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, mul_comm,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow] at hx
    simpa using hx
  have hfun : (fun x => (M x).det.coeff k) = fun x => (u x).coeff k := by
    funext x
    rw [key x]
  rw [hfun]
  exact hu k
end Formalism.RepresentationBoundsCohomology.ringDataObjects
