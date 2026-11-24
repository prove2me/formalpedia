-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.charpolyRev_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:40.960191+00:00
-- url     : https://prove2.me/submissions/7dc9fa9a-14e1-4614-b480-7141cb1bcfaf

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]
open Polynomial
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution [Nontrivial O] (P Q : Matrix r r O) (d : r → O)
    (hd : ∀ j, d j = 0 ∨ d j = 1) (hPQ : P * Q = 1) :
    (P * Matrix.diagonal d * Q).charpolyRev = (1 - X) ^ (Nat.card {j // d j = 1}) := by
  classical
  have hPQ' : P.map (Polynomial.C : O →+* Polynomial O) * Q.map Polynomial.C = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map (Polynomial.C : O →+* Polynomial O)) hPQ
  have hdiag : Matrix.diagonal (fun j => (1 : Polynomial O) - Polynomial.X * Polynomial.C (d j)) =
      1 - (Polynomial.X : Polynomial O) • Matrix.diagonal (fun j => Polynomial.C (d j)) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal_apply, Matrix.one_apply]
  have key : (1 : Matrix r r (Polynomial O)) - (Polynomial.X : Polynomial O) •
      (P * Matrix.diagonal d * Q).map Polynomial.C =
      P.map Polynomial.C * Matrix.diagonal (fun j => 1 - Polynomial.X * Polynomial.C (d j)) *
        Q.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _), hdiag, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul]
  have hfac : ∀ j, ((1 : Polynomial O) - Polynomial.X * Polynomial.C (d j)) =
      if d j = 1 then 1 - Polynomial.X else 1 := fun j => by
    rcases hd j with h | h <;> simp [h]
  unfold Matrix.charpolyRev
  rw [key, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (P.map Polynomial.C)), mul_assoc,
    ← Matrix.det_mul, hPQ', Matrix.det_one, mul_one, Matrix.det_diagonal]
  simp_rw [hfac]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
