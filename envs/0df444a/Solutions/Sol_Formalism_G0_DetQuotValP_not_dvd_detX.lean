-- Prove2me | solution 1 for Formalism.G0.DetQuotValP.not_dvd_detX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:36.947909+00:00
-- url     : https://prove2.me/submissions/d37783b1-326f-427f-b54b-9cb164fbdeb3

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetQuotValP
theorem _root_.solution {L : Type} [Field L] {r : ℕ} (A : Fin r → ι) (hA : Function.Injective A) :
    ¬ (MvPolynomial.C Polynomial.X : MvPolynomial (ι × Fin r) (Polynomial L)) ∣
      Matrix.det (Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) := by
  intro h
  let v : ι × Fin r → L := fun p => ∑ l, if p.1 = A l ∧ p.2 = l then 1 else 0
  have h2 := map_dvd (MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : L)) v) h
  rw [MvPolynomial.eval₂Hom_C, RingHom.map_det, RingHom.mapMatrix_apply] at h2
  have hM : (Matrix.of fun (l b : Fin r) =>
      (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))).map
        (MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : L)) v) = 1 := by
    refine Matrix.ext fun l b => ?_
    simp only [Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval₂Hom_X', Matrix.one_apply, v]
    rw [Finset.sum_eq_single l]
    · by_cases e : b = l
      · subst e; simp
      · simp [e, Ne.symm e]
    · intro k _ hk
      have : A l ≠ A k := fun x => hk (hA x).symm
      simp [this]
    · simp
  rw [hM, Matrix.det_one] at h2
  simp at h2
end Formalism.G0.DetQuotValP
