-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowGen_lpMinor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:10.058103+00:00
-- url     : https://prove2.me/submissions/ec9ccaa8-2b0e-4108-903d-89248f8a32d8

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowGen_X
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (hab : a < b)
    (m : ℕ) (hr : m ≤ r) (hn : m ≤ n) :
    rowGen R a b (lpMinor R m hr hn) = Polynomial.C (lpMinor R m hr hn) := by
  classical
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det]
  set N : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r × Fin n) R) :=
    Matrix.of fun p q : Fin m => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)
    with hN
  by_cases hb : b.val < m
  · have ha : a.val < m := lt_trans hab hb
    set i : Fin m := ⟨b.val, hb⟩ with hi
    set j : Fin m := ⟨a.val, ha⟩ with hj
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp [hi, hj] at this
      exact absurd this (Fin.val_ne_of_ne (ne_of_lt hab)).symm
    have hM : (rowGen R a b).toRingHom.mapMatrix N =
        Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) i
          (((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) i +
            (Polynomial.X : Polynomial (MvPolynomial (Fin r × Fin n) R)) • ((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) j) := by
      ext p q
      by_cases hp : p = i
      · subst hp
        have h1 : Fin.castLE hr i = b := Fin.ext (by simp [hi])
        have h2 : Fin.castLE hr j = a := Fin.ext (by simp [hj])
        simp [hN, Matrix.updateRow_apply, rowGen_X, h1, h2, smul_eq_mul]
      · have h1 : Fin.castLE hr p ≠ b := by
          intro h
          apply hp
          exact Fin.ext (by have := congrArg Fin.val h; simpa [hi] using this)
        simp [hN, Matrix.updateRow_apply, rowGen_X, h1, hp]
    change ((rowGen R a b).toRingHom.mapMatrix N).det = _
    rw [hM, Matrix.det_updateRow_add_smul_self _ hij]
  · have hM : (rowGen R a b).toRingHom.mapMatrix N =
        (Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N := by
      ext p q
      have h1 : Fin.castLE hr p ≠ b := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hN, rowGen_X, h1]
    change ((rowGen R a b).toRingHom.mapMatrix N).det = _
    rw [hM]
end Formalism.GradedWeylDivisibility
