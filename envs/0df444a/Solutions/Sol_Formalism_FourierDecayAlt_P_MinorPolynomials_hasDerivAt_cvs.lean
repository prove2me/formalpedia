-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.hasDerivAt_cvs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:51.027165+00:00
-- url     : https://prove2.me/submissions/19e14bd7-758a-4d9e-8443-a6f28378ac66

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_monoM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_prod_update_a
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_prod_update_b
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_polyD
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_polyDb
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_polyG
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_invpow__0b9fd55a1697
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_poly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X g : Mat k r) (t : CT k r nf)
    (hnz : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0)
    (hG : t.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) :
    HasDerivAt (fun s => cvs D t (crv (false, X) g s)) (((dscal D X t).map fun t' => cvs D t' g).sum) 0 := by

  have hF : ∀ l ∈ (Finset.univ : Finset (Fin (r + 2))), HasDerivAt (fun s => fct D.z D.z' t.a t.b (crv (false, X) g s) l)
      ((-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * (Dmin k r D.z D.z' g l)⁻¹ ^ (t.a l + 1)) *
          (star (Dmin k r D.z D.z' g l))⁻¹ ^ t.b l +
        (Dmin k r D.z D.z' g l)⁻¹ ^ t.a l *
          (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * (star (Dmin k r D.z D.z' g l))⁻¹ ^ (t.b l + 1)))
      0 := by
    intro l _
    have ha : t.a l = 0 ∨ Dmin k r D.z D.z' (crv (false, X) g 0) l ≠ 0 := by
      rw [crv_zero]; by_cases h : t.a l = 0
      · exact Or.inl h
      · exact Or.inr (hnz l (Or.inl h))
    have hb : t.b l = 0 ∨ star (Dmin k r D.z D.z' (crv (false, X) g 0) l) ≠ 0 := by
      rw [crv_zero]; by_cases h : t.b l = 0
      · exact Or.inl h
      · exact Or.inr (star_ne_zero.2 (hnz l (Or.inr h)))
    have h1 := hasDerivAt_invpow' (hasDerivAt_polyD X g D.z D.z' l) ha
    have h2 := hasDerivAt_invpow' (hasDerivAt_polyDb X g D.z D.z' l) hb
    have := h1.fun_mul h2
    simpa only [fct, crv_zero] using this
  have hprod := HasDerivAt.fun_finsetProd hF
  have hGd := hasDerivAt_invpow' (hasDerivAt_polyG X g D.z D.z') (a := t.c) (by
    rw [crv_zero]; by_cases h : t.c = 0
    · exact Or.inl h
    · exact Or.inr (hG h))
  have hP := hasDerivAt_poly X g t.q
  have hall := hP.fun_mul (hprod.fun_mul hGd)
  have hfun : (fun s => cvs D t (crv (false, X) g s)) = fun s => eval (vars (crv (false, X) g s)) t.q *
      ((∏ l ∈ Finset.univ, fct D.z D.z' t.a t.b (crv (false, X) g s) l) * ((Gf k r D.z D.z' (crv (false, X) g s) : ℝ) : ℂ)⁻¹ ^ t.c) := by
    funext s; simp [cvs, monoM_eq]
  rw [hfun]
  refine hall.congr_deriv ?_

  simp only [crv_zero]
  set P0 := eval (vars g) t.q
  set G0 := ((Gf k r D.z D.z' g : ℝ) : ℂ)
  set dG := eval (vars g) (dP X (qGf D.z D.z'))
  have hsum : ∑ l ∈ (Finset.univ : Finset (Fin (r + 2))), (∏ j ∈ Finset.univ.erase l, fct D.z D.z' t.a t.b g j) •
      ((-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * (Dmin k r D.z D.z' g l)⁻¹ ^ (t.a l + 1)) *
          (star (Dmin k r D.z D.z' g l))⁻¹ ^ t.b l +
        (Dmin k r D.z D.z' g l)⁻¹ ^ t.a l *
          (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * (star (Dmin k r D.z D.z' g l))⁻¹ ^ (t.b l + 1))) =
      ∑ l, (-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * ∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) +
      ∑ l, (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * ∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← prod_update_a, ← prod_update_b, smul_eq_mul]
    ring
  have hcq : cvs D { t with q := dP X t.q } g =
      eval (vars g) (dP X t.q) * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ t.c) := by
    simp [cvs, monoM_eq, G0]
  have hca : ∀ l, cvs D (if t.a l = 0 then { t with q := 0 } else
      { t with q := C (-(t.a l : ℂ)) * t.q * dP X (qDl D.z D.z' l), a := t.a + Pi.single l 1 }) g =
      -(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c) := by
    intro l
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0]; try ring
  have hcb : ∀ l, cvs D (if t.b l = 0 then { t with q := 0 } else
      { t with q := C (-(t.b l : ℂ)) * t.q * dP X (qDbl D.z D.z' l), b := t.b + Pi.single l 1 }) g =
      -(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c) := by
    intro l
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0]; try ring
  have hcc : cvs D (if t.c = 0 then { t with q := 0 } else
      { t with q := C (-(t.c : ℂ)) * t.q * dP X (qGf D.z D.z'), c := t.c + 1 }) g =
      -(t.c : ℂ) * P0 * dG * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ (t.c + 1)) := by
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0, dG]; try ring
  have hlist : ((dscal D X t).map fun t' => cvs D t' g).sum =
      eval (vars g) (dP X t.q) * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ t.c) +
      ∑ l, (-(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c)) +
      ∑ l, (-(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c)) +
      (-(t.c : ℂ) * P0 * dG * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ (t.c + 1))) := by
    simp only [dscal, List.map_append, List.map_cons, List.map_nil, List.map_ofFn, List.sum_append,
      List.sum_cons, List.sum_nil, List.sum_ofFn, add_zero, Function.comp_def, hcq, hca, hcb, hcc]
    try ring
  rw [hlist, hsum]
  have eA : P0 * (∑ l, (-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) *
      ∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j)) * G0⁻¹ ^ t.c =
      ∑ l, (-(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c)) := by
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
  have eB : P0 * (∑ l, (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) *
      ∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j)) * G0⁻¹ ^ t.c =
      ∑ l, (-(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c)) := by
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
  linear_combination eA + eB
end Formalism.FourierDecayAlt.P.MinorPolynomials
