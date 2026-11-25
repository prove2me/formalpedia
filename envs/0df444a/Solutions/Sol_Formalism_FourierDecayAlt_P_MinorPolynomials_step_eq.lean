-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.step_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:13:29.01735+00:00
-- url     : https://prove2.me/submissions/478dc68c-211b-4c7e-9487-a42c68efa568

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_domL_gpos
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_nz_of_domL
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_shape_flatMap__3b9f0dcdf734
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dx
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_cv
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_list_sum_apply
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_Rw_cons__735539f794a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
private lemma ckOn_rw_of_ckOn_add_length {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)}
    {f : Mat k r → E} : ∀ (w : List (Mat k r)) (n : ℕ∞), (∀ X ∈ w, inLie k r X) →
      CkOn (n + w.length) UU f → CkOn n UU (Rw w f) := by
  intro w
  induction w with
  | nil => intro n _ hf; simpa [Rw] using hf
  | cons X w ih =>
    intro n hw hf
    rw [Rw_cons']
    refine CkOn_Dx (x := (false, X)) (hw X (by simp)) (ih (n + 1) (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) ?_)
    have e : n + 1 + (w.length : ℕ∞) = n + ((X :: w).length : ℕ∞) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    rw [e]; exact hf
private lemma hasDerivAt_shape_crv_of_good (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    ∀ Lf : FS k r nf, (∀ e ∈ Lf, Good L e) → (∀ e ∈ Lf, e.2.length + 1 ≤ m) →
      HasDerivAt (fun s => shape D fib F Lf (crv (false, X) g s)) (shape D fib F (step D X Lf) g) 0 := by
  intro Lf
  induction Lf with
  | nil =>
    intro _ _
    simp only [shape, step, List.map_nil, List.sum_nil, List.flatMap_nil]
    exact hasDerivAt_const _ _
  | cons e Lf ih =>
    intro hL hm
    have he : Good L e := hL e (by simp)
    have hgp := domL_gpos hg
    have hnz := nz_of_domL hg he
    have hcv := hasDerivAt_cv D fib hfib hX hgp e.1 hnz.1 hnz.2 he.2.1
    have hRw : CkOn 1 (GV k r) (Rw e.2 F) := by
      refine ckOn_rw_of_ckOn_add_length e.2 1 he.2.2 (sCkOn_mono ?_ hF)
      have := hm e (by simp)
      rw [add_comm]; exact_mod_cast this
    have hR : HasDerivAt (fun s => Rw e.2 F (crv (false, X) g s)) (Rw (X :: e.2) F g) 0 := by
      rw [Rw_cons']
      exact CkOn_diff (x := (false, X)) hX hRw hgp.1 hgp.1
    have hcv' := ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℝ).hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) hcv
    have h1 := hcv'.clm_apply hR
    have h2 := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) (fun e' he' => hm e' (List.mem_cons_of_mem _ he'))
    have h3 := h1.add h2
    show HasDerivAt (fun s => cv D fib e.1 (crv (false, X) g s) (Rw e.2 F (crv (false, X) g s)) +
      shape D fib F Lf (crv (false, X) g s)) _ 0
    refine h3.congr_deriv ?_
    rw [crv_zero]
    have hs : shape D fib F (step D X (e :: Lf)) g =
        shape D fib F (stepOne D X e) g + shape D fib F (step D X Lf) g := by
      simp only [step, shape_flatMap', List.map_cons, List.sum_cons]
    rw [hs]
    congr 1
    simp only [shape, stepOne, List.map_append, List.map_map, List.sum_append, Function.comp_def, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [← list_sum_apply, crv_zero]
    try rfl
end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {Lf : FS k r nf}
    (hL : ∀ e ∈ Lf, Good L e) (hm : ∀ e ∈ Lf, e.2.length + 1 ≤ m) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    RdV X (shape D fib F Lf) g = shape D fib F (step D X Lf) g := by
  have hd := hasDerivAt_shape_crv_of_good D fib hfib L hF hX hg Lf hL hm
  rw [← hd.deriv]
  exact Dx_eq (false, X) (shape D fib F Lf) g
end Formalism.FourierDecayAlt.P.MinorPolynomials
