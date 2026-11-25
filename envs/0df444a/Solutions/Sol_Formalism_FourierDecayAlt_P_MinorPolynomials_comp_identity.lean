-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.comp_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:58.558884+00:00
-- url     : https://prove2.me/submissions/621851de-e5f9-4e38-8f2c-60bb33e306fb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_list_map_sum_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_ev
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_cv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_isOpen_big_cell_set
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_mem_domL
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_Rw_cons__735539f794a9
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_shape_flatMap__3b9f0dcdf734
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_expand

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
section mk
variable [FiniteDimensional ℂ Wp]
end mk
private lemma rw_congr_on_domL (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ {H H' : Mat k r → (Wq →L[ℂ] Wp)},
      (∀ g ∈ C6.domL D L, H g = H' g) → ∀ g ∈ C6.domL D L, Rw w H g = Rw w H' g := by
  intro w
  induction w with
  | nil => intro _ H H' hH g hg; exact hH g hg
  | cons X w ih =>
    intro hw H H' hH g hg
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) hH
    rw [Rw_cons', Rw_cons', Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    have hGV : g ∈ GV k r := ((mem_domL D L g).1 hg).1
    have hV0 : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
    filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV0] with t ht
    apply ih'
    rw [mem_domL]
    exact ⟨crv_mem (x := (false, X)) (hw X (by simp)) hGV t, ht⟩
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
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {L₁ L₂ : FS k r nf}
    (hg₁ : ∀ e ∈ L₁, Good L e) (hg₂ : ∀ e ∈ L₂, Good L e) {m : ℕ} (hm : ∀ e₁ ∈ L₁, ∀ e ∈ L₂, e.2.length + e₁.2.length ≤ m)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F) {H : Mat k r → (Wq →L[ℂ] Wp)}
    (hH : ∀ g ∈ C6.domL D L, H g = shape D fib F L₂ g) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    shape D fib H L₁ g = shape D fib F (compFS D L₁ L₂) g := by
  show (L₁.map fun e => cv D fib e.1 g (Rw e.2 H g)).sum = _
  unfold compFS
  rw [shape_flatMap']
  congr 1
  refine List.map_congr_left fun e₁ he₁ => ?_
  obtain ⟨-, -, hw⟩ := hg₁ e₁ he₁
  rw [rw_congr_on_domL D L e₁.2 hw hH g hg]
  rw [expand D fib hfib L hF e₁.2 L₂ hw hg₂ (fun e he => hm e₁ he₁ e he) g hg]
  unfold shape
  rw [list_map_sum_apply, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, cv_mul, ContinuousLinearMap.mul_apply]
end Formalism.FourierDecayAlt.P.MinorPolynomials
