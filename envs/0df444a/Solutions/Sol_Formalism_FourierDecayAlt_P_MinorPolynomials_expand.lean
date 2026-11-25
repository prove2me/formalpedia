-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:41.166944+00:00
-- url     : https://prove2.me/submissions/d5345bf6-a3fd-442f-8e99-9660f6c2e76c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_isOpen_big_cell_set
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_mem_domL
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_step_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_ev
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_good_steps
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_Rw_cons__735539f794a9
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_step_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (hF : CkOn (m : ℕ∞) (GV k r) F) :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), (∀ X ∈ w, inLie k r X) → (∀ e ∈ Lf, Good L e) →
      (∀ e ∈ Lf, e.2.length + w.length ≤ m) → ∀ g ∈ C6.domL D L,
        Rw w (shape D fib F Lf) g = shape D fib F (steps D w Lf) g := by
  intro w
  induction w with
  | nil => intro Lf _ _ _ g _; rfl
  | cons X w ih =>
    intro Lf hw hL hm g hg
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hm' : ∀ e ∈ Lf, e.2.length + w.length ≤ m := fun e he => by
      have := hm e he; simp only [List.length_cons] at this; omega
    have hev : (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) =ᶠ[𝓝 0]
        (fun t => shape D fib F (steps D w Lf) (crv (false, X) g t)) := by
      have hV : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
      filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV] with t ht
      exact ih Lf hw' hL hm' _ ((mem_domL D L _).2 ⟨crv_mem (x := (false, X)) hX hg.1 t, ht⟩)
    have hgood := good_steps D w hw' Lf hL
    have hstep := step_eq D fib hfib L hF hX (Lf := steps D w Lf) (fun e he => (hgood e he).1)
      (fun e he => by
        obtain ⟨-, e0, he0, hle⟩ := hgood e he
        have := hm e0 he0
        simp only [List.length_cons] at this
        omega) hg
    calc Rw (X :: w) (shape D fib F Lf) g
        = deriv (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) 0 := by
          rw [Rw_cons']; exact Dx_eq (false, X) _ g
      _ = deriv (fun t : ℝ => shape D fib F (steps D w Lf) (crv (false, X) g t)) 0 := hev.deriv_eq
      _ = RdV X (shape D fib F (steps D w Lf)) g := (Dx_eq (false, X) _ g).symm
      _ = shape D fib F (steps D (X :: w) Lf) g := hstep
end Formalism.FourierDecayAlt.P.MinorPolynomials
