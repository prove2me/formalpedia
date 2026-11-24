-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.cda_cvs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:06.278899+00:00
-- url     : https://prove2.me/submissions/1dffa4f1-27bf-4276-b3d5-8668c57f0dfa

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_cd_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_cd_dmin
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_cd_gf
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_cda_invpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_cda_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right


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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) {x : Mat k r} (hx : x ∈ V0 D L) : ContDiffAt ℝ ∞ (cvs D e.1) x := by
  obtain ⟨hab, -, -⟩ := he
  have hx0 : 0 < Gf k r D.z D.z' x := hx.1
  have hxL : ∀ l ∈ L, Dmin k r D.z D.z' x l ≠ 0 := fun l hl => Set.mem_iInter₂.1 hx.2 l hl
  have hlast : Dmin k r D.z D.z' x (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG := hx0
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' x ⟨r, by omega⟩))
    linarith
  have hnz : ∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' x l ≠ 0 := fun l hl => by
    rcases hab l hl with hl | rfl
    · exact hxL l hl
    · exact hlast
  have hA : ∀ l, e.1.a l = 0 ∨ Dmin k r D.z D.z' x l ≠ 0 := fun l => by
    by_cases h : e.1.a l = 0
    · exact Or.inl h
    · exact Or.inr (hnz l (Or.inl h))
  have hB : ∀ l, e.1.b l = 0 ∨ Complex.conjCLE (Dmin k r D.z D.z' x l) ≠ 0 := fun l => by
    by_cases h : e.1.b l = 0
    · exact Or.inl h
    · right
      simpa using hnz l (Or.inr h)
  show ContDiffAt ℝ ∞ (fun g => eval (vars g) e.1.q * C6.monoM D e.1.a e.1.b e.1.c g) x
  refine (cd_eval _).contDiffAt.mul ?_
  refine (cda_prod (f := fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ e.1.a l *
      (star (Dmin k r D.z D.z' g l))⁻¹ ^ e.1.b l) Finset.univ (fun l _ => ?_)).mul ?_
  · exact (cda_invpow (cd_dmin D.z D.z' l) _ (hA l)).mul
      (cda_invpow (Complex.conjCLE.contDiff.comp (cd_dmin (k := k) D.z D.z' l)) _ (hB l))
  · exact cda_invpow (cd_gf D.z D.z') _ (Or.inr (by exact_mod_cast hx0.ne'))
end Formalism.FourierDecayAlt.P.MinorPolynomials
