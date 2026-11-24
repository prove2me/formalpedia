-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.level_product_preserves_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:27:49.97044+00:00
-- url     : https://prove2.me/submissions/5eab6007-f316-4e99-a074-70a6aa63d1ae

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_of_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_of_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_one_hermitian_curvature


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)} [SFinite μ]
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (hS : SliceIn (S := S) P z z' π π' L st K l0) (w : List (Letter ℂ S))
    (hw : WordOK P z z' π π' st l0 w) (i : Fin (P.r + 1)) :
    ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → InK (K (Fin.last P.r)) (act (levelProduct L w i.val) x) := by
  suffices H : ∀ n i, P.r - i = n → ∀ (hi : i ≤ P.r) (x : Ix S → RadSp P.k P.r z z' π π'),
      InK (K ⟨i, Nat.lt_succ_of_le hi⟩) x → InK (K (Fin.last P.r)) (act (levelProduct L w i) x) by
    intro x hx
    exact H _ i.val rfl (Nat.lt_succ_iff.mp i.isLt) x hx
  intro n
  induction n with
  | zero =>
    intro i hn hi x hx
    have hir : i = P.r := by omega
    subst hir
    rw [level_product_of_ge L w _ le_rfl, act_one_hermitian_curvature]
    exact hx
  | succ n ihn =>
    intro i hn hi x hx
    have hlt : i < P.r := by omega
    rw [show levelProduct L w i = levelProduct L w (i + 1) * bTl L ⟨i, hlt⟩ w from level_product_of_lt L w i hlt, act_mul]
    exact ihn (i + 1) (by omega) hlt (act (bTl L ⟨i, hlt⟩ w) x) (hS w hw ⟨i, hlt⟩ x hx)
end Formalism.FourierDecayAlt.P5
