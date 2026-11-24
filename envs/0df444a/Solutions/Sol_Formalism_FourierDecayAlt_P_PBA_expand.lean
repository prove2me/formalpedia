-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:17:33.416422+00:00
-- url     : https://prove2.me/submissions/97cd4bd2-cdd8-46cb-b6f0-1f53900e3e3a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_mem_Wb
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_pw_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_supp_word

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
variable {S}
variable {A : Finset (Fin S.f)} {w : S.W} {n : ℕ} {U : Fin S.f → Finset (List C.Letter)}
  {θ : Fin S.f → List C.Letter → ℝ}
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v))
    (hU : ∀ v ∈ A, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ n) (hw : w.1.cnt ≤ n) (hn : n ≤ S.Ntop)
    (F : Fin S.f → List C.Letter → ℂ) :
    ∑ w' ∈ S.base.Wb n, (pθ S A w θ w' : ℂ) * ∏ v, F v (w'.1 v) =
      ∏ v, (if v ∈ A then ∑ a ∈ U v, (θ v a : ℂ) * F v a else F v (w.1 v)) := by
  classical
  have e1 : ∀ v, (if v ∈ A then ∑ a ∈ U v, (θ v a : ℂ) * F v a else F v (w.1 v)) =
      ∑ a ∈ supp S A w U v, (pw S A w θ v a : ℂ) * F v a := by
    intro v
    unfold supp pw
    by_cases hv : v ∈ A
    · simp only [if_pos hv]
    · simp [hv]
  simp only [e1]
  rw [Finset.prod_univ_sum]
  have e2 : ∀ w' : S.W, (pθ S A w θ w' : ℂ) * ∏ v, F v (w'.1 v) =
      ∏ v, (pw S A w θ v (w'.1 v) : ℂ) * F v (w'.1 v) := by
    intro w'
    unfold pθ
    push_cast
    rw [← Finset.prod_mul_distrib]
  simp only [e2]
  refine Finset.sum_bij_ne_zero (fun w' _ _ => w'.1) ?_ ?_ ?_ ?_
  · intro w' _ h
    rw [Fintype.mem_piFinset]
    intro v
    refine pw_ne_zero hP fun h0 => h ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [h0]; simp)]
  · intro a _ _ b _ _ h; exact Subtype.ext h
  · intro g hg h0
    obtain ⟨hadm, hcnt⟩ := supp_word hU hw hn hg
    exact ⟨⟨g, hadm⟩, mem_Wb S hcnt, h0, rfl⟩
  · intro w' _ _
    rfl
end Formalism.FourierDecayAlt.P.PBA
