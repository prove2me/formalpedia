-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.cutWord_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:51:56.121493+00:00
-- url     : https://prove2.me/submissions/c14597ce-4219-4b32-94b2-6112e437956d

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (hC : KB.CutInside S) (w : S.W) (v : Fin S.f) :
    KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := by
  have hA := w.2.1
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have h1 := hA.1 v a a.isLt
    have hnode := (hG v).2.2.2.2.2
    apply hC v
    set x := (w.1 v)[(a : ℕ)]'a.isLt with hx
    have hget : (w.1 v).get a = x := by simp [hx]
    rw [hget]
    have hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
      intro Y hY
      simp only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY
      simp only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]
      constructor <;> linarith [hY.1, hY.2]
    by_cases hp : x.1
    · rw [if_pos hp] at h1
      have hy : (∃ a, x.2 ∈ S.grid v a) ∨ x.2 ∈ S.grid1 v := by
        rcases Finset.mem_union.1 h1 with h | h
        · exact Or.inl ⟨_, h⟩
        · exact Or.inr h
      exact hcut _ (hnode _ hy).1
    · rw [if_neg hp] at h1
      have hy : (∃ a, x.2 - 1 ∈ S.grid v a) ∨ x.2 - 1 ∈ S.grid1 v := by
        rcases Finset.mem_union.1 h1 with h | h
        · exact Or.inl ⟨_, h⟩
        · exact Or.inr h
      have := hcut _ (hnode _ hy).2.1
      simpa using this
  · have h2 := hA.2 v a b a.isLt b.isLt (fun h => hab (Fin.ext h)) 0 (by norm_num) (by norm_num)
    simpa using h2
end Formalism.FourierDecayAlt.P.PBD
