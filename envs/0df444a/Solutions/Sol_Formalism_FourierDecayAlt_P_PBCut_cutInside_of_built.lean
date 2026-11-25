-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:41:39.463709+00:00
-- url     : https://prove2.me/submissions/aa60ee07-635f-4b79-8c23-c4bb3234928a

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCutInside

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBCut
open Formalism.FourierDecayAlt NumberField
namespace Formalism.FourierDecayAlt.P.PBCut
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (h : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : KB.CutInside S := by
  obtain ⟨-, -, -, -, -, hw1, hw2, hl1, hl2, hde, -⟩ := h
  intro v Y hY
  obtain ⟨hY1, hY2⟩ := hY
  unfold C.HidaSetting.cutLo at hY1
  unfold C.HidaSetting.cutHi at hY2
  have hne1 : S.l + 1 ≠ 1 := by omega
  have hne2 : S.l + 1 ≠ (S.G.place (S.pl v)).k := by simp only [Sz.Glob.place]; omega
  have hu : ∀ de : ℕ → ℝ, (S.G.place (S.pl v)).u de (S.l + 1) =
      (S.G.place (S.pl v)).v S.l - 1 / 2 - de S.l * (S.G.place (S.pl v)).Del := by
    intro de
    unfold Sz.Cfg.u
    rw [if_neg hne1, if_neg hne2, Nat.add_sub_cancel]
  simp only [D.parOf]
  unfold I.OnCut
  rw [hu S.de, hu S.de']
  rcases hw1.1 S.l with h | h <;> rcases hw2.1 S.l with h' | h'
  · exact absurd (h.trans h'.symm) hde
  · right
    rw [h, h']
    constructor <;> linarith
  · left
    rw [h, h']
    constructor <;> linarith
  · exact absurd (h.trans h'.symm) hde
end Formalism.FourierDecayAlt.P.PBCut
