-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.prod_lamCfg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:49.421369+00:00
-- url     : https://prove2.me/submissions/0cd6c761-6df7-4b39-8373-6644469a531b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSystemAdmissibleSize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField Finset
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Y : ℝ) : ∏ s, (Y + lamCfg S v s) = S.P v Y := by
  show ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) = (S.G.place (S.pl v)).P Y
  have hm : (S.G.place (S.pl v)).k + (S.G.place (S.pl v)).m - 1 =
      (D.parOf S v).k + 2 * (D.parOf S v).r + 1 := by
    show S.G.k + (2 * S.G.r + 2) - 1 = S.G.k + 2 * S.G.r + 1
    omega
  rw [Sz.Cfg.P, hm]
  have e1 : ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) =
      ∏ i ∈ Finset.range ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
        (Y + (S.G.place (S.pl v)).lam (i + 1)) :=
    Fin.prod_univ_eq_prod_range (fun i => Y + (S.G.place (S.pl v)).lam (i + 1)) _
  rw [e1, Finset.range_eq_Ico, Finset.prod_Ico_add' (fun i => Y + (S.G.place (S.pl v)).lam i), zero_add]
  rfl
end Formalism.FourierDecayAlt.P.CutMP
