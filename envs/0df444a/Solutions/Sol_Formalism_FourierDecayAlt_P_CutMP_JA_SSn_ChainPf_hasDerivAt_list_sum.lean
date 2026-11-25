-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.hasDerivAt_list_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:44.346859+00:00
-- url     : https://prove2.me/submissions/ff738e01-fb18-45b0-8478-1d4bdf37e694

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChainPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
theorem _root_.solution {ι : Type} (l : List ι) (f : ι → ℝ → E') (f' : ι → E')
    (h : ∀ i ∈ l, HasDerivAt (f i) (f' i) 0) :
    HasDerivAt (fun s => (l.map fun i => f i s).sum) (l.map f').sum 0 := by
  induction l with
  | nil => simpa using hasDerivAt_const (0 : ℝ) (0 : E')
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
