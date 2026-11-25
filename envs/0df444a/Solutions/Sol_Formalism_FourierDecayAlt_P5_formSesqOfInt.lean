-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.formSesqOfInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:23.448896+00:00
-- url     : https://prove2.me/submissions/48996fe8-9b3c-4be9-87c0-e9aa1dd75001

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_add_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_form_add_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P5_form_add_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution : FormSesqOfInt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st l0 K hI w hw i c hc x hx x' hx' y hy a
  have hK : ∀ v : Ix S → RadSp P.k P.r z z' π π', v ∈ Submodule.pi Set.univ (fun _ : Ix S => K i) → InK (K i) v :=
    fun v hv b => (Submodule.mem_pi.mp hv) b (Set.mem_univ b)
  have h1 := hI w hw i c hc x y (hK x hx) (hK y hy)
  have h2 := hI w hw i c hc x' y (hK x' hx') (hK y hy)
  have h3 := hI w hw i c hc y x (hK y hy) (hK x hx)
  have h4 := hI w hw i c hc y x' (hK y hy) (hK x' hx')
  constructor
  · show form μ i (act (RRi L st i w) (x + a • x')) y c =
      form μ i (act (RRi L st i w) x) y c + a * form μ i (act (RRi L st i w) x') y c
    rw [act_add_smul]
    exact form_add_smul_left μ i _ _ y c a h1.1 h2.1 h1.2 h2.2
  · show form μ i (act (RRi L st i w) y) (x + a • x') c =
      form μ i (act (RRi L st i w) y) x c + conj a * form μ i (act (RRi L st i w) y) x' c
    exact form_add_smul_right μ i _ x x' c a h3.1 h4.1 h3.2 h4.2
end Formalism.FourierDecayAlt.P5
