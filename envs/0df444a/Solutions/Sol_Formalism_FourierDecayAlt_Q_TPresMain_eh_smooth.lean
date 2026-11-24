-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.eh_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:12.539689+00:00
-- url     : https://prove2.me/submissions/598f414d-e888-417f-b13b-3d38db0cf33a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_exp_first_hermitian_mem_level
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_exp_second_hermitian_mem_level
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_mulX_cd
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresLie_rdV_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (p q : Fin (mdim k r i)) (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (EH k r (posL k r i p) (posL k r i q) f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  have hdF := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hF).2
  refine ⟨U, fun g => fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)) +
    Complex.I • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)),
    hU, hgU, ?_, fun g hg hgG => ?_⟩
  · exact (hdF.clm_apply (mulX_cd _).contDiffOn).add
      ((hdF.clm_apply (mulX_cd _).contDiffOn).const_smul Complex.I)
  · show RdV _ f g + Complex.I • RdV _ f g = _
    rw [rdV_ext i _ (exp_first_hermitian_mem_level p q) f F U g hU hg hgG hF hfF,
      rdV_ext i _ (exp_second_hermitian_mem_level p q) f F U g hU hg hgG hF hfF]
end Formalism.FourierDecayAlt.Q.TPresMain
