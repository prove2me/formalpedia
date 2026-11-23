-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSubstitution.mvsubst_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:31.614784+00:00
-- url     : https://prove2.me/submissions/60f5b4b0-c1ac-4f35-abb5-e99ff91c794c

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.WeierstrassSubstitution
namespace Formalism.ELL.WeierstrassSubstitution
theorem _root_.solution {K : Type u} [Field K] {τ σ : Type} (w : PowerSeries K)
    (a : MvPowerSeries τ K) (ha : MvPowerSeries.constantCoeff a = 0)
    (b : τ → MvPowerSeries σ K) (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (w.subst a) = w.subst (MvPowerSeries.subst b a) := by
  have ha' : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply ha' hb]
end Formalism.ELL.WeierstrassSubstitution
