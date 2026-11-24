-- Prove2me | solution 1 for Formalism.G.log_iff_hom_additive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:13.110639+00:00
-- url     : https://prove2.me/submissions/1decf2e1-ef10-4f15-84d0-401b7467b572

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
namespace Formalism.G
private theorem hom_hasSubst_pair {R : Type*} [CommRing R] {τ : Type*}
    (a b : MvPowerSeries τ R) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.HasSubst ![a, b] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simp [ha, hb]
private theorem hom_cc_at {R : Type*} [CommRing R] {τ : Type*} (f : PowerSeries R) (t : τ)
    (hf : constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (f.subst (MvPowerSeries.X t : MvPowerSeries τ R)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X t) f hf
end Formalism.G
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.G
namespace Formalism.G
theorem _root_.solution : LogIffHomGa := by
  unfold LogIffHomGa
  intro R _ F f

  have ga : constantCoeff f = 0 →
      MvPowerSeries.subst ![atX f, atY f] (FormalGroup.𝔾ₐ (R := R)).toPowerSeries = atX f + atY f := by
    intro h0
    have hv : MvPowerSeries.HasSubst ![atX f, atY f] :=
      hom_hasSubst_pair _ _ (hom_cc_at f 0 h0) (hom_cc_at f 1 h0)
    show MvPowerSeries.subst _ (MvPowerSeries.X 0 + MvPowerSeries.X 1) = _
    rw [← MvPowerSeries.coe_substAlgHom hv, map_add, MvPowerSeries.coe_substAlgHom,
      MvPowerSeries.subst_X hv, MvPowerSeries.subst_X hv]
    rfl
  unfold IsLog IsHom
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h0, by rw [h2, ga h0]⟩, h1⟩
  · rintro ⟨⟨h0, h2⟩, h1⟩
    exact ⟨h0, h1, by rw [h2, ga h0]⟩
end Formalism.G
