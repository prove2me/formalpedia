-- Prove2me | solution 1 for Formalism.G.homComp_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:12.789319+00:00
-- url     : https://prove2.me/submissions/95f10ab0-c090-4f76-b801-3b146fb31fe1

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
private theorem hom_ps_subst_mv_subst {R : Type*} [CommRing R] {σ τ : Type*}
    (g : PowerSeries R) (G : MvPowerSeries σ R) (v : σ → MvPowerSeries τ R)
    (hG : MvPowerSeries.constantCoeff G = 0) (hv : MvPowerSeries.HasSubst v) :
    MvPowerSeries.subst v (g.subst G) = g.subst (MvPowerSeries.subst v G) := by
  have hG' : MvPowerSeries.HasSubst (fun _ : Unit => G) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hG
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hG' hv]
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
theorem _root_.solution : HomComp := by
  unfold HomComp
  intro R _ F G H f g hf hg
  obtain ⟨hf0, hfe⟩ := hf
  obtain ⟨hg0, hge⟩ := hg
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hvf : MvPowerSeries.HasSubst ![atX f, atY f] :=
    hom_hasSubst_pair _ _ (hom_cc_at f 0 hf0) (hom_cc_at f 1 hf0)
  have hvg : MvPowerSeries.HasSubst ![atX g, atY g] :=
    hom_hasSubst_pair _ _ (hom_cc_at g 0 hg0) (hom_cc_at g 1 hg0)
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero hf0 g hg0, ?_⟩
  rw [PowerSeries.subst_comp_subst_apply hfs hF, hfe,
    ← hom_ps_subst_mv_subst g G.toPowerSeries _ G.zero_constantCoeff hvf, hge,
    MvPowerSeries.subst_comp_subst_apply hvg hvf]
  congr 1
  funext s

  have hcoord : ∀ t : Fin 2, MvPowerSeries.subst ![atX f, atY f]
      (g.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R)) =
      PowerSeries.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R) (PowerSeries.subst f g) := by
    intro t
    rw [hom_ps_subst_mv_subst g _ _ (MvPowerSeries.constantCoeff_X t) hvf, MvPowerSeries.subst_X hvf,
      PowerSeries.subst_comp_subst_apply hfs (PowerSeries.HasSubst.X t)]
    fin_cases t <;> rfl
  fin_cases s
  · exact hcoord 0
  · exact hcoord 1
end Formalism.G
