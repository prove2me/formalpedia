-- Prove2me | solution 1 for Formalism.G.homComp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:12.339716+00:00
-- url     : https://prove2.me/submissions/9d41644f-3bda-4142-95e6-177d8b97ceb9

import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.G
private lemma constantCoeff_powerSeries_subst_eq_zero' {R : Type*} [CommRing R] {τ : Type*} {a : MvPowerSeries τ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (p : PowerSeries R)
    (hp : PowerSeries.constantCoeff p = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a p) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hp]
  · simp [ha, hd.ne']
private lemma mvPowerSeries_subst_powerSeries_subst_eq_subst_subst {R : Type*} [CommRing R] {σ τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) {b : MvPowerSeries σ R} (hb : PowerSeries.HasSubst b)
    (p : PowerSeries R) :
    MvPowerSeries.subst a (PowerSeries.subst b p) = PowerSeries.subst (MvPowerSeries.subst a b) p :=
  MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const hb) ha p
end Formalism.G
end

set_option autoImplicit false
open Formalism Formalism.G
namespace Formalism.G
theorem _root_.solution : HomComp := by
  unfold HomComp
  intro R _ F G H f g hf hg
  unfold IsHom at hf hg ⊢
  unfold atX atY at hf hg ⊢
  have hf1 : MvPowerSeries.constantCoeff f = 0 := hf.1
  have hfS : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf.1
  have hFS : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hGS : PowerSeries.HasSubst G.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
    fun i => PowerSeries.HasSubst.X i
  have hu : ∀ (p : PowerSeries R), PowerSeries.constantCoeff p = 0 → ∀ i : Fin 2,
      MvPowerSeries.constantCoeff
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) p) = 0 :=
    fun p hp i => constantCoeff_powerSeries_subst_eq_zero' (MvPowerSeries.constantCoeff_X i) p hp
  have haS : MvPowerSeries.HasSubst
      (![PowerSeries.subst (MvPowerSeries.X 0) f, PowerSeries.subst (MvPowerSeries.X 1) f] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i
    · exact hu f hf.1 0
    · exact hu f hf.1 1
  have hbS : MvPowerSeries.HasSubst
      (![PowerSeries.subst (MvPowerSeries.X 0) g, PowerSeries.subst (MvPowerSeries.X 1) g] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i
    · exact hu g hg.1 0
    · exact hu g hg.1 1
  refine ⟨constantCoeff_powerSeries_subst_eq_zero' hf1 g hg.1, ?_⟩
  rw [PowerSeries.subst_comp_subst_apply hfS hFS, hf.2, ← mvPowerSeries_subst_powerSeries_subst_eq_subst_subst haS hGS, hg.2,
    MvPowerSeries.subst_comp_subst_apply hbS haS]
  congr 1
  funext i
  fin_cases i
  · show MvPowerSeries.subst
        (![PowerSeries.subst (MvPowerSeries.X 0) f, PowerSeries.subst (MvPowerSeries.X 1) f] :
          Fin 2 → MvPowerSeries (Fin 2) R) (PowerSeries.subst (MvPowerSeries.X 0) g) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) (PowerSeries.subst f g)
    rw [mvPowerSeries_subst_powerSeries_subst_eq_subst_subst haS (hX 0), MvPowerSeries.subst_X haS,
      PowerSeries.subst_comp_subst_apply hfS (hX 0)] <;> rfl
  · show MvPowerSeries.subst
        (![PowerSeries.subst (MvPowerSeries.X 0) f, PowerSeries.subst (MvPowerSeries.X 1) f] :
          Fin 2 → MvPowerSeries (Fin 2) R) (PowerSeries.subst (MvPowerSeries.X 1) g) =
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (PowerSeries.subst f g)
    rw [mvPowerSeries_subst_powerSeries_subst_eq_subst_subst haS (hX 1), MvPowerSeries.subst_X haS,
      PowerSeries.subst_comp_subst_apply hfS (hX 1)] <;> rfl
end Formalism.G
