-- Prove2me | solution 1 for Formalism.G.logIffHomGa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:12.912093+00:00
-- url     : https://prove2.me/submissions/951ce7fa-6c13-406a-8a6f-4277d93440d7

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
end Formalism.G
end

set_option autoImplicit false
open Formalism Formalism.G
namespace Formalism.G
theorem _root_.solution : LogIffHomGa := by
  unfold LogIffHomGa
  intro R _ F f
  unfold IsLog IsHom FormalGroup.𝔾ₐ
  have key : PowerSeries.constantCoeff f = 0 →
      MvPowerSeries.subst (![atX f, atY f] : Fin 2 → MvPowerSeries (Fin 2) R)
        (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = atX f + atY f := by
    intro h0
    have haS : MvPowerSeries.HasSubst (![atX f, atY f] : Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro i
      fin_cases i
      · exact constantCoeff_powerSeries_subst_eq_zero' (MvPowerSeries.constantCoeff_X (0 : Fin 2)) f h0
      · exact constantCoeff_powerSeries_subst_eq_zero' (MvPowerSeries.constantCoeff_X (1 : Fin 2)) f h0
    rw [MvPowerSeries.subst_add haS, MvPowerSeries.subst_X haS, MvPowerSeries.subst_X haS] <;> rfl
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h0, h2.trans (key h0).symm⟩, h1⟩
  · rintro ⟨⟨h0, h2⟩, h1⟩
    exact ⟨h0, h1, h2.trans (key h0)⟩
end Formalism.G
