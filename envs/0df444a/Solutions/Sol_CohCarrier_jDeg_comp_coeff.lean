-- Prove2me | solution 1 for CohCarrier.jDeg_comp_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7f4137ac-693a-5c28-b57d-7c630ce2910e

import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_comp_coeff

set_option autoImplicit false

open CohCarrier

namespace E5CoeffChange

private theorem map_diff {G : Type} [Group G] {K : Subgroup G} {C D : Type} [CommGroup C] [CommGroup D]
    (ϕ : ↥K →* C) (g : C →* D) (S T : K.LeftTransversal) [K.FiniteIndex] :
    g (Subgroup.leftTransversals.diff ϕ S T) = Subgroup.leftTransversals.diff (g.comp ϕ) S T := by
  unfold Subgroup.leftTransversals.diff
  rw [map_prod]
  rfl

private theorem map_transfer {G : Type} [Group G] {K : Subgroup G} {C D : Type} [CommGroup C]
    [CommGroup D] (ϕ : ↥K →* C) (g : C →* D) [K.FiniteIndex] (x : G) :
    g (MonoidHom.transfer ϕ x) = MonoidHom.transfer (g.comp ϕ) x := by
  rw [MonoidHom.transfer_def ϕ default, MonoidHom.transfer_def (g.comp ϕ) default, map_diff]

private theorem coresAdd_comp {G : Type} [Group G] (K : Subgroup G) [K.FiniteIndex]
    {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (φ : Additive ↥K →+ A) :
    coresAdd K (f.comp φ) = f.comp (coresAdd K φ) := by
  refine AddMonoidHom.ext fun x => ?_
  show Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight (f.comp φ))
      (Additive.toMul x)) =
    f (Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)
      (Additive.toMul x)))
  have hf : AddMonoidHom.toMultiplicativeRight (f.comp φ) =
      (AddMonoidHom.toMultiplicative f).comp (AddMonoidHom.toMultiplicativeRight φ) := by
    ext; rfl
  rw [hf, ← map_transfer]
  rfl

end E5CoeffChange

theorem solution (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type}
    [AddCommGroup A] [AddCommGroup B] {M' : ℕ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ}
    [NeZero M'] [NeZero d] (h : LevelLE M M' H H' d) (g : A →+ B) (ψ : H1 M' H' A) :
    jDeg M M' H H' d B h (g.comp ψ) = g.comp (jDeg M M' H H' d A h ψ) := by
  have hpush : pushChar M M' H H' d B h (g.comp ψ) = g.comp (pushChar M M' H H' d A h ψ) := rfl
  show coresAdd _ (pushChar M M' H H' d B h (g.comp ψ)) = g.comp (coresAdd _ (pushChar M M' H H' d A h ψ))
  rw [hpush, E5CoeffChange.coresAdd_comp]

end S_CohCarrier_jDeg_comp_coeff
end P2MW
export P2MW.S_CohCarrier_jDeg_comp_coeff (solution)
