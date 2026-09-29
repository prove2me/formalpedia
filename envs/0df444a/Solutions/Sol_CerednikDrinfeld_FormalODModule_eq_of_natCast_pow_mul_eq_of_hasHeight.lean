-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.eq_of_natCast_pow_mul_eq_of_hasHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/43a5a7f0-40ce-5603-81ad-b5be5709d48a

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_eq_of_natCast_pow_mul_eq_of_hasHeight

set_option autoImplicit false

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X : FormalODModule p B) {h : ℕ} (hX : X.HasHeight h) (d : ℕ) (x y : MvFormalGroup.End X.F)
    (hxy : ((p ^ d : ℕ) : MvFormalGroup.End X.F) * x = ((p ^ d : ℕ) : MvFormalGroup.End X.F) * y) : x = y := by
  classical

  rw [(Nat.cast_commute (p ^ d) x).eq, (Nat.cast_commute (p ^ d) y).eq] at hxy
  have hser : ((p ^ d : ℕ) : MvFormalGroup.End X.F).toPowerSeries = X.act ((p : Zp2 p) ^ d) := by
    rw [← map_natCast X.actRingHom (p ^ d), Nat.cast_pow, FormalODModule.actRingHom_apply,
      FormalODModule.actEnd_toPowerSeries]
  have key : ∀ i, subst (X.act ((p : Zp2 p) ^ d)) (x.toPowerSeries i) = subst (X.act ((p : Zp2 p) ^ d)) (y.toPowerSeries i) := by
    intro i
    have := congrArg (fun φ : MvFormalGroup.End X.F => φ.toPowerSeries i) hxy
    simp only [MvFormalGroup.End.toPowerSeries_mul] at this
    rwa [hser] at this

  have hinj : ∀ (d : ℕ) (f g : MvPowerSeries (Fin 2) B),
      subst (X.act ((p : Zp2 p) ^ d)) f = subst (X.act ((p : Zp2 p) ^ d)) g → f = g := by
    intro d
    induction d with
    | zero =>
      intro f g hfg
      rw [pow_zero, X.act_one] at hfg
      have e : ∀ f : MvPowerSeries (Fin 2) B, subst (Series.id B) f = f := fun f =>
        congrFun (Series.comp_id (fun _ : Fin 2 => f)) 0
      rwa [e, e] at hfg
    | succ d ih =>
      intro f g hfg
      rw [X.act_pow_add d 1, pow_one] at hfg
      have hc : ∀ d : ℕ, ∀ i, constantCoeff (X.act ((p : Zp2 p) ^ d) i) = 0 := fun d => (X.isLawHom_act _).1

      have e : ∀ f : MvPowerSeries (Fin 2) B,
          subst ((X.act ((p : Zp2 p) ^ d)).comp (X.act (p : Zp2 p))) f =
            subst (X.act (p : Zp2 p)) (subst (X.act ((p : Zp2 p) ^ d)) f) := by
        intro f
        rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (hc d))
          (hasSubst_of_constantCoeff_zero (by simpa using hc 1))]
        rfl
      rw [e, e] at hfg
      exact ih f g (CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree _ (by simpa using hc 1) hX _ _ hfg)
  apply MvFormalGroup.Hom.ext
  funext i
  exact hinj d _ _ (key i)

end S_CerednikDrinfeld_FormalODModule_eq_of_natCast_pow_mul_eq_of_hasHeight
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_eq_of_natCast_pow_mul_eq_of_hasHeight (solution)
