-- Prove2me | solution 1 for CerednikDrinfeld.EdgeFamily.edgeRingCharP.eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/72e73169-9a62-503f-a708-57bb149c6f0c

import Mathlib
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] {Ω : Type} [CommRing Ω]
    (f₀ : EdgeFamily.edgeRingCharP p k →+* k)
    (hf₀ : f₀.comp (algebraMap k (EdgeFamily.edgeRingCharP p k)) = RingHom.id k)
    (hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p k) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p k) = 0)
    (y : EdgeFamily.edgeRingCharP p k →+* Ω)
    (hyξ : y (EdgeFamily.edgeRingCharP.ξ p k) = 0) (hyη : y (EdgeFamily.edgeRingCharP.η p k) = 0) :
    y = (y.comp (algebraMap k (EdgeFamily.edgeRingCharP p k))).comp f₀ := by
  letI : Algebra k Ω := (y.comp (algebraMap k (EdgeFamily.edgeRingCharP p k))).toAlgebra

  let Y : EdgeFamily.edgeRingCharP p k →ₐ[k] Ω :=
    { toRingHom := y, commutes' := fun a => rfl }
  have hc : ∀ a : k, ((y.comp (algebraMap k (EdgeFamily.edgeRingCharP p k))).comp f₀) (algebraMap k (EdgeFamily.edgeRingCharP p k) a) =
      algebraMap k Ω a := by
    intro a
    show y (algebraMap k _ (f₀ (algebraMap k _ a))) = y (algebraMap k _ a)
    rw [← RingHom.comp_apply f₀, hf₀, RingHom.id_apply]
  let Y' : EdgeFamily.edgeRingCharP p k →ₐ[k] Ω :=
    { toRingHom := (y.comp (algebraMap k (EdgeFamily.edgeRingCharP p k))).comp f₀, commutes' := hc }
  have hYY : Y = Y' := by
    apply (FormalOmega.chartERing.corepEquiv k (0 : k) p Ω).injective
    apply Subtype.ext
    rw [FormalOmega.chartERing.corepEquiv_apply_val, FormalOmega.chartERing.corepEquiv_apply_val]
    show (y (EdgeFamily.edgeRingCharP.ξ p k), y (EdgeFamily.edgeRingCharP.η p k)) =
      (y (algebraMap k _ (f₀ (EdgeFamily.edgeRingCharP.ξ p k))), y (algebraMap k _ (f₀ (EdgeFamily.edgeRingCharP.η p k))))
    rw [hyξ, hyη, hf₀ξ, hf₀η, map_zero, map_zero]
  exact congrArg AlgHom.toRingHom hYY

end S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero (solution)
