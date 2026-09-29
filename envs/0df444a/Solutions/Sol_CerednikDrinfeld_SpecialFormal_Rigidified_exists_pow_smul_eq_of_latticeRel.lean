-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_of_latticeRel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a5013959-afd8-57a3-a043-3221792d10d7

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_of_latticeRel

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] {jS : Zp2 p →+* S} (E : GradedCartierModuleData p S jS)
    (n : ℕ) (r : (Fin 2 → ℤ_[p]) →+ E.NMod) (v : Fin 2 → ℚ_[p]) (ζ ζ' : E.NMod)
    (h : Rigidified.LatticeRel E n r ζ v) (h' : Rigidified.LatticeRel E n r ζ' v) :
    ∃ N : ℕ, p ^ N • ζ = p ^ N • ζ' := by
  obtain ⟨m, k, w, hv, hr⟩ := h
  obtain ⟨m', k', w', hv', hr'⟩ := h'

  have hw : p ^ m' • w = p ^ m • w' := by
    funext i
    have h1 : (p : ℚ_[p]) ^ m * v i = (w i : ℚ_[p]) := by
      have := congrFun hv i; simpa only [Pi.smul_apply, smul_eq_mul] using this
    have h2 : (p : ℚ_[p]) ^ m' * v i = (w' i : ℚ_[p]) := by
      have := congrFun hv' i; simpa only [Pi.smul_apply, smul_eq_mul] using this
    rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
    have h3 : ((p : ℚ_[p]) ^ m') * (w i : ℚ_[p]) = ((p : ℚ_[p]) ^ m) * (w' i : ℚ_[p]) := by
      rw [← h1, ← h2]; ring
    apply Subtype.ext
    push_cast
    exact h3
  have e1 : p ^ (k' + m') • (p ^ k • r w) = p ^ (k + k') • r (p ^ m' • w) := by
    rw [map_nsmul, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 1; ring
  have e2 : p ^ (k + m) • (p ^ k' • r w') = p ^ (k + k') • r (p ^ m • w') := by
    rw [map_nsmul, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 1; ring
  refine ⟨k + k' + n + m + m', ?_⟩
  calc p ^ (k + k' + n + m + m') • ζ = p ^ (k' + m') • (p ^ (k + n + m) • ζ) := by
        rw [smul_smul, ← pow_add]; congr 1; ring
    _ = p ^ (k' + m') • (p ^ k • r w) := by rw [hr]
    _ = p ^ (k + k') • r (p ^ m' • w) := e1
    _ = p ^ (k + k') • r (p ^ m • w') := by rw [hw]
    _ = p ^ (k + m) • (p ^ k' • r w') := e2.symm
    _ = p ^ (k + m) • (p ^ (k' + n + m') • ζ') := by rw [hr']
    _ = p ^ (k + k' + n + m + m') • ζ' := by
        rw [smul_smul, ← pow_add]; congr 1; ring

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_of_latticeRel
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_of_latticeRel (solution)
