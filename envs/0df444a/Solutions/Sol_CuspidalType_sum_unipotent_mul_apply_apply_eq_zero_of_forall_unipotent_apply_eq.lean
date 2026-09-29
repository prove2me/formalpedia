-- Prove2me | solution 1 for CuspidalType.sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e0753335-8757-513b-bbcd-80b7f47d92f7

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq

set_option autoImplicit false

theorem solution
    (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] {W : Type} [AddCommGroup W] [Module K W]
    (σ : Representation K (CuspidalType.GL2 q) W)
    (hN : ∀ w : W, (∀ t : ZMod q, σ (CuspidalType.unipotent q t) w = w) → w = 0)
    (V' : Type) [AddCommGroup V'] [Module K V'] (Φ : CuspidalType.GL2 q →* Module.End K V')
    (f : W →ₗ[K] V') (hf : ∀ x : CuspidalType.GL2 q, f ∘ₗ σ x = Φ x ∘ₗ f) :
    ∀ (w : W) (g : CuspidalType.GL2 q), (∑ t : ZMod q, Φ (CuspidalType.unipotent q t) * Φ g) (f w) = 0 := by
  intro w g
  classical

  have hmul : ∀ s t : ZMod q,
      CuspidalType.unipotent q s * CuspidalType.unipotent q t = CuspidalType.unipotent q (s + t) := by
    intro s t
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [CuspidalType.unipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

  have hsum : ∀ v : W, (∑ t : ZMod q, σ (CuspidalType.unipotent q t) v) = 0 := by
    intro v
    refine hN _ fun s => ?_
    rw [map_sum]
    simp_rw [← Module.End.mul_apply, ← map_mul, hmul]
    exact Fintype.sum_equiv (Equiv.addLeft s) _ _ fun t => rfl

  have hfx : ∀ (x : CuspidalType.GL2 q) (v : W), Φ x (f v) = f (σ x v) := fun x v => by
    simpa using (LinearMap.congr_fun (hf x) v).symm
  rw [LinearMap.sum_apply]
  simp_rw [Module.End.mul_apply, hfx, ← map_sum, hsum, map_zero]

end S_CuspidalType_sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq
end P2MW
export P2MW.S_CuspidalType_sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq (solution)
