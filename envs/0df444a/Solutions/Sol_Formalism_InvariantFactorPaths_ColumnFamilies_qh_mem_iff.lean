-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:12.251642+00:00
-- url     : https://prove2.me/submissions/28305939-bef8-48cd-8aed-4d389eb5c2f3

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_prod_castLE
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_diag_isUnit
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_zpow_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (f : GLCoord R n) :
    f ∈ inducedSections R mu ↔ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (b g : GL (Fin n) R') (u : Fin n → R'ˣ),
      (∀ a c : Fin n, a < c → b.val a c = 0) → (∀ a, (u a : R') = b.val a a) →
      evGLR (b * g) f = ((∏ a, u a ^ mu a : R'ˣ) : R') * evGLR g f := by
  have key : ∀ (R' : Type) [CommRing R'] (u : Fin n → R'ˣ),
      ((∏ a, u a ^ mu a : R'ˣ) : R') * ((∏ a, u a ^ (-(mu a)).toNat : R'ˣ) : R') =
        ((∏ a, u a ^ (mu a).toNat : R'ˣ) : R') := by
    intro R' _ u
    rw [← Units.val_mul, ← Finset.prod_mul_distrib]
    congr 2
    funext a
    exact qh_zpow_split _ _
  constructor
  · intro hf R' _ _ b g u hb hu
    have h := hf R' b g hb
    simp only [← hu] at h
    have e1 : ∏ a, (u a : R') ^ (-(mu a)).toNat = ((∏ a, u a ^ (-(mu a)).toNat : R'ˣ) : R') := by
      simp
    have e2 : ∏ a, (u a : R') ^ (mu a).toNat = ((∏ a, u a ^ (mu a).toNat : R'ˣ) : R') := by
      simp
    rw [e1, e2, ← key R' u] at h
    apply (Units.mul_left_inj (∏ a, u a ^ (-(mu a)).toNat : R'ˣ)).1
    rw [h]; ring
  · intro hf R' _ _ b g hb
    have h := hf R' b g (fun a => (qh_diag_isUnit b hb a).unit) hb (fun a => rfl)
    set u : Fin n → R'ˣ := fun a => (qh_diag_isUnit b hb a).unit with hu
    have hu' : ∀ a, b.val a a = (u a : R') := fun a => rfl
    simp only [hu']
    have e1 : ∏ a, (u a : R') ^ (-(mu a)).toNat = ((∏ a, u a ^ (-(mu a)).toNat : R'ˣ) : R') := by
      simp
    have e2 : ∏ a, (u a : R') ^ (mu a).toNat = ((∏ a, u a ^ (mu a).toNat : R'ˣ) : R') := by
      simp
    rw [e1, e2, ← key R' u, h]; ring
end Formalism.InvariantFactorPaths.ColumnFamilies
