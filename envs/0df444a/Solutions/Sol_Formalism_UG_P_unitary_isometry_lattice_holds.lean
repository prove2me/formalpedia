-- Prove2me | solution 1 for Formalism.UG.P.unitary_isometry_lattice_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:17.381795+00:00
-- url     : https://prove2.me/submissions/41495b1c-f2b5-4903-90bb-b4bb5a6ea578

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
import Theorems.Thm_Formalism_UG_P_csEasy_formJ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix NumberField
namespace Formalism.UG.P
private lemma hform_mulVec_mulVec_of_cT_mul_mul_eq {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (J M : Matrix n n E) (x y : n → E) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (A : Matrix n n E) (u v : n → E),
      Formalism.UG.hform σ A u v = (fun i => σ (u i)) ⬝ᵥ (A *ᵥ v) := by
    intro A u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    simp [mulVec, dotProduct, map_sum]
  rw [e, e, hs, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Formalism.UG.cT]
  simp only [Matrix.mul_assoc]
private lemma hform_single_single_stabilizer_orbit_volume {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (A : Matrix n n E) (i j : n) :
    Formalism.UG.hform σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [Formalism.UG.hform, Pi.single_apply]
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Matrix NumberField
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CS.IsomUJ := by
  intro E _ σ hσ n _ _ J c hc hcσ g
  have hg : ∀ x, Formalism.UG.glEquiv g x = (g : Matrix n n E) *ᵥ x := fun x => rfl
  show Formalism.UG.cT σ (g : Matrix n n E) * J * (g : Matrix n n E) = J ↔ _
  show _ ↔ ∀ x y, _ = _
  simp only [hg, csEasy_formJ_apply, hform_mulVec_mulVec_of_cT_mul_mul_eq, mul_right_inj' hc]
  constructor
  · intro h x y
    rw [h]
  · intro h
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_single_single_stabilizer_orbit_volume, hform_single_single_stabilizer_orbit_volume] at this
end Formalism.UG.P
