-- Prove2me | solution 1 for Formalism.L2.Geo.Def.G1.IsFrame.map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:13.785798+00:00
-- url     : https://prove2.me/submissions/656bcdc1-fb3c-4c94-8046-73368801520a

import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Matrix
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
variable {K : Type} [Field K] [StarRing K]
namespace Formalism.L2.Geo.Def.G1
namespace IsFrame
theorem _root_.solution {n k : ℕ} {H : Matrix (Fin n) (Fin n) K} {g w : Fin k → Fin n → K} (hf : IsFrame H g w)
    {A : Type} [CommRing A] (φ : K →+* A) (σ : A →+* A) (hσ : ∀ x, σ (φ x) = φ (star x)) (z : Fin n → A) :
    z = ∑ i, Formalism.UG.hform σ (H.map φ) (fun c => φ (w i c)) z • (fun a => φ (g i a)) := by
  funext a
  have e1 : ∀ d, φ (∑ i, g i a * ∑ c, star (w i c) * H c d) = if a = d then 1 else 0 := fun d => by
    rw [hf a d]; split_ifs <;> simp
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Formalism.UG.hform, Matrix.map_apply, hσ]
  calc z a = ∑ d, z d * (if a = d then 1 else 0) := by simp
    _ = ∑ d, z d * φ (∑ i, g i a * ∑ c, star (w i c) * H c d) := by simp only [e1]
    _ = _ := by
      simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
end IsFrame
end Formalism.L2.Geo.Def.G1
